`timescale 1ns / 1ps
import qcldpcPkg::*;
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Author: Ryan Bride 
// Create Date: 09/09/2025
// Module Name: Highspeed Paramatized QC-LDPC Encoder
// Description: 
//      The top level of this design takes a generic input that is the width of the 
//      defined maximum Z. For implementation inside an actual design, I would suggest 
//      Implementing a more robust FIFO or whatever you find best suits your Design.
//      Further the top level of the Controller stores all provided information data into
//      a singular buffer, for space reasons the fifo that I suggested would ideally be storing that
//      to instead of having a random very long buffer just sitting in this, 
//
//  The following Parameters Effect the architectural structure of the module. All other values Throw and Error
//  ROM_TYPE:  Chooses the Selected ROM Structure used to store Protoype Matrix/Shift Values. 
//      0 = Single-Rate LUT Based Rom (i.e only one speed and one Proto Matrix defined for that speed)   
//      1 = Multi-RATE LUT, Simple LUT Based rom that supports 3 seperate Z's
//      2 = BRAM Based ROM Supporting 3 Seperate Z's, shouldn't be used for this version of the QCLDPC
//
//  TODO: ADD the fact that Req_Z is static to readme
//  TODO  add to readme that Z_VALUE_ARRAY MUST Must be ordered Smallest to largest.
//        already throwing an error for this in the Config Check 
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
module QCLDPCEncoderController #(
    parameter int NUM_SUP_Z                              =      3,
    parameter int MAXZ                                   =      81,
    parameter int IBLKS_NUM                              =      20,
    parameter int NUM_PBLKS                              =      4,         
    parameter int ROM_TYPE                               =      1,          
    parameter int Z_VALUE_ARRAY[0:NUM_OF_SUPPORTED_Z-1]  =      {27, 54, 81}, 
    parameter int ROTATES_PER_CYCLE                      =      1,      
    parameter int NUM_ACCUM_PIPE_SPLITS                  =      2,                //Increase for more Head Room
    
    localparam int Gen_Dedicated_Rot    =  detr_nonfactor_z( MAXZ, Z_VALUE_ARRAY, NUM_SUP_Z );
    localparam int NonFactorZMask       =  nonfactor_z_mask( MAXZ, Z_VALUE_ARRAY, NUM_SUP_Z );
    
    localparam int PmRomDepth           = (IBLKS_NUM+NUM_PBLKS) * NUM_PBLKS * (NUM_SUP_Z - Gen_Dedicated_Rot),
    localparam int PmRomWidth           = $clog2(MAXZ),
    localparam int PmRomAddrW           = $clog2(PmRomDepth),
    //Non Factor Z LUT Rom
    localparam int NFZPmRomDepth        = (IBLKS_NUM+NUM_PBLKS) * NUM_PBLKS * Gen_Dedicated_Rot;
    localparam int NFZPmRomWidth        = $clog2(Z_VALUE_ARRAY[(Gen_Dedicated_Rot == 0) ? 1 : Gen_Dedicated_Rot]);   //Default to 1 to avoid compile errors from verilator 
    localparam int NFZPmRomAddrW        = $clog2(NFZPmRomDepth)
)(
    input  logic CLK,   rst_n, in_valid,   in_last,   //In_valid and in_last for handshake signals 
    input  z_req_t req_z,           //STATIC, 3'b100 is 27, 3'b010 is 54, 3'b001 is 81, regardless of how many req_z, change it in Package
    input  logic [MAXZ-1:0]                         i_data,   
    output logic [MAXZ*(NUM_PBLKS+IBLKS_NUM)-1:0]   p_data_out,
    output logic in_ready
);
    //**************************************************************************************************************
    // Configuration check/error handling Etc
    //**************************************************************************************************************
    generate
        if ( ROM_TYPE > 1 )
            initial $fatal(1, "Invalid ROM_TYPE=%0d \n  Supported Values are 1 and 0",ROM_TYPE);
        if (Gen_Dedicated_Rot > 1) begin
            initial $fatal(1, "Invalid Configuration, design supports only 1 non factor of MaxZ, Z value \
                your design has %0d non factor of MaxZ Z values requesting to be supported", Gen_Dedicated_Rot );
        end
        for (genvar i = 0; i < NUM_SUP_Z - 1; i++) begin : Z_ORDER_CHECK
            if (Z_VALUE_ARRAY[i] >= Z_VALUE_ARRAY[i+1]) begin
                initial $fatal(1, "Z_VALUE_ARRAY must be ordered least to greatest. \
                    Z_VALUE_ARRAY[%0d]=%0d >= Z_VALUE_ARRAY[%0d]=%0d", i, Z_VALUE_ARRAY[i], i+1, Z_VALUE_ARRAY[i+1]);
            end
        end
    endgenerate
    property req_z_onehot;
        @(posedge CLK) disable iff (!rst_n)
        $onehot(req_z);
    endproperty
    assert property (req_z_onehot)
        else $fatal(1, "req_z not one-hot: %0b", req_z);
    //**************************************************************************************************************
    //**************************************************************************************************************
    // -------------------------------------------------------------------------    
    // Declaration of Internal Module Signals
    // -------------------------------------------------------------------------    
    pipeline_pkt_t pkt_per_lane [0:NUM_PBLKS-1];  pipeline_pkt_t pkt_per_lane_NFZ [0:NUM_PBLKS-1];
    logic [PmRomAddrW-1:0] rom_offsets [0:NUM_SUP_Z-1];   //Used to generate constants in a generate function for ram offsets  

    wire  [MAXZ-1:0] i_data_proc [0:NUM_SUP_Z-1];
    pipeline_pkt_t rot_pkt_o_MaxZ   [0:NUM_PBLKS-1];  pipeline_pkt_t rot_pkt_o_NFZ    [0:NUM_PBLKS-1];    

    logic [PmRomAddrW-1:0]     shift_rom_addr;      logic [PmRomWidth-1:0]     shift_rom_out     [0:NUM_PBLKS-1]; 
    logic [NFZPmRomAddrW-1:0]  shift_rom_addr_NFZ;  logic [NFZPmRomWidth-1:0]  shift_rom_out_NFZ [0:NUM_PBLKS-1]; 
    
    logic [MAXZ:0] rotator_o [NUM_PBLKS-1:0];   
    //2 accumulator registers for each Parity block for Register Ping ponging 
    logic [MAXZ:0] accum_regs [0:NUM_PBLKS-1][0:NUM_ACCUM_PIPE_SPLITS-1][0:1]; 
    logic [MAXZ-1:0] parity_blk[(NUM_PBLKS*MAXZ)-1:0];    
    
    logic [$clog(IBLKS_NUM)-1:0] colm_cnt; 

    //==========================================================================    
    // Generate ROM
    //   The BRAM Rom is there for the currently not started Pointer Rotation
    //   Morph of this codebase for Z's of like 256 and 352. in the 3DPP Spec
    //   The Single LUT Rom is there for either single Z designs     
    //==========================================================================-    
    generate
        case (ROM_TYPE)
            0: begin : Single_LUT_ROM
                ProtoMatrixRom_SingleLUT #(   
                        .THE_Z(MAXZ), .NUM_PARITY_BLKS(NUM_PBLKS), 
                        .WIDTH(PmRomWidth), .DEPTH(PmRomDepth), .ADDRW(PmRomAddrW)
                    )  
                    GenROM (  .addr(shift_rom_addr),  .data_out(shift_rom_out)  );
            end
            1: begin : Multi_LUT_ROM 
                ProtoMatrixRom_MultiLUT #(
                        .NUM_Z(NUM_SUP_Z), .Z_VALUES(Z_VALUE_ARRAY), .NUM_PARITY_BLKS(NUM_PBLKS),
                        .DEPTH(PmRomDepth), .WIDTH(PmRomWidth), .ADDRW(PmRomAddrW)
                    )
                    GenROM (  .addr(shift_rom_addr),.data_out(shift_rom_out)    ); 
            end  
            // 2: begin : BRAM_ROM
            //     ProtoMatrixRom_BRAM #(
            //             .NUM_Z(NUM_SUP_Z), .NUM_PARITY_BLKS(NUM_PBLKS), .Z_VALUES(Z_VALUE_ARRAY),
            //             .DEPTH(PmRomDepth), .WIDTH(PmRomWidth), .ADDRW(PmRomAddrW)
            //         ) GenRom ( .CLK(CLK), .addr(shift_addr),.data_out(shift_values) );
            // end 
            default: begin : assert_invalid_cfg
                $fatal(1, "Invalid ROM Configuration Selected - Aborting");
            end
        endcase
        
        //Generate second single format Look up table for second dedicated Rot
        if(Gen_Dedicated_Rot) begin
            ProtoMatrixRom_SingleLUT #(
                .THE_Z(Z_VALUE_ARRAY[NonFactorZMask]),  .NUM_PARITY_BLKS(NUM_PBLKS), 
                .WIDTH(NFZPmRomWidth), .DEPTH(NFZPmRomDepth), .ADDRW(NFZPmRomAddrW)
            )
            GenROMDedicateROT ( .addr(shift_addr_NFZ),  .data_out(shift_values_NFZ)  );
        end
    endgenerate
    //==========================================================================    
    // Generate the requested pipelined Circular Shifter for MAXZ and Z=54
    //==========================================================================    
    genvar nori, allen;         //<-- Named after my cats lovely!      
    generate
        for(nori=0; nori<NUM_PBLKS; nori++) begin : MAXZ_SHIFTER_INST
            (* keep_hierarchy = "yes" *)
            pipelinedCircularShifter #( .MAXZ(MAXZ), .ROTATES_PER_CYCLE(ROTATES_PER_CYCLE) )
            circ_shftr_inst (
                .CLK( CLK ), .rst_n( rst_n ), .pkt_i( pkt_per_lane[nori] ), .pkt_o( rot_pkt_o_MaxZ[nori] )        );
        end
    endgenerate
    generate 
        if(Gen_Dedicated_Rot) begin  
            for(allen=0; allen<NUM_PBLKS; allen++) begin : DEDICATED_NON_FACTOR_SHIFTER_INST
                (* keep_hierarchy = "yes" *)
                pipelinedCircularShifter #(
                    .MAXZ(Z_VALUE_ARRAY[NonFactorZMask]), .ROTATES_PER_CYCLE(ROTATES_PER_CYCLE) )
                circ_shftr_inst (
                    .CLK( CLK ), .rst_n( rst_n ), .pkt_i( pkt_per_lane_NFZ[allen] ), .pkt_o( rot_pkt_o_NFZ[allen] ) ); 
            end
        end else begin 
             assign rot_pkt_o_NFZ = '{default: '0};  //Assign it to 0 if not there 
        end 
    endgenerate
    // +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++    
    //  Process 1:  PRE-PROCESSING
    //      Loading data into the registers that feed the Rotators 
    //      Check the valid and ready handshake to feed valid into Pipe
    //      Zero pad input into pipeline if is is not width of Max Z        
    // +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++    
    //Constant Generate Function to attach the wires correctly to rotator inputs, and generate ram OFFsets dynamically
    //To support a config specifying any subset of the 3 Z's and maintain functionality regardless
    //This is a generate fuction to remove any runtime logic in determining the i_data part and the Rom Offset calc 
    //is here to keep both operations together in the code instead of one being a function in the pkg file or
    genvar ipz;
    generate
        for(ipz=0; ipz<NUM_SUP_Z; ipz++) begin
            localparam int tilecnt = MAXZ / Z_VALUE_ARRAY[ipz]
            //Factor so Tile
            if(MAXZ % Z_VALUE_ARRAY[ipz] == 0) begin  
                localparam int widthz  = Z_VALUE_ARRAY[ipz];
                assign i_data_proc[ipz] = { tilecnt{pkt_in.data[widthz-1:0]} };
            end 
            //Nonfactor so pad 
            else   
                assign i_data_proc[ipz] = { (MAXZ-widthz){1'b0}, pkt_in.data[widthz-1:0]}; 

            //Generate ROM Address offsets
            if( Gen_Dedicated_Rot==1 && (ipz == NonFactorZMask)) 
                assign rom_offsets[ipz] = { PmRomAddrW{1'b0} };
            else 
                assign rom_offsets[ipz] = PmRomAddrW'(ipz * (NUM_INFO_BLKS + NUM_PARITY_BLKS) * NUM_PARITY_BLKS);
        end
    endgenerate

    //Combinational logic to get ROM Addresses, #TODO, investigate the critical path implications, this adds to the 
    //overall logic of the first step, if necessary consider pushing out to its own step to decrease critical path of This step
    //Could even do something super wacky too. Ideas abound! 
    always_comb begin
        shift_rom_addr     = '0;
        shift_rom_addr_NFZ = '0;
        for(int gzdoom=0; gzdoom<NUM_SUP_Z; gzdoom++)begin
            if(req_z[i])
        end
    end

    always_ff @(posedge CLK) begin
        if(!rst_n) begin
            pkt_in_processed           <= '0;
            pkt_in_processed_NFZ       <= '0;
            shift_addr                 <= '0;
            shift_addr_NFZ             <= '0
        end else begin
            pkt_in_processed.valid     <= 1'b0;
            pkt_in_processed.last      <= in_last;
            pkt_in_processed.data      <= '0;
            pkt_in_processed.svals     <= '0;

            pkt_in_processed_NFZ.valid <= 1'b0;  
            pkt_in_processed_NFZ.last  <= in_last;
            pkt_in_processed_NFZ.data  <= '0;
            pkt_in_processed_NFZ.svals <= '0;
            
            unique case (req_z)
                Z_27 : begin
                    pkt_in_processed.data       <= i_data_proc[0];
                    pkt_in_processed.valid      <= (in_valid && in_ready);
                    pkt_in_processed.svals      <= 
                end
                Z_54 : begin
                    
                end
                
                3'b100 : begin 
                    

                    i_data_processed <= {i_data[(Z_VALUE_ARRAY[0]-1):0], i_data[(Z_VALUE_ARRAY[0]-1):0], i_data[(Z_VALUE_ARRAY[0]-1):0]};
                end
                3'b010 : begin 
                    i_data_processed <= {{ (MAXZ-Z_VALUE_ARRAY[1]){1'b0} }, i_data[(Z_VALUE_ARRAY[1]-1):0] };
                end
                3'b100 : begin 
                    i_data_processed <= i_data;
                    
                end
                default : begin 
                    i_data_processed <= '0;
                    shift_addr <= '0;
                end
            endcase
                
            //Actual Fire instruction is this 
            if(in_valid && in_ready)
                valid_flag_pipe <= '1;
            else 
                valid_flag_pipe <= '0;     
                                    shift_addr <= '0;   //************ IT SHOULD BE FINE AN INFERED COMBINATIONAL LINE WITH THE COMPILER 
                    shift_addr <= PmRomAddrW'(PmRomDepth/NUM_SUP_Z*2)-1;
                    shift_addr <= PmRomAddrW'(PmRomDepth/NUM_SUP_Z)-1; 
        end
    end
    // +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++    
    // Process 2: feed Accumulators with output of Pipelined Rotators, and 
    //            Manage accumulators and block count, then when frame is complete
    //            output to Final step of generating final parity.  
    // +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++    
    //-------------------------------------------------------------------------
    // Count the pipeline value, & flip the top bit to select the right accum bank
    //-------------------------------------------------------------------------
    always_ff @(posedge CLK) begin
        if(!rst_n) begin
            pipeline_cnt <= '0;
        end else begin
            //Decided to use the middle accumulator to theoretically reduce fanout for all rotators 
            if((rotator_o[(NUM_PBLKS/2)][MAXZ]) == 1'b1) begin
                pipeline_cnt <= (pipeline_cnt[$clog2(IBLKS_NUM)-1:0] == PipelineCntrDepth'(IBLKS_NUM-1)) ?  
                                { ~pipeline_cnt[$clog2(IBLKS_NUM)], {($clog2(IBLKS_NUM)){1'b0}} }  :
                                pipeline_cnt + 1;
            end else 
                pipeline_cnt <= pipeline_cnt;
        end
    end
    //-------------------------------------------------------------------------   
    // Generate the logic to send output of each rotator to the accums regs
    // -------------------------------------------------------------------------    
    genvar jj; 
    //reg [MAXZ:0] accum_regs [0:$clog2(NUM_PBLKS)-1][NUM_ACCUM_PIPE_SPLITS][0:1]; 
    generate 
        for(jj=0; jj<NUM_PBLKS; jj++) begin
            logic last_in_frame;
            
            always_ff @(posedge CLK) begin
                if(!rst_n) begin
                    last_in_frame   <= '0;   
                    for (int i=0; i<=$clog2(NUM_PBLKS); i++) begin
                        for (int j=0; j<=NUM_ACCUM_PIPE_SPLITS; j++) begin
                            for (int k=0; k<=1; k++) begin
                                accum_regs[i][j][k] <= '0;
                            end
                        end
                    end
                end else begin
                    //Throw the last indicate 
                    if(!(last_in_frame && pipeline_cnt[$clog2(IBLKS_NUM)])) begin
                        last_in_frame <= ~last_in_frame;
                        accum_regs[jj][1][last_in_frame][MAXZ] <= 1; 
                    end
                    
                    //If local Rotator out is giving a valid, then read it into stuff
                    if(rotator_o[jj][MAXZ]) begin
                        unique case (req_z)
                            //The lowest bit corresponds to a selection of the first item in the array
                            3'b001 : begin 
                                accum_regs[jj][0][pipeline_cnt[$clog2(IBLKS_NUM)]][MAXZ-1:0] 
                                    <= { {(MAXZ-Z_VALUE_ARRAY[0]){1'b0}}, rotator_o[jj][(Z_VALUE_ARRAY[0]-1):0] };
                                accum_regs[jj][0][pipeline_cnt[$clog2(IBLKS_NUM)]][MAXZ] <= 0; 
                            end
                            
                            3'b010 : begin 
                                accum_regs[jj][0][pipeline_cnt[$clog2(IBLKS_NUM)]] 
                                    <= { (MAXZ+1){1'b0} }; //this one is broken #FIXME needs the LUT map and stuff     
                                accum_regs[jj][0][pipeline_cnt[$clog2(IBLKS_NUM)]][MAXZ] <= 0;         
                            end
                            3'b100 : begin 
                                accum_regs[jj][0][pipeline_cnt[$clog2(IBLKS_NUM)]][MAXZ-1:0] <= rotator_o[jj][MAXZ-1:0];
                                accum_regs[jj][0][pipeline_cnt[$clog2(IBLKS_NUM)]][MAXZ] <= 0; 
                            end
                            default : begin 
                                accum_regs[jj][0][pipeline_cnt[$clog2(IBLKS_NUM)]] <= '0;
                                accum_regs[jj][0][pipeline_cnt[$clog2(IBLKS_NUM)]][MAXZ] <= 0; 
                            end
                        endcase
                    end
                    else begin
                        accum_regs[jj][0][pipeline_cnt[$clog2(IBLKS_NUM)]] <= '0; //Just input a zero it doesn't matter
                    end


                    //CURRENTLY ASSUMING NO PIPELINE #TODO Take this into account for N=192
                    accum_regs[jj][1][0][MAXZ-1:0] <= accum_regs[jj][0][0][MAXZ-1:0] ^ accum_regs[jj][0][0][MAXZ-1:0];
                    accum_regs[jj][1][1][MAXZ-1:0] <= accum_regs[jj][0][1][MAXZ-1:0] ^ accum_regs[jj][0][1][MAXZ-1:0];
                    
                end
            end        
        end
    endgenerate
    




    
    
     
endmodule


