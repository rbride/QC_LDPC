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
//  LEVEL_OF_PARALLELIZATION: Indicates the number of Column calculations done per step. 
//      if the initial base matrix given is 20 columns of m and 4 rows, it will take 20 steps to do with Par 1
//      1 step for each Column, if its to it will take 20, and do 2 columns at a time.
//      Trades througput for dramatically increasing Resource utilization and space. 
//      Default is 1. 
//
//  ADD TO README: Common Lifting factos I've seen used for the smaller Z's 
//  | 27, 54, 81 | 28, 56, 112 | 24, 48, 96 | 48, 72, 96 |
//  All of these have some sort of metric where atleast 1 of teh smaller numbers divides evenly into one of the higher
//  values, for sake of keeping the actual design being minimized I recommend you do the same. Further it is recommended
//  that for the smallest z segment of this circuit you utilize a highest value of a z that has a Clog2(MAXZ) of 7 or less
//  And then utilize to larger values with a version of this circuit such as 192 and like 162 at a lower FMAX For middle
//  Size values, and ultimately the to be done pointer implementation that utilizes the Bram Memory for Z=352 for
//  Large data outputs You can achieve higher FMAX by using a subset like 24, 48, and 96 or 28, 56, 112, 
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
module QCLDPCEncoderController #(
    parameter int NUM_SUP_Z                         =               3,
    parameter int MAXZ                              =               81,
    parameter int IBLKS_NUM                         =               20,
    parameter int NUM_PBLKS                         =               4,         
    parameter int ROM_TYPE                          =               1,          
    parameter int Z_VALUE_ARRAY[NUM_OF_SUPPORTED_Z] =               {27, 54, 81},
    parameter int ROTATES_PER_CYCLE                 =               1,      
    parameter int NUM_ACCUM_PIPE_SPLITS             =               2,      //Starting with 2 
 
    //ROM Related Local Params
    localparam int PmRomDepth = (IBLKS_NUM+NUM_PBLKS) * NUM_PBLKS * NUM_SUP_Z,
    localparam int PmRomWidth = $clog2(MAXZ),
    localparam int PmRomAddrW = $clog2(PmRomDepth),

    localparam int PipelineCntrDepth = $clog2(IBLKS_NUM)
)(
    input logic CLK, rst_n, in_valid, in_last, //In_valid and in_last for handshake signals 
    output logic in_ready,
    input logic [NUM_SUP_Z-1:0] req_z,  //Unused in ROM_Type 0 Highest Value corresponds to  
    input  logic [MAXZ-1:0]                           i_data,   
    output logic [(MAXZ*(NUM_PBLKS+IBLKS_NUM))-1:0]   p_data_out
);
    // -------------------------------------------------------------------------
    // 
    // -------------------------------------------------------------------------
    localparam int NumNonFactorSupportedLens = 1;

    // -------------------------------------------------------------------------    
    // Declaration of Internal Module Signals
    // -------------------------------------------------------------------------    
    pipeline_pkt_t rot_pkt_in  [NUM_PBLKS-1:0];
    pipeline_pkt_t rot_pkt_out [NUM_PBLKS-1:0];
    

    logic [MAXZ:0] rotator_o [NUM_PBLKS-1:0];   
    //2 accumulator registers for each Parity block for Register Ping ponging 
    logic [MAXZ:0] accum_regs [0:NUM_PBLKS-1][0:NUM_ACCUM_PIPE_SPLITS-1][0:1]; 
    logic [MAXZ-1:0] parity_blk[(NUM_PBLKS*MAXZ)-1:0];    

    logic [PmRomAddrW-1:0] shift_addr;
    logic [PmRomWidth-1:0] shift_values [0:(NUM_PBLKS)-1]; 


    //Calculate # of stages of the Shifter Pipeline, to determine the needed Valid depth
    localparam int numPipelineSteps = ($clog2(MAXZ) % ROTATES_PER_CYCLE  != 0) ?
                                      (($clog2(MAXZ) / ROTATES_PER_CYCLE) +1 )  :
                                      ($clog2(MAXZ) / ROTATES_PER_CYCLE);

    logic valid_flag_pipe; 
    //not -1 because the highest bit is used to select the Accumulation Register Bank
    logic [$clog2(IBLKS_NUM):0]    pipeline_cnt;

    
    



    // -------------------------------------------------------------------------    
    // Generate ROM
    //      The BRAM Rom is there for the currently not started Pointer Rotation
    //      Morph of this codebase for Z's of like 256 and 352. in the 3DPP Spec
    //      The Single LUT Rom is there for either single Z designs like a 
    //      Second rotator for the IEEE Spec version
    // -------------------------------------------------------------------------    
    generate
        case (ROM_TYPE)
            0: begin : Single_LUT_ROM
                ProtoMatrixRom_SingleLUT #(   
                        .THE_Z(MAXZ), .NUM_PARITY_BLKS(NUM_PBLKS), .WIDTH(PmRomWidth), 
                        .DEPTH(PmRomDepth), .ADDRW(PmRomAddrW)
                    )  
                    GenROM (
                        .addr(shift_addr),  .data_out(shift_values)
                    );
            end

            1: begin : Multi_LUT_ROM 
                ProtoMatrixRom_MultiLUT #(
                        .NUM_Z(NUM_SUP_Z), .Z_VALUES(Z_VALUE_ARRAY), .NUM_PARITY_BLKS(NUM_PBLKS),
                        .DEPTH(PmRomDepth), .WIDTH(PmRomWidth), .ADDRW(PmRomAddrW)
                    )
                    GenROM (
                        .addr(shift_addr),.data_out(shift_values)
                    ); 
            end
            
            // //Same for .data_out since multidimentional 
            // 2: begin : BRAM_ROM
            //     ProtoMatrixRom_BRAM #(
            //             .NUM_Z(NUM_SUP_Z), .NUM_PARITY_BLKS(NUM_PBLKS), .Z_VALUES(Z_VALUE_ARRAY),
            //             .DEPTH(PmRomDepth), .WIDTH(PmRomWidth), .ADDRW(PmRomAddrW)
            //         )
            //         GenRom (
            //             .CLK(CLK), .addr(shift_addr),.data_out(shift_values)
            //         );
            // end 

            default: begin : assert_invalid_cfg
                $fatal(1, "Invalid ROM Configuration Selected - Aborting");
            end
        endcase 
    endgenerate


    // -------------------------------------------------------------------------    
    // Generate the requested pipelined Circular Shifter for MAXZ and any others
    // Requested for the Z's given
    // -------------------------------------------------------------------------    
    genvar nori; 
    generate
        for(nori=0; nori<NUM_PBLKS; nori++) begin
            pipelinedCircularShifter #(
                .MAXZ(MAXZ), .ROTATES_PER_CYCLE(ROTATES_PER_CYCLE)
            )
            circ_shftr_inst (
                .CLK(CLK), .rst_n(rst_n), .valid_in(valid_flag_pipe), 
                .in_data(i_data_processed), .shift_val(shift_values[nori]),
                .out_data(rotator_o[nori][MAXZ-1:0]), .valid_out(rotator_o[nori][MAXZ])
            );
        end
    endgenerate


    // +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++    
    //  Process 1:  Check the valid and ready handshake to feed valid into Pipe
    //              Zero pad input into pipeline if is is not width of Max Z
    // +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++    

    
    
    always_ff @(posedge CLK) begin
        if(!rst_n) begin
            i_data_processed    <= '0;
            shift_addr          <= '0;
            valid_flag_pipe     <= '0;
        end else begin
            // FIXME : Note to the user, it as of this moment chose to save time by not writing code
            // to manage the input of case statement so that if the number of possible combinations changes
            // from the default 3 it is dealt with automatically so you have to change it yourself manually as of now 
            unique case (req_z)
                //The lowest bit corresponds to a selection of the first item in the array
                3'b001 : begin 
                    //27 has great extraction because it fits neatly into 81
                    i_data_processed <= {i_data[(Z_VALUE_ARRAY[0]-1):0], i_data[(Z_VALUE_ARRAY[0]-1):0], i_data[(Z_VALUE_ARRAY[0]-1):0]};
                    shift_addr <= '0;   //************ IT SHOULD BE FINE AN INFERED COMBINATIONAL LINE WITH THE COMPILER 
                end
                3'b010 : begin 
                    i_data_processed <= {{ (MAXZ-Z_VALUE_ARRAY[1]){1'b0} }, i_data[(Z_VALUE_ARRAY[1]-1):0] };
                    shift_addr <= PmRomAddrW'(PmRomDepth/NUM_SUP_Z)-1;
                end
                3'b100 : begin 
                    i_data_processed <= i_data;
                    shift_addr <= PmRomAddrW'(PmRomDepth/NUM_SUP_Z*2)-1;
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

