`timescale 1ns / 1ps
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
//      2 = BRAM Based ROM Supporting 3 Seperate Z's  
//  
//  LEVEL_OF_PARALLELIZATION: Indicates the number of Column calculations done per step. 
//      if the initial base matrix given is 20 columns of m and 4 rows, it will take 20 steps to do with Par 1
//      1 step for each Column, if its to it will take 20, and do 2 columns at a time.
//      Trades througput for dramatically increasing Resource utilization and space. 
//      Default is 1. 
//  
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
module QCLDPCEncoderController #(
    parameter int NUM_OF_SUPPORTED_Z                =               3,
    parameter int HIGHEST_SUPPORTED_Z_VAL           =               81,
    parameter int NUM_INFO_BLKS_PER_CODE_BLK        =               20,
    parameter int NUM_PARITY_BLKS_PER_CODE_BLK      =               4,         
    parameter int ROM_TYPE                          =               1,          
    parameter int Z_VALUE_ARRAY[NUM_OF_SUPPORTED_Z] =               {27, 54, 81},
    parameter int LEVEL_OF_PARALLELIZATION          =               1,
    parameter int ROTATES_PER_CYCLE                 =               1,      //TODO: CHANGE THIS NAME
    // -------------------------------------------------------------------------    
    // LocalParam Defines, a Lot of them are alias for readability
    // -------------------------------------------------------------------------    
    //Creating Alias for readability and to shorten code lines, Originally this
    //Was outside of the top decl but verilator strictly enforces
    //All ports being inside so I had to move it back up here, 
    // #TODO: CLEAN IT UP
    localparam int MaxZ        = HIGHEST_SUPPORTED_Z_VAL,
    localparam int NumPBlks    = NUM_PARITY_BLKS_PER_CODE_BLK,
    localparam int IBlksNum    = NUM_INFO_BLKS_PER_CODE_BLK,
    localparam int ZsN         = NUM_OF_SUPPORTED_Z,
    localparam int PLvl        = LEVEL_OF_PARALLELIZATION,
    //ROM Related Local Params
    localparam int PmRomDepth = (IBlksNum+NumPBlks) * NumPBlks * ZsN,
    localparam int PmRomWidth = $clog2(MaxZ),
    localparam int PmRomAddrW = $clog2(PmRomDepth)
)(
    input logic CLK,
    input logic rst_n,
    //Handshake Signals
    input logic in_valid,
    input logic in_last,
    output logic in_ready,

    //TODO assert   assert property (@(posedge clk) $onehot(req_Z)) 
    input logic [ZsN-1:0] req_z,  //Unused in ROM_Type 0 Highest Value corresponds to 
    input  logic [(MaxZ*PLvl)-1:0]                  i_data,
    output logic [(MaxZ*(NumPBlks+IBlksNum))-1:0]   p_data_out
    
);
    // -------------------------------------------------------------------------    
    // Declaration of Internal Module Signals
    // -------------------------------------------------------------------------    
    reg [MaxZ-1:0] i_data_processed;
    //Tbh could be wire Top bit stays for the purpose of the valid out
    logic [NumPBlks*PLvl-1:0][MaxZ:0] rotator_o;

    logic [MaxZ-1:0] parity_blk[(NumPBlks*MaxZ)-1:0];    

    //Define storage registers for the intermediate values used by accumulators one for each generated Parity Block
    reg [MaxZ-1:0] accum_regs [0:$clog2(NumPBlks)-1]; 
    
    logic shift_addr  [PmRomAddrW-1:0];   
    logic [PmRomWidth-1:0] shift_values [0:(NumPBlks*PLvl)-1];

    //output of the rotate functions
    logic [MaxZ-1:0] rotated_data [0:$clog2(NumPBlks*PLvl)-1];

    logic [$clog2(IBlksNum/PLvl)-1:0] c_cnt;

    //Calculate # of stages of the Shifter Pipeline, to determine the needed Valid depth
    //TODO: Remove this from the Pipelined Shifter code and make it a parameter MAYBE
    localparam int numPipelineSteps = ($clog2(MaxZ) % ROTATES_PER_CYCLE  != 0) ?
                                      (($clog2(MaxZ) / ROTATES_PER_CYCLE) +1 )  :
                                      ($clog2(MaxZ) / ROTATES_PER_CYCLE);

    logic [numPipelineSteps+1:0]  valid_flag_pipe; 
    //No reason to take make this one hot, it has the time to check the lower bits, just make the 
    //The highest bit its one flag for a quick check on the cycle after the computation is done
    //So don't -1
    logic [$clog2(IBlksNum):0]    pipeline_cnt;

    typedef enum  logic {IDLE, LOAD, GEN_PARITY, PUSH_DATA} state_t;

    // -------------------------------------------------------------------------    
    // Generate ROM
    // TODO: Add more asserts to throw errors when the value provide is invalid.
    // -------------------------------------------------------------------------    
    generate
        case (ROM_TYPE)
            0: begin : Single_LUT_ROM
                ProtoMatrixRom_SingleLUT #(   
                        .THE_Z(MaxZ), .NUM_PARITY_BLKS(NumPBlks), .WIDTH(PmRomWidth), 
                        .DEPTH(PmRomDepth), .ADDRW(PmRomAddrW), .P_LVL(PLvl)
                    )  
                    GenROM (
                        .addr(shift_addr),  .data_out(shift_values)
                    );
            end

            1: begin : Multi_LUT_ROM 
                ProtoMatrixRom_MultiLUT #(
                        .NUM_Z(ZsN), .Z_VALUES(Z_VALUE_ARRAY), .NUM_PARITY_BLKS(NumPBlks),
                        .DEPTH(PmRomDepth), .WIDTH(PmRomWidth), .ADDRW(PmRomAddrW), .P_LVL(PLvl)
                    )
                    GenROM (
                        .addr(shift_addr),.data_out(shift_values)
                    ); 
            end
            
            //TODO Possible error could be improper port defintion of Z_values but whatever
            //Same for .data_out since multidimentional 
            2: begin : BRAM_ROM
                ProtoMatrixRom_BRAM #(
                        .NUM_Z(ZsN), .NUM_PARITY_BLKS(NumPBlks), .Z_VALUES(Z_VALUE_ARRAY),
                        .DEPTH(PmRomDepth), .WIDTH(PmRomWidth), .ADDRW(PmRomAddrW), .P_LVL(PLvl)
                    )
                    GenRom (
                        .addr(shift_addr),.data_out(shift_values)
                    );
            end 

            default: begin : assert_invalid_cfg
                $fatal(1, "Invalid ROM Configuration Selected - Aborting");
            end
        endcase 
    endgenerate

    // -------------------------------------------------------------------------    
    // Generate the requested pipelined Circular Shifter for. 
    // TODO: Add support for pointer based one for Z>=384
    // -------------------------------------------------------------------------    
    genvar nori; 
    generate
        for(nori=0; nori<NumPBlks*PLvl; nori++) begin
            pipelinedCircularShifter #(
                .MAXZ(MaxZ), .ROTATES_PER_CYCLE(ROTATES_PER_CYCLE)
            )
            circ_shftr_inst (
                .CLK(CLK), .rst_n(rst_n), .valid_in(valid_flag_pipe[1]), 
                .in_data(i_data_processed), .shift_val(shift_values[nori]),
                .out_data(rotator_o[nori][MaxZ-1:0]), .valid_out(rotator_o[nori][MaxZ])
            );
        end
    endgenerate



    // -------------------------------------------------------------------------    
    // Stage 0: Input register / Zero padding if input is not width of Max Z
    // -------------------------------------------------------------------------    
    always_ff @(posedge CLK) begin
        if(!rst_n)
            i_data_processed <= '0;
            shift_addr <= '0;

        else begin
            // NOTE: Note to the user, I decided not to go about using hours of my life working on 
            // complex bunch of code to manage the input of this  one hot case if you change the number
            // of possible combinations from the default 3 so you have to change it yourself manually because 
            // I felt like not spending a bunch of time on this
            unique case (req_z)
                //The lowest bit corresponds to a selection of the first item in the array
                3'b001 : begin 
                    i_data_processed <= {{ (MaxZ-Z_VALUE_ARRAY[0]){1'b0} }, i_data[(Z_VALUE_ARRAY[0]-1):0] };
                    shift_addr <= '0;   //************ IT SHOULD BE FINE AN INFERED COMBINATION WITH THE COMPILER 
                    ///DIRECTOR SET IN THE FILE. REMOVE THIS NOTE AFTER SYNTHESIS CHECK
                end
                3'b010 : begin 
                    i_data_processed <= {{ (MaxZ-Z_VALUE_ARRAY[1]){1'b0} }, i_data[(Z_VALUE_ARRAY[1]-1):0] };
                    shift_addr <= (PmRomDepth/ZsN)-1;
                end
                3'b100 : begin 
                    i_data_processed <= i_data;
                    shift_addr <= (PmRomDepth/ZsN*2)-1;
                end
                default : begin 
                    i_data_processed <= '0;
                    shift_addr <= '0;
                end
            endcase
        end
    end

    // -------------------------------------------------------------------------    
    // Stage 1-N, Feed the data into the Circular Rotation Pipeline
    // -------------------------------------------------------------------------    
    

    //Some old note that was still here, I'll leave it for now 
    //THE REQUESTED ADDRESS FOR THE MEMORY NEEDS TO BE #of Z * depth / num_z -1
    // i.e. 81 is 2 in the array, so starting address is 288/3 = 96, *2 = 192 - 1 = 191

    // -------------------------------------------------------------------------    
    // Control Signal FSM Definition, Obviously connected to the above
    // But split into its own definition for readability or something idk #TODO: <--- Top tier Comment Ryan
    // -------------------------------------------------------------------------    
    always_ff @(posedge CLK) begin
        if(!rst_n) begin
            valid_flag_pipe <= '0;
            pipeline_cnt    <= '0;
        end else begin
            valid_flag_pipe[0] <= in_valid;
            for(int i = 1; i <= numPipelineSteps; i++) begin
                valid_flag_pipe[i] <= valid_flag_pipe[i-1];
            end
        end


    end

    
endmodule
