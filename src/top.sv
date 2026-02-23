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
//  #TODO ADD TO README: Common Lifting factos I've seen used for the smaller Z's 
//  | 27, 54, 81 | 28, 56, 112 | 24, 48, 96 | 48, 72, 96 |
//  All of these have some sort of metric where atleast 1 of teh smaller numbers divides evenly into one of the higher
//  values, for sake of keeping the actual design being minimized I recommend you do the same. Further it is recommended
//  that for the smallest z segment of this circuit you utilize a highest value of a z that has a Clog2(MaxZ) of 7 or less
//  And then utilize to larger values with a version of this circuit such as 192 and like 162 at a lower FMAX For middle
//  Size values, and ultimately the to be done pointer implementation that utilizes the Bram Memory for Z=352 for
//  Large data outputs 
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
module QCLDPCEncoderController #(
    parameter int NUM_OF_SUPPORTED_Z                =               3,
    parameter int HIGHEST_SUPPORTED_Z_VAL           =               81,
    parameter int NUM_INFO_BLKS_PER_CODE_BLK        =               20,
    parameter int NUM_PARITY_BLKS_PER_CODE_BLK      =               4,         
    parameter int ROM_TYPE                          =               1,          
    parameter int Z_VALUE_ARRAY[NUM_OF_SUPPORTED_Z] =               {27, 54, 81},
    parameter int LEVEL_OF_PARALLELIZATION          =               1,
    parameter int ROTATES_PER_CYCLE                 =               1,      
    parameter int NUM_ACCUM_PIPE_SPLITS             =               3,      //Starting with 3 
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
    input logic in_last,            //At the moment this is unused, but included none-the less 
    output logic in_ready,

    //TODO assert   assert property (@(posedge clk) $onehot(req_Z)) 
    input logic [ZsN-1:0] req_z,  //Unused in ROM_Type 0 Highest Value corresponds to 
    input  logic [(MaxZ*PLvl)-1:0]                  i_data,
    output logic [(MaxZ*(NumPBlks+IBlksNum))-1:0]   p_data_out
    
);
    // -------------------------------------------------------------------------
    // TODO: Currently I do not have logic to handle the case that is a variety of legnths and stuff
    //  As it stands there is mostly just a hard limit on it being required to use 81, 54, and 27
    //  add combo logic to support this, like do divisions to see if one is evenly divided into
    //  fmax and compute it, also use a function to compute these inputs and stuff and recommend
    //  TODO TODO TODO TODO, recommend to use primarily factorized inputs for the includes
    //  Below is placeholder stuff for it
    // -------------------------------------------------------------------------
    localparam int NumNonFactorSupportedLens = 1;


    // -------------------------------------------------------------------------    
    // Declaration of Internal Module Signals
    // -------------------------------------------------------------------------    
    reg [MaxZ-1:0] i_data_processed;
    //Tbh could be wire Top bit stays for the purpose of the valid out
    //TODO TODO ensure its treated as a wire remove the definition of "Wire" after design completes, this is just 
    //TO gate sythnesis and design because I am tired. 
    wire logic [MaxZ:0] rotator_o [NumPBlks*PLvl-1:0];

    logic [MaxZ-1:0] parity_blk[(NumPBlks*MaxZ)-1:0];    

    
    
    logic shift_addr  [PmRomAddrW-1:0];   
    logic [PmRomWidth-1:0] shift_values [0:(NumPBlks*PLvl)-1];

    //output of the rotate functions
    logic [MaxZ-1:0] rotated_data [0:$clog2(NumPBlks*PLvl)-1];

    //Calculate # of stages of the Shifter Pipeline, to determine the needed Valid depth
    //TODO: Remove this from the Pipelined Shifter code and make it a parameter MAYBE
    localparam int numPipelineSteps = ($clog2(MaxZ) % ROTATES_PER_CYCLE  != 0) ?
                                      (($clog2(MaxZ) / ROTATES_PER_CYCLE) +1 )  :
                                      ($clog2(MaxZ) / ROTATES_PER_CYCLE);

    logic valid_flag_pipe; 
    //not -1 because the highest bit is used to select the Accumulation Register Bank
    logic [$clog2(IBlksNum):0]    pipeline_cnt;
    //2 accumulator registers for each Parity block for Register Ping ponging 
    reg [MaxZ-1:0] accum_regs [0:$clog2(NumPBlks*PLvl)-1][0:1]; 

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
                .CLK(CLK), .rst_n(rst_n), .valid_in(valid_flag_pipe), 
                .in_data(i_data_processed), .shift_val(shift_values[nori]),
                .out_data(rotator_o[nori][MaxZ-1:0]), .valid_out(rotator_o[nori][MaxZ])
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
                    //i_data_processed <= {{ (MaxZ-Z_VALUE_ARRAY[0]){1'b0} }, i_data[(Z_VALUE_ARRAY[0]-1):0] };
                    i_data_processed <= {i_data[(Z_VALUE_ARRAY[0]-1):0], i_data[(Z_VALUE_ARRAY[0]-1):0], i_data[(Z_VALUE_ARRAY[0]-1):0]}
                    shift_addr <= '0;   //************ IT SHOULD BE FINE AN INFERED COMBINATIONAL LINE WITH THE COMPILER 
                    ///Director SET IN THE FILE. REMOVE THIS NOTE AFTER SYNTHESIS CHECK #FIXME 
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
                
            //Actual Fire instruction is this 
            if(valid_in && in_ready)
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
    //Always ff exist to count the pipeline value, and flip the top bit to select the right
    //accumulator bank
    always_ff @(posedge CLK) begin
        if(!rst_n) begin
            pipeline_cnt <= '0;
        end else begin
            //Decided to use the middle accumulator to theoretically reduce fanout for all rotators 
            if((rotator_o[(NumPBlks*PLvl/2)][MaxZ]) == 1'b1) begin
                pipeline_cnt <= (pipeline_cnt == IBlksNum-1) ?  
                                { ~pipeline_cnt[$clog2(IBlksNum)], {($clog2(IBlksNum)-1){1'b0}} }  :
                                pipeline_cnt + 1;
            end else 
                pipeline_cnt <= pipeline_cnt;
        end
    end
    // -------------------------------------------------------------------------    
    // Generate the logic to send output of each rotator to the accums regs
    // -------------------------------------------------------------------------    
    genvar allen; 
    generate 
        for(allen=0; allen<NumPBlks*PLvl; allen++) begin
            
        end
    endgenerate
    generate
        for(nori=0; nori<NumPBlks*PLvl; nori++) begin
            pipelinedCircularShifter #(
                .MAXZ(MaxZ), .ROTATES_PER_CYCLE(ROTATES_PER_CYCLE)
            )
            circ_shftr_inst (
                .CLK(CLK), .rst_n(rst_n), .valid_in(valid_flag_pipe), 
                .in_data(i_data_processed), .shift_val(shift_values[nori]),
                .out_data(rotator_o[nori][MaxZ-1:0]), .valid_out(rotator_o[nori][MaxZ])
            );
        end
    endgenerate



    
endmodule



