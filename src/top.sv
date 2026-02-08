`timescale 1ns / 1ps
`default_nettype none
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
module QCLDPCEncoder #(
    parameter int NUM_OF_SUPPORTED_Z                =               3,
    parameter int HIGHEST_SUPPORTED_Z_VAL           =               81,
    parameter int NUM_INFO_BLKS_PER_CODE_BLK        =               20,
    parameter int NUM_PARITY_BLKS_PER_CODE_BLK      =               4,         
    parameter int ROM_TYPE                          =               1,          
    parameter int Z_VALUE_ARRAY[NUM_OF_SUPPORTED_Z] =               {27, 54, 81},
    parameter int LEVEL_OF_PARALLELIZATION          =               1
);
    //Creating Alias for readability
    localparam int MaxZ        = HIGHEST_SUPPORTED_Z_VAL;
    localparam int NumPBlks    = NUM_PARITY_BLKS_PER_CODE_BLK;
    localparam int IBlksNum    = NUM_INFO_BLKS_PER_CODE_BLK;
    localparam int ZsN         = NUM_OF_SUPPORTED_Z; 
    localparam int PLvl        = LEVEL_OF_PARALLELIZATION;

    //ROM Related Local Params
    localparam int PmRomDepth = (IBlksNum+NumPBlks) * NumPBlks * ZsN;
    localparam int PmRomWidth = $clog2(MaxZ);
    localparam int PmRomAddrW = $clog2(PmRomDepth)

    // :( input and output defines outside of ( ) because they depend on the Localparam names 
    input  logic CLK;
    input  logic rst_n;
    input  logic en_enc;

    //TODO assert   assert property (@(posedge clk) $onehot(req_Z)) 
    input  logic [ZsN-1:0]                          req_z;   //Unused in ROM_Type 0 Highest Value corresponds to 
    input  logic [(MaxZ*PLvl)-1:0]                  data_in;  
    output logic [(MaxZ*(NumPBlks+IBlksNum))-1:0]   p_data_out;
    // -------------------------------------------------------------------------    
    // End of Module input declaration
    // -------------------------------------------------------------------------    

    //Don't need to initialize because it gets written to anyway and it doesn't matter what start values are
    logic [(MaxZ*(IBlksNum+NumPBlks))-1:0] data_buffer;
    logic [MaxZ-1:0] parity_blk[(NumPBlks*MaxZ)-1:0];    
    
    //Define storage registers for the intermediate values used by accumulators one for each generated Parity Block
    reg [MaxZ-1:0] accum_regs [0:$clog2(NumPBlks)-1]; 

    wire shift_addr  [PmRomAddrW-1:0];   
    wire [PmRomWidth-1:0] shift_values [0:(NumPBlks*PLvl)-1];

    //output of the rotate functions
    logic [MaxZ-1:0] rotated_data [0:$clog2(NumPBlks*)-1];

    logic [$clog2(IBlksNum/PLvl)-1:0] c_cnt;




    // -------------------------------------------------------------------------    
    // Generate ROM
    // TODO: Add more asserts to throw errors when the values given
    // to these generate functions are proper.
    // -------------------------------------------------------------------------    
    generate
        case (`ROM_TYPE)
            0: begin : Single_LUT_ROM
                ProtoMatrixRom_SingleLUT #(   
                                .THE_Z(MaxZ), 
                                .NUM_PARITY_BLKS(NumPBlks),
                                .WIDTH(PmRomWidth), 
                                .DEPTH(PmRomDepth), 
                                .ADDRW(PmRomAddrW)
                                .P_LVL(PLvl)
                            )  
                    GenROM (
                            .addr(shift_addr),
                            .data_out(shift_values)
                    );
            end

            1: begin : Multi_LUT_ROM 
                ProtoMatrixRom_MultiLUT #(
                                .NUM_Z(ZsN),
                                .Z_VALUES(Z_VALUE_ARRAY),
                                .NUM_PARITY_BLKS(NumPBlks),
                                .DEPTH(PmRomDepth),
                                .WIDTH(PmRomWidth),
                                .ADDRW(PmRomAddrW),
                                .P_LVL(PLvl)
                            )
                    GenROM (
                            .addr(shift_addr),
                            .data_out(shift_values)
                    ); 
            end
            
            //TODO Possible error could be improper port defintion of Z_values but whatever
            //Same for .data_out since multidimentional 
            2: begin : BRAM_ROM
                ProtoMatrixRom_BRAM #(
                                .NUM_Z(ZsN),
                                .NUM_PARITY_BLKS(NumPBlks),
                                .Z_VALUES(Z_VALUE_ARRAY),
                                .DEPTH(PmRomDepth),
                                .WIDTH(PmRomWidth),
                                .ADDRW(PmRomAddrW),
                                .P_LVL(PLvl)
                                )
                    GenRom (
                            .addr(shift_addr),
                            .data_out(shift_values)
                    );
            end 

            default: begin : assert_invalid_cfg
                $fatal(1, "Invalid ROM Configuration Selected - Aborting");
            end
        endcase 
    endgenerate

    // -------------------------------------------------------------------------
    // Barrel Shifting function called N-M*ParLvl times based, must be in parallel
    // thus defined as function automatic as it should be called dynamically
    // -------------------------------------------------------------------------
    function automatic logic [MaxZ-1:0] RightCyclicShifter(
        input logic [MaxZ-1:0]          data,
        input logic [PmRomWidth-1:0]    rotval
    );

    logic [2*MAX_Z -1: 0] data_repeated;
    begin
        data_repeated = {data, data};
        //Add a diagram of this working or example of this working from notes or whatever maybe
        return( data_repeated[ (Z-1) + rotval -: Z]);
    end 

    endfunction : RightCyclicShifter


    // -------------------------------------------------------------------------    
    // Stage 0: Input register / Zero padding if input is not width of Max Z
    //      TODO: Must add support for P_Level
    // -------------------------------------------------------------------------    
    always_ff @posedge CLK) begin
        if(!rst)
            info_reg <= '0;
        else begin
            // NOTE: Note to the user, I decided not to go about using hours of my life working on 
            // complex bunch of code to manage the input of this  one hot case if you change the number
            // of possible combinations from the default 3 so you have to change it yourself manually because 
            // I felt like not spending a bunch of time on this
            unique case (req_z)
                //The lowest bit corresponds to a selection of the first item in the array
                3'b001 : 
                    cur_info_reg <= {{ (MaxZ-Z_VALUE_ARRAY[0]){1'b0} }, info_in[(Z_VALUE_ARRAY[0]-1):0] };

                3'b010 : 
                    cur_info_reg <= {{ (MaxZ-Z_VALUE_ARRAY[1]){1'b0} }, info_in[(Z_VALUE_ARRAY[1]-1):0] };
                    
                3'b100 : 
                    cur_info_reg <= info_in;

                default : 
                    cur_info_reg <= '0;
            endcase
        end
    end

    // ??? TODO TODO  TODO TODO TODO TODO TODO TODO 
    //THE REQUESTED ADDRESS FOR THE MEMORY NEEDS TO BE #of Z * depth / num_z -1
    // i.e. 81 is 2 in the array, so starting address is 288/3 = 96, *2 = 192 - 1 = 191
    // * 


    always_ff @(posedge CLK) begin
        if(!rst_n) begin
            c_cnt   <= '0;
        end

    end
    

endmodule