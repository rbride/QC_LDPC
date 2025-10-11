`timescale 1ns / 1ps
`default_nettype none
//at compilation provide the requested number of supported blk Lengths 
`define NUM_SUPPORTED_BLK_LEN                   3
`define NUM_INFO_BLKS_PER_CODE_BLK              20
`define NUM_PARITY_BLKS_PER_CODE_BLK            4
`define HIGHEST_SUPPORTED_Z_VAL                 81
// 2 = BRAM     1 = LUT (Multiple Rates)    0 = Single Rate LUT (i.e only one speed)
// For single rate LUT Highest Z supported is also the only Z supported and used   
`define ROM_TYPE                                1
/////////////////////////////////////////////////////////////////////////////////////////////////
// Author: Ryan Bride 
// Create Date: 09/09/2025
// Module Name: Highspeed Paramatized QC-LDPC Encoder
// Description: 
//      The top level of this design takes a generic input that is the width of the 
//      defined maximum Z. For implementation inside an actual design, I would suggest 
//      Implementing a more robust FIFO or whatever you find best suits your Design.
//      Further the top level of the Controller stores all provided information data into
//      a singular buffer, recommend that you resuse some already existing buffer for this data
//      assuming you have one to reduce redundancy and wasteful resource usage.
//      The designs top level is structured in such a way as to not be standalone for the purpose 
//      of determine resource utilization assessments that will be performed upon completion
/////////////////////////////////////////////////////////////////////////////////////////////////
module QCLDPCController #(
    parameter int NUM_Z =               `NUMBER_OF_SUPPORTED_BLOCK_LENGTHS,
    parameter int MAX_Z =               `HIGHEST_SUPPORTED_Z_VAL,
    parameter int NUM_INFO_BLKS =       `NUM_INFO_BLKS_PER_CODE_BLK,
    parameter int NUM_PAR_BLK =         `NUM_PARITY_BLKS_PER_CODE_BLK,
    parameter int ARRAY_VALUE[NUM_Z] =  {27, 54, 81}
)(
    input logic CLK,
    input logic rst_n,

    //assert   assert property (@(posedge clk) $onehot(req_Z)) 
    input logic [NUM_Z-1:0] req_z,  
    
    //The input of data into this block is not defined at all. Manage this in an incorperating design
    //As a result the input width is just defined as the maximum possible value 
    input logic [MAX_Z-1:0] data_in,
    output logic [(MAX_Z*(NUM_PAR_BLK+NUM_INFO_BLKS))-1:0] p_data_out
);

    //Don't need to initialize because it gets written to anyway and it doesn't matter what start values are
    logic [(MAX_Z*(NUM_INFO_BLKS+NUM_PAR_BLK))-1:0] data_buffer;

    logic [MAX_Z-1:0] parity_blk[(NUM_PAR_BLK*MAX_Z)-1:0];

    QCLDPCEncoder #(                 
                .NUM_Z (NUM_Z),
                .MAX_Z (MAX_Z),
                .NUM_INFO_BLKS  ( `NUM_INFO_BLKS_PER_CODE_BLK ),
                .NUM_PARITY_BLKS( `NUM_PARITY_BLKS_PER_CODE_BLK ),
                )
        Encoder (
            .CLK(CLK),
            .rst_n(rst_n),
            .req_z(req_Z),  
            .info_blk(data_in),
            .parity_blk(parity_blk)

)

endmodule

// Standard Z sizes are 27, 54, and 81
module QCLDPCEncoder #(
    parameter int NUM_Z = 1,
    parameter int MAX_Z = 81,
    parameter int NUM_INFO_BLKS = 20,  // number of info blocks
    parameter int NUM_PARITY_BLKS = 4, // number of parity blocks (also number of rows in the proto matrix)
    parameter int TOTAL_BLKS = NUM_INFO_BLKS + NUM_PARITY_BLKS,
    parameter int Z_VALUES[NUM_Z] = {27, 54, 81},
) (
    input  logic                   CLK,
    input  logic                   rst_n,
    input  logic [NUM_Z-1:0]       req_z,
    input  logic [Z-1:0]           info_blk, // input blocks
    output logic [Z-1:0]           parity_blk[NUM_PARITY_BLKS-1:0], // parity blocks
);


    localparam int PmRomDepth = (NUM_INFO_BLKS+NUM_PARITY_BLKS) * NUM_PARITY_BLKS * NUM_Z;
    localparam int PmRomWidth = $clog2(MAX_Z);
    localparam int PmRomAddrW = $clog2(PmRomDepth)
    
    wire shift_addr  [PmRomAddrW-1:0];
    wire shift_value [PmRomWidth-1:0];

    //Define storage registers for the intermediate values used by accumulators one for each generated Parity Block
    logic [Z-1:0] accum_regs [0:$clog2(NUM_PARITY_BLKS)-1]; 

    // -------------------------------------------------------------------------
    // Memory block Module Generated based on parameter input for the matrix 
    // prototype tables provided in the Standard. 
    // Potential Expand to: Accept parameters for LUT Or BRAM based on a parameter
    // to test area and speed tradeoffs of the two (would change timing), however,
    // by concating columns together, I would be able to reduce number of cycles
    // while creating a somewhat more generic circuit that is potentially capable,
    // of on the fly swithching between code lenghts and maybe even rates. 
    // -------------------------------------------------------------------------
    generate
        case (`ROM_TYPE)
            0: begin: Single_LUT
                ProtoMatrixRom_SingleLUT #(   
                                .Z(Z), 
                                .WIDTH(PmRomWidth), 
                                .DEPTH(PmRomDepth), 
                                .ADDRW(PmRomAddrW)
                            )  
                    GenROM (
                            .addr(shift_addr),
                            .data(shift_value)
                    );
            end

            1: begin: Multi_LUT 
                ProtoMatrixRom_MultiLUT #(
                                .NUM_Z(NUM_Z),
                                .Z_VALUES(Z_VALUES),
                                .DEPTH(PmRomDepth),
                                .WIDTH(PmRomWidth),
                                .ADDRW(PmRomAddrW)
                            )
                    GenROM (
                        .addr(shift_addr),
                        .data(shift_value)
                    ); 
            end
            
            //TODO 
            2: begin

            end 

            default: begin : assert_invalid_cfg
                $fatal(1, "Invalid ROM Configuration Selected - Aborting");
            end
        endcase 
    endgenerate
    
    // -------------------------------------------------------------------------
    // Barrel Shifting function called N-M times based, must be in parallel
    // thus defined as function automatic as it should be called dynamically
    // -------------------------------------------------------------------------
    function automatic logic [Z-1:0] CyclicShifter(
        input logic [Z-1:0]                 msgBlk,
        input logic [PmRomWidth-1:0]        shiftVal,
    )

        return ((msgBlk << shiftVal) | (msgBlk >> (Z - shiftVal)));
    endfunction



    always_ff @(posedge CLK or negedge rst_n) begin
        if(!rst_n) begin
            //Flush 

        end else 
            
        end
    end





endmodule


// Given the undefined (See to tired to remember and look it up) Nature 
// Of the shift operator, define in test bench a check that checks to see
// that the shift is actually occuring the correct number of times in whatever
// wacky crazy simulator and systhesis that occurs should be fine


// assert that at no point the memory data is unknown because 
// the barrel shift function by design cast to int and it is necessary that 
// there won't be any X or Z values contained 
//assert (!$isunknown(signal))
//        a = signal;
// else
//   $error("signal is unknown");



//Note the design is mostly suitable for only the highest rate at this point
//After completetion consider restructuring the Memory so that it compacts given
//inputs for slower rates. 