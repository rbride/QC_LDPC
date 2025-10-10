`timescale 1ns / 1ps
`default_nettype none

//at compilation provide the requested number of supported blk Lengths 
//If one the design synthesizes a single block based around 
`define NUM_Z   3

// Standard Z sizes are 27, 54, and 81
module qc_ldpc_encoder #(
    parameter int Z = 54,              // circulant size
    parameter int NUM_INFO_BLKS = 20,  // number of info blocks
    parameter int NUM_PARITY_BLKS = 4, // number of parity blocks (also number of rows in the proto matrix)
    parameter int TOTAL_BLKS = NUM_INFO_BLKS + NUM_PARITY_BLKS
) (
    input  logic                   CLK,
    input  logic                   rst_n,
    input  logic [Z-1:0]           info_blk [NUM_INFO_BLKS-1:0], // input blocks
    output logic [Z-1:0]           parity_blk[NUM_PARITY_BLKS-1:0], // parity blocks
    output logic [Z-1:0]           codeword  [TOTAL_BLKS-1:0]   // final encoded codeword
);

    localparam int PmRomWidth = $clog2(Z); //Width needed to store values from 0 to Z-1
    //localparam int PM_ROM_DEPTH = 24*4;   //The depth would differ if the rate changed 
    localparam int PmRomDepth = (NUM_INFO_BLKS+NUM_PARITY_BLKS)*NUM_PARITY_BLKS;
    localparam int PmRomAddrW = $clog2(PmRomDepth);   
    
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
    ProtoMatrixRom #(.Z(Z), .WIDTH(PM_ROM_WIDTH), 
                            .DEPTH(PROTO_MATRIX_DEPTH), 
                            .ADDRW(PROTO_MATRIX_ADDRW)
                    )  
        GenROM (
            .addr(shift_addr),
            .data(shift_value)   
    );
    
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