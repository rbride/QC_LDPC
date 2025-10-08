`timescale 1ns / 1ps
`default_nettype none

// Z sizes are 27, 54, and 81
module qc_ldpc_encoder #(
    parameter int Z = 54,              // circulant size
    parameter int NUM_INFO_BLKS = 20,  // number of info blocks
    parameter int NUM_PARITY_BLKS = 4, // number of parity blocks
    parameter int TOTAL_BLKS = NUM_INFO_BLKS + NUM_PARITY_BLKS
) (
    input  logic                   clk,
    input  logic                   rst,
    input  logic [Z-1:0]           info_blk [NUM_INFO_BLKS-1:0], // input blocks
    output logic [Z-1:0]           parity_blk[NUM_PARITY_BLKS-1:0], // parity blocks
    output logic [Z-1:0]           codeword  [TOTAL_BLKS-1:0]   // final encoded codeword
);

    localparam int CODEWORD_LEN = Z * 24;
    localparam int PROTO_MATRIX_WIDTH = $clog2(Z); //Width needed to store values from 0 to Z-1
    localparam int PROTO_MATRIX_DEPTH = 24*4;   //The depth would differ if the rate changed 
    localparam int PROTO_MATRIX_ADDRW = $clog2(DEPTH);   
    wire shift_addr  [PROTO_MATRIX_ADDRW-1:0];
    wire shift_value [PROTO_MATRIX_WIDTH-1:0];


    // -------------------------------------------------------------------------
    // Memory block Module Generated based on parameter input for the matrix 
    // prototype tables provided in the Standard. 
    // Potential Expand to: Accept parameters for LUT Or BRAM based on a parameter
    // to test area and speed tradeoffs of the two (would change timing), however,
    // by concating columns together, I might be able to number of cycles
    // while creating a somewhat more generic circuit that is potentially capable,
    // of on the fly swithching between code lenghts and maybe even rates. 
    // -------------------------------------------------------------------------
    ProtoMatrixRom #(.Z(Z), .CODEWORD_LEN(CODEWORD_LEN), 
                     .WIDTH(PROTO_MATRIX_WIDTH), .DEPTH(PROTO_MATRIX_DEPTH), 
                     .ADDRW(PROTO_MATRIX_ADDRW)
                    )  
        GenROM (
            .addr(shift_addr),
            .data(shift_value)   
    );
    
    

    // -------------------------------------------------------------------------
    // Barrel shift function (cyclic left shift)
    // -------------------------------------------------------------------------
    function automatic logic [Z-1:0] barrel_shift(
        input logic [Z-1:0] vec,
        input int           shift
    );
        if (shift == 0) 
            return vec;
        else 
            return (vec << shift) | (vec >> (Z - shift));
    endfunction

    // -------------------------------------------------------------------------
    // Generate parity blocks: each is XOR of shifted info blocks
    // -------------------------------------------------------------------------
    always_comb begin
        for (int p = 0; p < NUM_PARITY_BLKS; p++) begin
            logic [Z-1:0] acc = '0;
            for (int i = 0; i < NUM_INFO_BLKS; i++) begin
                if (shift_table[p][i] != -1) begin
                    acc ^= barrel_shift(info_blk[i], shift_table[p][i]);
                end
            end
            parity_blk[p] = acc;
        end
    end

    // -------------------------------------------------------------------------
    // Concatenate info + parity into final codeword
    // -------------------------------------------------------------------------
    always_comb begin
        for (int i = 0; i < NUM_INFO_BLKS; i++)
            codeword[i] = info_blk[i];
        for (int p = 0; p < NUM_PARITY_BLKS; p++)
            codeword[NUM_INFO_BLKS + p] = parity_blk[p];
    end

endmodule
