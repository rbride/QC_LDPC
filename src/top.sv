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

    // -------------------------------------------------------------------------
    // Memory block Module Generated based on parameter input for the matrix 
    // prototype tables provided in the Standard. Should except parameter for LUT
    // Or BRAM based on a parameter to test area and speed tradeoffs of the two
    // Should be generic enough to fill the needs of all the different coding rates
    // Atleast for n=1296 and z=54
    // -------------------------------------------------------------------------
    matrix_proto_mem #(
        .Z(Z),
        .NUM_INFO_BLKS(NUM_INFO_BLKS),
        .NUM_PARITY_BLKS(NUM_PARITY_BLKS)
    ) mem_inst (
        .clk(clk),
        .rst(rst)
        // Additional ports as needed
    );
    

    // -------------------------------------------------------------------------
    // Shift values table (from LDPC base matrix in the standard)
    // Example: For each parity row, define the shifts relative to info blocks
    // -1 means "zero block" (skip)
    // You would initialize this from the standard’s base matrix
    // -------------------------------------------------------------------------
    int shift_table [NUM_PARITY_BLKS-1:0][NUM_INFO_BLKS-1:0] = '{
        '{  0,  12, -1, 47, -1, ... }, // parity row 0
        '{ -1,  25, 33, -1,  9, ... }, // parity row 1
        // etc...
    };

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
