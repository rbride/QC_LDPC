// -------------------------------------------------------------------------
// LUT Based Memory Module, Has the benefits of Being Asynchronous and fast
// -------------------------------------------------------------------------
module ProtoMatrixRom #(
    parameter int Z = 54,              // circulant size
    parameter int NUM_INFO_BLKS = 20,  // number of info blocks
    parameter int NUM_PARITY_BLKS = 4, // number of parity blocks
    parameter int TOTAL_BLKS = NUM_INFO_BLKS + NUM_PARITY_BLKS
)(

); 


module rom_async #(
    parameter WIDTH=8, 
    parameter DEPTH=256, 
    parameter INIT_F="",
    localparam ADDRW=$clog2(DEPTH)
    ) (
    input wire logic [ADDRW-1:0] addr,
    output     logic [WIDTH-1:0] data
    );

    logic [WIDTH-1:0] memory [DEPTH];

    initial begin
        if (INIT_F != 0) begin
            $display("Creating rom_async from init file '%s'.", INIT_F);
            $readmemh(INIT_F, memory);
        end
    end

    always_comb data = memory[addr];
endmodule