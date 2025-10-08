// -------------------------------------------------------------------------
// LUT Based Memory Module, Has the benefits of Being Asynchronous and fast
// Given Z we can determine the total Codelength as the 5/6 Rate Parity Matrix Has 
// 24 entries per row regardless of Z size in the default LDPC Parity Matrix
// The depth of the memory is 24*4 but it would change if the rate changed
// -------------------------------------------------------------------------
module ProtoMatrixRom #(
    parameter int Z = 54,                   
    localparam int CODEWORD_LEN = Z * 24,
    localparam int DEPTH = 24*4,   //The depth would differ if the rate changed 
    localparam int ADDRW = $clog2(Z) 
)(
    input wire logic [ADDRW-1:0] addr,
    output     logic [CODEWORD_LEN-1:0] data
); 

//Since the Input matrix stores either a value from 0 to Z-1 or a - for a zero block
//we can store the - as the max value of the Width since none of the Z's have a value
//greater than the 2^ADDRW






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