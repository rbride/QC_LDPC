`timescale 1ns / 1ps
`default_nettype none
// -------------------------------------------------------------------------
// LUT Based Memory Module, Has the benefits of Being Asynchronous and fast
// Given Z we can determine the total Codelength as the 5/6 Rate Parity Matrix Has 
// 24 entries per row regardless of Z size in the default LDPC Parity Matrix
// The depth of the memory is 24*4 but it would change if the rate changed
// -------------------------------------------------------------------------
module ProtoMatrixRom #(
    parameter int Z = 54,                   
    parameter int WIDTH = 6, //Clog2(Z)
    //Provided Prototype Matrix is 24x4 for all rates and code lengths in IEEE Std. 
    parameter int DEPTH = 96,   
    parameter int ADDRW = 7    //Clog2(Depth)
)(
    input wire logic [ADDRW-1:0] addr,
    output     logic [WIDTH-1:0] data 
); 
    
    /* Note: "-" (zero block/skip) values are stored as the maximum value available for the 
    given WIDTH as none of the possible Z values are equal to The maximum value of the WIDTH*/
    logic [WIDTH-1:0] memory [DEPTH-1:0];

    initial begin
        if (Z == 27) begin
            $readmemh("ProtoMatrixRom_27.mem", memory);
        end
        else if (Z == 54) begin
            $readmemh("ProtoMatrixRom_54.mem", memory);
        end else if (Z == 81) begin
            $readmemh("ProtoMatrixRom_81.mem", memory);
        end else begin : assert_invalid_cfg
            $fatal( 1, "Invalid Configuration detected, Unsupported Z value: %0d. Supported values are 27, 54, and 81. - aborting", Z);
        end

    always_comb begin
        data = memory[addr];
    end
endmodule