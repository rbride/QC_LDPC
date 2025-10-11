`timescale 1ns / 1ps
`default_nettype none
// -------------------------------------------------------------------------
// LUT Based Memory Module, Has the benefits of Being Asynchronous and fast
// Given Z we can determine the total Codelength as the 5/6 Rate Parity Matrix Has 
// 24 entries per row regardless of Z size in the default LDPC Parity Matrix
// The depth of the memory is 24*4 but it would change if the rate changed
// -------------------------------------------------------------------------
module ProtoMatrixRom_SingleLUT #(
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

module ProtoMatrixRom_MultiLUT #(
    parameter int NUM_Z             =   3,
    parameter int Z_VALUES[NUM_Z]   =   {27, 54, 81},
    parameter int DEPTH             =   288,  
    parameter int WIDTH             =   7,
    parameter int ADDRW             =   9
)(
    input wire logic [ADDRW-1:0] addr,
    output     logic [WIDTH-1:0] data 
);
    /* Note: "-" (zero block/skip) values are stored as the maximum value available for the 
    given WIDTH as none of the possible Z values are equal to The maximum value of the WIDTH */
    logic [WIDTH-1:0] memory [DEPTH-1:0];

    initial begin
        $readmemh("ProtoMatrixRom_27.mem", memory, 0,   95);
        $readmemh("ProtoMatrixRom_54.mem", memory, 96,  191);
        $readmemh("ProtoMatrixRom_81.mem", memory, 192, 287);
    end
    
    always_comb begin
        data = memory[addr];
    end
endmodule

//parameter int ARRAY_VALUE[4] = {1,3,5,10};
/*
`define X 3

module my_module #(parameter int X = `X) (
    input int arr [X]
);
    initial begin
        $display("X = %0d", X);
        foreach (arr[i])
            $display("arr[%0d] = %0d", i, arr[i]);
    end
endmodule

module top;
    int my_array [`X] = '{10, 20, 30};
    my_module #(.X(`X)) inst (.arr(my_array));
endmodule


If you want the module to have a parameterized array, use a parameter array of size `X.
For an input port, you’ll use a packed or unpacked array depending on your needs.

Here’s an example for integer array inputs:

module my_module #(
    parameter int X = `X
) (
    input int data_in [X]   // Unpacked array of X integers
);
    initial begin
        $display("Array length = %0d", X);
        for (int i = 0; i < X; i++) begin
            $display("data_in[%0d] = %0d", i, data_in[i]);
        end
    end
endmodule




module top #(parameter int N = 4);

    generate
        for (genvar i = 0; i < N; i++) begin : gen_seg
            // Each segment gets its own width
            localparam int WIDTH = 8 + i * 2;
            
            // Declare signals inside the block
            logic [WIDTH-1:0] data;
            
            initial $display("Segment %0d width = %0d", i, WIDTH);
        end
    endgenerate

endmodule
✅ This creates 4 generate blocks:

top.gen_seg[0].data → 8 bits

top.gen_seg[1].data → 10 bits

top.gen_seg[2].data → 12 bits

top.gen_seg[3].data → 14 bits*/