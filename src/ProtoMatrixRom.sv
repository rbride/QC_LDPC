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
    logic [WIDTH-1:0] memory [0:DEPTH-1];

    initial begin
        if (Z == 27) begin
            $readmemh("648B_5_6_ProtoMat.mem", memory);
        end else if (Z == 54) begin
            $readmemh("1296B_5_6_ProtoMat.mem", memory);
        end else if (Z == 81) begin
            $readmemh("1944B_5_6_ProtoMat.mem", memory);
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
    logic [WIDTH-1:0] memory [0:DEPTH-1];
    
    string filenames[3];
    
    initial begin
        foreach (Z_VALUES[i]) begin
            filenames[i] = {sformatf("%0d", Z_VALUES[i]), "B_5_6_ProtoMat.mem"};
            readmemh(filenames[i], memory, (i*(DEPTH/3)), (((i+1)*(DEPTH/3))-1));
        end 
    end
    /* initial begin
        $readmemh("648B_5_6_ProtoMat.mem", memory);
        $readmemh("1296B_5_6_ProtoMat.mem", memory);
        $readmemh("1944B_5_6_ProtoMat.mem", memory);
    end */
    always_comb begin
        data = memory[addr];
    end
endmodule

//BRAM Version of ram
module ProtoMatrixRom_BRAM #(
    parameter int NUM_Z             =   3,
    parameter int NUM_PARITY_BLKS   =   4,
    parameter int Z_VALUES[NUM_Z]   =   {27, 54, 81},
    parameter int DEPTH             =   288,  
    parameter int WIDTH             =   7,
    parameter int ADDRW             =   9
)(
    input wire logic [ADDRW-1:0] addr,
    output           [WIDTH-1:0] data_out [$clog2(NUM_PARITY_BLKS)-1:0]
);
    //For yosys (* ram_style = "block" *) selects block RAM
    //For Vivado(* rom_style = "block" *) reg [data_size-1:0] myrom [2**addr_size-1:0];

    (* ram_style = "block" *) reg [WIDTH-1:0] ram [0:DEPTH-1];
    //Width times 4 because I need 4 at once 
    reg [WIDTH-1:0] data_out [0:NUM_PARITY_BLKS-1];

    initial begin
        foreach (Z_VALUES[i]) begin
            filenames[i] = {sformatf("%0d", Z_VALUES[i]), "B_5_6_ProtoMat.mem"};
            readmemh(filenames[i], ram, (i*(DEPTH/3)), (((i+1)*(DEPTH/3))-1));
        end 
    end

    always @(posedge clk) begin
        for(int i=0; i<NUM_PARITY_BLKS; i++) begin
            data_out[i] <= ram[addr + (i*(DEPTH/NUM_Z))]; 
        end
    end

endmodule

//infers Ultra (* ram_style = "ultra" *) reg [data_size-1:0] myram [2**addr_size-1:0];
//infers LUT(* rom_style = "distributed" *) reg [data_size-1:0] myrom [2**addr_size-1:0];
//infers block (* rom_style = "block" *) reg [data_size-1:0] myrom [2**addr_size-1:0];\