`timescale 1ns / 1ps
// -------------------------------------------------------------------------
//
//  All defined Roms Support the included standard 5/6 rate with the 3 standard Z values of 27,54,81
//
// ------------------------------------------------------------------------
//For yosys (* ram_style = "block" *) selects block RAM
//for yosys (* ram_style = "distributed" *) selects LUT RAM
//For Vivado(* rom_style = "block" *) reg [data_size-1:0] myrom [2**addr_size-1:0];
//infers Ultra (* ram_style = "ultra" *) reg [data_size-1:0] myram [2**addr_size-1:0]; Vivado
//infers LUT(* rom_style = "distributed" *) reg [data_size-1:0] myrom [2**addr_size-1:0]; Vivado
//infers block (* rom_style = "block" *) reg [data_size-1:0] myrom [2**addr_size-1:0]; Vivado 
// Quartus: // synthesis ramstyle = "logic" or "lcell_ram"   Forces LUT based
/* Note: "-" (zero block/skip) values are stored as the maximum value available for the 
    given WIDTH as none of the possible Z values are equal to The maximum value of the WIDTH   */
// -------------------------------------------------------------------------
//TODO: model a LUT rom that auto-concatinates the 4 addresses into a single memory location to see if there is a effect on the 
//final simulation
// -------------------------------------------------------------------------
module ProtoMatrixRom_SingleLUT #(
    parameter int THE_Z = 54,                   
    parameter int WIDTH = $clog2(THE_Z), // 6
    //Provided Prototype Matrix is 24x4 for all rates and code lengths in IEEE Std. 
    parameter int DEPTH = 96,   
    parameter int ADDRW = 7,    //Clog2(Depth)
    parameter int NUM_PARITY_BLKS = 4,
    parameter int P_LVL = 1
)(
    input wire logic [ADDRW-1:0] addr,
    //output           [WIDTH-1:0] data_out [0:$clog2(NUM_PARITY_BLKS*P_LVL)-1]
    output logic        [WIDTH-1:0] data_out [0:NUM_PARITY_BLKS*P_LVL-1]
); 
    
    (* ram_style = "distributed" *) logic [WIDTH-1:0] memory [0:DEPTH-1];
    initial begin
        if (THE_Z == 27) begin
            memory={5'h11,5'hD,5'h8,5'h15,5'h9,5'h3,5'h12,5'hC,5'hA,5'h0,5'h4,5'hF,5'h13, 5'h2,5'h5,
                    5'hA,5'h1A,5'h13,5'hD,5'hD,5'h1,5'h0,5'h1F,5'h1F,5'h3,5'hC,5'hB,5'hE,5'hB,5'h19,
                    5'h5,5'h12,5'h0,5'h9,5'h2,5'h1A,5'h1A,5'hA,5'h18,5'h7,5'hE,5'h14,5'h4,5'h2,5'h1F,
                    5'h0,5'h0,5'h1F,5'h16,5'h10,5'h4,5'h3,5'hA,5'h15,5'hC,5'h5,5'h15,5'hE,5'h13,5'h5,
                    5'h1F,5'h8,5'h5,5'h12,5'hB,5'h5,5'h5,5'hF,5'h0,5'h1F,5'h0,5'h0,5'h7,5'h7,5'hE,5'hE,
                    5'h4,5'h10,5'h10,5'h18,5'h18,5'hA,5'h1,5'h7,5'hF,5'h6,5'hA,5'h1A,5'h8,5'h12,5'h15,
                    5'hE,5'h1,5'h1F,5'h1F,5'h0};
        end else if (THE_Z == 54) begin
            memory={6'h30,6'h1D,6'h25,6'h34,6'h2,6'h10,6'h6,6'hE,6'h35,6'h1F,6'h22,6'h5,6'h12,6'h2A,6'h35,
                    6'h1F,6'h2D,6'h3F,6'h2E,6'h34,6'h1,6'h0,6'h3F,6'h3F,6'h11,6'h4,6'h1E,6'h7,6'h2B, 6'hB,
                    6'h18,6'h6,6'hE,6'h15,6'h6,6'h27,6'h11,6'h28,6'h2F,6'h7,6'hF,6'h29,6'h13,6'h3F,6'h3F,
                    6'h0,6'h0,6'h3F,6'h7,6'h2,6'h33,6'h1F,6'h2E,6'h17,6'h10,6'hB,6'h35,6'h28,6'hA,6'h7,6'h2E,
                    6'h35,6'h21,6'h23,6'h3F,6'h19,6'h23,6'h26,6'h0,6'h3F,6'h0,6'h0,6'h13,6'h30,6'h29,6'h1,6'hA,
                    6'h7,6'h24,6'h2F,6'h5,6'h1D,6'h34,6'h34,6'h1F,6'hA,6'h1A,6'h6,6'h3,6'h2,6'h3F,6'h33,6'h1,6'h3F,
                    6'h3F,6'h0};
        end else if (THE_Z == 81) begin
            memory={7'hD,7'h30,7'h50,7'h42,7'h4,7'h4A,7'h7,7'h1E,7'h4C,7'h34,7'h25,7'h3C,7'h7F,7'h31,7'h49,
                    7'h1F,7'h4A,7'h49,7'h17,7'h7F,7'h1,7'h0,7'h7F,7'h7F,7'h45,7'h3F,7'h4A,7'h38,7'h40,7'h4D,
                    7'h39,7'h41,7'h6,7'h10,7'h33,7'h7F,7'h40,7'h7F,7'h44,7'h9,7'h30,7'h3E,7'h36,7'h1B,7'h7F,
                    7'h0,7'h0,7'h7F,7'h33,7'hF,7'h0,7'h50,7'h18,7'h19,7'h2A,7'h36,7'h2C,7'h47,7'h47,7'h9,
                    7'h43,7'h23,7'h7F,7'h3A,7'h7F,7'h1D,7'h7F,7'h35,7'h0,7'h7F,7'h0,7'h0,7'h10,7'h1D,7'h24,
                    7'h29,7'h2C,7'h38,7'h3B,7'h25,7'h32,7'h18,7'h7F,7'h41,7'h4,7'h41,7'h34,7'h7F,7'h4,7'h7F,
                    7'h49,7'h34,7'h1,7'h7F,7'h7F,7'h0};
        end else begin : assert_invalid_cfg
            $fatal( 1, "Invalid Configuration detected, Unsupported Z value: %0d. Supported values are 27, 54, 81\n\
                    f you need a different Z value, ensure that a file is provided and change the code In \n\
                    ProtoMatrixRom.sv to load the .mem file values for your specific Z - aborting", THE_Z);
        end
    end

    // data_out[i+q] = memory[addr + (( i*(DEPTH/THE_Z) + q )-1)]; 
    always_comb begin
        for(int i=0; i<NUM_PARITY_BLKS; i++) begin
            for(int q=0; q<P_LVL; q++) begin
                data_out[i+q] = memory[addr+q +(i*(DEPTH/NUM_PARITY_BLKS)-1)];
            end
        end
    end
endmodule

// ------------------------------------------------------------------------- 
// -------------------------------------------------------------------------
// -------------------------------------------------------------------------
module ProtoMatrixRom_MultiLUT #(
    parameter int NUM_Z             =   3,
    parameter int Z_VALUES[NUM_Z]   =   {27, 54, 81},
    parameter int DEPTH             =   288,  
    parameter int WIDTH             =   7,
    parameter int ADDRW             =   9,
    parameter int NUM_PARITY_BLKS   =   4,
    parameter int P_LVL             =   1

)(
    input wire logic [ADDRW-1:0] addr,
    //output           [WIDTH-1:0] data_out [0:$clog2(NUM_PARITY_BLKS*P_LVL)-1]
    output logic          [WIDTH-1:0] data_out [0:NUM_PARITY_BLKS*P_LVL-1]

);
 
    (* ram_style = "distributed" *) logic [WIDTH-1:0] memory [0:DEPTH-1];
    //string filenames[3];
    
    initial begin
        memory = {7'h11,7'hD,7'h8,7'h15,7'h9,7'h3,7'h12,7'hC,7'hA,7'h0,7'h4,7'hF,7'h13, 7'h2,7'h5,
                  7'hA,7'h1A,7'h13,7'hD,7'hD,7'h1,7'h0,7'h1F,7'h1F,7'h3,7'hC,7'hB,7'hE,7'hB,7'h19,
                  7'h5,7'h12,7'h0,7'h9,7'h2,7'h1A,7'h1A,7'hA,7'h18,7'h7,7'hE,7'h14,7'h4,7'h2,7'h1F,
                  7'h0,7'h0,7'h1F,7'h16,7'h10,7'h4,7'h3,7'hA,7'h15,7'hC,7'h5,7'h15,7'hE,7'h13,7'h5,
                  7'h1F,7'h8,7'h5,7'h12,7'hB,7'h5,7'h5,7'hF,7'h0,7'h1F,7'h0,7'h0,7'h7,7'h7,7'hE,7'hE,
                  7'h4,7'h10,7'h10,7'h18,7'h18,7'hA,7'h1,7'h7,7'hF,7'h6,7'hA,7'h1A,7'h8,7'h12,7'h15,
                  7'hE,7'h1,7'h1F,7'h1F,7'h0,7'h30,7'h1D,7'h25,7'h34,7'h2,7'h10,7'h6,7'hE,7'h35,7'h1F,
                  7'h22,7'h5,7'h12,7'h2A,7'h35,7'h1F,7'h2D,7'h3F,7'h2E,7'h34,7'h1,7'h0,7'h3F,7'h3F,
                  7'h11,7'h4,7'h1E,7'h7,7'h2B, 7'hB,7'h18,7'h6,7'hE,7'h15,7'h6,7'h27,7'h11,7'h28,
                  7'h2F,7'h7,7'hF,7'h29,7'h13,7'h3F,7'h3F,7'h0,7'h0,7'h3F,7'h7,7'h2,7'h33,7'h1F,7'h2E,
                  7'h17,7'h10,7'hB,7'h35,7'h28,7'hA,7'h7,7'h2E,7'h35,7'h21,7'h23,7'h3F,7'h19,7'h23,7'h26,
                  7'h0,7'h3F,7'h0,7'h0,7'h13,7'h30,7'h29,7'h1,7'hA,7'h7,7'h24,7'h2F,7'h5,7'h1D,7'h34,
                  7'h34,7'h1F,7'hA,7'h1A,7'h6,7'h3,7'h2,7'h3F,7'h33,7'h1,7'h3F,7'h3F,7'h0,
                  7'hD,7'h30,7'h50,7'h42,7'h4,7'h4A,7'h7,7'h1E,7'h4C,7'h34,7'h25,7'h3C,7'h7F,7'h31,7'h49,
                  7'h1F,7'h4A,7'h49,7'h17,7'h7F,7'h1,7'h0,7'h7F,7'h7F,7'h45,7'h3F,7'h4A,7'h38,7'h40,7'h4D,
                  7'h39,7'h41,7'h6,7'h10,7'h33,7'h7F,7'h40,7'h7F,7'h44,7'h9,7'h30,7'h3E,7'h36,7'h1B,7'h7F,
                  7'h0,7'h0,7'h7F,7'h33,7'hF,7'h0,7'h50,7'h18,7'h19,7'h2A,7'h36,7'h2C,7'h47,7'h47,7'h9,
                  7'h43,7'h23,7'h7F,7'h3A,7'h7F,7'h1D,7'h7F,7'h35,7'h0,7'h7F,7'h0,7'h0,7'h10,7'h1D,7'h24,
                  7'h29,7'h2C,7'h38,7'h3B,7'h25,7'h32,7'h18,7'h7F,7'h41,7'h4,7'h41,7'h34,7'h7F,7'h4,7'h7F,
                  7'h49,7'h34,7'h1,7'h7F,7'h7F,7'h0};
    end
    
    //data_out = memory[addr + ((i*(DEPTH/NUM_Z))-1)];
    //Note the order for the Req_Z is the last Z value defined in the Z_VAl Array is corresponds to the most sig bit of Req_z
    //Determine in the encoder logic send the address offset with the requested z don't handle it in memory 
    always_comb begin
        for(int i=0; i<NUM_PARITY_BLKS; i++) begin
            for(int q=0; q<P_LVL; q++) begin
                data_out[i+q] = memory[addr+q +(i*(DEPTH/NUM_PARITY_BLKS)-1)];
            end
        end
    end
endmodule

//BRAM Version of ram
module ProtoMatrixRom_BRAM #(
    parameter int NUM_Z             =   3,
    parameter int NUM_PARITY_BLKS   =   4,
    parameter int Z_VALUES[NUM_Z]   =   {27, 54, 81},
    parameter int DEPTH             =   288,  
    parameter int WIDTH             =   7,
    parameter int ADDRW             =   9,
    parameter int P_LVL             =   1
)(
    input logic CLK, 
    input wire logic [ADDRW-1:0] addr,
    //output           [WIDTH-1:0] data_out [0:$clog2(NUM_PARITY_BLKS)-1]
    output logic         [WIDTH-1:0] data_out [0:NUM_PARITY_BLKS*P_LVL-1]
);

    (* ram_style = "block" *) reg [WIDTH-1:0] ram [0:DEPTH-1];
     initial begin
         ram = {7'h11,7'hD,7'h8,7'h15,7'h9,7'h3,7'h12,7'hC,7'hA,7'h0,7'h4,7'hF,7'h13, 7'h2,7'h5,
                      7'hA,7'h1A,7'h13,7'hD,7'hD,7'h1,7'h0,7'h1F,7'h1F,7'h3,7'hC,7'hB,7'hE,7'hB,7'h19,
                      7'h5,7'h12,7'h0,7'h9,7'h2,7'h1A,7'h1A,7'hA,7'h18,7'h7,7'hE,7'h14,7'h4,7'h2,7'h1F,
                      7'h0,7'h0,7'h1F,7'h16,7'h10,7'h4,7'h3,7'hA,7'h15,7'hC,7'h5,7'h15,7'hE,7'h13,7'h5,
                      7'h1F,7'h8,7'h5,7'h12,7'hB,7'h5,7'h5,7'hF,7'h0,7'h1F,7'h0,7'h0,7'h7,7'h7,7'hE,7'hE,
                      7'h4,7'h10,7'h10,7'h18,7'h18,7'hA,7'h1,7'h7,7'hF,7'h6,7'hA,7'h1A,7'h8,7'h12,7'h15,
                      7'hE,7'h1,7'h1F,7'h1F,7'h0,7'h30,7'h1D,7'h25,7'h34,7'h2,7'h10,7'h6,7'hE,7'h35,7'h1F,
                      7'h22,7'h5,7'h12,7'h2A,7'h35,7'h1F,7'h2D,7'h3F,7'h2E,7'h34,7'h1,7'h0,7'h3F,7'h3F,
                      7'h11,7'h4,7'h1E,7'h7,7'h2B, 7'hB,7'h18,7'h6,7'hE,7'h15,7'h6,7'h27,7'h11,7'h28,
                      7'h2F,7'h7,7'hF,7'h29,7'h13,7'h3F,7'h3F,7'h0,7'h0,7'h3F,7'h7,7'h2,7'h33,7'h1F,7'h2E,
                      7'h17,7'h10,7'hB,7'h35,7'h28,7'hA,7'h7,7'h2E,7'h35,7'h21,7'h23,7'h3F,7'h19,7'h23,7'h26,
                      7'h0,7'h3F,7'h0,7'h0,7'h13,7'h30,7'h29,7'h1,7'hA,7'h7,7'h24,7'h2F,7'h5,7'h1D,7'h34,
                      7'h34,7'h1F,7'hA,7'h1A,7'h6,7'h3,7'h2,7'h3F,7'h33,7'h1,7'h3F,7'h3F,7'h0,
                      7'hD,7'h30,7'h50,7'h42,7'h4,7'h4A,7'h7,7'h1E,7'h4C,7'h34,7'h25,7'h3C,7'h7F,7'h31,7'h49,
                      7'h1F,7'h4A,7'h49,7'h17,7'h7F,7'h1,7'h0,7'h7F,7'h7F,7'h45,7'h3F,7'h4A,7'h38,7'h40,7'h4D,
                      7'h39,7'h41,7'h6,7'h10,7'h33,7'h7F,7'h40,7'h7F,7'h44,7'h9,7'h30,7'h3E,7'h36,7'h1B,7'h7F,
                      7'h0,7'h0,7'h7F,7'h33,7'hF,7'h0,7'h50,7'h18,7'h19,7'h2A,7'h36,7'h2C,7'h47,7'h47,7'h9,
                      7'h43,7'h23,7'h7F,7'h3A,7'h7F,7'h1D,7'h7F,7'h35,7'h0,7'h7F,7'h0,7'h0,7'h10,7'h1D,7'h24,
                      7'h29,7'h2C,7'h38,7'h3B,7'h25,7'h32,7'h18,7'h7F,7'h41,7'h4,7'h41,7'h34,7'h7F,7'h4,7'h7F,
                      7'h49,7'h34,7'h1,7'h7F,7'h7F,7'h0};
     end
    
    //Determine in the encoder logic send the address offset with the requested z don't handle it in memory 
    //Note the order for the Req_Z is the last Z value defined in the Z_VAl Array is corresponds to the most sig bit of Req_z
    //Determine in the encoder logic send the address offset with the requested z don't handle it in memory 
    always @(posedge CLK) begin
        for(int i=0; i<NUM_PARITY_BLKS; i++) begin
            for(int q=0; q<P_LVL; q++) begin
                data_out[i+q] <= ram[addr+q +(i*(DEPTH/NUM_PARITY_BLKS)-1)];
            end
        end
    end

endmodule