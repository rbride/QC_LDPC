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
// ------------------------------------------------------------------------
module ProtoMatrixRom_SingleLUT #(
    parameter int THE_Z = 54,                   
    parameter int WIDTH = $clog2(THE_Z), // 6
    parameter int DEPTH = 96,   
    parameter int ADDRW = 7,    //Clog2(Depth)
    parameter int NUM_PARITY_BLKS = 4,
    parameter int P_LVL = 1
)(
    input wire logic [ADDRW-1:0] addr,
    output logic        [WIDTH-1:0] data_out [0:NUM_PARITY_BLKS-1]
); 
    
    (* ram_style = "distributed" *) logic [WIDTH-1:0] memory [0:DEPTH-1];

    initial begin
        if (THE_Z == 27) begin
            $readmemh("648B_5_6_ProtoMat.mem", memory);
        end else if (THE_Z == 54) begin
            $readmemh("1296B_5_6_ProtoMat.mem", memory);
        end else if (THE_Z == 81) begin
            $readmemh("1944B_5_6_ProtoMat.mem", memory);
        end else begin : assert_invalid_cfg
            $fatal( 1, "Invalid Configuration detected, Unsupported Z value: %0d. Supported values are 27, 54, 81\n\
                    f you need a different Z value, ensure that a file is provided and change the code In \n\
                    ProtoMatrixRom.sv to load the .mem file values for your specific Z - aborting", THE_Z);
        end
    end

    always_comb begin
        for(int i=0; i<NUM_PARITY_BLKS; i++) begin
            data_out[i] = memory[addr +(i*(DEPTH/NUM_PARITY_BLKS)-1)];
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

)(
    input wire logic [ADDRW-1:0] addr,
    output logic          [WIDTH-1:0] data_out [0:NUM_PARITY_BLKS-1]

);
 
    (* ram_style = "distributed" *) logic [WIDTH-1:0] memory [0:DEPTH-1];    
    initial begin
        readmemh("27B_5_6_ProtoMat.mem", memory, 0*(DEPTH/NUM_Z), 1*(DEPTH/NUM_Z)-1);
        //readmemh("54B_5_6_ProtoMat.mem", memory, 1*(DEPTH/NUM_Z), 2*(DEPTH/NUM_Z)-1);
        readmemh("81B_5_6_ProtoMat.mem", memory, 2*(DEPTH/NUM_Z), 3*(DEPTH/NUM_Z)-1);
    end
    
    //Note the order for the Req_Z is the last Z value defined in the Z_VAl Array is corresponds to the most sig bit of Req_z
    //Determine in the encoder logic send the address offset with the requested z don't handle it in memory 
    always_comb begin
        for(int i=0; i<NUM_PARITY_BLKS; i++) begin
            data_out[i] = memory[addr+(i*(DEPTH/NUM_PARITY_BLKS)-1)];
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
)(
    input logic CLK,
    input wire logic [ADDRW-1:0] addr,
    output logic         [WIDTH-1:0] data_out [0:NUM_PARITY_BLKS-1]
);

    (* ram_style = "block" *) reg [WIDTH-1:0] ram [0:DEPTH-1];
    
    initial begin
        readmemh("27B_5_6_ProtoMat.mem", ram, 0*(DEPTH/NUM_Z), 1*(DEPTH/NUM_Z)-1);
        readmemh("54B_5_6_ProtoMat.mem", ram, 1*(DEPTH/NUM_Z), 2*(DEPTH/NUM_Z)-1);
        readmemh("81B_5_6_ProtoMat.mem", ram, 2*(DEPTH/NUM_Z), 3*(DEPTH/NUM_Z)-1);
    end
     
    //Determine in the encoder logic send the address offset with the requested z don't handle it in memory 
    //Note the order for the Req_Z is the last Z value defined in the Z_VAl Array is corresponds to the most sig bit of Req_z
    //Determine in the encoder logic send the address offset with the requested z don't handle it in memory 
    always @(posedge CLK) begin
        for(int i=0; i<NUM_PARITY_BLKS; i++) begin
            data_out[i+] <= ram[addr +(i*(DEPTH/NUM_PARITY_BLKS)-1)];
        end
    end
    

endmodule

/*
    string filenames[3];
    initial begin
        foreach (Z_VALUES[i]) begin
            filenames[i] = {sformatf("%0d", Z_VALUES[i]), "B_5_6_ProtoMat.mem"};
            readmemh(filenames[i], ram, (i*(DEPTH/3)), (((i+1)*(DEPTH/3))-1));
        end 
    end
*/