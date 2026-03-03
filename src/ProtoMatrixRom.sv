`timescale 1ns / 1ps
//For yosys (* ram_style = "block" *) selects block RAM
//for yosys (* ram_style = "distributed" *) selects LUT RAM
//For Vivado(* rom_style = "block" *) reg [data_size-1:0] myrom [2**addr_size-1:0];
//infers Ultra (* ram_style = "ultra" *) reg [data_size-1:0] myram [2**addr_size-1:0]; Vivado
//infers LUT(* rom_style = "distributed" *) reg [data_size-1:0] myrom [2**addr_size-1:0]; Vivado
//infers block (* rom_style = "block" *) reg [data_size-1:0] myrom [2**addr_size-1:0]; Vivado 
// Quartus: // synthesis ramstyle = "logic" or "lcell_ram"   Forces LUT based
// ==========================================================================
// Proto Matrix LUT Distributed ROM
// Author: Ryan Bride
// Description: 
//      The Module belows provides a manner to load in a nd store the shift 
//      Values in rom, as an input the module takes an address, and by default
//      outputs 4 (or the total number of generated parity blks) shift values
//      the module also outputs a skip bit as well that is stored in the MSB
//      of the output.
// 
//      To use this module for a different system:
//          1. Set parameters to match your proto matrix dimensions
//          2. Replace $readmemh calls with your shift value files
//             File format: one hex value per line
//             Each value is (NUM_PBLKS * WIDTH) bits wide
//             parity lane 0 in LSBs, lane N in MSBs
//          3. Update Z_VALUES to match your supported Z set
//
//      MEM FILE FORMAT per entry:
//          The memory File should be formated in the same way it is listed 
//          in the IEEE standard for the 801.11, so for instance 4 rows of 20 
//          finally any sentinal value or skip value or whatever (-1) should be 
//          stored as the highest value possible in $Clog2(Z)
// ==========================================================================
module ProtoMatrixRom #(
    parameter int MAXZ                    = 81,
    parameter int NUM_SUP_Z               = 2,
    parameter int NUM_PBLKS               = 4,   //The top module defines one rotator per PBLK ROW 
    parameter int NUM_IBLKS               = 20,  //Also equal to the amount of data messages sen 
    parameter int Z_VALS [0:NUM_SUP_Z-1]  = {27,81},
    
    localparam int WIDTH                  = $clog2(MAXZ),
    localparam int DEPTH                  = NUM_IBLKS*NUM_PBLKS,
    localparam int ADDRW                  = $clog2(DEPTH),
    localparam int WORD_WIDTH             = NUM_PBLKS*WIDTH
)(
    input  logic [ADDRW-1:0] addr,
    output logic [WIDTH:0]   data_out [0:NUM_PBLKS-1]   //Not minus one so there is room for the skip bit [msb = skip bit]
);
    (* ram_style = "distributed" *) logic [WIDTH:0] mem [0:DEPTH*NUM_SUP_Z-1];
    logic [WIDTH-1:0] shift_vals [0:NUM_PBLKS-1];
    logic             skip_vals  [0:NUM_PBLKS-1];

    //Populate the ROM
    genvar zi;
    generate
        for(zi=0; zi< NUM_SUP_Z; zi++) begin : ROM_INIT_SYN
            localparam int OFFSET   = zi * DEPTH;
            localparam int SENTINEL = (1<<$clog2(Z_VALS[zi]))-1;
            
            initial begin
                //Load in the Desired memory block
                if          (Z_VALUES[zi] == 27) begin
                    $readmemh("z27_protomat.mem", mem, OFFSET, (OFFSET+DEPTH-1));
                end else if (Z_VALUES[zi] == 54) begin
                    $readmemh("z54_protomat.mem", mem, OFFSET, (OFFSET+DEPTH-1));
                end else if (Z_VALUES[zi] == 81) begin
                    $readmemh("z81_protomat.mem", mem, OFFSET, (OFFSET+DEPTH-1));
                end

                //Populate Skip Values, scan every lane and put the msb to one if its a skip
                for(int mem_entry=OFFSET; mem_entry<(OFFSET+DEPTH); mem_entry++) begin
                    automatic logic [WIDTH:0] raw_val;
                    raw_val = mem[mem_entry];

                    if(raw_val == WIDTH'(SENTINEL)) begin
                        //Set the skip bit and clear the rest 
                        mem[mem_entry][WIDTH]     = 1'b1;   
                        mem[mem_entry][WIDTH-1:0] = '0;
                    end else begin
                        mem[mem_entry][WIDTH]     = 1'b0;
                    end
                end
            end
        end
    endgenerate

    //Generate Outputs/combine output lanes corresponding to the address
    genvar lane
    generate
        for(lane=0; lane<NUM_PBLKS; lane++) begin
            assign data_out[lane][WIDTH-1:0] = mem[addr+(lane*(DEPTH/NUM_PBLKS)-1)][WIDTH-1:0];
            assign data_out[lane][WIDTH]     = mem[addr+(lane*(DEPTH/NUM_PBLKS)-1)][WIDTH];
        end
    endgenerate

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