`timescale 1ns / 1ps
`default_nettype none
//at compilation provide the requested number of supported blk Lengths 
`define NUM_SUPPORTED_BLK_LEN                   3
`define NUM_INFO_BLKS_PER_CODE_BLK              20
`define NUM_PARITY_BLKS_PER_CODE_BLK            4
`define HIGHEST_SUPPORTED_Z_VAL                 81
// 2 = BRAM     1 = LUT (Multiple Rates)    0 = Single Rate LUT (i.e only one speed)
// For single rate LUT Highest Z supported is also the only Z supported and used   
`define ROM_TYPE                                1
/////////////////////////////////////////////////////////////////////////////////////////////////
// Author: Ryan Bride 
// Create Date: 09/09/2025
// Module Name: Highspeed Paramatized QC-LDPC Encoder
// Description: 
//      The top level of this design takes a generic input that is the width of the 
//      defined maximum Z. For implementation inside an actual design, I would suggest 
//      Implementing a more robust FIFO or whatever you find best suits your Design.
//      Further the top level of the Controller stores all provided information data into
//      a singular buffer, recommend that you resuse some already existing buffer for this data
//      assuming you have one to reduce redundancy and wasteful resource usage.
//      The designs top level is structured in such a way as to not be standalone for the purpose 
//      of determine resource utilization assessments that will be performed upon completion
/////////////////////////////////////////////////////////////////////////////////////////////////
module QCLDPCController #(
    parameter int NUM_Z =               `NUMBER_OF_SUPPORTED_BLOCK_LENGTHS,
    parameter int MAX_Z =               `HIGHEST_SUPPORTED_Z_VAL,
    parameter int NUM_INFO_BLKS =       `NUM_INFO_BLKS_PER_CODE_BLK,
    parameter int NUM_PAR_BLK =         `NUM_PARITY_BLKS_PER_CODE_BLK,
    parameter int ARRAY_VALUE[NUM_Z] =  {27, 54, 81}
)(
    input logic CLK,
    input logic rst_n,
    input logic enable,

    //assert   assert property (@(posedge clk) $onehot(req_Z)) 
    input logic [NUM_Z-1:0] req_z,  
    
    //TODO: The input of data into this block is not defined at all. Manage this in an incorperating design
    //As a result the input width is just defined as the maximum possible value 
    input logic [MAX_Z-1:0] data_in,
    output logic [(MAX_Z*(NUM_PAR_BLK+NUM_INFO_BLKS))-1:0] p_data_out
);

    //Don't need to initialize because it gets written to anyway and it doesn't matter what start values are
    logic [(MAX_Z*(NUM_INFO_BLKS+NUM_PAR_BLK))-1:0] data_buffer;

    logic [MAX_Z-1:0] parity_blk[(NUM_PAR_BLK*MAX_Z)-1:0];    


    QCLDPCEncoder #(                 
                .NUM_Z (NUM_Z),
                .MAX_Z (MAX_Z),
                .NUM_INFO_BLKS  ( `NUM_INFO_BLKS_PER_CODE_BLK ),
                .NUM_PARITY_BLKS( `NUM_PARITY_BLKS_PER_CODE_BLK ),
                )
        Encoder (
            .CLK(CLK),
            .rst_n(rst_n),
            .en_encoder(enable) 
            .req_z(req_Z),  
            .info_blk(data_in),
            .parity_blk(parity_blk)
        );

endmodule

/////////////////////////////////////////////////////////////////////////////////////////////////
// The module below defines the actual encoder itself, generation fo this encoder 
// is highly parameterized and should be structured in such a way as to be 
// highly re-usable and thus utilizes as generic definitions as possible within
//
// TODO: 
//          Add parameters and to perform the number of Column Xoring and Accumulation requested 
//          instead of the defined 1, to allow for changes in the number of pipeline stages 
//          at the cost of greater area, and higher timing requirements.  
/////////////////////////////////////////////////////////////////////////////////////////////////
module QCLDPCEncoder #(
    parameter int NUM_Z = 1,
    parameter int MAX_Z = 81,
    parameter int NUM_INFO_BLKS = 20,  // number of info blocks
    parameter int NUM_PARITY_BLKS = 4, // number of parity blocks (also number of rows in the proto matrix)
    parameter int TOTAL_BLKS = NUM_INFO_BLKS + NUM_PARITY_BLKS,
    parameter int Z_VALUES[NUM_Z] = {27, 54, 81},
) (
    input  logic                   CLK,
    input  logic                   rst_n,
    input  logic                   en_encoder,
    input  logic [NUM_Z-1:0]       req_z,      //NOTE: Must always be ONE_Hot otherwise its going to give an error
    input  logic [Z-1:0]           info_blk, // input blocks
    output logic [Z-1:0]           parity_blk[NUM_PARITY_BLKS-1:0], // parity blocks
);

    localparam int PmRomDepth = (NUM_INFO_BLKS+NUM_PARITY_BLKS) * NUM_PARITY_BLKS * NUM_Z;
    localparam int PmRomWidth = $clog2(MAX_Z);
    localparam int PmRomAddrW = $clog2(PmRomDepth)
    
    //TODO: Investigate how restruturing the rom to be groups of 4 values at an address or in a row affects sythesis
    wire shift_addr  [PmRomAddrW-1:0];   
    wire [PmRomWidth-1:0] shift_values [0:NUM_PARITY_BLKS];

    //Define storage registers for the intermediate values used by accumulators one for each generated Parity Block
    reg [Z-1:0] accum_regs [0:$clog2(NUM_PARITY_BLKS)-1]; 

    //output of the rotate functions
    logic [Z-1:0] rotated_data [0:$clog2(NUM_PARITY_BLKS)-1];

    //Counter Block for counting cycle number
    logic [$clog2(NUM_INFO_BLKS)-1:0] c_cnt;

 
    generate
        case (`ROM_TYPE)
            0: begin : Single_LUT_ROM
                ProtoMatrixRom_SingleLUT #(   
                                .Z(Z), 
                                .NUM_PARITY_BLKS(NUM_PARITY_BLKS),
                                .WIDTH(PmRomWidth), 
                                .DEPTH(PmRomDepth), 
                                .ADDRW(PmRomAddrW)

                            )  
                    GenROM (
                            .addr(shift_addr),
                            .data_out(shift_values)
                    );

            end

            1: begin : Multi_LUT_ROM 
                ProtoMatrixRom_MultiLUT #(
                                .NUM_Z(NUM_Z),
                                .Z_VALUES(Z_VALUES),
                                .NUM_PARITY_BLKS(NUM_PARITY_BLKS),
                                .DEPTH(PmRomDepth),
                                .WIDTH(PmRomWidth),
                                .ADDRW(PmRomAddrW)
                            )
                    GenROM (
                            .addr(shift_addr),
                            .data_out(shift_values)
                    ); 
            end
            
            //TODO Possible error could be improper port defintion of Z_values but whatever
            //Same for .data_out since multidimentional Array Port declarations can be...
            2: begin : BRAM_ROM
                ProtoMatrixRom_BRAM #(
                                .NUM_Z(NUM_Z),
                                .NUM_PARITY_BLKS(NUM_PARITY_BLKS),
                                .Z_VALUES(Z_VALUES),
                                .DEPTH(PmRomDepth),
                                .WIDTH(PmRomWidth),
                                .ADDRW(PmRomAddrW)
                                )
                    GenRom (
                            .addr(shift_addr),
                            .data_out(shift_values)
                    );
            end 

            default: begin : assert_invalid_cfg
                $fatal(1, "Invalid ROM Configuration Selected - Aborting");
            end
        endcase 
    endgenerate

    
    // -------------------------------------------------------------------------
    // Barrel Shifting function called N-M times based, must be in parallel
    // thus defined as function automatic as it should be called dynamically
    // -------------------------------------------------------------------------    
    // TODO  TODO TODO TODO TODO TODO TODO MAKE SURE You do nothing for max value 
    // TODO TODO TODO DEFINE A WIDTH THAT CORRESPONDS TO Z that is selected see the top part of notes!!!!
    // as that is the storage value for do nothing or whatever don't shift
    // Function uses concat then slice approach, TODO: look into multi-stage Mux for speed trade offs
    function automatic logic [Z-1:0] Right_CyclicShifter(
        input logic [Z-1:0]             data,
        input logic [PmRomWidth-1:0]    rotval
    );
    logic [2*Z -1: 0] data_repeated;
    begin
        data_repeated = {data, data};
        //Add a diagram of this working or example of this working from notes or whatever maybe
        return( data_repeated[ (Z-1) + rotval -: Z]);
    end 
    endfunction : Right_CyclicShifter
    
    //Call the function for each of the Lanes 
    genvar inari;
    generate 
        for(inari = 0; inari<NUM_PARITY_BLKS; inari++) begin : ROTATE_INST
            assign rotated_data[i] = Right_CyclicShifter(info_blk ,shift_values[i] )
        end

    endgenerate





    // -------------------------------------------------------------------------
    // This is a small outward nested always_ff block that is used for counting
    // Cycles, then finally doing the parity additions and 
    // -------------------------------------------------------------------------
    always_ff @(posedge CLK or negedge rst_n) begin
        if(!rst_n) begin
            c_cnt           <= '0;
            shift_addr      <= '0;
            foreach (accum_regs[i])
                accum_regs[i] <= '0;
        end else if(!en_encoder) begin
            //Pretty much do nothing just hold
            c_cnt           <= c_cnt;
            shift_addr      <= shift_addr;
        end 
        //Otherwise start encoding
        else begin
            
        end
    end

    always_comb



endmodule


