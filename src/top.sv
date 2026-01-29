`timescale 1ns / 1ps
`default_nettype none
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Author: Ryan Bride 
// Create Date: 09/09/2025
// Module Name: Highspeed Paramatized QC-LDPC Encoder
// Description: 
//      The top level of this design takes a generic input that is the width of the 
//      defined maximum Z. For implementation inside an actual design, I would suggest 
//      Implementing a more robust FIFO or whatever you find best suits your Design.
//      Further the top level of the Controller stores all provided information data into
//      a singular buffer, for space reasons the fifo that I suggested would ideally be storing that
//      to instead of having a random very long buffer just sitting in this, 
//
//  The following Parameters Effect the architectural structure of the module. All other values Throw and Error
//  ROM_TYPE:  Chooses the Selected ROM Structure used to store Protoype Matrix/Shift Values. 
//      0 = Single-Rate LUT Based Rom (i.e only one speed and one Proto Matrix defined for that speed)   
//      1 = Multi-RATE LUT, Simple LUT Based rom that supports 3 seperate Z's
//      2 = BRAM Based ROM Supporting 3 Seperate Z's  
//  
//  LEVEL_OF_PARALLELIZATION: Indicates the number of Column calculations done per step. 
//      if the initial base matrix given is 20 columns of m and 4 rows, it will take 20 steps to do with Par 1
//      1 step for each Column, if its to it will take 20, and do 2 columns at a time.
//      Trades througput for dramatically increasing Resource utilization and space. 
//      Default is 1. 
//  
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
module QCLDPCController #(
    parameter int NUM_OF_SUPPORTED_Z                =               3,
    parameter int HIGHEST_SUPPORTED_Z_VAL           =               81,
    parameter int NUM_INFO_BLKS_PER_CODE_BLK        =               20,
    parameter int NUM_PARITY_BLKS_PER_CODE_BLK      =               4,         
    parameter int ROM_TYPE                          =               1,          
    parameter int Z_VALUE_ARRAY[NUM_OF_SUPPORTED_Z] =               {27, 54, 81},
    parameter int LEVEL_OF_PARALLELIZATION          =               1
);
    //Creating Alias for readability
    localparam int MaxZ        = HIGHEST_SUPPORTED_Z_VAL;
    localparam int NumPBlks    = NUM_PARITY_BLKS_PER_CODE_BLK;
    localparam int NumIBlks    = NUM_INFO_BLKS_PER_CODE_BLK;
    localparam int ZsN         = NUM_OF_SUPPORTED_Z; 
    localparam int PLvl        = LEVEL_OF_PARALLELIZATION;

    //ROM Related Local Params
    localparam int PM_ROMDEPTHPmRomDepth = (NumIBlks+NumPBlks) * NumPBlks * ZsN;
    localparam int PmRomWidth = $clog2(MaxZ);
    localparam int PmRomAddrW = $clog2(PmRomDepth)

    // :( input and output defines outside of ( ) because they depend on the Localparam names 
    input  logic CLK;
    input  logic rst_n;
    input  logic en_enc;

    //assert   assert property (@(posedge clk) $onehot(req_Z)) 
    input  logic [ ZsN-1 : 0]                          req_z;   //Unused in ROM_Type 0
    input  logic [ (MaxZ*PLvl)-1 : 0]                  data_in;  
    output logic [ (MaxZ*(NumPBlks+NumIBlks))-1 : 0]   p_data_out;
    // -------------------------------------------------------------------------    
    // End of Module input declaration
    // -------------------------------------------------------------------------    

    //Don't need to initialize because it gets written to anyway and it doesn't matter what start values are
    logic [(MaxZ*(NumIBlks+NumPBlks))-1 : 0] data_buffer;
    logic [MaxZ-1 : 0] parity_blk[(NumPBlks*MaxZ)-1 : 0];    
    


    

endmodule