`timescale 1ns/10ps 
import qcldpcPkg::*;


module qcldpc_tb_top;
    localparam real CLK_PERIOD = 1.1111; //Approx 900Mhz
    localparam int MAXZ        = 81;
    localparam int NUM_PBLKS   = 4;
    localparam int IBLKS_NUM   = 20;


    logic CLK, rst_n
    //DUT Signals for the Encoder Top
    logic in_valid, in_last, in_ready;
    z_req_t req_z; 
    logic [MAXZ-1:0]            i_data;
    logic [MAXZ*NUM_PBLKS-1:0]  p_data_out;
    
    

    always #(CLK_PERIOD/2) CLK = ~CLK;

    //Initial reset
    initial begin
        rst_n = 0;
        repeat(10) @(posedge CLK);  //Hold Reset for 10 seconds
        rst_n = 1;  
    end

    

endmodule