`timescale 1ns/10ps
module tb_pipelinedCircularShifter;

    // Test parameters
    localparam int MAXZ = 81;
    localparam int PIPE1_ROTATES_PER_CYCLE = 1;  //One for every Split 
    localparam int PIPE2_ROTATES_PER_CYCLE = 2;  
    localparam int PIPE3_ROTATES_PER_CYCLE = 3;  
    localparam int PIPE4_ROTATES_PER_CYCLE = 4;   
    localparam int PIPE5_ROTATES_PER_CYCLE = 5;  
    localparam int PIPE6_ROTATES_PER_CYCLE = 6;  
    localparam int PIPE7_ROTATES_PER_CYCLE = 7;  
    
    // DUT IO
    logic clk;
    logic rst_n;
    logic valid_in;
    logic [MAXZ-1:0] in_data;
    logic [$clog2(MAXZ)-1:0] shift_val;
    logic [MAXZ-1:0] expected;

    //Pipeline Valid Signals    
    logic valid_out1, valid_out2, valid_out3;
    logic valid_out4, valid_out5, valid_out6;
    logic valid_out7, valid_outFMax;

    //Pipeline Data output Signals
    logic [MAXZ-1:0] out_data1, out_data2;
    logic [MAXZ-1:0] out_data3, out_data4;
    logic [MAXZ-1:0] out_data5, out_data6;
    logic [MAXZ-1:0] out_data7, out_dataFMax;

    logic pipe1waiting, pipe2waiting, pipe3waiting;
    logic pipe4waiting, pipe5waiting, pipe6waiting;
    logic pipe7waiting, pipeFMaxwaiting;

    // ------------------------------------------------------------
    // Instatiate all the shifters 
    // ------------------------------------------------------------
    pipelinedCircularShifter #(
        .MAXZ(MAXZ),
        .ROTATES_PER_CYCLE(PIPE1_ROTATES_PER_CYCLE)
    ) dut1 
    (
        .CLK(clk),
        .rst_n(rst_n),
        .valid_in(valid_in),
        .in_data(in_data),
        .shift_val(shift_val),
        .valid_out(valid_out1),
        .out_data(out_data1)
    );
    pipelinedCircularShifter #(
        .MAXZ(MAXZ),
        .ROTATES_PER_CYCLE(PIPE2_ROTATES_PER_CYCLE)
    ) dut2
    (
        .CLK(clk),
        .rst_n(rst_n),
        .valid_in(valid_in),
        .in_data(in_data),
        .shift_val(shift_val),
        .valid_out(valid_out2),
        .out_data(out_data2)
    );
    pipelinedCircularShifter #(
        .MAXZ(MAXZ),
        .ROTATES_PER_CYCLE(PIPE3_ROTATES_PER_CYCLE)
    ) dut3 
    (
        .CLK(clk),
        .rst_n(rst_n),
        .valid_in(valid_in),
        .in_data(in_data),
        .shift_val(shift_val),
        .valid_out(valid_out3),
        .out_data(out_data3)
    );
    pipelinedCircularShifter #(
        .MAXZ(MAXZ),
        .ROTATES_PER_CYCLE(PIPE4_ROTATES_PER_CYCLE)
    ) dut4 
    (
        .CLK(clk),
        .rst_n(rst_n),
        .valid_in(valid_in),
        .in_data(in_data),
        .shift_val(shift_val),
        .valid_out(valid_out4),
        .out_data(out_data4)
    );
    pipelinedCircularShifter #(
        .MAXZ(MAXZ),
        .ROTATES_PER_CYCLE(PIPE5_ROTATES_PER_CYCLE)
    ) dut5 
    (
        .CLK(clk),
        .rst_n(rst_n),
        .valid_in(valid_in),
        .in_data(in_data),
        .shift_val(shift_val),
        .valid_out(valid_out5),
        .out_data(out_data5)
    );
    pipelinedCircularShifter #(
        .MAXZ(MAXZ),
        .ROTATES_PER_CYCLE(PIPE6_ROTATES_PER_CYCLE)
    ) dut6
    (
        .CLK(clk),
        .rst_n(rst_n),
        .valid_in(valid_in),
        .in_data(in_data),
        .shift_val(shift_val),
        .valid_out(valid_out6),
        .out_data(out_data6)
    );

    pipelinedCircularShifter #(
        .MAXZ(MAXZ),
        .ROTATES_PER_CYCLE(PIPE6_ROTATES_PER_CYCLE)
    ) dut7
    (
        .CLK(clk),
        .rst_n(rst_n),
        .valid_in(valid_in),
        .in_data(in_data),
        .shift_val(shift_val),
        .valid_out(valid_out7),
        .out_data(out_data7)
    );

    // Instantiate DUTs
    pipelinedCircularShifterFMAX #(
        .MAXZ(MAXZ)
    ) dutFMax (
        .CLK(clk),
        .rst_n(rst_n),
        .valid_in(valid_in),
        .in_data(in_data),
        .shift_val(shift_val),
        .out_data(out_dataFMax),
        .valid_out(valid_outFMax)
    );


    initial clk = 0;
    always #1 clk = ~clk;
    //Time waste task
    task tick(int n = 1);
        repeat(n) @(posedge clk);
    endtask

    // rotate-right reference function
    function automatic logic [MAXZ-1:0] rot_right(input logic [MAXZ-1:0] data, input int s);
        int ss;
        begin
            ss = s % MAXZ;
            if (ss == 0) rot_right = data;
            else rot_right = (data >> ss) | (data << (MAXZ - ss));
        end
    endfunction

    int seed = 32'h12345678;
    
    // ------------------------------------------------------------
    // Testbench
    // ------------------------------------------------------------
    initial begin
        int total_tests = 0;        int total_fail  = 0;
        pipe1waiting = 0;   pipe2waiting = 0;   pipe3waiting = 0;
        pipe4waiting = 0;   pipe5waiting = 0;   pipe6waiting = 0;
        pipe7waiting = 0;   pipeFMaxwaiting = 0;
        
        $urandom(seed);
        //Reset
        rst_n = 0;  valid_in = 0;   in_data = '0;   shift_val = '0;
        tick(5);
        rst_n = 1;


        $display("STARTING pipelinedCircularShifter TEST (MAXZ=%0d) For all Permutations Allowed Under MAXZ of 81", MAXZ);

        for (int test_idx = 0; test_idx < 500; test_idx++) begin
            // Random input and shift
            in_data = {$urandom, $urandom, $urandom}[MAXZ-1:0];
       
            shift_val = $urandom_range(0, MAXZ-1)[$clog2(MAXZ)-1:0];
            expected = rot_right(in_data, int'(shift_val));
            
            valid_in  = 1;

            pipe1waiting = 0;   pipe2waiting = 0;   pipe3waiting = 0;
            pipe4waiting = 0;   pipe5waiting = 0;   pipe6waiting = 0;
            pipe7waiting = 0;   pipeFMaxwaiting = 0;
            
            //Hold the valid for a cycle
            tick(1);
            valid_in = 0;

            //Wait for Each DUT To Assert Valid_out
            while( !(pipe1waiting & pipe2waiting & pipe3waiting & pipeFMaxwaiting & pipe4waiting
                        &pipe5waiting &pipe6waiting &pipe7waiting )) begin
                tick(1);

                if (valid_out1) begin
                    //logic [MAXZ-1:0] expected;
                    pipe1waiting = 1'b1;
                    //expected = rot_right(in_data, int'(shift_val));

                    total_tests++;
                    if (out_data1 !== expected) begin
                        $display("%0t ERROR: Rotates_Per_Cycle=%d in=%b shift=%0d out=%b expected=%b",
                                 $time, 1, in_data, shift_val, out_data1, expected);
                        total_fail++;
                    end
                end

                if (valid_out2) begin
                    pipe2waiting = 1'b1;
                    total_tests++;
                    if (out_data2 !== expected) begin
                        $display("%0t ERROR: Rotates_Per_Cycle=%d in=%b shift=%0d out=%b expected=%b",
                                 $time, 2, in_data, shift_val, out_data2, expected);
                        total_fail++;
                    end
                end

                if (valid_out3) begin
                     pipe3waiting = 1'b1;
                    total_tests++;
                    if (out_data3 !== expected) begin
                        $display("%0t ERROR: Rotates_Per_Cycle=%d in=%b shift=%0d out=%b expected=%b",
                                 $time, 3, in_data, shift_val, out_data3, expected);
                        total_fail++;
                    end
                end
                
                
                if (valid_out4) begin
                    pipe4waiting = 1'b1;
                    total_tests++;
                    if (out_data4 !== expected) begin
                        $display("%0t ERROR: Rotates_Per_Cycle=%d in=%b shift=%0d out=%b expected=%b",
                                 $time, 4, in_data, shift_val, out_data4, expected);
                        total_fail++;
                    end
                end

                if (valid_out5) begin
                    logic [MAXZ-1:0] expected;
                    pipe5waiting = 1'b1;
                    expected = rot_right(in_data, int'(shift_val));

                    total_tests++;
                    if (out_data5 !== expected) begin
                        $display("%0t ERROR: Rotates_Per_Cycle=%d in=%b shift=%0d out=%b expected=%b",
                                 $time, 5, in_data, shift_val, out_data5, expected);
                        total_fail++;
                    end
                end

                if (valid_out6) begin
                    logic [MAXZ-1:0] expected;
                    pipe6waiting = 1'b1;
                    expected = rot_right(in_data, int'(shift_val));

                    total_tests++;
                    if (out_data6 !== expected) begin
                        $display("%0t ERROR: Rotates_Per_Cycle=%d in=%b shift=%0d out=%b expected=%b",
                                 $time, 6, in_data, shift_val, out_data6, expected);
                        total_fail++;
                    end
                end

                if (valid_out7) begin
                    logic [MAXZ-1:0] expected;
                    pipe7waiting = 1'b1;
                    expected = rot_right(in_data, int'(shift_val));

                    total_tests++;
                    if (out_data7 !== expected) begin
                        $display("%0t ERROR: Rotates_Per_Cycle=%d in=%b shift=%0d out=%b expected=%b",
                                 $time, 7, in_data, shift_val, out_data7, expected);
                        total_fail++;
                    end
                end

                if (valid_outFMax) begin
                    pipeFMaxwaiting = 1'b1;
                    total_tests++;
                    if (out_dataFMax !== expected) begin
                        $display("%0t ERROR: FMAX_PIPE                     in=%b shift=%0d out=%b expected=%b",
                                 $time, in_data, shift_val, out_data3, expected);
                        total_fail++;
                    end
                end

            end
        end
        
        if (total_fail == 0)
            $display("ALL TESTS PASSED: %0d vectors", total_tests);
        else
            $display("TESTS FAILED: %0d failures out of %0d vectors", total_fail, total_tests);

        $finish;

    end

    //--- VCD dump ---
    initial begin
        $dumpfile("sim.vcd");   // name of the VCD file
        $dumpvars(0, tb);       // dump all signals in tb hierarchy
    end

endmodule
