// `timescale 1ns/1ps
// module tb_pipelinedCircularShifter;

//     // Test parameters
//     localparam int MAXZ = 81;
//     localparam int CLK_PERIOD = 10;
//     localparam int PIPE1_ROTATES_PER_CYCLE = 2;

//     // DUT IO
//     logic clk;
//     logic rst_n;

//     // shared inputs for both shifters
//     logic [MAXZ-1:0] in_data;
//     logic [$clog2(MAXZ)-1:0] shift_val;

//     // outputs
//     logic [MAXZ-1:0] out2; // pipelinedCircularShifter2
//     logic [MAXZ-1:0] out1; // pipelinedCircularShifter1

//     // test vectors and control declared at module scope (Verilator-friendly)
//     logic [MAXZ-1:0] patterns [0:5];
//     int latency;
//     int total_tests;
//     int total_fail;
//     int p;
//     int s;
//     logic [MAXZ-1:0] expected;

//     // Instantiate DUTs
//     pipelinedCircularShifterFMAX #(.MAXZ(MAXZ)) dut2 (
//         .CLK(clk),
//         .rst_n(rst_n),
//         .in_data(in_data),
//         .shift_val(shift_val),
//         .out_data(out2)
//     );

//     pipelinedCircularShifter #(
//         .MAXZ(MAXZ),
//         .ROTATES_PER_CYCLE(PIPE1_ROTATES_PER_CYCLE)
//     ) dut1 (
//         .CLK(clk),
//         .rst_n(rst_n),
//         .in_data(in_data),
//         .shift_val(shift_val),
//         .out_data(out1)
//     );

//     // clock
//     initial clk = 0;
//     always #(CLK_PERIOD/2) clk = ~clk;

//     // rotate-right reference function
//     function automatic logic [MAXZ-1:0] rot_right(input logic [MAXZ-1:0] data, input int s);
//         int ss;
//         begin
//             ss = s % MAXZ;
//             if (ss == 0) rot_right = data;
//             else rot_right = (data >> ss) | (data << (MAXZ - ss));
//         end
//     endfunction

//     // helper: tick n clock cycles
//     task automatic tick(input int cycles);
//         int i;
//         for (i = 0; i < cycles; i++) @(posedge clk);
//     endtask



//     initial begin
//         // populate patterns (module-scope vars)
//         // patterns[0] = 16'b10110101_10110101;
//         // patterns[1] = 16'b00001111_00001111;
//         // patterns[2] = 16'b11110000_11110000;
//         // patterns[3] = 16'b01010101_01010101;
//         // patterns[4] = 16'b00110011_00110011;
//         // patterns[5] = 16'hA5_A5;
//         patterns[0] = 81'b001101111100100000001101101011101110101101100100010001000111110101001101000111110;
//         patterns[1] = 81'b101111100100101000110000101111011101101111010010001101011010101010010110011101110;
//         patterns[2] = 81'b001010011100100001001001011111010101000011000011100010110101001110100011010011001;
//         patterns[3] = 81'b111010001011111001001100010011100100001000111111000100000010010011011001110010011;
//         patterns[4] = 81'b101001110001101001111010010000110111101001011101100101001000011001110010101000111;
//         patterns[5] = 81'b010010011010110000001111010100110101100011011001111100001100001110101111000100101;
        
//         // reset
//         rst_n = 0;
//         in_data = '0;
//         shift_val = '0;
//         tick(5);
//         rst_n = 1;
//         tick(1);

//         $display("STARTING pipelinedCircularShifter TEST (MAXZ=%0d)", MAXZ);

//         // set latency and counters
//         latency = 10;
//         total_tests = 0;
//         total_fail = 0;

//         // run tests
//         for (p = 0; p <= 5; p = p + 1) begin
//             in_data = patterns[p];
//             for (s = 0; s < MAXZ; s = s + 1) begin
//                 shift_val = s[$clog2(MAXZ)-1:0];
//                 // wait enough cycles for pipeline to produce valid output
//                 tick(latency);

                
//                 expected = rot_right(in_data, s);

//                 total_tests = total_tests + 1;

//                 if (out2 !== expected) begin
//                     $display("%0t ERROR dut2: in=%b shift=%0d out=%b expected=%b", $time, in_data, s, out2, expected);
//                     total_fail = total_fail + 1;
//                 end

//                 if (out1 !== expected) begin
//                     $display("%0t ERROR dut1: in=%b shift=%0d out=%b expected=%b", $time, in_data, s, out1, expected);
//                     total_fail = total_fail + 1;
//                 end
//             end
//         end

//         if (total_fail == 0)
//             $display("ALL TESTS PASSED: %0d vectors", total_tests);
//         else
//             $display("TESTS FAILED: %0d failures out of %0d vectors", total_fail, total_tests);

//         $finish;
//     end

//     // --- VCD dump ---
//     initial begin
//         $dumpfile("sim.vcd");   // name of the VCD file
//         $dumpvars(0, tb);       // dump all signals in tb hierarchy
//     end

// endmodule

`timescale 1ns/100ps
module tb_pipelinedCircularShifter;

    // Test parameters
    localparam int MAXZ = 81;
    localparam int PIPE1_ROTATES_PER_CYCLE = 1;  //One for every Split 
    localparam int PIPE2_ROTATES_PER_CYCLE = 2;  //One for every Split 
    localparam int PIPE3_ROTATES_PER_CYCLE = 3;  //One for every Split 
    localparam int PIPE4_ROTATES_PER_CYCLE = 4;  //One for every Split 

    
    // DUT IO
    logic clk;
    logic rst_n;
    logic valid_in;
    logic [MAXZ-1:0] in_data;
    logic [$clog2(MAXZ)-1:0] shift_val;
    logic [MAXZ-1:0] expected;
    
    logic valid_out1;
    logic [MAXZ-1:0] out_data1;

    logic valid_out2;
    logic [MAXZ-1:0] out_data2;

    logic valid_out3;
    logic [MAXZ-1:0] out_data3;

    logic valid_out4;
    logic [MAXZ-1:0] out_data4;

    logic valid_out5;
    logic [MAXZ-1:0] out_data5;

    logic valid_out6;
    logic [MAXZ-1:0] out_data6;
    
    logic valid_out7;
    logic [MAXZ-1:0] out_data7;

    logic valid_outFMax;
    logic [MAXZ-1:0] out_dataFMax;

    logic pipe1waiting;
    logic pipe2waiting;
    logic pipe3waiting;
    logic pipe4waiting;
    logic pipe5waiting;
    logic pipe6waiting;
    logic pipe7waiting;
    
    logic pipeFMaxwaiting;

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
    // pipelinedCircularShifter #(
    //     .MAXZ(MAXZ),
    //     .ROTATES_PER_CYCLE(PIPE5_ROTATES_PER_CYCLE)
    // ) dut5 
    // (
    //     .CLK(clk),
    //     .rst_n(rst_n),
    //     .valid_in(valid_in),
    //     .in_data(in_data),
    //     .shift_val(shift_val),
    //     .valid_out(valid_out5),
    //     .out_data(out_data5)
    // );
    // pipelinedCircularShifter #(
    //     .MAXZ(MAXZ),
    //     .ROTATES_PER_CYCLE(PIPE6_ROTATES_PER_CYCLE)
    // ) dut6
    // (
    //     .CLK(clk),
    //     .rst_n(rst_n),
    //     .valid_in(valid_in),
    //     .in_data(in_data),
    //     .shift_val(shift_val),
    //     .valid_out(valid_out6),
    //     .out_data(out_data6)
    // );

    //Doesn't work for 7
    // pipelinedCircularShifter #(
    //     .MAXZ(MAXZ),
    //     .ROTATES_PER_CYCLE(PIPE6_ROTATES_PER_CYCLE)
    // ) dut7
    // (
    //     .CLK(clk),
    //     .rst_n(rst_n),
    //     .valid_in(valid_in),
    //     .in_data(in_data),
    //     .shift_val(shift_val),
    //     .valid_out(valid_out7),
    //     .out_data(out_data7)
    // );

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
        int total_tests = 0;
        int total_fail  = 0;
        pipe1waiting = 0;
        pipe2waiting = 0;
        pipe3waiting = 0;
        pipe4waiting = 0;
        pipe5waiting = 0;
        pipe6waiting = 0;
        pipe7waiting = 0;
        pipeFMaxwaiting = 0;
        

        $urandom(seed);
        //Reset
        rst_n = 0;
        valid_in = 0;
        in_data = '0;
        shift_val = '0;
        tick(5);
        rst_n = 1;

        $display("STARTING pipelinedCircularShifter TEST (MAXZ=%0d)", MAXZ);

        for (int test_idx = 0; test_idx < 101; test_idx++) begin
            // Random input and shift
            in_data = {$urandom, $urandom, $urandom}[MAXZ-1:0];
       
            shift_val = $urandom_range(0, MAXZ-1)[$clog2(MAXZ)-1:0];
            expected = rot_right(in_data, int'(shift_val));
            
            valid_in  = 1;

            pipe1waiting = 0;
            pipe2waiting = 0;
            pipe3waiting = 0;
            pipe4waiting = 0;
            pipeFMaxwaiting = 0;
            
            //Hold the valid for a cycle
            tick(1);
            valid_in = 0;

            //Wait for Each DUT To Assert Valid_out
            while( !(pipe1waiting & pipe2waiting & pipe3waiting & pipeFMaxwaiting )) begin
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

                // if (valid_out5) begin
                //     logic [MAXZ-1:0] expected;
                //     pipe5waiting = 1'b1;
                //     expected = rot_right(in_data, int'(shift_val));

                //     total_tests++;
                //     if (out_data5 !== expected) begin
                //         $display("%0t ERROR: Rotates_Per_Cycle=%d in=%b shift=%0d out=%b expected=%b",
                //                  $time, 5, in_data, shift_val, out_data5, expected);
                //         total_fail++;
                //     end
                // end

                // if (valid_out6) begin
                //     logic [MAXZ-1:0] expected;
                //     pipe6waiting = 1'b1;
                //     expected = rot_right(in_data, int'(shift_val));

                //     total_tests++;
                //     if (out_data6 !== expected) begin
                //         $display("%0t ERROR: Rotates_Per_Cycle=%d in=%b shift=%0d out=%b expected=%b",
                //                  $time, 6, in_data, shift_val, out_data6, expected);
                //         total_fail++;
                //     end
                // end

                // if (valid_out7) begin
                //     logic [MAXZ-1:0] expected;
                //     pipe7waiting = 1'b1;
                //     expected = rot_right(in_data, int'(shift_val));

                //     total_tests++;
                //     if (out_data7 !== expected) begin
                //         $display("%0t ERROR: Rotates_Per_Cycle=%d in=%b shift=%0d out=%b expected=%b",
                //                  $time, 7, in_data, shift_val, out_data7, expected);
                //         total_fail++;
                //     end
                // end

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


