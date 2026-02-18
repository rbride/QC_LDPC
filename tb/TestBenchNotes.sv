// `timescale 1ns/1ps
// module tb_pipelinedCircularShifter;

//     // Test parameters
//     localparam int MAXZ = 81;
//     localparam int PIPE1_ROTATES_PER_CYCLE = 1;  //One for every Split 

    
//     // DUT IO
//     logic clk;
//     logic rst_n;
//     logic valid_in;
//     logic [MAXZ-1:0] in_data;
//     logic [$clog2(MAXZ)-1:0] shift_val;
    
//     logic valid_out1;
//     logic [MAXZ-1:0] out_data1;

//     logic valid_out2;
//     logic [MAXZ-1:0] out_data2;

//     logic valid_out3;
//     logic [MAXZ-1:0] out_data3;

//     logic valid_out4;
//     logic [MAXZ-1:0] out_data4;

//     logic valid_out5;
//     logic [MAXZ-1:0] out_data5;

//     logic valid_out6;
//     logic [MAXZ-1:0] out_data6;
    
//     logic valid_out7;
//     logic [MAXZ-1:0] out_data7;

//     logic pipe1waiting;
//     logic pipe2waiting;
//     logic pipe3waiting;
//     logic pipe4waiting;
//     logic pipe5waiting;
//     logic pipe6waiting;
//     logic pipe7waiting;


//     // ------------------------------------------------------------
//     // Instatiate all the shifters 
//     // ------------------------------------------------------------
//     pipelinedCircularShifter #(
//         .MAXZ(MAXZ),
//         .ROTATES_PER_CYCLE(PIPE1_ROTATES_PER_CYCLE)
//     ) dut1 
//     (
//         .CLK(clk),
//         .rst_n(rst_n),
//         .valid_in(valid_in),
//         .in_data(in_data),
//         .shift_val(shift_val),
//         .valid_out(valid_out1),
//         .out_data(out_data1)
//     );
//     pipelinedCircularShifter #(
//         .MAXZ(MAXZ),
//         .ROTATES_PER_CYCLE(PIPE2_ROTATES_PER_CYCLE)
//     ) dut2
//     (
//         .CLK(clk),
//         .rst_n(rst_n),
//         .valid_in(valid_in),
//         .in_data(in_data),
//         .shift_val(shift_val),
//         .valid_out(valid_out2),
//         .out_data(out_data2)
//     );
//     pipelinedCircularShifter #(
//         .MAXZ(MAXZ),
//         .ROTATES_PER_CYCLE(PIPE3_ROTATES_PER_CYCLE)
//     ) dut3 
//     (
//         .CLK(clk),
//         .rst_n(rst_n),
//         .valid_in(valid_in),
//         .in_data(in_data),
//         .shift_val(shift_val),
//         .valid_out(valid_out3),
//         .out_data(out_data3)
//     );
//     // pipelinedCircularShifter #(
//     //     .MAXZ(MAXZ),
//     //     .ROTATES_PER_CYCLE(PIPE4_ROTATES_PER_CYCLE)
//     // ) dut4 
//     // (
//     //     .CLK(clk),
//     //     .rst_n(rst_n),
//     //     .valid_in(valid_in),
//     //     .in_data(in_data),
//     //     .shift_val(shift_val),
//     //     .valid_out(valid_out4),
//     //     .out_data(out_data4)
//     // );
//     // pipelinedCircularShifter #(
//     //     .MAXZ(MAXZ),
//     //     .ROTATES_PER_CYCLE(PIPE5_ROTATES_PER_CYCLE)
//     // ) dut5 
//     // (
//     //     .CLK(clk),
//     //     .rst_n(rst_n),
//     //     .valid_in(valid_in),
//     //     .in_data(in_data),
//     //     .shift_val(shift_val),
//     //     .valid_out(valid_out5),
//     //     .out_data(out_data5)
//     // );
//     // pipelinedCircularShifter #(
//     //     .MAXZ(MAXZ),
//     //     .ROTATES_PER_CYCLE(PIPE6_ROTATES_PER_CYCLE)
//     // ) dut6
//     // (
//     //     .CLK(clk),
//     //     .rst_n(rst_n),
//     //     .valid_in(valid_in),
//     //     .in_data(in_data),
//     //     .shift_val(shift_val),
//     //     .valid_out(valid_out6),
//     //     .out_data(out_data6)
//     // );

//     //Doesn't work for 7
//     // pipelinedCircularShifter #(
//     //     .MAXZ(MAXZ),
//     //     .ROTATES_PER_CYCLE(PIPE6_ROTATES_PER_CYCLE)
//     // ) dut7
//     // (
//     //     .CLK(clk),
//     //     .rst_n(rst_n),
//     //     .valid_in(valid_in),
//     //     .in_data(in_data),
//     //     .shift_val(shift_val),
//     //     .valid_out(valid_out7),
//     //     .out_data(out_data7)
//     // );


//     initial clk = 0;
//     always #1 clk = ~clk;
//     //Time waste task
//     task tick(int n = 1);
//         repeat(n) @(posedge clk);
//     endtask

//     // rotate-right reference function
//     function automatic logic [MAXZ-1:0] rot_right(input logic [MAXZ-1:0] data, input int s);
//         int ss;
//         begin
//             ss = s % MAXZ;
//             if (ss == 0) rot_right = data;
//             else rot_right = (data >> ss) | (data << (MAXZ - ss));
//         end
//     endfunction

//     int seed = 32'h12345678;
    
//     // ------------------------------------------------------------
//     // Testbench
//     // ------------------------------------------------------------
//     initial begin
//         int total_tests = 0;
//         int total_fail  = 0;
//         pipe1waiting = 0;
//         pipe2waiting = 0;
//         pipe3waiting = 0;
//         pipe4waiting = 0;
//         pipe5waiting = 0;
//         pipe6waiting = 0;
//         pipe7waiting = 0;

//         $urandom(seed);
//         //Reset
//         rst_n = 0;
//         valid_in = 0;
//         in_data = '0;
//         shift_val = '0;
//         tick(5);
//         rst_n = 1;

        

//         $display("STARTING pipelinedCircularShifter TEST (MAXZ=%0d)", MAXZ);

//         for (int test_idx = 0; test_idx < 501; test_idx++) begin
//             // Random input and shift
//             in_data = {$urandom, $urandom, $urandom}[MAXZ-1:0];
       
//             shift_val = $urandom_range(0, MAXZ-1)[$clog2(MAXZ)-1:0];
//             valid_in  = 1;

//             pipe1waiting = 0;
//             pipe2waiting = 0;
//             pipe3waiting = 0;
//             pipe4waiting = 0;
//             pipe5waiting = 0;
//             pipe6waiting = 0;
//             pipe7waiting = 0;


//             //Hold the valid for a cycle
//             tick(1);
//             valid_in = 0;

//             //Wait for Each DUT To Assert Valid_out
//             forever begin
//                 tick(1);

//                 if (valid_out1) begin
//                     logic [MAXZ-1:0] expected;
//                     pipe1waiting = 1'b1;
//                     expected = rot_right(in_data, int'(shift_val));

//                     total_tests++;
//                     if (out_data1 !== expected) begin
//                         $display("%0t ERROR: Rotates_Per_Cycle=%d in=%b shift=%0d out=%b expected=%b",
//                                  $time, 1, in_data, shift_val, out_data1, expected);
//                         total_fail++;
//                     end
//                 end

//                 if (valid_out2) begin
//                     logic [MAXZ-1:0] expected;
//                     pipe2waiting = 1'b1;
//                     expected = rot_right(in_data, int'(shift_val));

//                     total_tests++;
//                     if (out_data2 !== expected) begin
//                         $display("%0t ERROR: Rotates_Per_Cycle=%d in=%b shift=%0d out=%b expected=%b",
//                                  $time, 2, in_data, shift_val, out_data2, expected);
//                         total_fail++;
//                     end
//                 end

//                 if (valid_out3) begin
//                     logic [MAXZ-1:0] expected;
//                     pipe3waiting = 1'b1;
//                     expected = rot_right(in_data, int'(shift_val));

//                     total_tests++;
//                     if (out_data3 !== expected) begin
//                         $display("%0t ERROR: Rotates_Per_Cycle=%d in=%b shift=%0d out=%b expected=%b",
//                                  $time, 3, in_data, shift_val, out_data3, expected);
//                         total_fail++;
//                     end
//                 end

//                 // if (valid_out4) begin
//                 //     logic [MAXZ-1:0] expected;
//                 //     pipe4waiting = 1'b1;
//                 //     expected = rot_right(in_data, int'(shift_val));

//                 //     total_tests++;
//                 //     if (out_data4 !== expected) begin
//                 //         $display("%0t ERROR: Rotates_Per_Cycle=%d in=%b shift=%0d out=%b expected=%b",
//                 //                  $time, 4, in_data, shift_val, out_data4, expected);
//                 //         total_fail++;
//                 //     end
//                 // end

//                 // if (valid_out5) begin
//                 //     logic [MAXZ-1:0] expected;
//                 //     pipe5waiting = 1'b1;
//                 //     expected = rot_right(in_data, int'(shift_val));

//                 //     total_tests++;
//                 //     if (out_data5 !== expected) begin
//                 //         $display("%0t ERROR: Rotates_Per_Cycle=%d in=%b shift=%0d out=%b expected=%b",
//                 //                  $time, 5, in_data, shift_val, out_data5, expected);
//                 //         total_fail++;
//                 //     end
//                 // end

//                 // if (valid_out6) begin
//                 //     logic [MAXZ-1:0] expected;
//                 //     pipe6waiting = 1'b1;
//                 //     expected = rot_right(in_data, int'(shift_val));

//                 //     total_tests++;
//                 //     if (out_data6 !== expected) begin
//                 //         $display("%0t ERROR: Rotates_Per_Cycle=%d in=%b shift=%0d out=%b expected=%b",
//                 //                  $time, 6, in_data, shift_val, out_data6, expected);
//                 //         total_fail++;
//                 //     end
//                 // end

//                 // if (valid_out7) begin
//                 //     logic [MAXZ-1:0] expected;
//                 //     pipe7waiting = 1'b1;
//                 //     expected = rot_right(in_data, int'(shift_val));

//                 //     total_tests++;
//                 //     if (out_data7 !== expected) begin
//                 //         $display("%0t ERROR: Rotates_Per_Cycle=%d in=%b shift=%0d out=%b expected=%b",
//                 //                  $time, 7, in_data, shift_val, out_data7, expected);
//                 //         total_fail++;
//                 //     end
//                 // end

//                 //When all are done exit the loop 
//                 //if( pipe1waiting & pipe2waiting & pipe3waiting & pipe4waiting & pipe5waiting & pipe6waiting & pipe7waiting)
//                 if( pipe1waiting & pipe2waiting & pipe3waiting )

//                    disable fork; //exit forever loop and move on to next test 
//             end
//         end
//     end

//     // --- VCD dump ---
//     initial begin
//         $dumpfile("sim.vcd");   // name of the VCD file
//         $dumpvars(0, tb);       // dump all signals in tb hierarchy
//     end

// endmodule

`timescale 1ns/1ps

module tb_pipelinedCircularShifter;

    // ------------------------------------------------------------
    // Parameters
    // ------------------------------------------------------------
    parameter int MAXZ = 16;
    parameter int PIPE_STAGES_PER_CYCLE = 2;

    // ------------------------------------------------------------
    // DUT signals
    // ------------------------------------------------------------
    logic clk;
    logic rst_n;
    logic valid_in;
    logic [MAXZ-1:0] in_data;
    logic [$clog2(MAXZ)-1:0] shift_val;

    logic valid_out;
    logic [MAXZ-1:0] out_data;

    // ------------------------------------------------------------
    // DUT instantiation
    // ------------------------------------------------------------
    pipelinedCircularShifter #(
        .MAXZ(MAXZ),
        .PIPE_STAGES_PER_CYCLE(PIPE_STAGES_PER_CYCLE)
    ) dut (
        .CLK(clk),
        .rst_n(rst_n),
        .valid_in(valid_in),
        .in_data(in_data),
        .shift_val(shift_val),
        .valid_out(valid_out),
        .out_data(out_data)
    );

    // ------------------------------------------------------------
    // Clock
    // ------------------------------------------------------------
    initial clk = 0;
    always #1 clk = ~clk; // 500 MHz simulation

    // ------------------------------------------------------------
    // Tick helper
    // ------------------------------------------------------------
    task tick(int n = 1);
        repeat(n) @(posedge clk);
    endtask

    // ------------------------------------------------------------
    // Reference rotation function
    // ------------------------------------------------------------
    function automatic logic [MAXZ-1:0] rot_right(input logic [MAXZ-1:0] val, input int sh);
        rot_right = (val >> sh) | (val << (MAXZ - sh));
    endfunction

    // ------------------------------------------------------------
    // Testbench
    // ------------------------------------------------------------
    initial begin
        int total_tests = 0;
        int total_fail  = 0;

        // Reset
        rst_n     = 0;
        valid_in  = 0;
        in_data   = '0;
        shift_val = '0;
        tick(5);
        rst_n = 1;

        $display("STARTING pipelinedCircularShifter TEST (MAXZ=%0d)", MAXZ);

        // ------------------------------------------------------------
        // Run random coverage tests
        // ------------------------------------------------------------
        for (int test_idx = 0; test_idx < 100; test_idx++) begin
            // Random input and shift
            in_data   = $urandom_range(0, 2**MAXZ-1);
            shift_val = $urandom_range(0, MAXZ-1);
            valid_in  = 1;

            // Keep valid high for one cycle
            tick(1);
            valid_in = 0;

            // Wait for DUT to assert valid_out
            forever begin
                tick(1);
                if (valid_out) begin
                    logic [MAXZ-1:0] expected;
                    expected = rot_right(in_data, shift_val);

                    total_tests++;
                    if (out_data !== expected) begin
                        $display("%0t ERROR: in=%b shift=%0d out=%b expected=%b",
                                 $time, in_data, shift_val, out_data, expected);
                        total_fail++;
                    end
                    disable fork; // exit forever loop
                end
            end
        end

        // ------------------------------------------------------------
        // Test summary
        // ------------------------------------------------------------
        if (total_fail == 0)
            $display("ALL TESTS PASSED: %0d vectors", total_tests);
        else
            $display("TESTS FAILED: %0d failures out of %0d vectors", total_fail, total_tests);

        $finish;
    end

endmodule
