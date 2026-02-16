`timescale 1ns/1ps
module tb_pipelinedCircularShifter;

    // Test parameters
    localparam int MAXZ = 8;
    localparam int CLK_PERIOD = 10;
    localparam int PIPE1_STAGES_PER_CYCLE = 2;

    // DUT IO
    logic clk;
    logic rst_n;

    // shared inputs for both shifters
    logic [MAXZ-1:0] in_data;
    logic [$clog2(MAXZ)-1:0] shift_val;

    // outputs
    logic [MAXZ-1:0] out2; // pipelinedCircularShifter2
    logic [MAXZ-1:0] out1; // pipelinedCircularShifter1

    // test vectors and control declared at module scope (Verilator-friendly)
    logic [MAXZ-1:0] patterns [0:5];
    int latency;
    int total_tests;
    int total_fail;
    int p;
    int s;
    logic [MAXZ-1:0] expected;

    // Instantiate DUTs
    pipelinedCircularShifter2 #(.MAXZ(MAXZ)) dut2 (
        .CLK(clk),
        .rst_n(rst_n),
        .in_data(in_data),
        .shift_val(shift_val),
        .out_data(out2)
    );

    pipelinedCircularShifter1 #(
        .MAXZ(MAXZ),
        .PIPE_STAGES_PER_CYCLE(PIPE1_STAGES_PER_CYCLE)
    ) dut1 (
        .CLK(clk),
        .rst_n(rst_n),
        .in_data(in_data),
        .shift_val(shift_val),
        .out_data(out1)
    );

    // clock
    initial clk = 0;
    always #(CLK_PERIOD/2) clk = ~clk;

    // rotate-right reference function
    function automatic logic [MAXZ-1:0] rot_right(input logic [MAXZ-1:0] data, input int s);
        int ss;
        begin
            ss = s % MAXZ;
            if (ss == 0) rot_right = data;
            else rot_right = (data >> ss) | (data << (MAXZ - ss));
        end
    endfunction

    // helper: tick n clock cycles
    task automatic tick(input int cycles);
        int i;
        for (i = 0; i < cycles; i++) @(posedge clk);
    endtask



    initial begin
        // populate patterns (module-scope vars)
        patterns[0] = 8'b10110101;
        patterns[1] = 8'b00001111;
        patterns[2] = 8'b11110000;
        patterns[3] = 8'b01010101;
        patterns[4] = 8'b00110011;
        patterns[5] = 8'hA5;

        // reset
        rst_n = 0;
        in_data = '0;
        shift_val = '0;
        tick(2);
        rst_n = 1;
        tick(1);

        $display("STARTING pipelinedCircularShifter TEST (MAXZ=%0d)", MAXZ);

        // set latency and counters
        latency = 16;
        total_tests = 0;
        total_fail = 0;

        // run tests
        for (p = 0; p <= 5; p = p + 1) begin
            in_data = patterns[p];
            for (s = 0; s < MAXZ; s = s + 1) begin
                shift_val = s[$clog2(MAXZ)-1:0];
                // wait enough cycles for pipeline to produce valid output
                tick(latency);

                
                expected = rot_right(in_data, s);

                total_tests = total_tests + 1;

                if (out2 !== expected) begin
                    $display("%0t ERROR dut2: in=%b shift=%0d out=%b expected=%b", $time, in_data, s, out2, expected);
                    total_fail = total_fail + 1;
                end

                if (out1 !== expected) begin
                    $display("%0t ERROR dut1: in=%b shift=%0d out=%b expected=%b", $time, in_data, s, out1, expected);
                    total_fail = total_fail + 1;
                end
            end
        end

        if (total_fail == 0)
            $display("ALL TESTS PASSED: %0d vectors", total_tests);
        else
            $display("TESTS FAILED: %0d failures out of %0d vectors", total_fail, total_tests);

        $finish;
    end

endmodule