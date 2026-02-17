`timescale 1ns/1ps
module tb_pipelinedCircularShifter;

    // Test parameters
    localparam int MAXZ = 81;
    localparam int CLK_PERIOD = 10;
    localparam int PIPE1_ROTATES_PER_CYCLE = 1;

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
    pipelinedCircularShifterFMAX #(.MAXZ(MAXZ)) dut2 (
        .CLK(clk),
        .rst_n(rst_n),
        .in_data(in_data),
        .shift_val(shift_val),
        .out_data(out2)
    );

    pipelinedCircularShifter #(
        .MAXZ(MAXZ),
        .ROTATES_PER_CYCLE(PIPE1_ROTATES_PER_CYCLE)
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
        // patterns[0] = 16'b10110101_10110101;
        // patterns[1] = 16'b00001111_00001111;
        // patterns[2] = 16'b11110000_11110000;
        // patterns[3] = 16'b01010101_01010101;
        // patterns[4] = 16'b00110011_00110011;
        // patterns[5] = 16'hA5_A5;
        patterns[0] = 81'b001101111100100000001101101011101110101101100100010001000111110101001101000111110;
        patterns[1] = 81'b101111100100101000110000101111011101101111010010001101011010101010010110011101110;
        patterns[2] = 81'b001010011100100001001001011111010101000011000011100010110101001110100011010011001;
        patterns[3] = 81'b111010001011111001001100010011100100001000111111000100000010010011011001110010011;
        patterns[4] = 81'b101001110001101001111010010000110111101001011101100101001000011001110010101000111;
        patterns[5] = 81'b010010011010110000001111010100110101100011011001111100001100001110101111000100101;
        
        // reset
        rst_n = 0;
        in_data = '0;
        shift_val = '0;
        tick(5);
        rst_n = 1;
        tick(1);

        $display("STARTING pipelinedCircularShifter TEST (MAXZ=%0d)", MAXZ);

        // set latency and counters
        latency = 10;
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

    // --- VCD dump ---
    initial begin
        $dumpfile("sim.vcd");   // name of the VCD file
        $dumpvars(0, tb);       // dump all signals in tb hierarchy
    end

endmodule
