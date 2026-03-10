`timescale 1ns/1ps
// =============================================================================
// Author: Ryan Bride
// File:   qcldpc_tb_top.sv
// Desc:   Top-level testbench for QCLDPCEncoderController
//         Instantiates DUT, driver, monitor, scoreboard, and coverage
//         Runs directed, random, and corner case tests
//         Self-checking — exits 0 on pass, 1 on fail
//
// Usage (Verilator):
//     See Makefile — run 'make sim' from tb/ directory
// =============================================================================
module qcldpc_tb_top;

    import qcldpcPkg::*;
    import qcldpc_tb_pkg::*;

    localparam int MAXZ      = TB_MAXZ;       // 81
    localparam int NUM_PBLKS = TB_NUM_PBLKS;  // 4
    localparam int IBLKS_NUM = TB_IBLKS_NUM;  // 20
    localparam int NUM_SUP_Z = TB_NUM_SUP_Z;  // 3

    // Clock — 900MHz
    localparam real CLK_PERIOD = 1.111;  // ns
    logic CLK = 0;
    always #(CLK_PERIOD / 2.0) CLK = ~CLK;

    // Reset
    logic rst_n = 0;
    initial begin
        rst_n = 1'b0;
        repeat(10) @(posedge CLK);
        @(negedge CLK);
        rst_n = 1'b1;
    end

    // -------------------------------------------------------------------------
    // DUT interfaces and instantiation
    // -------------------------------------------------------------------------
    logic in_valid; logic in_last; logic in_ready;                z_req_t req_z;
    logic [MAXZ-1:0] i_data;   logic [MAXZ*(NUM_PBLKS+IBLKS_NUM)-1:0]p_data_out;

    QCLDPCEncoderController #(
        .NUM_SUP_Z(3),  .MAXZ(81),  .IBLKS_NUM(20),  .NUM_PBLKS(4),
        .ROM_TYPE(1),   .Z_VALUE_ARRAY('{27, 54, 81}),
        .ROTATES_PER_CYCLE(1), .NUM_ACCUM_PIPE_SPLITS  (2)
    ) dut (
        .CLK(CLK), .rst_n(rst_n), .in_valid(in_valid), .in_last(in_last),
        .in_ready(in_ready), .req_z(req_z), .i_data(i_data), .p_data_out(p_data_out)
    );
    // -------------------------------------------------------------------------
    // TB components
    // -------------------------------------------------------------------------
    qcldpc_driver driver_i (
        .CLK(CLK), .rst_n(rst_n), .in_ready(in_ready), .in_valid(in_valid),
        .in_last(in_last), .req_z(req_z), .i_data(i_data)
    );

    qcldpc_monitor monitor_i (
        .CLK(CLK), .rst_n(rst_n), .in_valid(in_valid), .in_ready(in_ready),
        .in_last(in_last), .req_z(req_z), .p_data_out (p_data_out)
    );

    qcldpc_scoreboard scoreboard_i (
        .CLK(CLK),  .rst_n(rst_n)
    );

    qcldpc_coverage coverage_i (
        .CLK(CLK), .rst_n(rst_n), .req_z(req_z),
        .in_valid(in_valid), .in_ready(in_ready), .in_last(in_last)
    );

    // Waveform dump
    initial begin
        $dumpfile("waves.vcd");
        $dumpvars(0, qcldpc_tb_top);
    end
    // -------------------------------------------------------------------------
    // Timeout watchdog — catches infinite loops and hangs
    // 1ms at 900MHz = 900,000 cycles — more than enough for any test
    // -------------------------------------------------------------------------
    initial begin
        #1_000_000;
        $fatal(1, "[TIMEOUT] Simulation exceeded maximum time — possible hang");
    end
    // -------------------------------------------------------------------------
    // Main test execution
    // -------------------------------------------------------------------------
    initial begin
        $display("==============================================");
        $display("  QC-LDPC Encoder Testbench");
        $display("  Configuration: Z={27,54,81}, Rate=5/6");
        $display("  Target: 802.11n Annex R compliance");
        $display("==============================================\n");

        // Wait for reset to deassert
        @(posedge rst_n);
        repeat(5) @(posedge CLK);

        // Test suite
        run_directed_tests();
        run_random_tests(500);
        run_corner_cases();

        // Wait for all results to flush through pipeline
        repeat(50) @(posedge CLK);

        // Reports
        scoreboard_i.report();
        coverage_i.report();

        // Final pass/fail
        if(scoreboard_i.stats.tests_failed == 0) begin
            $display("╔══════════════════════════════════════╗");
            $display("║      ALL TESTS PASSED  %-5d/%-5d   ║",
                     scoreboard_i.stats.tests_passed,
                     scoreboard_i.stats.tests_run);
            $display("╚══════════════════════════════════════╝\n");
            $finish(0);
        end else begin
            $display("╔══════════════════════════════════════╗");
            $display("║      TESTS FAILED  %0d / %0d           ║",
                     scoreboard_i.stats.tests_failed,
                     scoreboard_i.stats.tests_run);
            $display("╚══════════════════════════════════════╝\n");
            $finish(1);
        end
    end
    // =========================================================================
    // Test tasks
    // =========================================================================
    // run_directed_tests
    // Known inputs with known expected outputs
    // Tests specific corner values — all zeros, all ones, walking ones
    // A walking-ones test catches individual ROM entry errors
    // -------------------------------------------------------------------------
    task automatic run_directed_tests();
        automatic test_vector_t tv;
        automatic int           test_id = 0;
        automatic z_req_t       z_vals [3] = '{Z_27, Z_54, Z_81};

        $display("[TEST] Starting directed tests...");

        // All-zeros info — parity should be all zeros for systematic code
        foreach(z_vals[zi]) begin
            tv.info_bits       = '0;
            tv.z_sel           = z_vals[zi];
            tv.test_id         = test_id;
            tv.parity_expected = compute_reference(tv.info_bits, tv.z_sel);

            driver_i.drive_codeword(tv);
            scoreboard_i.ref_mailbox.put(tv);
            monitor_i.capture_result(test_id);
            test_id++;
        end

        // All-ones info
        foreach(z_vals[zi]) begin
            tv.info_bits       = '1;
            tv.z_sel           = z_vals[zi];
            tv.test_id         = test_id;
            tv.parity_expected = compute_reference(tv.info_bits, tv.z_sel);

            driver_i.drive_codeword(tv);
            scoreboard_i.ref_mailbox.put(tv);
            monitor_i.capture_result(test_id);
            test_id++;
        end

        // Walking ones — one bit set at each position in the info field
        // Tests every proto matrix entry individually
        // Only do this for Z=81 — would be 81*20=1620 tests per Z otherwise
        for(int bit = 0; bit < MAXZ * IBLKS_NUM; bit++) begin
            tv.info_bits       = '0;
            tv.info_bits[bit]  = 1'b1;
            tv.z_sel           = Z_81;
            tv.test_id         = test_id;
            tv.parity_expected = compute_reference(tv.info_bits, tv.z_sel);

            driver_i.drive_codeword(tv);
            scoreboard_i.ref_mailbox.put(tv);
            monitor_i.capture_result(test_id);
            test_id++;
        end

        $display("[TEST] Directed tests complete — %0d tests queued", test_id);
    endtask

    // -------------------------------------------------------------------------
    // run_random_tests
    // Bulk test — the main correctness regression
    // -------------------------------------------------------------------------
    task automatic run_random_tests(input int count);
        automatic test_vector_t tv;
        automatic int base_id = 10000;
        automatic z_req_t z_vals [3] = '{Z_27, Z_54, Z_81};

        $display("[TEST] Starting %0d random tests...", count);

        for(int i = 0; i < count; i++) begin
            // Random info bits — fill word by word
            for(int w = 0; w < MAXZ * IBLKS_NUM / 32; w++)
                tv.info_bits[w*32 +: 32] = $urandom();

            // Random Z
            tv.z_sel           = z_vals[$urandom_range(0, 2)];
            tv.test_id         = base_id + i;
            tv.parity_expected = compute_reference(tv.info_bits, tv.z_sel);

            // 30% chance of gap injection — tests non-continuous input
            if($urandom_range(0, 99) < 30)
                driver_i.drive_codeword_with_gaps(tv, 25);
            else
                driver_i.drive_codeword(tv);

            scoreboard_i.ref_mailbox.put(tv);
            monitor_i.capture_result(tv.test_id);
        end

        $display("[TEST] Random tests complete");
    endtask

    // -------------------------------------------------------------------------
    // run_corner_cases
    // Specific scenarios that stress the control logic
    // -------------------------------------------------------------------------
    task automatic run_corner_cases();
        automatic test_vector_t tv;
        automatic int base_id = 30000;

        $display("[TEST] Starting corner case tests...");

        // Corner 1 — reset mid-codeword, then clean codeword
        // Verifies accumulator resets properly after mid-codeword reset
        begin
            automatic logic rst_n_local;

            req_z    = Z_81;
            in_valid = 1'b1;
            i_data   = $urandom();
            repeat(10) @(posedge CLK);

            // Assert reset
            rst_n = 1'b0;
            in_valid = 1'b0;
            repeat(5) @(posedge CLK);
            rst_n = 1'b1;
            repeat(5) @(posedge CLK);

            // Clean codeword after recovery
            tv.info_bits       = $urandom();
            tv.z_sel           = Z_81;
            tv.test_id         = base_id;
            tv.parity_expected = compute_reference(tv.info_bits, tv.z_sel);

            driver_i.drive_codeword(tv);
            scoreboard_i.ref_mailbox.put(tv);
            monitor_i.capture_result(tv.test_id);
        end

        // Corner 2 — back-to-back codewords, zero gap between them
        // Verifies accumulator resets between consecutive codewords
        for(int i = 0; i < 5; i++) begin
            tv.info_bits       = $urandom();
            tv.z_sel           = Z_81;
            tv.test_id         = base_id + 1 + i;
            tv.parity_expected = compute_reference(tv.info_bits, tv.z_sel);

            driver_i.drive_codeword(tv);   // no inter-codeword gap
            scoreboard_i.ref_mailbox.put(tv);
            monitor_i.capture_result(tv.test_id);
        end

        // Corner 3 — Z transitions between every consecutive pair
        // Tests that switching Z does not corrupt state
        begin
            z_req_t z_sequence [9] = '{
                Z_27, Z_54, Z_81,   // ascending
                Z_81, Z_54, Z_27,   // descending
                Z_54, Z_54, Z_81    // same-Z repeat then switch
            };

            foreach(z_sequence[i]) begin
                tv.info_bits       = $urandom();
                tv.z_sel           = z_sequence[i];
                tv.test_id         = base_id + 10 + i;
                tv.parity_expected = compute_reference(tv.info_bits, tv.z_sel);

                driver_i.drive_codeword(tv);
                scoreboard_i.ref_mailbox.put(tv);
                monitor_i.capture_result(tv.test_id);
            end
        end

        // Corner 4 — maximum gap between blocks (stress back-pressure)
        begin
            tv.info_bits       = $urandom();
            tv.z_sel           = Z_81;
            tv.test_id         = base_id + 30;
            tv.parity_expected = compute_reference(tv.info_bits, tv.z_sel);

            driver_i.drive_codeword_with_gaps(tv, 80);  // 80% chance of gap
            scoreboard_i.ref_mailbox.put(tv);
            monitor_i.capture_result(tv.test_id);
        end

        $display("[TEST] Corner case tests complete");
    endtask

endmodule
