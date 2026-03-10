`timescale 1ns/1ps
// =============================================================================
// Author: Ryan Bride
// File:   qcldpc_scoreboard.sv
// Desc:   Testbench scoreboard — compares DUT output against reference model
//         Self-checking — no human inspection required
//         Tracks pass/fail counts, latency statistics
//         On failure prints detailed diff showing which parity bits are wrong
// =============================================================================
module qcldpc_scoreboard (
    input logic CLK,
    input logic rst_n
);
    import qcldpcPkg::*;
    import qcldpc_tb_pkg::*;

    mailbox #(test_vector_t) ref_mailbox;   // expected values from test
    mailbox #(dut_result_t)  dut_mailbox;   // actual values from monitor

    test_stats_t stats;

    initial begin
        ref_mailbox = new();
        dut_mailbox = new();
        stats       = '{0, 0, 0, 32'hFFFF_FFFF, 0, 0.0};
    end

    // -------------------------------------------------------------------------
    // Checker — runs once per completed codeword
    // -------------------------------------------------------------------------
    task automatic check_next();
        automatic test_vector_t expected;
        automatic dut_result_t  actual;

        ref_mailbox.get(expected);
        dut_mailbox.get(actual);

        stats.tests_run++;

        // Ordering sanity — test IDs must match
        if(expected.test_id !== actual.test_id) begin
            $fatal(1, "[SCOREBOARD] Test ID ordering mismatch — expected %0d got %0d\n"
                    , expected.test_id, actual.test_id);
        end

        // Z must match
        if(expected.z_sel !== actual.z_sel) begin
            $fatal(1, "[SCOREBOARD] Z mismatch on test %0d", expected.test_id);
        end

        // Parity correctness — main check
        if(expected.parity_expected === actual.parity_actual) begin
            stats.tests_passed++;

            if(actual.cycle_count < stats.latency_min)
                stats.latency_min = actual.cycle_count;
            if(actual.cycle_count > stats.latency_max)
                stats.latency_max = actual.cycle_count;
            stats.latency_avg = stats.latency_avg +
                                 real'(actual.cycle_count - stats.latency_avg) /
                                 real'(stats.tests_passed);

        end else begin
            stats.tests_failed++;
            report_failure(expected, actual);
        end
    endtask

    task automatic report_failure(
        input test_vector_t expected,
        input dut_result_t  actual
    );
        automatic logic [TB_MAXZ*TB_NUM_PBLKS-1:0] diff;
        automatic int first_bad_bit;

        diff         = expected.parity_expected ^ actual.parity_actual;
        first_bad_bit = -1;

        for(int i = 0; i < TB_MAXZ*TB_NUM_PBLKS; i++) begin
            if(diff[i]) begin
                first_bad_bit = i;
                break;
            end
        end

        $display("\n[FAIL] ============================================");
        $display("  Test ID:          %0d",   expected.test_id);
        $display("  Z selection:      %s",    expected.z_sel.name());
        $display("  Expected parity:  %h",    expected.parity_expected);
        $display("  Actual   parity:  %h",    actual.parity_actual);
        $display("  XOR diff:         %h",    diff);
        $display("  First bad bit:    %0d",   first_bad_bit);
        $display("  Parity lane:      %0d",   first_bad_bit / TB_MAXZ);
        $display("  Bit within lane:  %0d",   first_bad_bit % TB_MAXZ);
        $display("=====================================================\n");
    endtask

    task automatic report();
        $display("\n========== SCOREBOARD REPORT ==========");
        $display("  Tests run:    %0d", stats.tests_run);
        $display("  Tests passed: %0d", stats.tests_passed);
        $display("  Tests failed: %0d", stats.tests_failed);

        if(stats.tests_run > 0) begin
            $display("  Pass rate:    %.1f%%",
                     100.0 * real'(stats.tests_passed) / real'(stats.tests_run));
            $display("  Latency min:  %0d cycles", stats.latency_min);
            $display("  Latency max:  %0d cycles", stats.latency_max);
            $display("  Latency avg:  %.1f cycles", stats.latency_avg);
        end

        $display("========================================\n");
    endtask

endmodule
