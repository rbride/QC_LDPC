`timescale 1ns/1ps
// =============================================================================
// Author: Ryan Bride
// File:   qcldpc_monitor.sv
// Desc:   Testbench monitor — observes DUT outputs passively
//         Captures parity output when valid, timestamps with cycle count
//         Posts results to scoreboard via mailbox
//         Also monitors input side to track codeword start for latency measurement
// =============================================================================
module qcldpc_monitor (
    input logic    CLK,
    input logic    rst_n,
    input logic    in_valid,
    input logic    in_ready,
    input logic    in_last,
    input z_req_t  req_z,
    input logic [qcldpc_tb_pkg::TB_MAXZ*(qcldpc_tb_pkg::TB_NUM_PBLKS
                 +qcldpc_tb_pkg::TB_IBLKS_NUM)-1:0] p_data_out
);
    import qcldpcPkg::*;
    import qcldpc_tb_pkg::*;

    // -------------------------------------------------------------------------
    // Mailbox — posts captured results to scoreboard
    // Scoreboard creates this and shares the handle
    // -------------------------------------------------------------------------
    mailbox #(dut_result_t) result_mailbox;

    // -------------------------------------------------------------------------
    // Internal tracking
    // -------------------------------------------------------------------------
    int  codeword_start_cycle;
    int  current_cycle;
    int  captured_test_id;
    bool first_block_seen;

    z_req_t captured_z;

    initial begin
        result_mailbox    = new();
        current_cycle     = 0;
        first_block_seen  = 0;
        captured_z        = Z_81;
        captured_test_id  = 0;
    end

    // Cycle counter
    always_ff @(posedge CLK) begin
        if(!rst_n) current_cycle <= 0;
        else       current_cycle <= current_cycle + 1;
    end

    // -------------------------------------------------------------------------
    // Input monitor — track codeword start for latency measurement
    // -------------------------------------------------------------------------
    always_ff @(posedge CLK) begin
        if(!rst_n) begin
            first_block_seen     <= 0;
            codeword_start_cycle <= 0;
            captured_z           <= Z_81;
        end else begin
            if(in_valid && in_ready && !first_block_seen) begin
                codeword_start_cycle <= current_cycle;
                captured_z           <= req_z;
                first_block_seen     <= 1;
            end
            // Reset after last block seen
            if(in_valid && in_ready && in_last)
                first_block_seen <= 0;
        end
    end

    // -------------------------------------------------------------------------
    // Output monitor — capture parity when output valid
    // p_data_out MSBs carry parity — lower bits carry info (systematic code)
    // Parity is in the upper NUM_PBLKS*MAXZ bits of p_data_out
    // -------------------------------------------------------------------------
    always_ff @(posedge CLK) begin
        if(rst_n) begin
            // TODO: add valid signal from DUT output when accumulator
            //       exposes a parity_valid signal
            //       For now poll p_data_out change as proxy
            //       Replace this with proper handshake when available
        end
    end

    // -------------------------------------------------------------------------
    // capture_result
    // Called by top-level test after each codeword to capture result
    // Waits for parity_valid from DUT then posts to mailbox
    // -------------------------------------------------------------------------
    task automatic capture_result(input int test_id);
        automatic dut_result_t result;

        // Wait for parity_valid — DUT signals completion
        // TODO: connect to actual parity_valid output when added to DUT port list
        // For now use a fixed delay based on pipeline depth
        // Pipeline = 1 (preprocess) + 7 (shifter Z=81) + 1 (accum) = 9 cycles
        // Plus IBLKS_NUM cycles to feed all blocks = 20 + 9 = 29 cycles min
        repeat(TB_IBLKS_NUM + 12) @(posedge CLK);

        result.parity_actual = p_data_out[TB_MAXZ*(TB_NUM_PBLKS+TB_IBLKS_NUM)-1
                                          -: TB_MAXZ*TB_NUM_PBLKS];
        result.z_sel         = captured_z;
        result.test_id       = test_id;
        result.cycle_count   = current_cycle - codeword_start_cycle;

        result_mailbox.put(result);
    endtask

endmodule
