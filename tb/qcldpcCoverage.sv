`timescale 1ns/1ps
// =============================================================================
// Author: Ryan Bride
// File:   qcldpc_coverage.sv
// Desc:   Functional coverage model
//         Tracks which Z values, handshake conditions, and Z transitions
//         have been exercised. Coverage closure confirms the test suite
//         has adequately stimulated the DUT.
//
//         Target: 100% functional coverage before sign-off
// =============================================================================
module qcldpc_coverage (
    input logic    CLK,
    input logic    rst_n,
    input z_req_t  req_z,
    input logic    in_valid,
    input logic    in_ready,
    input logic    in_last
);
    import qcldpcPkg::*;
    import qcldpc_tb_pkg::*;

    // -------------------------------------------------------------------------
    // Z selection coverage
    // Every supported Z value must be exercised
    // -------------------------------------------------------------------------
    covergroup cg_z_selection @(posedge CLK iff rst_n);
        cp_z: coverpoint req_z {
            bins z27 = {Z_27};
            bins z54 = {Z_54};
            bins z81 = {Z_81};
        }
    endgroup

    // -------------------------------------------------------------------------
    // Handshake coverage
    // All valid/ready combinations must occur
    // Back-pressure (valid=1, ready=0) is the key one to hit
    // -------------------------------------------------------------------------
    covergroup cg_handshake @(posedge CLK iff rst_n);
        cp_valid: coverpoint in_valid {
            bins low  = {0};
            bins high = {1};
        }
        cp_ready: coverpoint in_ready {
            bins low  = {0};
            bins high = {1};
        }
        cp_last: coverpoint in_last {
            bins low  = {0};
            bins high = {1};
        }

        // Back-pressure: valid asserted but DUT not ready
        cp_backpressure: coverpoint (in_valid & ~in_ready) {
            bins active = {1};
            bins idle   = {0};
        }

        // Successful transfer: both valid and ready
        cp_transfer: coverpoint (in_valid & in_ready) {
            bins active = {1};
            bins idle   = {0};
        }

        // Back-pressure must occur for each Z value
        cx_z_backpressure: cross cp_z, cp_backpressure;

        // Last block transfer for each Z
        cx_z_last: cross cp_z, cp_last;
    endgroup

    // -------------------------------------------------------------------------
    // Z transition coverage
    // Design must handle switching Z between consecutive codewords
    // All 9 transition pairs (including same-Z) must be exercised
    // -------------------------------------------------------------------------
    z_req_t prev_z;

    always_ff @(posedge CLK) begin
        if(!rst_n) prev_z <= Z_81;
        else if(in_valid && in_ready && in_last)
            prev_z <= req_z;
    end

    covergroup cg_z_transitions @(posedge CLK iff (rst_n && in_valid && in_ready && in_last));
        cp_from_z: coverpoint prev_z {
            bins z27 = {Z_27};
            bins z54 = {Z_54};
            bins z81 = {Z_81};
        }
        cp_to_z: coverpoint req_z {
            bins z27 = {Z_27};
            bins z54 = {Z_54};
            bins z81 = {Z_81};
        }
        // All 9 combinations: 27→27, 27→54, 27→81,
        //                     54→27, 54→54, 54→81,
        //                     81→27, 81→54, 81→81
        cx_transition: cross cp_from_z, cp_to_z;
    endgroup

    // -------------------------------------------------------------------------
    // Reset coverage
    // Reset must be seen at least once during active operation
    // -------------------------------------------------------------------------
    covergroup cg_reset @(posedge CLK);
        cp_rst: coverpoint rst_n {
            bins deasserted = {0};
            bins asserted   = {1};
        }
        // Reset while a transfer is in progress
        cp_reset_during_transfer: coverpoint (~rst_n & in_valid) {
            bins active = {1};
        }
    endgroup

    // -------------------------------------------------------------------------
    // Instantiate coverage groups
    // -------------------------------------------------------------------------
    cg_z_selection   cg_z_sel_i   = new();
    cg_handshake     cg_hs_i      = new();
    cg_z_transitions cg_trans_i   = new();
    cg_reset         cg_rst_i     = new();

    // -------------------------------------------------------------------------
    // report — print coverage percentages at end of sim
    // -------------------------------------------------------------------------
    task automatic report();
        $display("\n========== COVERAGE REPORT ==========");
        $display("  Z selection:          %.1f%%", cg_z_sel_i.get_coverage());
        $display("  Handshake:            %.1f%%", cg_hs_i.get_coverage());
        $display("  Z transitions:        %.1f%%", cg_trans_i.get_coverage());
        $display("  Reset conditions:     %.1f%%", cg_rst_i.get_coverage());
        $display("  Overall functional:   %.1f%%", $get_coverage());
        $display("======================================\n");
    endtask

endmodule
