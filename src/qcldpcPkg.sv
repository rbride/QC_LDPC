package qcldpcPkg;

    parameter int MAXZ       = 81;

    typedef struct packed {
        logic               valid;
        logic               last;
        logic [MAXZ-1:0]    data;
    } pipeline_pkt_t;


    function automatic logic [MAXZ-1:0] get_tiled_input(
        input logic [MAXZ-1:0]  raw_data,
        input int unsigned      z_val,
        input int unsigned      maxz
    );
    automatic logic [MAXZ-1:0] result = '0;
    if (maxz % z_val == 0) begin
        // Factor — tile
        for (int t = 0; t < maxz / z_val; t++)
            result[t*z_val +: z_val] = raw_data[z_val-1:0];
    end else begin
        // Non-factor — zero pad
        result[z_val-1:0] = raw_data[z_val-1:0];
    end
    return result;
endfunction



endpackage


// One processed signal per Z — generated statically
logic [MAXZ-1:0] i_data_tiled [0:NUM_SUPPORTED_Z-1];

// This generate unrolls at elaboration into NUM_SUPPORTED_Z
// independent constant assignments — zero runtime logic
genvar zi;
generate
    for (zi = 0; zi < NUM_SUPPORTED_Z; zi++) begin : TILE_GEN

        // Each iteration is a constant expression at elaboration
        // tools see this as hardwired bit connections, not logic
        // equivalent to writing each case manually
        always_comb begin
            i_data_tiled[zi] = get_tiled_input(i_data, Z_VALUE_ARRAY[zi], MAXZ);
        end

    end
endgenerate

// Final mux — one register, select driven by req_z one-hot
// synthesizes to exactly the same mux you have now
// but the inputs are pre-computed wiring not runtime logic
always_ff @(posedge CLK) begin
    if (!rst_n) begin
        i_data_processed <= '0;
    end else begin
        i_data_processed <= '0;
        for (int i = 0; i < NUM_SUPPORTED_Z; i++) begin
            if (req_z[i])
                i_data_processed <= i_data_tiled[i];
        end
    end
end
```

The synthesized result for your 27/54/81 config:
```
TILE_GEN[0]:  i_data_tiled[0] = {i_data[26:0], i_data[26:0], i_data[26:0]}  — pure wiring
TILE_GEN[1]:  i_data_tiled[1] = {27'b0, i_data[53:0]}                        — pure wiring
TILE_GEN[2]:  i_data_tiled[2] = i_data[80:0]                                 — pure wiring

Final mux:    req_z[0] ? i_data_tiled[0] :
              req_z[1] ? i_data_tiled[1] :
              req_z[2] ? i_data_tiled[2] :
              '0



 // -------------------------------------------------------------------------
    // Returns the number of Z values that are NOT evenly divisible into maxz
    // -------------------------------------------------------------------------
    function automatic int unsigned count_nonfactor_z(
        input int unsigned maxz,
        input int unsigned z_values [],   // unpacked array — variable length
        input int unsigned num_z
    );
        automatic int unsigned count = 0;
        for (int i = 0; i < num_z; i++) begin
            if (maxz % z_values[i] != 0)
                count++;
        end
        return count;
    endfunction

    // -------------------------------------------------------------------------
    // Returns 1 if ALL z values divide evenly into maxz, 0 if any do not
    // -------------------------------------------------------------------------
    function automatic logic all_z_factor(
        input int unsigned maxz,
        input int unsigned z_values [],
        input int unsigned num_z
    );
        for (int i = 0; i < num_z; i++) begin
            if (maxz % z_values[i] != 0)
                return 1'b0;
        end
        return 1'b1;
    endfunction

    // -------------------------------------------------------------------------
    // Returns a bitmask indicating WHICH z values are non-factors
    // bit i is set if z_values[i] does not divide evenly into maxz
    // allows caller to identify exactly which ones are problematic
    // -------------------------------------------------------------------------
    function automatic int unsigned nonfactor_z_mask(
        input int unsigned maxz,
        input int unsigned z_values [],
        input int unsigned num_z
    );
        automatic int unsigned mask = 0;
        for (int i = 0; i < num_z; i++) begin
            if (maxz % z_values[i] != 0)
                mask |= (1 << i);
        end
        return mask;
    endfunction

endpackage

module QCLDPCEncoderController #(
    parameter int MAXZ              = `MAXZ,
    parameter int NUM_SUPPORTED_Z   = `NUM_SUPPORTED_Z,
    parameter int Z_VALUE_ARRAY [0:2] = '{27, 54, 81}
)(
    ...
);
    // Call functions with module parameters to get derived info
    localparam int NUM_NONFACTOR    = count_nonfactor_z(MAXZ, Z_VALUE_ARRAY, NUM_SUPPORTED_Z);
    localparam int NONFACTOR_MASK   = nonfactor_z_mask(MAXZ, Z_VALUE_ARRAY, NUM_SUPPORTED_Z);
    localparam logic ALL_FACTOR     = all_z_factor(MAXZ, Z_VALUE_ARRAY, NUM_SUPPORTED_Z);

    // Elaboration time reporting — visible in synthesis and sim logs
    initial begin
        $display("MAXZ = %0d", MAXZ);
        $display("NUM_NONFACTOR = %0d", NUM_NONFACTOR);
        $display("NONFACTOR_MASK = %0b", NONFACTOR_MASK);

        // Per-Z breakdown
        for (int i = 0; i < NUM_SUPPORTED_Z; i++) begin
            if (NONFACTOR_MASK & (1 << i))
                $display("  Z[%0d] = %0d is NON-FACTOR of MAXZ=%0d — requires dedicated shifter",
                         i, Z_VALUE_ARRAY[i], MAXZ);
            else
                $display("  Z[%0d] = %0d divides evenly into MAXZ=%0d — tiling valid",
                         i, Z_VALUE_ARRAY[i], MAXZ);
        end

        // Fatal if config is unsupported
        if (NUM_NONFACTOR > 1)
            $fatal(1, "CONFIG ERROR: %0d non-factor Z values detected. \
                       Maximum supported is 1 (Z=54). \
                       Adjust Z_VALUE_ARRAY or MAXZ.", NUM_NONFACTOR);
    end

endmodule


  // -------------------------------------------------------------------------
    // Functions that compute derived values from architectural parameters
    // All take explicit inputs — no dependency on .svh or global constants
    // -------------------------------------------------------------------------

    function automatic int unsigned shifter_stages(
        input int unsigned maxz,
        input int unsigned rotates_per_cycle
    );
        automatic int unsigned mux_levels = $clog2(maxz);
        return (mux_levels % rotates_per_cycle != 0) ?
               (mux_levels / rotates_per_cycle) + 1 :
               (mux_levels / rotates_per_cycle);
    endfunction

    function automatic int unsigned rom_depth(
        input int unsigned num_info_blks,
        input int unsigned num_parity_blks,
        input int unsigned num_supported_z
    );
        return (num_info_blks + num_parity_blks) 
               * num_parity_blks 
               * num_supported_z;
    endfunction

    function automatic int unsigned rom_addr_width(
        input int unsigned num_info_blks,
        input int unsigned num_parity_blks,
        input int unsigned num_supported_z
    );
        return $clog2(rom_depth(num_info_blks, num_parity_blks, num_supported_z));
    endfunction

    function automatic int unsigned shift_val_width(
        input int unsigned maxz
    );
        return $clog2(maxz);
    endfunction

    function automatic int signed throughput_headroom(
        input int unsigned num_info_blks,
        input int unsigned maxz,
        input int unsigned rotates_per_cycle,
        input int unsigned parallelization_lvl
    );
        return int'(num_info_blks / parallelization_lvl) 
               - int'(shifter_stages(maxz, rotates_per_cycle));
    endfunction

