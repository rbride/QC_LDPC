// -----------------------------
// Column pointer for streaming
// -----------------------------
logic [$clog2(NUM_COLS)-1:0] col_idx;
always_ff @(posedge clk) begin
    if (rst)
        col_idx <= 0;
    else if (valid_in)
        col_idx <= (col_idx == NUM_COLS-1) ? 0 : col_idx + 1;
end

// -----------------------------
// Row-parallel streaming pipeline
// -----------------------------
genvar r;
generate
    for (r = 0; r < NUM_ROW_GROUPS; r=r+1) begin : ROW_ROTATORS

        // accumulator per row
        logic [ZMAX-1:0] accum;
        assign row_parity[r] = accum;

        // valid pipeline shift register
        logic [PIPE_DEPTH*NUM_COLS-1:0] valid_pipe;

        // current rotator output
        logic [ZMAX-1:0] rotator_out;

        // barrel shifter instance for current row/column
        barrel_shifter_pipelined #(ZMAX) rotator_inst (
            .clk(clk),
            .rst(rst),
            .in_data(info_in),
            .shift_amt(shift_matrix[r][col_idx]),
            .out_data(rotator_out)
        );

        // XOR accumulation and valid shift
        always_ff @(posedge clk) begin
            if (rst) begin
                accum       <= '0;
                valid_pipe  <= '0;
            end else if (valid_in) begin
                accum <= accum ^ rotator_out;           // continuous accumulation
                valid_pipe <= {valid_pipe[PIPE_DEPTH*NUM_COLS-2:0], 1'b1}; // shift in valid
            end else begin
                valid_pipe <= {valid_pipe[PIPE_DEPTH*NUM_COLS-2:0], 1'b0};
            end
        end

        // output row valid
        assign row_valid[r] = valid_pipe[PIPE_DEPTH*NUM_COLS-1];

    end
endgenerate

always_ff @(posedge clk or posedge rst) begin
    if (rst)
        stage[i+1] <= '0;
    else
        stage[i+1] <= circular_shift_right(stage[i], shift_amt[i]);
end

function automatic logic [WIDTH-1:0] circular_shift_right;
    input logic [WIDTH-1:0] data_in;
    input int unsigned shift_amt;
    parameter int WIDTH = 81;
    
    circular_shift_right = (data_in >> shift_amt) | (data_in << (WIDTH - shift_amt));
endfunction

// Parameters
parameter WIDTH = 81;
parameter NUM_STAGES = $clog2(WIDTH);

// Pipeline registers
logic [WIDTH-1:0] stage [0:NUM_STAGES];

// Assume stage[0] is input
assign stage[0] = in_data;


//Call the function for each of the Lanes 
    genvar inari;
    generate 
        for(inari = 0; inari<NUM_PARITY_BLKS; inari++) begin : ROTATE_INST
            assign rotated_data[i] = Right_CyclicShifter(info_blk ,shift_values[i] )
        end

    endgenerate


    // data_out[i+q] = memory[addr + (( i*(DEPTH/THE_Z) + q )-1)]; 
    always_comb begin
        for(int i=0; i<NUM_PARITY_BLKS*; i++) begin
            for(int q=0; q<P_LVL; q++) begin
                data_out[i+q] = memory[addr+q +(i*(DEPTH/NUM_PARITY_BLKS)-1)];
            end
        end
    end


// Pipeline each stage using the function
genvar i;
generate
    for (i = 0; i < NUM_STAGES; i=i+1) begin : SHIFTER_STAGE
        always_ff @(posedge clk or posedge rst) begin
            if (rst)
                stage[i+1] <= '0;
            else
                stage[i+1] <= circular_shift_right(stage[i], shift_amt[i]);
        end
    end
endgenerate


genvar i, j;
generate
  for (i = 0; i < PIPELINE_STAGES; i++) begin : stage_gen
    localparam int NUM_SUBSTEPS = (i == PIPELINE_STAGES-1) ? last_stage_substeps : standard_substeps;

    // wire array for substep outputs
    wire [MAXZ-1:0] substep_wires [0:NUM_SUBSTEPS];

    assign substep_wires[0] = stage_in[i]; // input to this stage

    for (j = 0; j < NUM_SUBSTEPS; j++) begin : substep_gen
      localparam int shift_val = 1 << j;

      rot_stage #(
        .MAXZ(MAXZ),
        .SHIFT(shift_val)
      ) u_rot (
        .in_data(substep_wires[j]),
        .out_data(substep_wires[j+1]),
        .enable(1'b1) // can make conditional for skipping substeps
      );
    end

    assign stage_out[i] = substep_wires[NUM_SUBSTEPS];
  end
endgenerate