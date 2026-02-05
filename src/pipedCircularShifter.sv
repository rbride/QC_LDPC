// ===========================================================
// Fully Pipelined Barrel Shifter
// ===========================================================
module pipelinedCircularShifter #(
    parameter int MAXZ = 81
)(
    input logic CLK,
    input logic rst_n,
    input logic [MAXZ-1:0] in_data,
    input logic [$clog2(MAXZ)-1:0] shift_val,
    output logic [MAXZ-1:0] out_data
);

    localparam int NumStages = $clog2(MAXZ);
    
    //pipeline stages, stage[0] is the currently most recently streamed in data
    logic [MAXZ-1:0] stage [0:NumStages];  
    assign stage[0] = in_data;

    genvar q;
    generate
        for (q=0; i < NumStages; i++) begin : CircularShifterStage
            logic [MAXZ-1:0] rotated;

            always_comb begin
                if(shift_val[i]) 
                    rotated = {stage[i][(1<<i)-1:0], stage[i][MAXZ-1:(1<<i)]};

                else
                    rotated = stage[i];
            end

            //pipeline Registers 
            always_ff @(posedge CLK) begin
                if(!rst_n)
                    stage[i+1] <= '0;
                else
                    stage[i+1] <= rotated;
            end
        end
    endgenerate
    
    assign out_data = stage[NumStages]

endmodule
