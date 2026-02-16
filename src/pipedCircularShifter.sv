`timescale 1ns / 1ps
// ==========================================================================
// Fully Pipelined Barrel Shifter
// Author: Ryan Bride
// Description: 
//      Generic Pipelined Circular Shifter Module, Shifts right
//      and contains Clog2(MAXZ) stages (1 stage per max shift val bit),
//      The Module can be changed to do X shifts per cycle
// MAXZ: 
//      The Maximum Value should always be used for the Z, as the logic
//      incorperating this module has a step that Zero pads the input data
//
// PIPE_STAGES_PER_CYCLE:
//      As the name suggest, the number of pipeline stages per cycle
//      That the module is aiming to achieve
// ==========================================================================
module pipelinedCircularShifter2 #(
    parameter int MAXZ  = 81
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

    genvar i;
    generate
        for (i=0; i < NumStages; i++) begin : CircularShifterStage
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
    
    assign out_data = stage[NumStages];

endmodule

module pipelinedCircularShifter1 #(
    parameter int MAXZ                    = 81,
    parameter int PIPE_STAGES_PER_CYCLE   = 1
)(
    input logic CLK,
    input logic rst_n,
    input logic [MAXZ-1:0] in_data,
    input logic [$clog2(MAXZ)-1:0] shift_val,
    output logic [MAXZ-1:0] out_data
);

    localparam int NumStages = $clog2(MAXZ);
    //Pipelinelevels is equal to NumStages if the parameter is 1,
    localparam int PipelineLevels = 
        (NumStages + PIPE_STAGES_PER_CYCLE -1) / PIPE_STAGES_PER_CYCLE;
    
    //pipeline stages, stage[0] is the currently most recently streamed in data
    //
    logic [MAXZ-1:0] stage_regs [0:PipelineLevels];  
    assign stage_regs[0] = in_data;

    genvar i, q;
    generate
        for (i=0; i<PipelineLevels; i++) begin : CircularShifterStage
            logic [MAXZ-1:0] rotated;
            logic [MAXZ-1:0] temp;

            for(q=0; q<PIPE_STAGES_PER_CYCLE; q++) begin
                always_comb begin
                    temp = stage_regs[i];
                    if((i*PIPE_STAGES_PER_CYCLE+q) < NumStages) begin
                        if(shift_val[i*PIPE_STAGES_PER_CYCLE+q]) begin
                            //rotated = {rotated[temp][(1<<temp)-1:0], rotated[temp][MAXZ-1:(1<<temp)]};
                            temp = {rotated[(1<<i*PIPE_STAGES_PER_CYCLE+q)-1:0], rotated[MAXZ-1:(1<<i*PIPE_STAGES_PER_CYCLE+q)]};
                        end
                    end
                    rotated = temp;
                end

            end

            always_ff @(posedge CLK) begin
                if(!rst_n)
                    stage_regs[i+1] <= '0;
                else
                    stage_regs[i+1] <= rotated;
            end
        end
    endgenerate
    
    assign out_data = stage_regs[NumStages];

endmodule

module pipelinedCircularShifter1 #(
    parameter int MAXZ                    = 81,
    parameter int PIPE_STAGES_PER_CYCLE   = 1
)(
    input logic CLK,
    input logic rst_n,
    input logic [MAXZ-1:0] in_data,
    input logic [$clog2(MAXZ)-1:0] shift_val,
    output logic [MAXZ-1:0] out_data
);  



    localparam int NumMuxlevels             = $clog2(MAXZ);
    localparam int StagesPerPipelineLevel   = PIPE_STAGES_PER_CYCLE;
    localparam int NumStages                = (NumMuxlevels % StagesPerPipelineLevel) ?
                                              (NumMuxlevels / StagesPerPipelineLevel) :
                                              (NumMuxlevels / StagesPerPipelineLevel +1 );

    logic [MAXZ-1:0] stage_regs [0:NumStages];  
    //stage[0] is the currently most recently streamed in data so load it in
    assign stage_regs[0] = in_data;

    

 


endmodule




/*
genvar i;
    generate
        for (i=0; i<PipelineLevels; i++) begin : CircularShifterStage
            logic [MAXZ-1:0] rotated;

            always_comb begin
                //Assign the rotated the value at input so its already there incase there is no rotate
                rotated = stage_regs[i];
                //Do one barrel shift level for each of the requested Pipeline Stages per Cycle
                for(int q=0; q<PIPE_STAGES_PER_CYCLE; q++) begin
                    //For Request to split the pipeline into stages the total stages is not equally
                    //Divisible by the circuit must skip the steps requested for those rotate stages
                    //TODO: In the higher level module, use this decreased combinational logic
                    //For this stage to move in another stage into the second half of this stage
                    //To optimize the pipeline 
                    int temp = i*PIPE_STAGES_PER_CYCLE+q;
                    if(temp < NumStages) begin
                        if(shift_val[temp]) begin
                            //rotated = {rotated[temp][(1<<temp)-1:0], rotated[temp][MAXZ-1:(1<<temp)]};
                            rotated = {rotated[(1<<temp)-1:0], rotated[MAXZ-1:(1<<temp)]};

                        end
                    end
                end        
            end

            always_ff @(posedge CLK) begin
                if(!rst_n)
                    stage_regs[i+1] <= '0;
                else
                    stage_regs[i+1] <= rotated;
            end
        end
    endgenerate
*/