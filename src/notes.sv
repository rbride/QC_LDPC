
If you don't need to write data at the same time you're reading, you can use a dual port RAM to reduce the number of duplicated RAMs by half.
 Also if you're able to control where the data is stored, you can use banking which would allow you to use 4 smaller BRAMs
 . If you don't need max throughput (i.e. you're reading in a bursty fashion), you could use banking and a small queue. 
 One other solution is to use a higher clock frequency for the BRAM, but if the rest of your system is already running fast you probably
 won't get much improvement from that as the max frequency for BRAM isn't much faster than the max frequency 
 you could run heavily pipelined logic at. Otherwise, if you need to access 4 values every single clock cycle and their
 locations can be anywhere in memory, you'd need to just duplicate RAMs.



    // genvar c;
    // generate
    // for (c = 0; c < ROWBITS; c = c + 1) begin: test
    //     always @(posedge sysclk) begin
    //         temp[c] <= 1'b0;
    //     end
    // end
    // endgenerate
    // Generates the following 4
    //always @(posedge sysclk) temp[0] <= 1'b0;
    //always @(posedge sysclk) temp[1] <= 1'b0;
    //always @(posedge sysclk) temp[2] <= 1'b0;
    //always @(posedge sysclk) temp[3] <= 1'b0;
    
    //Assert the Reset of the Accum Registers in a generic Always block 

    // Given the undefined (See to tired to remember and look it up) Nature 
// Of the shift operator, define in test bench a check that checks to see
// that the shift is actually occuring the correct number of times in whatever
// since the input isn't an int
// wacky crazy simulator and systhesis that occurs should be fine


// assert that at no point the memory data is unknown because 
// the barrel shift function by design cast to int and it is necessary that 
// there won't be any X or Z values contained 
//  assert (!$isunknown(signal))
//        a = signal;
// else
//   $error("signal is unknown");



//Note the design is mostly suitable for only the highest rate at this point
//After completetion consider restructuring the Memory so that it compacts given
//inputs for slower rates. 



  // -------------------------------------------------------------------------
    // Memory block Module Generated based on parameter input for the matrix 
    // prototype tables provided in the Standard. 
    // Potential Expand to: Accept parameters for LUT Or BRAM based on a parameter
    // to test area and speed tradeoffs of the two (would change timing), however,
    // by concating columns together, I would be able to reduce number of cycles
    // while creating a somewhat more generic circuit that is potentially capable,
    // of on the fly swithching between code lenghts and maybe even rates. 
    // -------------------------------------------------------------------------
    
module rotate_right #(
    parameter int WIDTH = 32
)(
    input  logic [WIDTH-1:0] data_in,
    input  logic [$clog2(WIDTH)-1:0] rot_amt,
    output logic [WIDTH-1:0] data_out
);

    logic [2*WIDTH-1:0] doubled;

    // Pure wiring — no cost in hardware
    assign doubled = {data_in, data_in};

    // Single combinational select
    assign data_out = doubled[(WIDTH-1) + rot_amt -: WIDTH];

function automatic logic [WIDTH-1:0]
    rotate_right (
        input logic [WIDTH-1:0] data,
        input logic [$clog2(WIDTH)-1:0] rot
    );
    logic [2*WIDTH-1:0] doubled;
    begin
        doubled     = {data, data};
        rotate_right = doubled[(WIDTH-1) + rot -: WIDTH];
    end
endfunction



rot1 = rotate_right(data1, shift1);
rot2 = rotate_right(data2, shift2);
rot3 = rotate_right(data3, shift3);
rot4 = rotate_right(data4, shift4);

always_comb begin
    rotated = rotate_right(reg_in, shift_amt);
end

    always_ff @(posedge clk) begin
        out_data <= rotated;
    end