// Greg Stitt
// University of Florida

// Module: simple_pipeline
// Description: This module takes 8 WIDTH-bit inputs, multiplies the 4 pairs,
// and then sums the products using a 2-level adder tree. Each stage of the
// pipeline is registered, and all overflow is ignored at each stage.

//===================================================================
// Parameter Description
// WIDTH : The data width (number of bits) of the input and output
//===================================================================

//===================================================================
// Interface Description
// clk  : Clock input
// rst  : Reset input (active high)
// in   : An array of 8 WIDTH-bit inputs
// valid_in : User should assert any time the input data on "in" is valid.
// out  : The output of the multiply accumulate computation.
// valid_out : Asserted whenever "out" contains valid data.
//===================================================================

module simple_pipeline
  #(
    parameter int WIDTH=16
    )
   (
    input logic 	     clk,
    input logic 	     rst,
    input logic [WIDTH-1:0]  in[8],
    input logic 	     valid_in,
    output logic [WIDTH-1:0] out,
    output logic 	     valid_out
    );

   // Specifies the cycle latency of the pipeline.
   localparam int 	     LATENCY = 4;
   
   logic [WIDTH-1:0] 	     in_r[8];
   logic [WIDTH-1:0] 	     mult_r[4];
   logic [WIDTH-1:0] 	     add_r[2];
   logic [WIDTH-1:0] 	     out_r;   
   logic [0:LATENCY-1] 	     valid_delay_r;

   assign out = out_r;
   
   always_ff @(posedge clk or posedge rst) begin
      if (rst) begin
	 // Reset all the registers.
	 for (int i=0; i < 8; i++) in_r[i] <= '0;
	 for (int i=0; i < 4; i++) mult_r[i] <= '0;
	 for (int i=0; i < 2; i++) add_r[i] <= '0;
	 out_r <= '0;	 
      end
      else begin
	 // Register the inputs.
	 for (int i=0; i < 8; i++) in_r[i] <= in[i];
	 // Perform the multiplications.
	 for (int i=0; i < 4; i++) mult_r[i] <= in_r[i*2] * in_r[i*2+1];
	 // Create the first level of adders.
	 for (int i=0; i < 2; i++) add_r[i] <= mult_r[i*2] + mult_r[i*2+1];
	 // Create the final adder.
	 out_r <= add_r[0] + add_r[1];
      end
   end 

   // Delay that determines when out is valid based on the pipeline latency.
   always_ff @(posedge clk or posedge rst) begin
      if (rst) begin
	 for (int i=0; i < LATENCY; i++) valid_delay_r[i] = '0;
      end
      else begin
	 valid_delay_r[0] <= valid_in;	 
	 for (int i=1; i < LATENCY; i++) valid_delay_r[i] <= valid_delay_r[i-1];
      end      
   end

   assign valid_out = valid_delay_r[LATENCY-1];   

int count;    
always_ff @(posedge clk or posedge rst)
if (rst) count = 0;
else if (count < LATENCY) count ++;
assert property(@(posedge clk) disable iff (rst) count < LATENCY |-> valid_out == 1'b0);
assert property(@(posedge clk) disable iff (rst) count == LATENCY |-> valid_out == $past(valid_in, LATENCY));

assert property (@(posedge clk) disable iff (rst) (count < LATENCY |-> valid_out == 0));
assert property (@(posedge clk) disable iff (rst) (count < LATENCY |-> valid_out == 1'b0) iff (count < LATENCY |-> valid_out == 0));
assert property (@(posedge clk) disable iff (rst) (count == LATENCY |-> $past(valid_out, LATENCY) == valid_in));
assert property (@(posedge clk) disable iff (rst) (count == LATENCY |-> valid_out == $past(valid_in, LATENCY)) iff (count == LATENCY |-> $past(valid_out, LATENCY) == valid_in));

endmodule
