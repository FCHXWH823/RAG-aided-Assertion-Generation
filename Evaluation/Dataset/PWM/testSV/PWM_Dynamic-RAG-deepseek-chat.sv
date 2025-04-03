module PWM #(parameter CBITS = 10) 
(input clk, input rst, input [3:0] sw, output reg pulse);
  
  wire [CBITS-1:0] pulse_wide;
  assign pulse_wide = {1'b0, sw[3:1], 6'd0};     // (CBTIS-4)

  reg [CBITS-1:0] cntR;

  always @(posedge clk) begin
    cntR <= cntR + 1;
    
    if (cntR < pulse_wide)
      pulse = 1'b1;
    else
      pulse = 1'b0;
  end


assert property(@(posedge clk) 1 |-> s_eventually(~pulse));

// assert property (@(posedge clk)  (GENERATE_NO_ASSERTION));
// assert property (@(posedge clk)  (1 |-> s_eventually(~pulse)) iff (GENERATE_NO_ASSERTION));

endmodule
