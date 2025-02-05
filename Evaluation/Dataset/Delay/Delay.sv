module Delay 
#(
          parameter N = 750, 
          parameter CBITS = 10
) 
(input clk, input rst, output reg sig);
  reg [CBITS-1 :0] cnt;
  always @(posedge clk) begin
    if (rst) cnt = 0;
    else cnt = cnt + 1;
    if (cnt > N) begin sig = 1;
      cnt = 0; end
    else sig = 0;
  end

endmodule