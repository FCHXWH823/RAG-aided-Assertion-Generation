module delay2 
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


assert property(@(posedge clk) s_eventually (rst || sig == 1));

assert property (@(posedge clk)  (s_eventually (rst || s_eventually (sig == 1))));
assert property (@(posedge clk)  (s_eventually (rst || sig == 1)) iff (s_eventually (rst || s_eventually (sig == 1))));

endmodule
