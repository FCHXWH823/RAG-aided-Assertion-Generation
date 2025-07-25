module gray #(parameter CBITS = 8) (input clk, input rst, output reg [CBITS-1:0] gray_cnt, output reg sig);
  reg [CBITS-1:0] cnt;
  always@(posedge clk, posedge rst) begin
    if (rst) begin
      cnt = 0;
    end
    else begin
      cnt = cnt + 1;
      gray_cnt = (cnt) ^ ((cnt) >> 1);
      if(gray_cnt == 0)
        sig = 1;
      else
        sig = 0;
    end
  end
  // F G (rst = F) -> G F (sig = T)

assert property(@(posedge clk) s_eventually (rst || sig == 1));

assert property (@(posedge clk)  ($rose(rst) || $fell(sig)));
assert property (@(posedge clk)  (s_eventually (rst || sig == 1)) iff ($rose(rst) || $fell(sig)));

endmodule
