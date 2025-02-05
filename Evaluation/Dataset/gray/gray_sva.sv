module gray_sva #(parameter CBITS = 8) (input clk, input rst, input logic [CBITS-1:0] gray_cnt, input logic sig);

  p1: assert property (@(posedge clk) s_eventually (rst || sig == 1));
  // F G (rst = F) -> G F (sig = T)
endmodule