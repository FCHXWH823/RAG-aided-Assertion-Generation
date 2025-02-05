bind arb2
  arb2_sva u_arb2_sva (
  .clk(clk),
  .rst(rst),
  .gnt1(gnt1),
  .gnt2(gnt2),
  .req1(req1),
  .req2(req2),
  .state(state)
  );
