module arb2(clk, rst, req1, req2, gnt1, gnt2);

input clk, rst;
input req1, req2;
output gnt1, gnt2;

reg state;
reg gnt1, gnt2;

always @ (posedge clk or posedge rst)
	if (rst)
		state <= 0;
	else
		state <= gnt1;

always @ (*)
	if (state)
	begin
		gnt1 = req1 & ~req2;
		gnt2 = req2;
	end
	else
	begin
		gnt1 = req1;
		gnt2 = req2 & ~req1;
	end


assert property(@(posedge clk) (state == 1 & req2 == 1) |-> (gnt1 == 0));
assert property(@(posedge clk) (req1 == 1 & state == 0) |-> (gnt1 == 1));
assert property(@(posedge clk) (req1 == 0) |-> (gnt1 == 0));
assert property(@(posedge clk) (req1 == 1 & req2 == 0) |-> (gnt1 == 1));
assert property(@(posedge clk) (req1 == 1 & state == 0) |-> (gnt2 == 0));
assert property(@(posedge clk) (req2 == 1 & state == 1) |-> (gnt2 == 1));
assert property(@(posedge clk) (req2 == 0) |-> (gnt2 == 0));
assert property(@(posedge clk) (req2 == 1 & req1 == 0) |-> (gnt2 == 1));

assert property (@(posedge clk)  (state & req2 |-> !gnt1));
assert property (@(posedge clk)  ((state == 1 & req2 == 1) |-> (gnt1 == 0)) iff (state & req2 |-> !gnt1));
assert property (@(posedge clk)  (@(posedge clk) (req1 == 1 and state == 0) |-> (gnt1 == 1)));
assert property (@(posedge clk)  ((req1 == 1 & state == 0) |-> (gnt1 == 1)) iff (@(posedge clk) (req1 == 1 and state == 0) |-> (gnt1 == 1)));
assert property (@(posedge clk)  ((!req1) |-> (!gnt1)));
assert property (@(posedge clk)  ((req1 == 0) |-> (gnt1 == 0)) iff ((!req1) |-> (!gnt1)));
assert property (@(posedge clk)  ((req1 == 1 && req2 == 0) |-> (gnt1 == 1)));
assert property (@(posedge clk)  ((req1 == 1 & req2 == 0) |-> (gnt1 == 1)) iff ((req1 == 1 && req2 == 0) |-> (gnt1 == 1)));
// assert property (@(posedge clk)  (p_req1_state0_gnt2_0));
// assert property (@(posedge clk)  ((req1 == 1 & state == 0) |-> (gnt2 == 0)) iff (p_req1_state0_gnt2_0));
assert property (@(posedge clk)  ((req2 && state) |-> gnt2));
assert property (@(posedge clk)  ((req2 == 1 & state == 1) |-> (gnt2 == 1)) iff ((req2 && state) |-> gnt2));
// assert property (@(posedge clk)  (req2 == 0 ⇒ gnt2 == 0));
// assert property (@(posedge clk)  ((req2 == 0) |-> (gnt2 == 0)) iff (req2 == 0 ⇒ gnt2 == 0));
assert property (@(posedge clk)  ((arb2.req2 == 1 && arb2.req1 == 0) |-> arb2.gnt2 == 1));
assert property (@(posedge clk)  ((req2 == 1 & req1 == 0) |-> (gnt2 == 1)) iff ((arb2.req2 == 1 && arb2.req1 == 0) |-> arb2.gnt2 == 1));

endmodule
