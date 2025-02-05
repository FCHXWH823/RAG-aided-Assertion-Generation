module PSGBusArb_sva(
input req3,
input sel4,
input sel3,
input sel6,
input sel1,
input req4,
input req2,		// ...
input req6,
input ack,		// bus transfer completed
input req1,		// requester 1 wants the bus
input sel7,
input req0,		// requester 0 wants the bus
input sel2,
input req5,
input rst,		// reset
input req7,
input ce,		// clock enable (eg 25MHz)
input clk,		// clock (eg 100MHz)
input sel5,
input [2:0] seln,
input sel0
);

property a10;
@(posedge clk) (ce == 1 & req1 == 1) |=> (sel7 == 0);
endproperty
// assert_a10: assert property(a10);

property a0;
@(posedge clk) (req4 == 1 & req1 == 1) |=> (sel7 == 0);
endproperty
// assert_a0: assert property(a0);

property a5;
@(posedge clk) (req4 == 1 & ce == 1) |=> (sel7 == 0);
endproperty
// assert_a5: assert property(a5);

property a14;
@(posedge clk) (req2 == 0 & req6 == 0 & req4 == 0 & req0 == 0 & ack == 1 & ce == 1 & req5 == 0 & req1 == 0 & req7 == 1) |=> (sel7 == 1);
endproperty
// assert_a14: assert property(a14);

property a7;
@(posedge clk) (sel7 == 0 & req0 == 1) |=> (sel7 == 0);
endproperty
assert_a7: assert property(a7);

property a1;
@(posedge clk) (sel7 == 0 & req1 == 1) |=> (sel7 == 0);
endproperty
assert_a1: assert property(a1);

property a13;
@(posedge clk) (sel7 == 1 & ack == 0) |=> (sel7 == 1);
endproperty
assert_a13: assert property(a13);

property a12;
@(posedge clk) (sel7 == 1 & ce == 0) |=> (sel7 == 1);
endproperty
assert_a12: assert property(a12);

property a3;
@(posedge clk) (sel7 == 0 & ack == 0) |=> (sel7 == 0);
endproperty
assert_a3: assert property(a3);

property a2;
@(posedge clk) (sel7 == 0 & ce == 0) |=> (sel7 == 0);
endproperty
// assert_a2: assert property(a2);

property a4;
@(posedge clk) (sel7 == 0 & req2 == 1) |=> (sel7 == 0);
endproperty
assert_a4: assert property(a4);

property a6;
@(posedge clk) (sel7 == 0 & req3 == 1) |=> (sel7 == 0);
endproperty
assert_a6: assert property(a6);

property a11;
@(posedge clk) (sel7 == 0 & req5 == 1) |=> (sel7 == 0);
endproperty
assert_a11: assert property(a11);

property a8;
@(posedge clk) (sel7 == 0 & req6 == 1) |=> (sel7 == 0);
endproperty
assert_a8: assert property(a8);

property a19;
@(posedge clk) (sel5 == 0 & req0 == 1) |=> (sel5 == 0);
endproperty
assert_a19: assert property(a19);

property a20;
@(posedge clk) (sel5 == 0 & req1 == 1) |=> (sel5 == 0);
endproperty
assert_a20: assert property(a20);

property a26;
@(posedge clk) (sel5 == 1 & ce == 0) |=> (sel5 == 1);
endproperty
assert_a26: assert property(a26);

property a27;
@(posedge clk) (sel5 == 1 & ack == 0) |=> (sel5 == 1);
endproperty
assert_a27: assert property(a27);

property a16;
@(posedge clk) (sel5 == 0 & ack == 0) |=> (sel5 == 0);
endproperty
assert_a16: assert property(a16);

property a15;
@(posedge clk) (sel5 == 0 & ce == 0) |=> (sel5 == 0);
endproperty
assert_a15: assert property(a15);

property a18;
@(posedge clk) (sel5 == 0 & req2 == 1) |=> (sel5 == 0);
endproperty
assert_a18: assert property(a18);

property a17;
@(posedge clk) (sel5 == 0 & req3 == 1) |=> (sel5 == 0);
endproperty
assert_a17: assert property(a17);

property a21;
@(posedge clk) (sel5 == 0 & req4 == 1) |=> (sel5 == 0);
endproperty
assert_a21: assert property(a21);

property a23;
@(posedge clk) (sel5 == 0 & req5 == 0) |=> (sel5 == 0);
endproperty
assert_a23: assert property(a23);

property a35;
@(posedge clk) (sel4 == 0 & req1 == 1) |=> (sel4 == 0);
endproperty
assert_a35: assert property(a35);

property a40;
@(posedge clk) (sel4 == 1 & ack == 0) |=> (sel4 == 1);
endproperty
assert_a40: assert property(a40);

property a31;
@(posedge clk) (sel4 == 0 & ack == 0) |=> (sel4 == 0);
endproperty
assert_a31: assert property(a31);

property a30;
@(posedge clk) (sel4 == 0 & ce == 0) |=> (sel4 == 0);
endproperty
assert_a30: assert property(a30);

property a39;
@(posedge clk) (sel4 == 1 & ce == 0) |=> (sel4 == 1);
endproperty
assert_a39: assert property(a39);

property a32;
@(posedge clk) (sel4 == 0 & req2 == 1) |=> (sel4 == 0);
endproperty
assert_a32: assert property(a32);

property a33;
@(posedge clk) (sel4 == 0 & req3 == 1) |=> (sel4 == 0);
endproperty
assert_a33: assert property(a33);

property a37;
@(posedge clk) (sel4 == 0 & req4 == 0) |=> (sel4 == 0);
endproperty
assert_a37: assert property(a37);

endmodule