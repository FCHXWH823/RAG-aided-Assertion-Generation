module full_adder 
(
    input a,
    input b,
    input cin,
    output sum,
    output cout
);

assign sum = a ^ b ^ cin;
assign cout = (a & b) | (a & cin) | (b & cin);
endmodule

module Ripple_Carry_Adder #(
	parameter DATA_WIDTH=8
)
(
    input [DATA_WIDTH-1:0] a,
    input [DATA_WIDTH-1:0] b,
    input clk,
    input rst,
    output logic [DATA_WIDTH-0:0] sum,
    output logic [DATA_WIDTH-1:0] cout_int
);

logic [DATA_WIDTH:0] carry;
assign carry[0] = 1'b0;

genvar x;
generate
	for( x = 0; x < DATA_WIDTH; x++ ) begin
		// instanciate adder module
		full_adder m_adder(
			.a( a[x] ),
			.b( b[x] ),
			.cin( carry[x]),
			.sum( sum[x] ),
			.cout( carry[x+1] )
		);
	end
endgenerate
// output
assign sum[DATA_WIDTH] = carry[DATA_WIDTH];
assign cout_int        = carry[DATA_WIDTH-1:0];


logic [DATA_WIDTH:0] res;
assign res = a + b;
assert property(@(posedge clk) disable iff (~rst) res == sum);

assert property (@(posedge clk) disable iff (~rst) ({carry, sum} == (a + b)));
assert property (@(posedge clk) disable iff (~rst) (res == sum) iff ({carry, sum} == (a + b)));

endmodule
