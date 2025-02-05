// `include "full_adder.sv"
module Ripple_Carry_Adder_sva #(
	parameter DATA_WIDTH=8
)
(
    input [DATA_WIDTH-1:0] a,
    input [DATA_WIDTH-1:0] b,
    input clk,
    input rst,
    input logic [DATA_WIDTH-0:0] sum,
    input logic [DATA_WIDTH-1:0] cout_int
);

default clocking cb @(posedge clk);
endclocking
default disable iff (~rst);

logic [DATA_WIDTH:0] res;
assign res = a + b;

sva_adder : assert property ( res == sum );

endmodule