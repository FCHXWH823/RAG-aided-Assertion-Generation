module rounding_division #(parameter
  DIV_LOG2=1,
  OUT_WIDTH=3,
  IN_WIDTH=OUT_WIDTH+DIV_LOG2
) (
  input [IN_WIDTH-1:0] din,
  input clk,
  input rst,
  output logic [OUT_WIDTH-1:0] dout
);

wire unused_res;
wire [OUT_WIDTH-1:0] log2;
wire [DIV_LOG2-1:0]  rnd;
wire [OUT_WIDTH-1:0] res;

assign { log2, rnd } = din;

assign { unused_res, res } = log2  + { {OUT_WIDTH-1{1'b0}} , |rnd };
assign dout = res;

`ifdef FORMAL
if ( IN_WIDTH > 63 ) $error("Longint overflows");
// assert

`endif
endmodule