module Flip_Flop_Array_sva #(
	parameter DATA_W = 8,
	parameter ADDR_W = 3,
	parameter DATA_N = 8 // getting non constant error when using $pow(2,ADDR_W)
)
(
    input clk,
    input resetn,

    input [DATA_W-1:0] din,
    input [ADDR_W-1:0] addr,
    input              wr,
    input              rd,

    input logic [DATA_W-1:0] dout,
    input logic              error,
    input logic rd_v,
    input logic [DATA_N-1:0] data_v_q,
    input logic [DATA_N-1:0] rd_en
);

sva_collision_err: assert property (@(posedge clk) ~( rd & wr ) | ( rd & wr & error ));
sva_invalid_read : assert property (@(posedge clk) ~(~data_v_q & rd_en )  | (~data_v_q & rd_en & ( dout == '0 )));  
sva_sel_onehot0 : assert property (@(posedge clk) $onehot0(rd_v)); 

endmodule