module Flip_Flop_Array #(
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

    output logic [DATA_W-1:0] dout,
    output logic              error
);

// register file
reg   [DATA_W-1:0] data_q[DATA_N-1:0];
reg   [DATA_N-1:0] data_v_q;
logic [DATA_W-1:0] data_rd[DATA_N-1:0];
logic [DATA_N-1:0] data_v_next;
logic [DATA_N-1:0] rd_en;
logic [DATA_N-1:0] wr_en;
logic [DATA_N-1:0] addr_v;
logic rd_v;
always @(posedge clk)
begin
	if ( ~resetn ) begin
		data_v_q <= {DATA_N{1'b0}};
	end else begin
		data_v_q <= data_v_next;
	end
end

genvar x;
generate
	for( x=0; x < DATA_N; x++) begin
		assign addr_v[x] = addr == x;
		assign wr_en[x]  = wr & addr_v[x];	
		assign rd_en[x]  = rd & addr_v[x];

		assign data_v_next[x] = wr_en[x];
		assign data_rd[x] = {DATA_W{rd_en[x]}} & data_q[x];
 
		always @(posedge clk) begin
			if ( wr_en[x] ) begin
				data_q[x] <= din;
			end
		end	
	end
endgenerate
// read valid
assign rd_v  = data_v_q & rd_en;

assign error = ( rd & ~|rd_v) |  wr & rd ;

always_comb begin
	for( int i=0; i < DATA_N; i++ ) begin
		if ( 1 << i == rd_v ) dout = data_rd[i];
	end
	dout = {DATA_W{1'b0}};
end


assert property(@(posedge clk) ~(rd & wr) | (rd & wr & error));
assert property(@(posedge clk) ~(~data_v_q & rd_en) | (~data_v_q & rd_en & (dout == '0)));
assert property(@(posedge clk) $onehot0(rd_v));

assert property (@(posedge clk)  (!(wr && rd) || error));
assert property (@(posedge clk)  (~(rd & wr) | (rd & wr & error)) iff (!(wr && rd) || error));
// assert property (@(posedge clk)  (!(rd & ~|rd_v) || (rd & ~data_v_q[addr] => dout == {DATA_W{1'b0}})));
//assert property (@(posedge clk)  (~(~data_v_q & rd_en) | (~data_v_q & rd_en & (dout == '0))) iff (!(rd & ~|rd_v) || (rd & ~data_v_q[addr] => dout == {DATA_W{1'b0}})));
assert property (@(posedge clk)  (rd_v != 0 && (rd_v == (rd_v & (rd_v - 1)))));
assert property (@(posedge clk)  ($onehot0(rd_v)) iff (rd_v != 0 && (rd_v == (rd_v & (rd_v - 1)))));

endmodule
