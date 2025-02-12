module Gray_Code_Counter #(parameter
  DATA_WIDTH = 4
) (
  input clk,
  input resetn,
  output logic [DATA_WIDTH-1:0] out
);

reg  [DATA_WIDTH-1:0] bin_q;	
wire [DATA_WIDTH-1:0] bin_next;	
wire                  unused_bin_inc;
reg  [DATA_WIDTH-1:0] gray_q;	
wire [DATA_WIDTH-1:0] gray_next;	

always @(posedge clk)
begin
	if(~resetn) begin
		bin_q  <= {DATA_WIDTH{1'd1}};;
		gray_q <= {DATA_WIDTH{1'd0}};
	end else begin
		bin_q  <= bin_next;
		gray_q <= gray_next;
	end
end

assign { unused_bin_inc, bin_next } = bin_q + {DATA_WIDTH{1'd1}};
assign gray_next = bin_q ^ ( bin_q >> 1 );

assign out = gray_q;


assert property (@(posedge clk) disable iff (~resetn) (unused_bin_inc || (gray_next != gray_q && $countones(gray_next ^ gray_q) == 1)));
assert property (@(posedge clk) disable iff (~resetn) (unused_bin_inc | $onehot(gray_next ^ gray_q)) iff (unused_bin_inc || (gray_next != gray_q && $countones(gray_next ^ gray_q) == 1)));

endmodule
