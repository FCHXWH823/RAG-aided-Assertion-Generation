module second_largest #(parameter
  DATA_WIDTH = 32
) (
  input clk,
  input resetn,
  input [DATA_WIDTH-1:0] din,
  output logic [DATA_WIDTH-1:0] dout
);

reg  [DATA_WIDTH-1:0] max_q;
wire [DATA_WIDTH-1:0] max_next;
reg  [DATA_WIDTH-1:0] max2_q; // second largest
wire [DATA_WIDTH-1:0] max2_next;

wire new_max;

assign new_max   = ( max_q < din);
assign max_next  = new_max ? din : max_q;
assign max2_next = new_max ? max_q : max2_q; 

always @(posedge clk)
begin
	if(~resetn) begin
		max_q  <= {DATA_WIDTH{1'b0}}; 
		max2_q <= {DATA_WIDTH{1'b0}}; 
	end
	else begin
		max_q  <= max_next;
		max2_q <= max2_next;
	end
end

// output 
assign dout = max2_q;

`ifdef FORMAL

initial begin
	// assumption
	// max_q and max2_q are not equal on init unless 0
	a_init : assume property ( (max_q == 0 & max2_q == 0) | ( max2_q < max_q));
end

always @(posedge clk)
begin
	if (~resetn) begin
		
		// assertions
		sva_max_greater_max2: assert( (max_q == 0) | ( max_q > max2_q )); 

		// cover
		c_max_zero : cover ( max_q == 0 );
		c_change : cover ( din != dout );
		c_max_greater : cover ( max_q > max2_q );	
		c_max_update : cover ( new_max );
	end
	c_reset : cover ( resetn );
end
`endif // FORMAL 

assert property(@(posedge clk) disable iff (~resetn) (max_q == 0) | (max_q > max2_q));

assert property (None None ((max_q == 0 & max2_q == 0) | (max2_q < max_q)));
assert property (None None ((max_q == 0 & max2_q == 0) | (max2_q < max_q)) iff ((max_q == 0 & max2_q == 0) | (max2_q < max_q)));
assert property (@(posedge clk) None ((max_q == 0) | (max_q > max2_q)));
assert property (@(posedge clk) None ((max_q == 0) | (max_q > max2_q)) iff ((max_q == 0) | (max_q > max2_q)));
assert property (@(posedge clk) within the active reset branch None (max_q == 0));
assert property (@(posedge clk) within the active reset branch None (max_q == 0) iff (max_q == 0));
assert property (@(posedge clk) within the active reset branch None (din != dout));
assert property (@(posedge clk) within the active reset branch None (din != dout) iff (din != dout));
assert property (@(posedge clk) within the active reset branch None (max_q > max2_q));
assert property (@(posedge clk) within the active reset branch None (max_q > max2_q) iff (max_q > max2_q));
assert property (@(posedge clk) within the active reset branch None (new_max == 1'b1));
assert property (@(posedge clk) within the active reset branch None (new_max) iff (new_max == 1'b1));
assert property (@(posedge clk) None (resetn));
assert property (@(posedge clk) None (resetn) iff (resetn));
assert property (@(posedge clk) disable iff (~resetn) ((resetn | (max_q == 0) | (max_q > max2_q))));
assert property (@(posedge clk) disable iff (~resetn) ((max_q == 0) | (max_q > max2_q)) iff ((resetn | (max_q == 0) | (max_q > max2_q))));

endmodule
