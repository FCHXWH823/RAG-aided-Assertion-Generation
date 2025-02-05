module Edge_Detector_sva (
	input  clk,
	input  resetn,
	input  din,
	input dout
);

default clocking cb @(posedge clk);
endclocking
default disable iff (~resetn);

reg din_f_q;
always @(posedge clk)
begin
	if ( ~resetn ) begin
		din_f_q <= 1'b0;
	end
	if (resetn) begin
		din_f_q <= din;
	end
end

sva_pulse : assert property ( $rose(din_f_q) == dout );

endmodule