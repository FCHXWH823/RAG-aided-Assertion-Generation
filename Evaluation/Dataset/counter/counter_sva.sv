module	counter_sva #(
		parameter	[15:0]	MAX_AMOUNT = 22
	) (
		input	wire	i_clk,
		input	wire	i_start_signal,
		input	logic	o_busy,
                    input     logic [15:0] counter
	);


default clocking cb @(posedge i_clk);
endclocking
default disable iff (~i_start_signal);

initial counter = 15'b0;

counter_sva: assert property (counter < MAX_AMOUNT);

endmodule
