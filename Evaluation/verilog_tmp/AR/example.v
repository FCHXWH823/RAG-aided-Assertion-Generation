module main (clk);
input clk;
reg [2500:0] a,b;	
	
initial a = 1;
initial b = 0;


always @ (posedge clock) begin
	if (a<100) 
	   a<=b+a;

	b <=a;
end

//always begin

//assert property: (a<200);
//end

endmodule