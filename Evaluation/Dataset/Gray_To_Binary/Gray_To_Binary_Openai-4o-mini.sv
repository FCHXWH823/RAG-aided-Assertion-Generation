module Gray_To_Binary #(
	parameter DATA_WIDTH = 3
) 
(
          input clk,
          input rst,
	input [DATA_WIDTH-1:0]        gray,
	output logic [DATA_WIDTH-1:0] bin
);

wire [DATA_WIDTH-1:0] tmp [DATA_WIDTH-1:1]; 
assign tmp[1] = ( gray >> 1 ) ^ gray;

genvar x;
generate
	for( x = 2; x < DATA_WIDTH ; x++) begin
		assign tmp[x] = ( gray >> x ) ^ tmp[x-1];
	end 
endgenerate

assign bin = tmp[DATA_WIDTH-1];


wire [DATA_WIDTH-1:0] gray_f;
assign gray_f = bin ^ ( bin >> 1 );
assert property(@(posedge clk) disable iff (~rst) gray_f == gray);

// assert property (@(posedge clk) disable iff (~rst) (bin == (gray ^ (gray >> 1)) &&                   forall (i : integer) (i >= 2 && i < DATA_WIDTH) |->                   (tmp[i] == (gray >> i) ^ tmp[i-1])));
// assert property (@(posedge clk) disable iff (~rst) (gray_f == gray) iff (bin == (gray ^ (gray >> 1)) &&                   forall (i : integer) (i >= 2 && i < DATA_WIDTH) |->                   (tmp[i] == (gray >> i) ^ tmp[i-1])));

endmodule
