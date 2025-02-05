module bit4counter(clk, reset, counter, overflow);

input clk, reset;
output [3:0] counter;
output reg overflow;

reg [3:0] counter;

always_ff @(posedge clk, posedge reset)
begin
    //set counter and overflow to 0 if reset is 1
    if (reset) begin
        counter <= 0;
        overflow <= 0;
    end
    else begin
        counter <= counter + 1;
        //set overflow to 1 if counter is 15n
        if (counter == 4'b1111)
            overflow <= 1;
        //overflow is 0
        else 
            overflow <= 0;
    end
end

endmodule