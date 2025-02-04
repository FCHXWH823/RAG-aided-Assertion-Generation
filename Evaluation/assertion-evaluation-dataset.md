code	assertion	link	HumanExplanation	pure code
"module register
  #(
    parameter WIDTH,
    parameter logic HAS_ASYNC_RESET = 1'b1,
    parameter logic RESET_ACTIVATION_LEVEL = 1'b1,
    parameter logic [WIDTH-1:0] RESET_VALUE = '0
    )
   (
    input logic 	     clk,
    input logic 	     rst,
    input logic 	     en,
    input logic [WIDTH-1:0]  in,
    output logic [WIDTH-1:0] out
    );

   generate
      if (HAS_ASYNC_RESET) begin
	 always_ff @(posedge clk or posedge rst) begin
	    if (rst == RESET_ACTIVATION_LEVEL)
	      out <= RESET_VALUE;
	    else if (en)
	      out <= in;    	
	 end
      end
      else begin
	 always_ff @(posedge clk) begin
	    if (rst == RESET_ACTIVATION_LEVEL)
	      out <= RESET_VALUE;	      
	    else if (en)
	      out <= in;
	 end	
      end
   endgenerate
endmodule // register

// Module: delay
// Description: This module delays a provided WIDTH-bit input by CYCLES cycles.
// It also has configuration parmaters for reset type, activation level, and
// value. Finally, it has an enable signal that stalls the delay when not
// not asserted.
//
// See delay.pdf for an illustration of the schematic.

module delay
  #(
    parameter int 		CYCLES=4,
    parameter int 		WIDTH=8,
    parameter logic 		HAS_ASYNC_RESET = 1'b1,
    parameter logic 		RESET_ACTIVATION_LEVEL = 1'b1,
    parameter logic [WIDTH-1:0] RESET_VALUE = '0
    )
   (
    input logic 	     clk, rst, en,
    input logic [WIDTH-1:0]  in,
    output logic [WIDTH-1:0] out
    );

   // Ideally, every module would validate its parameters because often
   // certain values are undefined. For example, a negative cycles delay
   // doesn't make sense. Similarly, only positive widths make sense.
   // Unfortunately, parameter validation is somewhat lacking in SystemVerilog,
   // at least in the older versions. Some of the possibilities are shown
   // below.
   
   if (CYCLES < 0) begin
      // One workaround to missing validation constructs is to simply call
      // an undefined module with a name that specifies the error.
      cycles_parameter_must_be_ge_0();

      // The 2009 SV standard defines the $error function, which prints during
      // compilation. However, not every tool supports it yet. Also, despite 
      // the name, $error only created a warning in the version of Quartus
      // used for testing.
      //
      // $error(""ERROR: CYCLES parameter must be >= 0."");

      // $fatal does caused Quartus synthesis to terminate, but is not 
      // supported by every synthesis tool.
      //
      // $fatal(""ERROR: CYCLES parameter must be >= 0."");
   end
   if (WIDTH < 1) begin
      width_parameter_must_be_gt_0();      
      //$error(""ERROR: WIDTH parameter must be >= 1."");
      //$fatal(1, ""ERROR: WIDTH parameter must be >= 1."");      
   end

   // Create an array of WIDTH-bit signals, which will connect all the registers
   // together (see delay.pdf). The array uses CYCLES+1 elements because there
   // are CYCLES register outputs, plus the input to the first register.
   //
   // When creating an array this way, the CYCLES+1 section creates an unpacked
   // array. The [WIDTH-1:0] section creates a packed array. Packed arrays and
   // unpacked arrays support different operations, but generally you will use
   // the unpacked section to specify bits, and the unpacked section to specify
   // the total number of elements.
   //
   // The CYCLES+1 notation is short for [0:CYCLES+1-1]. A common convention is
   // to use ""downto"" syntax for the packed array, and ""to"" syntax for the
   // unpacked array. Most people are used to thinking of arrays starting at 
   // index 0, and the MSB starting at the highest number.
   //
   // VHDL COMPARISON: packed arrays are missing from VHDL, where you instead 
   // have to create a custom array type. In SV, every signal can become an
   // unpacked array simply by adding [], which is very convenient.
   logic [WIDTH-1:0] 	     regs[CYCLES+1];
   
   if (CYCLES == 0) begin
      // For CYCLES == 0, there is no delay, so just use a wire.
      assign out = in;
   end
   else if (CYCLES > 0) begin
      // Create a sequence of CYCLES registers, where each register adds one
      // cycle to the delay.
      
      for (genvar i=0; i < CYCLES; i++) begin : reg_array
	 register #(.WIDTH(WIDTH),
		    .HAS_ASYNC_RESET(HAS_ASYNC_RESET),
		    .RESET_ACTIVATION_LEVEL(RESET_ACTIVATION_LEVEL),
		    .RESET_VALUE(RESET_VALUE))
	 reg_array (.in(regs[i]), .out(regs[i+1]), .*);	 	 
      end

      // The first register's input comes from the delay's input.
      assign regs[0] = in;
      
      // The last register's output goes to the delay's output.
      assign out = regs[CYCLES];      
      
   end       
endmodule"	"module delay_sva
  #(
    parameter int 		CYCLES=4,
    parameter int 		WIDTH=8,
    parameter logic 		HAS_ASYNC_RESET = 1'b1,
    parameter logic 		RESET_ACTIVATION_LEVEL = 1'b1,
    parameter logic [WIDTH-1:0] RESET_VALUE = '0
    )
   (
    input logic 	     clk, rst, en,
    input logic [WIDTH-1:0]  in,
    input logic [WIDTH-1:0] out
    );
      
//   localparam CYCLES = 4;  
//   localparam WIDTH = 8;  
//   localparam logic HAS_ASYNC_RESET = 1'b1;   
//   localparam logic RESET_ACTIVATION_LEVEL = 1'b1;   
//   localparam logic [WIDTH-1:0] RESET_VALUE = '0; 

   default clocking cb @(posedge clk);
   endclocking
   default disable iff (rst);

   int count;    
   always_ff @(posedge clk or posedge rst)
     if (rst) count = 0;
     else if (en == 1'b1 && count < CYCLES) count ++;

   assert property(count < CYCLES || out == $past(in, CYCLES, en));

   assert property(count == CYCLES || out == RESET_VALUE);

   assert property(!en |=> $stable(out));
         
endmodule // delay_tb4"	https://github.com/ARC-Lab-UF/sv-tutorial/blob/main/testbenches/assertions/delay_tb.sv	"This file is a testbench. 
Assertion 1:
This assertion checks that at every rising edge of the clock (posedge clk), the value of the output (out) from the delay module matches the expected value (reference_queue[0])."	"module delay_tb2;

   localparam NUM_TESTS = 1000;
      
   localparam CYCLES = 30;  
   localparam WIDTH = 8;  
   localparam logic HAS_ASYNC_RESET = 1'b1;   
   localparam logic RESET_ACTIVATION_LEVEL = 1'b1;   
   localparam logic [WIDTH-1:0] RESET_VALUE = '0; 
   logic             clk = 1'b0;
   logic             rst;
   logic             en;
   logic [WIDTH-1:0] in; 
   logic [WIDTH-1:0] out;

   delay #(.CYCLES(CYCLES), .WIDTH(WIDTH), .HAS_ASYNC_RESET(HAS_ASYNC_RESET),
           .RESET_ACTIVATION_LEVEL(RESET_ACTIVATION_LEVEL), 
           .RESET_VALUE(RESET_VALUE))
   
   DUT (.*);
   
   initial begin : generate_clock
      while (1)
        #5 clk = ~clk;      
   end
           
   initial begin
      $timeformat(-9, 0, "" ns"");

      rst <= 1'b1;
      en <= 1'b0;      
      in <= '0;      
      for (int i=0; i < 5; i++)
        @(posedge clk);

      @(negedge clk);
      rst <= 1'b0;

      for (int i=0; i < NUM_TESTS; i++) begin
         in <= $random;
         en <= $random;         
         @(posedge clk);
      end  

      disable generate_clock;
      $display(""Tests completed."");      
   end

   logic [WIDTH-1:0] reference_queue[$];
   
   always_ff @(posedge clk or posedge rst)
     if (rst) begin
        reference_queue = {};
        for (int i=0; i < CYCLES; i++) reference_queue = {reference_queue, RESET_VALUE};
     end
     else if (en) begin
        reference_queue = {reference_queue[1:$], in};
     end

         
endmodule"
"module ff
  (
   input logic clk, rst, en, in,
   output logic out   
   );

   always_ff @(posedge clk or posedge rst)
      if (rst) out = 1'b0;
      else if (en) out = in;         
endmodule"	"module ff_sva(
input logic clk,
input logic rst, 
input logic en,
input logic in,
input logic out
);

    default clocking cb @(posedge clk);
    endclocking
    default disable iff (rst);

   assert property(en |=> out == $past(in,1));

   assert property(!en |=> out == $past(out,1));
   // assert property(@(posedge clk) disable iff (rst) !en |=> $stable(out));

endmodule"	https://github.com/ARC-Lab-UF/sv-tutorial/blob/main/testbenches/assertions/ff_tb.sv 	"Assertion 1:
This assertion ensures that the output (out) of the delay module matches the input (in) delayed by the specified number of cycles (CYCLES) on the posedge of clk. But this assertion is disabled when the reset signal (rst) is active or the delay cycle count (count) is less than CYCLES.
Assertion 2:
This assertion ensures that the output (out) of the delay module matches the parameter RESET_VALUE on the posedge of clk. But this assertion is disabled when count equals CYCLES.
"	"module delay_tb3;

   localparam NUM_TESTS = 1000;
      
   localparam CYCLES = 30;  
   localparam WIDTH = 8;  
   localparam logic HAS_ASYNC_RESET = 1'b1;   
   localparam logic RESET_ACTIVATION_LEVEL = 1'b1;   
   localparam logic [WIDTH-1:0] RESET_VALUE = '0; 
   logic             clk = 1'b0;
   logic             rst;
   logic             en;
   logic [WIDTH-1:0] in; 
   logic [WIDTH-1:0] out;

   delay #(.CYCLES(CYCLES), .WIDTH(WIDTH), .HAS_ASYNC_RESET(HAS_ASYNC_RESET),
           .RESET_ACTIVATION_LEVEL(RESET_ACTIVATION_LEVEL), 
           .RESET_VALUE(RESET_VALUE))

   DUT (.en(1'b1), .*);
   
   initial begin : generate_clock
      while (1)
        #5 clk = ~clk;      
   end
           
   initial begin
      $timeformat(-9, 0, "" ns"");

      rst <= 1'b1;
      in <= '0;      
      for (int i=0; i < 5; i++)
        @(posedge clk);
      
      @(negedge clk);
      rst <= 1'b0;

      for (int i=0; i < NUM_TESTS; i++) begin
         in <= $random;
         @(posedge clk);
      end  

      disable generate_clock;
      $display(""Tests completed."");      
   end

   int count;    
   always_ff @(posedge clk or posedge rst)
     if (rst) count = 0;
     else if (count < CYCLES) count ++;

  
endmodule"
"// Greg Stitt
// University of Florida

// Module: register
// Description: Implements a register with an active high, asynchronous reset
// and an enable signal.

module register
  #(
    parameter WIDTH
    )
   (
    input logic              clk,
    input logic              rst,
    input logic              en,
    input logic [WIDTH-1:0]  in,
    output logic [WIDTH-1:0] out
    );
   
   always_ff @(posedge clk or posedge rst) begin
      if (rst)
        out <= '0;
      else if (en)
        out <= in;      
   end 
   
endmodule"	"module register_sva  #(
    parameter WIDTH=8
    )
   (
    input logic              clk,
    input logic              rst,
    input logic              en,
    input logic [WIDTH-1:0]  in,
    input logic [WIDTH-1:0] out
    );

    default clocking cb @(posedge clk);
    endclocking
    default disable iff (rst);
   // For the enable, we can use the same strategy as the FF example.
   // Verify output when enable is asserted.
   assert property(en |=> out == $past(in,1));

   // Verify output when enable isn't asserted. Only one of these is needed
   // since they are equivalent.
   assert property(!en |=> out == $past(out,1));

endmodule"	https://github.com/ARC-Lab-UF/sv-tutorial/blob/main/testbenches/assertions/register_tb.sv	"Assertion 1:
Checks that whenever the signal in is true on a clock cycle (at the rising edge of clk), the signal out must be true in the following clock cycle and this assertion is only evaluated on the rising edge of clk and is disabled (not checked) when the rst signal is asserted (i.e., rst is high). 
Assertion 2:
Check to make sure the reset is working correctly. Technically, this is checking for an synchronous reset because it checks to see if out is not asserted on every rising edge after rst is 1. 
Assertion 3:
Check for the asynchronous reset, i.e., when rst is 1, out signal should be 0."	"module ff_tb1;

   localparam NUM_TESTS = 10000;   
   logic clk=1'b0, rst, en, in, out;

   ff DUT (.en(1'b1), .*);

   initial begin : generate_clock
      while(1)
        #5 clk = ~clk;      
   end

   initial begin : drive_inputs
      $timeformat(-9, 0, "" ns"");         

      rst <= 1'b1;
      in <= 1'b0;      
      en <= 1'b0;

      for (int i=0; i < 5; i++)
        @(posedge clk);

      @(negedge clk);
      rst <= 1'b0;

      for (int i=0; i < NUM_TESTS; i++) begin    
         in <= $random;
         en <= $random;
         @(posedge clk);
      end

      disable generate_clock;
      $display(""Tests completed."");
   end 
     
endmodule"
"module fifo
  #(
    parameter WIDTH=8,
    parameter DEPTH=16
    )
   (
    input logic              clk,
    input logic              rst,
    output logic             full,
    input logic              wr_en,
    input logic [WIDTH-1:0]  wr_data,
    output logic             empty, 
    input logic              rd_en,
    output logic [WIDTH-1:0] rd_data  
    );

   localparam int READ_LATENCY = 1;
   
   logic [WIDTH-1:0]         ram[DEPTH];
   logic                     valid_wr, valid_rd;

   localparam int            ADDR_WIDTH = $clog2(DEPTH)+1;
   logic [ADDR_WIDTH-1:0]   wr_addr_r, rd_addr_r;

   always_ff @(posedge clk) begin
      if (valid_wr) ram[wr_addr_r[ADDR_WIDTH-2:0]] <= wr_data;
      rd_data <= ram[rd_addr_r[ADDR_WIDTH-2:0]];      
   end
      
   always_ff @(posedge clk or posedge rst) begin
      if (rst) begin
         rd_addr_r <= '0;
         wr_addr_r <= '0;
      end
      else begin         
         if (valid_wr) wr_addr_r <= wr_addr_r + 1'b1;
         if (valid_rd) rd_addr_r <= rd_addr_r + 1'b1;
      end
   end 
      
   assign valid_wr = wr_en && !full;
   assign valid_rd = rd_en && !empty;

   assign full = rd_addr_r[ADDR_WIDTH-2:0] == wr_addr_r[ADDR_WIDTH-2:0] && rd_addr_r[ADDR_WIDTH-1] != wr_addr_r[ADDR_WIDTH-1];

   assign empty = rd_addr_r == wr_addr_r;
      
endmodule
"	"module fifo_sva  #(
    parameter WIDTH=8,
    parameter DEPTH=16
    )
   (
    input logic              clk,
    input logic              rst,
    input logic             full,
    input logic              wr_en,
    input logic [WIDTH-1:0]  wr_data,
    input logic             empty, 
    input logic              rd_en,
    input logic [WIDTH-1:0] rd_data,  
    input logic valid_wr, 
    input logic valid_rd
    );

   default clocking cb @(posedge clk);
   endclocking
   default disable iff (rst);
   assert property (valid_wr |-> !full);
   assert property (valid_rd |-> !empty);

endmodule"	https://github.com/ARC-Lab-UF/sv-tutorial/blob/main/testbenches/assertions/fifo_tb.sv		
"// Greg Stitt
// University of Florida

// Module: simple_pipeline
// Description: This module takes 8 WIDTH-bit inputs, multiplies the 4 pairs,
// and then sums the products using a 2-level adder tree. Each stage of the
// pipeline is registered, and all overflow is ignored at each stage.

//===================================================================
// Parameter Description
// WIDTH : The data width (number of bits) of the input and output
//===================================================================

//===================================================================
// Interface Description
// clk  : Clock input
// rst  : Reset input (active high)
// in   : An array of 8 WIDTH-bit inputs
// valid_in : User should assert any time the input data on ""in"" is valid.
// out  : The output of the multiply accumulate computation.
// valid_out : Asserted whenever ""out"" contains valid data.
//===================================================================

module simple_pipeline
  #(
    parameter int WIDTH=16
    )
   (
    input logic 	     clk,
    input logic 	     rst,
    input logic [WIDTH-1:0]  in[8],
    input logic 	     valid_in,
    output logic [WIDTH-1:0] out,
    output logic 	     valid_out
    );

   // Specifies the cycle latency of the pipeline.
   localparam int 	     LATENCY = 4;
   
   logic [WIDTH-1:0] 	     in_r[8];
   logic [WIDTH-1:0] 	     mult_r[4];
   logic [WIDTH-1:0] 	     add_r[2];
   logic [WIDTH-1:0] 	     out_r;   
   logic [0:LATENCY-1] 	     valid_delay_r;

   assign out = out_r;
   
   always_ff @(posedge clk or posedge rst) begin
      if (rst) begin
	 // Reset all the registers.
	 for (int i=0; i < 8; i++) in_r[i] <= '0;
	 for (int i=0; i < 4; i++) mult_r[i] <= '0;
	 for (int i=0; i < 2; i++) add_r[i] <= '0;
	 out_r <= '0;	 
      end
      else begin
	 // Register the inputs.
	 for (int i=0; i < 8; i++) in_r[i] <= in[i];
	 // Perform the multiplications.
	 for (int i=0; i < 4; i++) mult_r[i] <= in_r[i*2] * in_r[i*2+1];
	 // Create the first level of adders.
	 for (int i=0; i < 2; i++) add_r[i] <= mult_r[i*2] + mult_r[i*2+1];
	 // Create the final adder.
	 out_r <= add_r[0] + add_r[1];
      end
   end 

   // Delay that determines when out is valid based on the pipeline latency.
   always_ff @(posedge clk or posedge rst) begin
      if (rst) begin
	 for (int i=0; i < LATENCY; i++) valid_delay_r[i] = '0;
      end
      else begin
	 valid_delay_r[0] <= valid_in;	 
	 for (int i=1; i < LATENCY; i++) valid_delay_r[i] <= valid_delay_r[i-1];
      end      
   end

   assign valid_out = valid_delay_r[LATENCY-1];   
endmodule"	"// Greg Stitt
// University of Florida
//
// This testbench illustrates how to create a testbench for a simple pipeline
// without an enable. It also demonstrates subtle timing differences when 
// functions are used within assertion properties.
//
// TODO: Change the commented out assertion properties to test each version. 

`timescale 1 ns / 100 ps

module simple_pipeline_sva   #(
    parameter int WIDTH=16,
    parameter int LATENCY=4
    )
   (
    input logic 	     clk,
    input logic 	     rst,
    input logic [WIDTH-1:0]  in[8],
    input logic 	     valid_in,
    input logic [WIDTH-1:0] out,
    input logic 	     valid_out
    );

    default clocking cb @(posedge clk);
    endclocking
    default disable iff (rst);
      

   function automatic logic is_out_correct1(logic [WIDTH-1:0] in[8]);      
     logic [WIDTH-1:0] sum = 0;
      
      for (int i=0; i < 4; i++) begin
         sum += in[i*2] * in[i*2+1];     
      end
      
      return sum == out;      
   endfunction
   
   // To solve the problem with the previous function, we simply add a parameter
   // to the function that takes the output from the assertion property, which
   // ensures that the output has not been changed yet after the clock edge.
   function automatic logic is_out_correct2(logic [WIDTH-1:0] in[8], logic [WIDTH-1:0] out);
      logic [WIDTH-1:0] sum = 0;
      
      for (int i=0; i < 4; i++) begin
         sum += in[i*2] * in[i*2+1];     
      end
      
      return sum == out;      
   endfunction
   
   int count;    
   always_ff @(posedge clk or posedge rst)
     if (rst) count = 0;
     else if (count < LATENCY) count ++;
      
   // Make sure the valid output is not asserted after reset until the pipeline
   // fills up.
   assert property (count < LATENCY |-> valid_out == 1'b0);

   // Make sure valid out is asserted correctly after the pipeline is full.
   assert property (count == LATENCY |-> valid_out == $past(valid_in, LATENCY));
   
      
endmodule"	https://github.com/ARC-Lab-UF/sv-tutorial/blob/main/testbenches/assertions/fifo_tb.sv	"Assertion 1: 
Check to see if the output is not asserted one cycle after the input is not asserted. In other words, what we ideally want is to check if the output is equal to the input from one cycle in the past. 
Assertion 2-3:
Both to check to make sure that the output doesn't change when the enable isn't asserted. We can either do this by using the $past function to check the output on the previous cycle, or by using the $stable function, which is semantically equivalent. 
Assertion 4:
Check for the asynchronous reset, i.e., when rst is 1, out signal should be 0."	"module ff_tb2;

   localparam NUM_TESTS = 10000;   
   logic clk=1'b0, rst, en, in, out;

   ff DUT (.*);

   initial begin : generate_clock
      while(1)
        #5 clk = ~clk;      
   end

   initial begin : drive_inputs
      $timeformat(-9, 0, "" ns"");         

      rst <= 1'b1;
      in <= 1'b0;      
      en <= 1'b0;
      
      for (int i=0; i < 5; i++)
        @(posedge clk);

      @(negedge clk);
      rst <= 1'b0;

      for (int i=0; i < NUM_TESTS; i++) begin    
         in <= $random;
         en <= $random;
         @(posedge clk);
      end

      disable generate_clock;
      $display(""Tests completed."");
   end 

endmodule"
"
// AHB to APG Bridge | Maven Silicon
//
//
//
// APB FSM Controller
// Date:08-06-2022
//
// By-Prajwal Kumar Sahu

module APB_FSM_Controller( Hclk,Hresetn,valid,Haddr1,Haddr2,Hwdata1,Hwdata2,Prdata,Hwrite,Haddr,Hwdata,Hwritereg,tempselx, 
			   Pwrite,Penable,Pselx,Paddr,Pwdata,Hreadyout);

input Hclk,Hresetn,valid,Hwrite,Hwritereg;
input [31:0] Hwdata,Haddr,Haddr1,Haddr2,Hwdata1,Hwdata2,Prdata;
input [2:0] tempselx;
output reg Pwrite,Penable;
output reg Hreadyout;  
output reg [2:0] Pselx;
output reg [31:0] Paddr,Pwdata;

//////////////////////////////////////////////////////PARAMETERS

parameter ST_IDLE=3'b000;
parameter ST_WWAIT=3'b001;
parameter ST_READ= 3'b010;
parameter ST_WRITE=3'b011;
parameter ST_WRITEP=3'b100;
parameter ST_RENABLE=3'b101;
parameter ST_WENABLE=3'b110;
parameter ST_WENABLEP=3'b111;


//////////////////////////////////////////////////// PRESENT STATE LOGIC

reg [2:0] PRESENT_STATE,NEXT_STATE;

always @(posedge Hclk)
 begin:PRESENT_STATE_LOGIC
  if (~Hresetn)
    PRESENT_STATE<=ST_IDLE;
  else
    PRESENT_STATE<=NEXT_STATE;
 end


/////////////////////////////////////////////////////// NEXT STATE LOGIC

always @(PRESENT_STATE,valid,Hwrite,Hwritereg)
 begin:NEXT_STATE_LOGIC
  case (PRESENT_STATE)
    
 	ST_IDLE:begin
		 if (~valid)
		  NEXT_STATE=ST_IDLE;
		 else if (valid && Hwrite)
		  NEXT_STATE=ST_WWAIT;
		 else 
		  NEXT_STATE=ST_READ;
		end    

	ST_WWAIT:begin
		 if (~valid)
		  NEXT_STATE=ST_WRITE;
		 else
		  NEXT_STATE=ST_WRITEP;
		end

	ST_READ: begin
		   NEXT_STATE=ST_RENABLE;
		 end

	ST_WRITE:begin
		  if (~valid)
		   NEXT_STATE=ST_WENABLE;
		  else
		   NEXT_STATE=ST_WENABLEP;
		 end

	ST_WRITEP:begin
		   NEXT_STATE=ST_WENABLEP;
		  end

	ST_RENABLE:begin
		     if (~valid)
		      NEXT_STATE=ST_IDLE;
		     else if (valid && Hwrite)
		      NEXT_STATE=ST_WWAIT;
		     else
		      NEXT_STATE=ST_READ;
		   end

	ST_WENABLE:begin
		     if (~valid)
		      NEXT_STATE=ST_IDLE;
		     else if (valid && Hwrite)
		      NEXT_STATE=ST_WWAIT;
		     else
		      NEXT_STATE=ST_READ;
		   end

	ST_WENABLEP:begin
		      if (~valid && Hwritereg)
		       NEXT_STATE=ST_WRITE;
		      else if (valid && Hwritereg)
		       NEXT_STATE=ST_WRITEP;
		      else
		       NEXT_STATE=ST_READ;
		    end

	default: begin
		   NEXT_STATE=ST_IDLE;
		  end
  endcase
 end


////////////////////////////////////////////////////////OUTPUT LOGIC:COMBINATIONAL

reg Penable_temp,Hreadyout_temp,Pwrite_temp;
reg [2:0] Pselx_temp;
reg [31:0] Paddr_temp, Pwdata_temp;

always @(*)
 begin:OUTPUT_COMBINATIONAL_LOGIC
   case(PRESENT_STATE)
    
	ST_IDLE: begin
			  if (valid && ~Hwrite) 
			   begin:IDLE_TO_READ
			        Paddr_temp=Haddr;
				Pwrite_temp=Hwrite;
				Pselx_temp=tempselx;
				Penable_temp=0;
				Hreadyout_temp=0;
			   end
			  
			  else if (valid && Hwrite)
			   begin:IDLE_TO_WWAIT
			        Pselx_temp=0;
				Penable_temp=0;
				Hreadyout_temp=1;			   
			   end
			   
			  else
                            begin:IDLE_TO_IDLE
			        Pselx_temp=0;
				Penable_temp=0;
				Hreadyout_temp=1;	
			   end
		     end    

	ST_WWAIT:begin
	          if (~valid) 
			   begin:WAIT_TO_WRITE
			    Paddr_temp=Haddr1;
				Pwrite_temp=1;
				Pselx_temp=tempselx;
				Penable_temp=0;
				Pwdata_temp=Hwdata;
				Hreadyout_temp=0;
			   end
			  
			  else 
			   begin:WAIT_TO_WRITEP
			    Paddr_temp=Haddr1;
				Pwrite_temp=1;
				Pselx_temp=tempselx;
				Pwdata_temp=Hwdata;
				Penable_temp=0;
				Hreadyout_temp=0;		   
			   end
			   
		     end  

	ST_READ: begin:READ_TO_RENABLE
			  Penable_temp=1;
			  Hreadyout_temp=1;
		     end

	ST_WRITE:begin
              if (~valid) 
			   begin:WRITE_TO_WENABLE
				Penable_temp=1;
				Hreadyout_temp=1;
			   end
			  
			  else 
			   begin:WRITE_TO_WENABLEP ///DOUBT
				Penable_temp=1;
				Hreadyout_temp=1;		   
			   end
		     end

	ST_WRITEP:begin:WRITEP_TO_WENABLEP
               Penable_temp=1;
			   Hreadyout_temp=1;
		      end

	ST_RENABLE:begin
	            if (valid && ~Hwrite) 
				 begin:RENABLE_TO_READ
					Paddr_temp=Haddr;
					Pwrite_temp=Hwrite;
					Pselx_temp=tempselx;
					Penable_temp=0;
					Hreadyout_temp=0;
				 end
			  
			  else if (valid && Hwrite)
			    begin:RENABLE_TO_WWAIT
			     Pselx_temp=0;
				 Penable_temp=0;
				 Hreadyout_temp=1;			   
			    end
			   
			  else
                begin:RENABLE_TO_IDLE
			     Pselx_temp=0;
				 Penable_temp=0;
				 Hreadyout_temp=1;	
			    end

		       end

	ST_WENABLEP:begin
                 if (~valid && Hwritereg) 
			      begin:WENABLEP_TO_WRITEP
			       Paddr_temp=Haddr2;
				   Pwrite_temp=Hwrite;
				   Pselx_temp=tempselx;
				   Penable_temp=0;
				   Pwdata_temp=Hwdata;
				   Hreadyout_temp=0;
				  end

			  
			    else 
			     begin:WENABLEP_TO_WRITE_OR_READ /////DOUBT
			      Paddr_temp=Haddr2;
				  Pwrite_temp=Hwrite;
				  Pselx_temp=tempselx;
				  Pwdata_temp=Hwdata;
				  Penable_temp=0;
				  Hreadyout_temp=0;		   
			     end
		        end

	ST_WENABLE :begin
	             if (~valid && Hwritereg) 
			      begin:WENABLE_TO_IDLE
				   Pselx_temp=0;
				   Penable_temp=0;
				   Hreadyout_temp=0;
				  end

			  
			    else 
			     begin:WENABLE_TO_WAIT_OR_READ /////DOUBT
				  Pselx_temp=0;
				  Penable_temp=0;
				  Hreadyout_temp=0;		   
			     end

		        end

 endcase
end


////////////////////////////////////////////////////////OUTPUT LOGIC:SEQUENTIAL

always @(posedge Hclk)
 begin
  
  if (~Hresetn)
   begin
    Paddr<=0;
	Pwrite<=0;
	Pselx<=0;
	Pwdata<=0;
	Penable<=0;
	Hreadyout<=0;
   end
  
  else
   begin
        Paddr<=Paddr_temp;
	Pwrite<=Pwrite_temp;
	Pselx<=Pselx_temp;
	Pwdata<=Pwdata_temp;
	Penable<=Penable_temp;
	Hreadyout<=Hreadyout_temp;
   end
 end
 ///////////////////////


endmodule"	"module APB_FSM_Controller_sva(input wire Hclk,
                              input wire Hresetn,
                              input wire valid,
                              input wire Hwrite,
                              input wire [31:0] Hwdata,
                              input wire [31:0] Haddr,
                              input wire [31:0] Haddr1,
                              input wire [31:0] Haddr2,
                              input wire [31:0] Hwdata1,
                              input wire [31:0] Hwdata2,
                              input wire [31:0] Prdata,
                              input wire [2:0] tempselx,
                              input wire Hwritereg,
                              input wire Pwrite,
                              input wire Penable,
                              input wire [2:0] Pselx,
                              input wire [31:0] Paddr,
                              input wire [31:0] Pwdata,
                              input wire Hreadyout,
                              input wire [2:0] PRESENT_STATE,
                              input wire [2:0] NEXT_STATE);
//PARAMETERS

parameter ST_IDLE=3'b000;
parameter ST_WWAIT=3'b001;
parameter ST_READ= 3'b010;
parameter ST_WRITE=3'b011;
parameter ST_WRITEP=3'b100;
parameter ST_RENABLE=3'b101;
parameter ST_WENABLE=3'b110;
parameter ST_WENABLEP=3'b111;

    // Assertions, assumptions and cover properties go here

// Property to verify that PRESENT_STATE becomes NEXT_STATE one cycle later
property p_state_transition;
    @(posedge Hclk) disable iff (!Hresetn) 1 |-> ##2 PRESENT_STATE == $past(NEXT_STATE);
endproperty
assert_state_transition: assert property (p_state_transition);



// Transition from ST_IDLE
property p_IDLE_to_WWAIT;
    @(posedge Hclk) disable iff (!Hresetn) 
    (PRESENT_STATE == ST_IDLE && valid && Hwrite) |-> (NEXT_STATE == ST_WWAIT);
endproperty
assert_IDLE_to_WWAIT: assert property (p_IDLE_to_WWAIT);

property p_IDLE_to_READ;
    @(posedge Hclk) disable iff (!Hresetn) PRESENT_STATE == ST_IDLE && valid && !Hwrite |-> NEXT_STATE == ST_READ;
endproperty
assert_IDLE_to_READ: assert property (p_IDLE_to_READ);

property p_IDLE_to_IDLE;
    @(posedge Hclk) disable iff (!Hresetn) PRESENT_STATE == ST_IDLE && !valid |-> NEXT_STATE == ST_IDLE;
endproperty
assert_IDLE_to_IDL: assert property (p_IDLE_to_IDLE);
///////////////////////////

// Transition from ST_WWAIT
property p_WWAIT_to_WRITE;
    @(posedge Hclk) disable iff (!Hresetn) PRESENT_STATE == ST_WWAIT && !valid |-> NEXT_STATE == ST_WRITE;
endproperty
assert_WWAIT_to_WRITE: assert property (p_WWAIT_to_WRITE);

property p_WWAIT_to_WRITEP;
    @(posedge Hclk) disable iff (!Hresetn) PRESENT_STATE == ST_WWAIT && valid |-> NEXT_STATE == ST_WRITEP;
endproperty
assert_WWAIT_to_WRITEP: assert property (p_WWAIT_to_WRITEP);
///////////////////////////

// Transition from ST_READ
property p_READ_to_RENABLE;
    @(posedge Hclk) disable iff (!Hresetn) PRESENT_STATE == ST_READ |-> NEXT_STATE == ST_RENABLE;
endproperty
assert_READ_to_RENABLE: assert property (p_READ_to_RENABLE);
///////////////////////////

// Transition from ST_WRITE
property p_WRITE_to_WENABLE;
    @(posedge Hclk) disable iff (!Hresetn) PRESENT_STATE == ST_WRITE && !valid |-> NEXT_STATE == ST_WENABLE;
endproperty
assert_WRITE_to_WENABLE: assert property (p_WRITE_to_WENABLE);

property p_WRITE_to_WENABLEP;
    @(posedge Hclk) disable iff (!Hresetn) PRESENT_STATE == ST_WRITE && valid |-> NEXT_STATE == ST_WENABLEP;
endproperty
assert_WRITE_to_WENABLEP: assert property (p_WRITE_to_WENABLEP);
///////////////////////////

// Transition from ST_WRITEP
property p_WRITEP_to_WENABLEP;
    @(posedge Hclk) disable iff (!Hresetn) PRESENT_STATE == ST_WRITEP |-> NEXT_STATE == ST_WENABLEP;
endproperty
assert_WRITEP_to_WENABLEP: assert property (p_WRITEP_to_WENABLEP);
///////////////////////////

// Transitions from ST_RENABLE
property p_RENABLE_to_IDLE;
    @(posedge Hclk) disable iff (!Hresetn) PRESENT_STATE == ST_RENABLE && !valid |-> NEXT_STATE == ST_IDLE;
endproperty
assert_RENABLE_to_IDLE: assert property (p_RENABLE_to_IDLE);

property p_RENABLE_to_WWAIT;
    @(posedge Hclk) disable iff (!Hresetn) PRESENT_STATE == ST_RENABLE && valid && Hwrite |-> NEXT_STATE == ST_WWAIT;
endproperty
assert_RENABLE_to_WWAIT: assert property (p_RENABLE_to_WWAIT);

property p_RENABLE_to_READ;
    @(posedge Hclk) disable iff (!Hresetn) PRESENT_STATE == ST_RENABLE && valid && !Hwrite |-> NEXT_STATE == ST_READ;
endproperty
assert_RENABLE_to_READ: assert property (p_RENABLE_to_READ);
///////////////////////////

// Transitions from ST_WENABLE
property p_WENABLE_to_IDLE;
    @(posedge Hclk) disable iff (!Hresetn) PRESENT_STATE == ST_WENABLE && !valid |-> NEXT_STATE == ST_IDLE;
endproperty
assert_WENABLE_to_IDLE: assert property (p_WENABLE_to_IDLE);

property p_WENABLE_to_WWAIT;
    @(posedge Hclk) disable iff (!Hresetn) PRESENT_STATE == ST_WENABLE && valid && Hwrite |-> NEXT_STATE == ST_WWAIT;
endproperty
assert_WENABLE_to_WWAIT: assert property (p_WENABLE_to_WWAIT);

property p_WENABLE_to_READ;
    @(posedge Hclk) disable iff (!Hresetn) PRESENT_STATE == ST_WENABLE && valid && !Hwrite |-> NEXT_STATE == ST_READ;
endproperty
assert_WENABLE_to_READ: assert property (p_WENABLE_to_READ);
///////////////////////////

// Transitions from ST_WENABLEP
property p_WENABLEP_to_WRITE;
    @(posedge Hclk) disable iff (!Hresetn) PRESENT_STATE == ST_WENABLEP && !valid && Hwritereg |-> NEXT_STATE == ST_WRITE;
endproperty
assert_WENABLEP_to_WRITE: assert property (p_WENABLEP_to_WRITE);

property p_WENABLEP_to_WRITEP;
    @(posedge Hclk) disable iff (!Hresetn) PRESENT_STATE == ST_WENABLEP && valid && Hwritereg |-> NEXT_STATE == ST_WRITEP;
endproperty
assert_WENABLEP_to_WRITEP: assert property (p_WENABLEP_to_WRITEP);

property p_WENABLEP_to_READ;
    @(posedge Hclk) disable iff (!Hresetn) PRESENT_STATE == ST_WENABLEP && !Hwritereg |-> NEXT_STATE == ST_READ;
endproperty
assert_WENABLEP_to_READ: assert property (p_WENABLEP_to_READ);


endmodule


"	https://github.com/Ghonimo/Formal-Verification-of-an-AHB2APB-Bridge/tree/main	"Assertion 1-2:
The two asserions see inside the always block. They are used to check to make sure that when clk is at posedge, there is never a write while the FIFO is full, or a read while the FIFO is empty. 
Assertion 3:
This assertion is used to check when clk is at posedge, the DUT.valid_wr and full signal can not be 1 at the same time. Its purpose is to avoid such a case: there is a write and the FIFO is full.
Assertion 4:
This assertion is used to check when clk is at posedge, the DUT.valid_rd and empty signal can not be 1 at the same time. Its purpose is to avoid such a case: there is a read and the FIFO is empty.
Assertion 5:
This assertion is to check if DUT.valid_wr is high, the full must be 0. Its purpose is to ensure when there is a write, the FIFO can not be full.
Assertion 6:
This assertion is to check if DUT.valid_rd is high, the empty must be 0. Its purpose is to ensure when there is a read, the FIFO can not be empty."	"""module fifo_tb1;

   localparam WIDTH = 8;
   localparam DEPTH = 16;
   
   logic             clk;
   logic             rst;
   logic             full;
   logic             wr_en;
   logic [WIDTH-1:0] wr_data;
   logic             empty;
   logic             rd_en; 
   logic [WIDTH-1:0] rd_data;

   fifo #(.WIDTH(WIDTH), .DEPTH(DEPTH)) DUT (.*);
   
   initial begin : generate_clock
      clk = 1'b0;
      while(1) #5 clk = ~clk;
   end

   initial begin
      rst <= 1'b1;
      rd_en <= 1'b0;
      wr_en <= 1'b0;
      wr_data <= '0;      
      for (int i=0; i < 5; i++) @(posedge clk);
      @(negedge clk);
      rst <= 1'b0;

      for (int i=0; i < 10000; i++) begin
         wr_data <= $random;
         wr_en <= $random;
         rd_en <= $random;
         @(posedge clk);         
      end

      disable generate_clock;
      $display(""""Tests Completed."""");      
   end // initial begin
   
endmodule"""
"parameter N_MASTERS = 3;
typedef bit [N_MASTERS-1:0] arb_vector;
parameter arb_vector NO_REQUEST = '{default: '0};
parameter arb_vector NO_GRANT = '{default: '0};

module busarbiter(input clk, reset, bus_ack, input arb_vector bus_req, output arb_vector bus_grant);

    enum {READY, BUSY} state_s;
    arb_vector prio_req;
    reg found;
    always @(bus_req) begin: prio
        arb_vector prio_req_v;
	found = 0;
        for (int i=0; i < N_MASTERS; i++) begin
            if(~found & (bus_req[i]==1'b1)) begin
                prio_req_v[i] = 1'b1;
                found = 1;
            end
            else begin
                prio_req_v[i] = 1'b0;
            end
        end
        prio_req <= prio_req_v;
    end

    always @(posedge clk or posedge reset) begin: ctrl
        if(reset) begin //always block triggered by reset
            state_s <= READY;
            bus_grant <= NO_GRANT;
        end
        else begin //always block triggered by clk
            case (state_s)
                READY: begin
                    if (bus_req == NO_REQUEST) begin
			state_s <= READY;
                    end
                    else begin
                        state_s <= BUSY;
                    end 
                    bus_grant <= prio_req;
                end

                BUSY: begin
                    if (bus_ack) begin
                        if (bus_req == NO_REQUEST) begin
                            state_s <= READY;
                        end
                        else begin
                            state_s <= BUSY;
                        end 
		        bus_grant <= prio_req;
		    end
                end
            endcase 
        end
    end
endmodule"	"// @lang=sva @ts=2

module busarbitersuit(clk, reset, bus_req, bus_grant, bus_ack); 

input logic clk;
input logic reset;

input logic [2:0] bus_req;
input logic [2:0] bus_grant;
input logic bus_ack;

parameter READY = 1'b0;
parameter BUSY  = 1'b1;

parameter NO_REQUEST = 3'b000; 
parameter NO_GRANT = 3'b000; 


// TIDAL properties must be enclosed within begin_tda and end_tda macros

// your definitions...
property p_reset;
          reset |-> bus_grant == NO_GRANT;
endproperty

property p_at_most_one_grant;
          bus_grant[0]+bus_grant[1]+bus_grant[2]<2;
endproperty

property p_at_most_one_grant_1;
          bus_grant[0] |-> (!bus_grant[1] && !bus_grant[2]);
          //bus_grant[0] |-> (!bus_grant[1] && !bus_grant[2]) || bus_grant[1] |-> (!bus_grant[0] && !bus_grant[2])  || bus_grant[2] |-> (!bus_grant[1] && !bus_grant[0]);
endproperty
property p_at_most_one_grant_2;
          bus_grant[1] |-> (!bus_grant[0] && !bus_grant[2]);
endproperty
property p_at_most_one_grant_3;
          bus_grant[2] |-> (!bus_grant[1] && !bus_grant[0]);
endproperty
property p_grant_stable;
          //bus_grant != NO_GRANT |=> ##[1:$] (bus_grant != NO_GRANT && !bus_ack);
          bus_grant != NO_GRANT && bus_ack != 1 |=> $stable(bus_grant) ;
endproperty
property p_arbitration_master0;
          (bus_req[0] && bus_grant== NO_GRANT)|| (bus_ack && bus_req[0]) |=>  (bus_grant[0] && !bus_grant[1] && !bus_grant[2]);
endproperty

property p_arbitration_master1;
          (bus_req[1] && !bus_req[0] && bus_grant== NO_GRANT) || (bus_ack && bus_req[1]&& !bus_req[0])|=>  (!bus_grant[0] && bus_grant[1] && !bus_grant[2]);
endproperty

property p_arbitration_master2;
          (bus_req[2] && !bus_req[1] && !bus_req[0] && bus_grant== NO_GRANT) || (bus_ack && bus_req[2]&& !bus_req[0] &&  !bus_req[1]) |=>  (!bus_grant[0] && !bus_grant[1] && bus_grant[2]);
endproperty

property p_grant_master1;
          //bus_grant[1] implies ($past(bus_req[1]) && !$past(bus_req[0]));
          $rose(bus_grant[1]) |-> ($past(bus_req[1]) && !$past(bus_req[0]));
endproperty
property p_grant_master2;
          //bus_grant[2] implies ($past(bus_req[2]) && !$past(bus_req[1]) && !$past(bus_req[0]));
          $rose(bus_grant[2]) |-> ($past(bus_req[2]) && !$past(bus_req[1]) && !$past(bus_req[0]));
endproperty

// assertions
// a_reset: assert property(@(posedge clk) p_reset);
a_atmostone: assert property(@(posedge clk) disable iff(reset) p_at_most_one_grant);
a_atmostone_1: assert property(@(posedge clk) disable iff(reset) p_at_most_one_grant_1);
a_atmostone_2: assert property(@(posedge clk) disable iff(reset) p_at_most_one_grant_2);
a_atmostone_3: assert property(@(posedge clk) disable iff(reset) p_at_most_one_grant_3);
a_grantstable: assert property(@(posedge clk) disable iff(reset) p_grant_stable);
a_arbmaster0: assert property(@(posedge clk) disable iff(reset) p_arbitration_master0);
a_arbmaster1: assert property(@(posedge clk) disable iff(reset) p_arbitration_master1);
a_arbmaster2: assert property(@(posedge clk) disable iff(reset) p_arbitration_master2);
a_grantmaster1: assert property(@(posedge clk) disable iff(reset) p_grant_master1);
a_grantmaster2: assert property(@(posedge clk) disable iff(reset) p_grant_master2);
endmodule"	https://github.com/ahmedsherif99/Bus-Arbiter-Systemverilog-module-with-Formal-Verification-SVA-on-OneSpin/tree/main	"Assertion 1-2:
To check certain FIFO properties, the two asserions see inside of the FIFO module. They are used to check to make sure that when clk is at posedge, there is never a write while the FIFO is full, or a read while the FIFO is empty. 
Assertion 3:
It first creates a property where if there is a valid write, we save the wr_data into the local data variable data. The valid write then implies that at some indefinite point in the future (i.e. ##[1:$]) there will be a valid read (i.e., rd_en is 1 and the FIFO is not empty) from the FIFO that has matching data .Then, this assertion checks whether the property can be satisfied and if it is satisfied, it will print a custom message containing the current time and rd_data."	"module fifo_tb2;

   localparam WIDTH = 8;
   localparam DEPTH = 16;
   
   logic             clk;
   logic             rst;
   logic             full;
   logic             wr_en;
   logic [WIDTH-1:0] wr_data;
   logic             empty; 
   logic             rd_en; 
   logic [WIDTH-1:0] rd_data;

   fifo #(.WIDTH(WIDTH), .DEPTH(DEPTH)) DUT (.*);
   
   initial begin : generate_clock
      clk = 1'b0;
      while(1) #5 clk = ~clk;
   end

   initial begin
      $timeformat(-9, 0, "" ns"");
      rst <= 1'b1;
      rd_en <= 1'b0;
      wr_en <= 1'b0;
      wr_data <= '0;      
      for (int i=0; i < 5; i++) @(posedge clk);
      @(negedge clk);
      rst <= 1'b0;

      for (int i=0; i < 10000; i++) begin
         wr_data <= $random;
         wr_en <= $random;
         rd_en <= $random;
         @(posedge clk);        
      end

      disable generate_clock;
      $display(""Tests Completed."");      
   end  
   
endmodule"
"module simple_router #(
	parameter DATA_WIDTH = 32
) (
  input  rst,
  input  clk,
  input  [DATA_WIDTH-1:0] din,
  input  din_en,
  input  [1:0] addr,
  output logic [DATA_WIDTH-1:0] dout0,
  output logic [DATA_WIDTH-1:0] dout1,
  output logic [DATA_WIDTH-1:0] dout2,
  output logic [DATA_WIDTH-1:0] dout3
);

// data should be forced to 0 when not driven 
assign dout0 = {DATA_WIDTH{din_en & ( addr == 2'd0 )}} & din; 
assign dout1 = {DATA_WIDTH{din_en & ( addr == 2'd1 )}} & din; 
assign dout2 = {DATA_WIDTH{din_en & ( addr == 2'd2 )}} & din; 
assign dout3 = {DATA_WIDTH{din_en & ( addr == 2'd3 )}} & din; 


endmodule"	"module simple_router_sva #(
	parameter DATA_WIDTH = 32
) (
  input  rst,
  input  clk,
  input  [DATA_WIDTH-1:0] din,
  input  din_en,
  input  [1:0] addr,
  input logic [DATA_WIDTH-1:0] dout0,
  input logic [DATA_WIDTH-1:0] dout1,
  input logic [DATA_WIDTH-1:0] dout2,
  input logic [DATA_WIDTH-1:0] dout3
);

dout_zero_din_en_false: assert property (din_en | ((dout0 == 0) & (dout1 == 0) & (dout2 == 0) & (dout3 == 0)));
dout_addr0_match: assert property ((~(din_en & (addr == 2'd0))) | ((dout0 == din) & (dout1 == 0) & (dout2 == 0) & (dout3 == 0)));
dout_addr1_match: assert property ((~(din_en & (addr == 2'd1))) | ((dout1 == din) & (dout0 == 0) & (dout2 == 0) & (dout3 == 0)));
dout_addr2_match: assert property ((~(din_en & (addr == 2'd2))) | ((dout2 == din) & (dout0 == 0) & (dout1 == 0) & (dout3 == 0)));
dout_addr3_match: assert property ((~(din_en & (addr == 2'd3))) | ((dout3 == din) & (dout0 == 0) & (dout1 == 0) & (dout2 == 0)));

endmodule"	https://github.com/Essenceia/formal_experiements/blob/master/1_Simple_Router/router.v	"Assertion 1-2:
To check certain FIFO properties, the two asserions see inside of the FIFO module. They are used to check to make sure that when clk is at posedge, there is never a write while the FIFO is full, or a read while the FIFO is empty. 
Assertion 3:
For this assertion, we assign each write a unique tag, and then maintain a ""serving"" counter in function inc_tag and inc_serving so we can determine which read applies to which write. This assertion is to check: on each valid write, we save the current tag into a local variable,  update the global tag counter, and save the write data, then at some point in the future there will be a valid read with a wr_tag that matches the current serving ID. We only care about the first matching instance, so we use the first_match function. Finally, when there is a valid read with the matching tag, on the next cycle (i.e. ##1) the read data should match the original write data."	"module fifo_tb3;

   localparam WIDTH = 8;
   localparam DEPTH = 16;
   
   logic             clk;
   logic             rst;
   logic             full;
   logic             wr_en;
   logic [WIDTH-1:0] wr_data;
   logic             empty; 
   logic             rd_en; 
   logic [WIDTH-1:0] rd_data;

   fifo #(.WIDTH(WIDTH), .DEPTH(DEPTH)) DUT (.*);
   
   initial begin : generate_clock
      clk = 1'b0;
      while(1) #5 clk = ~clk;
   end

   initial begin
      $timeformat(-9, 0, "" ns"");
      rst <= 1'b1;
      rd_en <= 1'b0;
      wr_en <= 1'b0;
      wr_data <= '0;      
      for (int i=0; i < 5; i++) @(posedge clk);
      @(negedge clk);
      rst <= 1'b0;

      for (int i=0; i < 10000; i++) begin
         wr_data <= $random;
         wr_en <= $random;
         rd_en <= $random;
         @(posedge clk);         
      end

      disable generate_clock;
      $display(""Tests Completed."");
   end         
endmodule"
"module second_largest #(parameter
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
endmodule"	"module second_largest_sva #(parameter
  DATA_WIDTH = 32
) (
  input clk,
  input resetn,
  input [DATA_WIDTH-1:0] din,
  input logic [DATA_WIDTH-1:0] dout,
  input logic [DATA_WIDTH-1:0] max_q,
  input logic [DATA_WIDTH-1:0] max2_q
);

default clocking cb @(posedge clk);
endclocking
default disable iff (~resetn);

sva_max_greater_max2: assert property ( (max_q == 0) | ( max_q > max2_q )); 

endmodule
"	https://github.com/Essenceia/formal_experiements/blob/master/2_Second_Largest/model.v	"Assertion 1-2:
To check certain FIFO properties, the two asserions see inside of the FIFO module. They are used to check to make sure that when clk is at posedge, there is never a write while the FIFO is full, or a read while the FIFO is empty. 
Assertion 3:
The always_ff block imitates the functionality of the FIFO with a queue and the correct_rd_data is set as the first element of data stored in this FIFO. Then, this assertion is to check if the read data rd_data should equal the first element correct_rd_data."	"module fifo_tb4;

   localparam WIDTH = 8;
   localparam DEPTH = 16;
   
   logic             clk;
   logic             rst;
   logic             full;
   logic             wr_en;
   logic [WIDTH-1:0] wr_data;
   logic             empty; 
   logic             rd_en; 
   logic [WIDTH-1:0] rd_data;

   fifo #(.WIDTH(WIDTH), .DEPTH(DEPTH)) DUT (.*);
   
   initial begin : generate_clock
      clk = 1'b0;
      while(1) #5 clk = ~clk;
   end

   initial begin
      $timeformat(-9, 0, "" ns"");
      rst <= 1'b1;
      rd_en <= 1'b0;
      wr_en <= 1'b0;
      wr_data <= '0;      
      for (int i=0; i < 5; i++) @(posedge clk);
      @(negedge clk);
      rst <= 1'b0;

      for (int i=0; i < 10000; i++) begin
         wr_data <= $random;
         wr_en <= $random;
         rd_en <= $random;
         @(posedge clk);         
      end

      disable generate_clock;
      $display(""Tests Completed."");
   end
            
endmodule"
"module Gray_Code_Counter #(parameter
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

endmodule"	"module Gray_Code_Counter_sva #(parameter
  DATA_WIDTH = 4
) (
  input clk,
  input resetn,
  input logic [DATA_WIDTH-1:0] out,
  input unused_bin_inc,
  input logic [DATA_WIDTH-1:0] gray_q,	
  input logic [DATA_WIDTH-1:0] gray_next
);

default clocking cb @(posedge clk);
endclocking
default disable iff (~resetn);

sva_gray_1_bit_diff : assert property ( unused_bin_inc |  $onehot( gray_next ^ gray_q ) );


endmodule"	https://github.com/Essenceia/formal_experiements/blob/master/4_Gray_Code_Counter/model.v	"Assertion 1:
This assertion is an ""immediate"" assertion because it occurs within a function (or always block). It is used to check whether actual equals correct."	"module mux2x1_tb;

   logic in0, in1, sel;
   
   logic out_assign, out_if, out_if2, out_case;   

   localparam period = 20;
   
   mux2x1_assign DUT_ASSIGN (.out(out_assign), .*);
   mux2x1_if DUT_IF (.out(out_if), .*);
   mux2x1_if2 DUT_IF2 (.out(out_if2), .*);
   mux2x1_case DUT_CASE (.out(out_case), .*);

endmodule"
"module reversing_bits #(
	parameter DATA_WIDTH=3
) 
(
  input clk,
  input rst,
  input  [DATA_WIDTH-1:0]       din,
  output logic [DATA_WIDTH-1:0] dout
);

genvar i;
generate;
	for (i=0; i<DATA_WIDTH; i++) begin
		assign dout[i] = din[DATA_WIDTH-i-1];
	end
endgenerate

endmodule"	"module reversing_bits_sva #(
	parameter DATA_WIDTH=3
) 
(
  input  [DATA_WIDTH-1:0]       din,
  input logic [DATA_WIDTH-1:0] dout,
  input clk,
  input rst
);

default clocking cb @(posedge clk);
endclocking
default disable iff (~rst);

sva_rev : assert property ( dout[0]  == din[DATA_WIDTH-1]);

endmodule"	https://github.com/Essenceia/formal_experiements/blob/master/5_Reversing_Bits/model.v	"Assertion 1:
This assertion is evaluated at the posedge of clk to check whether the output out equals the input in in the last cycle when rst is 0. Its purpose is to validate the output under the case of rst=0.
Assertion 2:
This assertion is evaluated at the posedge of clk to check whether the output out equals the input in in the last cycle if rst is 0. Its purpose is to validate the output under the case of rst=0.
Assertion 3:
This assertion is evaluated at the posedge of clk to check whether the output out equals 0 if rst is 1. Its purpose is to validate the output under the case of rst=1.
Assertion 4:
This assertion is an immediate assertion in an always blocks. When rst equals 1, this assertion will be used to check whether out equals 0."	"module register_tb1;

   localparam NUM_TESTS = 10000;
   localparam WIDTH = 8;
   logic clk, rst, en;
   logic [WIDTH-1:0] in, out;
   
   register #(.WIDTH(WIDTH)) DUT (.en(1'b1), .*);

   initial begin : generate_clock
      clk = 1'b0;
      while(1) #5 clk = ~clk;      
   end

   initial begin : drive_inputs
      $timeformat(-9, 0, "" ns"");         

      rst <= 1'b1;
      in <= 1'b0;      
      en <= 1'b1;

      for (int i=0; i < 5; i++)
        @(posedge clk);

      @(negedge clk);
      rst <= 1'b0;

      for (int i=0; i < NUM_TESTS; i++) begin    
         in <= $random;
         @(posedge clk);
      end

      disable generate_clock;
      $display(""Tests completed."");
   end 

endmodule"
"module Edge_Detector (
	input  clk,
	input  resetn,
	input  din,
	output dout
);

// trigger a pulse 1 cycle after din goes up
reg  edge_seen_q;
wire edge_seen_next;
reg  pulse_q;
wire pulse_next;
assign edge_seen_next = ( din & ~edge_seen_q) 
					  | ( din & edge_seen_q );
assign pulse_next      = din & ~edge_seen_q;
 
always @(posedge clk)
begin
	if ( ~resetn ) begin
		edge_seen_q <= 1'b0;
		pulse_q     <= 1'b0;
	end else begin
		edge_seen_q <= edge_seen_next;
		pulse_q     <= pulse_next;
	end
end

assign dout = pulse_q;

endmodule"	"module Edge_Detector_sva (
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

endmodule"	https://github.com/Essenceia/formal_experiements/blob/master/6_Edge_Detector/model.v	"Assertion 1:
This assertion is evaluated at the posedge of clk to check only when rst is 0 whether the output out equals the input in in the last cycle if  the enable signal en is 1. Its purpose is to validate the output under the case of rst=0 and en=1.
Assertion 2:
This assertion is evaluated at the posedge of clk to check only when rst is 0 whether the output out equals the output out in the last cycle if  the enable signal en is 0. Its purpose is to validate the output under the case of rst=0 and en=0.
Assertion 3:
This assertion is evaluated at the posedge of clk to check only when rst is 0 whether the output out does not change its value if  the enable signal en is 0. Its purpose is to validate the output under the case of rst=0 and en=0.
Assertion 4:
This assertion is an immediate assertion in the always block. When rst is 1, the assertion is used to check the output out equals 0."	"module register_tb2;

   localparam NUM_TESTS = 10000;
   localparam WIDTH = 8;
   logic clk, rst, en;
   logic [WIDTH-1:0] in, out;

   logic             output_check_en = 1'b0, first_en = 1'b0;
      
   register #(.WIDTH(WIDTH)) DUT (.*);

   initial begin : generate_clock
      clk = 1'b0;
      while(1) #5 clk = ~clk;      
   end

   initial begin : drive_inputs
      $timeformat(-9, 0, "" ns"");         

      rst <= 1'b1;
      in <= 1'b0;      
      en <= 1'b0;
      
      for (int i=0; i < 5; i++)
        @(posedge clk);

      rst <= 1'b0;

      for (int i=0; i < NUM_TESTS; i++) begin    
         in <= $random;
         en <= $random;
         @(posedge clk);

         if (first_en) output_check_en = 1'b1;
         if (en) first_en = 1'b1;         
      end

      disable generate_clock;
      $display(""Tests completed."");
   end 
endmodule"
"module Parallel_In_Serial_Out_Shift_Reg #(
	parameter DATA_WIDTH = 16
) 
(
	input clk,
	input resetn,
	input [DATA_WIDTH-1:0] din,
	input                  din_en,
	output logic           dout
);

reg  [DATA_WIDTH-1:0] data_q;
wire [DATA_WIDTH-1:0] data_next;

assign data_next = din_en ? din : data_q >> 1;

always @(posedge clk)
begin
	if( ~resetn) begin
		data_q <= '0;
	end else begin
		data_q <= data_next;
	end
end

assign dout = data_q[0]; 


endmodule"	"module Parallel_In_Serial_Out_Shift_Reg_sva #(
	parameter DATA_WIDTH = 16
) 
(
	input clk,
	input resetn,
	input [DATA_WIDTH-1:0] din,
	input                  din_en,
	input logic           dout
);

default clocking cb @(posedge clk);
endclocking
default disable iff (~resetn);

reg  v_f_q;
wire v_f_next;
reg  [DATA_WIDTH-1:0] din_f_q;
wire [DATA_WIDTH-1:0] din_f_next;
assign din_f_next = { 1'b0 , din_f_q[7:1] };
assign v_f_next   = resetn & din_en;

always @(posedge clk)
begin
	din_f_q <= ~resetn ? {DATA_WIDTH{1'bx}} : 
					din_en ? din : din_f_next; 
	v_f_q   <= v_f_next;
end

sva_shift_reg : assert property ( ~v_f_q | ( v_f_q & din_f_q[0] == dout )); 

endmodule"	https://github.com/Essenceia/formal_experiements/blob/master/7_Parallel_In_Serial_Out_Shift_Reg/model.v	"Assertion 1:
This assertion checks only when rst is 0 that once the pipeline reaches its defined latency (DUT.LATENCY), the output (out) is correct based on the input values from DUT.LATENCY cycles ago.
Assertion 2:
This assertion checks only when rst is 0 that valid_out remains low until the pipeline latency has been reached.
Assertion 3:
This assertion checks only when rst is 0 that valid_out matches valid_in from DUT.LATENCY cycles ago.
Assertion 4:
This assertion checks only when rst is 0 that out remains low until the pipeline latency has been reached.
"	"module simple_pipeline_tb;

   localparam int NUM_TESTS = 1000;
   localparam int WIDTH = 8;
      
   logic          clk, rst, valid_in, valid_out;
   logic [WIDTH-1:0] in[8];
   logic [WIDTH-1:0] out;
    
   simple_pipeline #(.WIDTH(WIDTH)) DUT (.*);

   initial begin : generate_clock
      clk = 1'b0;
      while (1) #5 clk = ~clk;      
   end

   initial begin
      $timeformat(-9, 0, "" ns"");

      rst <= 1'b1;
      valid_in <= 1'b0;
      for (int i=0; i < 8; i++) in[i] <= '0;
      for (int i=0; i < 5; i++) @(posedge clk);
      @(negedge clk);
      rst <= 1'b0;
      @(posedge clk);

      for (int i=0; i < NUM_TESTS; i++) begin
         for (int i=0; i < 8; i++) in[i] = $random;
         valid_in <= $random;
         @(posedge clk);
      end

      $display(""Tests completed."");      
      disable generate_clock;
   end
      
endmodule"
"module Gray_To_Binary #(
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

endmodule"	"module Gray_To_Binary_sva #(
	parameter DATA_WIDTH = 3
) 
(
	input [DATA_WIDTH-1:0]        gray,
	input logic [DATA_WIDTH-1:0] bin,
          input clk,
          input rst
);

default clocking cb @(posedge clk);
endclocking
default disable iff (~rst);

wire [DATA_WIDTH-1:0] gray_f;

// In order to construct our gray code we converter the binary
// gray = bin ^ ( bin >> 1 ) 

assign gray_f = bin ^ ( bin >> 1 );

sva_inv_bin : assert property ( gray_f == gray );

endmodule"	https://github.com/Essenceia/formal_experiements/tree/master/11_Gray_To_Binary	"Assertion 1:
This assertion is to check only when rst is 0 that once the pipeline reaches its defined latency (DUT.LATENCY), the output (out) matches the expected value produced by the model function based on the values of in from DUT.LATENCY cycles ago when en was high.
Assertion 2:
This assertion is to check only when rst is 0 that valid_out remains low until DUT.LATENCY clocks has gone, meaning no valid output is produced prematurely.
Assertion 3:
This assertion is to check only when rst is 0 that valid_out matches valid_in from DUT.LATENCY cycles ago, taking into account when the pipeline was enabled (en was high).
Assertion 4:
This assertion is to check only when rst is 0 that out remains zero until DUT.LATENCY clocks has gone.

"	"module simple_pipeline_with_en_tb;

   localparam int NUM_TESTS = 10000;
   localparam int WIDTH = 8;
      
   logic          clk, rst, en, valid_in, valid_out;
   logic [WIDTH-1:0] in[8];
   logic [WIDTH-1:0] out;
    
   simple_pipeline_with_en #(.WIDTH(WIDTH)) DUT (.*);

   initial begin : generate_clock
      clk = 1'b0;
      while (1) #5 clk = ~clk;      
   end

   initial begin
      $timeformat(-9, 0, "" ns"");

      rst <= 1'b1;
      en <= 1'b0;      
      valid_in <= 1'b0;
      for (int i=0; i < 8; i++) in[i] <= '0;
      for (int i=0; i < 5; i++) @(posedge clk);
      @(negedge clk);
      rst <= 1'b0;
      @(posedge clk);
 
      for (int i=0; i < NUM_TESTS; i++) begin
         en <= $random;  
         for (int i=0; i < 8; i++) in[i] <= $random;
         valid_in <= $random;    
         @(posedge clk);
      end

      $display(""Tests completed."");      
      disable generate_clock;
   end
      
endmodule"
"module Programmable_Sequence_Detector 
#(
	parameter SEQ_W = 5
)
(
  input clk,
  input resetn,
  input [SEQ_W-1:0] init,
  input             din,
  input logic      seen
);

reg  [SEQ_W-1:0] seq_q;
wire [SEQ_W-1:0] seq_next;

assign seq_next = { seq_q[SEQ_W-2:0] , din } ;

always @(posedge clk) 
begin
	if ( ~resetn ) begin
		seq_q <= '0;
	end else begin
		seq_q <= seq_next;
	end
end

assign seen = seq_q == init;

endmodule"	"module Programmable_Sequence_Detector_sva 
#(
	parameter SEQ_W = 5
)
(
  input clk,
  input resetn,
  input [SEQ_W-1:0] init,
  input             din,
  input logic      seen,
  input logic  [SEQ_W-1:0] seq_q
);

default clocking cb @(posedge clk);
endclocking
default disable iff (~resetn);

sva_seen : assert property ( seen == ( seq_q == init ));

endmodule"	https://github.com/Essenceia/formal_experiements/tree/master/19_Programmable_Sequence_Detector	"Assertion 1:
This assertion is to check thathat AxiIdWidth (the width of the AXI transaction ID) is at least 1 bit.
Assertion 2:
This assertion is to check that AxiMaxWriteTxns (the maximum number of outstanding write transactions) is at least 1."	"module axi_atop_filter #(
  parameter int unsigned AxiIdWidth = 0,
  parameter int unsigned AxiMaxWriteTxns = 0,
  parameter type axi_req_t  = logic,
  parameter type axi_resp_t = logic
) (
  input  logic      clk_i,
  input  logic      rst_ni,
  input  axi_req_t  slv_req_i,
  output axi_resp_t slv_resp_o,
  output axi_req_t  mst_req_o,
  input  axi_resp_t mst_resp_i
);

  localparam int unsigned COUNTER_WIDTH = (AxiMaxWriteTxns == 1) ? 2 : $clog2(AxiMaxWriteTxns+1);
  typedef struct packed {
    logic                     underflow;
    logic [COUNTER_WIDTH-1:0] cnt;
  } cnt_t;
  cnt_t   w_cnt_d, w_cnt_q;

  typedef enum logic [2:0] {
    W_RESET, W_FEEDTHROUGH, BLOCK_AW, ABSORB_W, HOLD_B, INJECT_B, WAIT_R
  } w_state_e;
  w_state_e   w_state_d, w_state_q;

  typedef enum logic [1:0] { R_RESET, R_FEEDTHROUGH, INJECT_R, R_HOLD } r_state_e;
  r_state_e   r_state_d, r_state_q;

  typedef logic [AxiIdWidth-1:0] id_t;
  id_t  id_d, id_q;

  typedef logic [7:0] len_t;
  len_t   r_beats_d,  r_beats_q;

  typedef struct packed {
    len_t len;
  } r_resp_cmd_t;
  r_resp_cmd_t  r_resp_cmd_push, r_resp_cmd_pop;

  logic aw_without_complete_w_downstream,
        complete_w_without_aw_downstream,
        r_resp_cmd_push_valid,  r_resp_cmd_push_ready,
        r_resp_cmd_pop_valid,   r_resp_cmd_pop_ready;

  assign aw_without_complete_w_downstream = !w_cnt_q.underflow && (w_cnt_q.cnt > 0);
  assign complete_w_without_aw_downstream = w_cnt_q.underflow && &(w_cnt_q.cnt);

  always_comb begin
    mst_req_o.aw_valid  = 1'b0;
    slv_resp_o.aw_ready = 1'b0;
    mst_req_o.w_valid   = 1'b0;
    slv_resp_o.w_ready  = 1'b0;
    mst_req_o.b_ready   = slv_req_i.b_ready;
    slv_resp_o.b_valid  = mst_resp_i.b_valid;
    slv_resp_o.b        = mst_resp_i.b;
    id_d = id_q;
    r_resp_cmd_push_valid = 1'b0;
    w_state_d = w_state_q;

    unique case (w_state_q)
      W_RESET: w_state_d = W_FEEDTHROUGH;

      W_FEEDTHROUGH: begin
        if (complete_w_without_aw_downstream || (w_cnt_q.cnt < AxiMaxWriteTxns)) begin
          mst_req_o.aw_valid  = slv_req_i.aw_valid;
          slv_resp_o.aw_ready = mst_resp_i.aw_ready;
        end
        if (aw_without_complete_w_downstream
            || ((slv_req_i.aw_valid && slv_req_i.aw.atop[5:4] == axi_pkg::ATOP_NONE)
                && !complete_w_without_aw_downstream)
        ) begin
          mst_req_o.w_valid  = slv_req_i.w_valid;
          slv_resp_o.w_ready = mst_resp_i.w_ready;
        end
        if (slv_req_i.aw_valid && slv_req_i.aw.atop[5:4] != axi_pkg::ATOP_NONE) begin
          mst_req_o.aw_valid  = 1'b0; 
          slv_resp_o.aw_ready = 1'b1;
          id_d = slv_req_i.aw.id;
          if (slv_req_i.aw.atop[axi_pkg::ATOP_R_RESP]) begin
            r_resp_cmd_push_valid = 1'b1;
          end
          if (aw_without_complete_w_downstream) begin
            w_state_d = BLOCK_AW;
          end else begin
            mst_req_o.w_valid  = 1'b0;
            slv_resp_o.w_ready = 1'b1;
            if (slv_req_i.w_valid && slv_req_i.w.last) begin
              if (slv_resp_o.b_valid && !slv_req_i.b_ready) begin
                w_state_d = HOLD_B;
              end else begin
                w_state_d = INJECT_B;
              end
            end else begin
              w_state_d = ABSORB_W;
            end
          end
        end
      end

      BLOCK_AW: begin
        if (aw_without_complete_w_downstream) begin
          mst_req_o.w_valid  = slv_req_i.w_valid;
          slv_resp_o.w_ready = mst_resp_i.w_ready;
        end else begin
          slv_resp_o.w_ready = 1'b1;
          if (slv_req_i.w_valid && slv_req_i.w.last) begin
            if (slv_resp_o.b_valid && !slv_req_i.b_ready) begin
              w_state_d = HOLD_B;
            end else begin
              w_state_d = INJECT_B;
            end
          end else begin
            w_state_d = ABSORB_W;
          end
        end
      end

      ABSORB_W: begin
        slv_resp_o.w_ready = 1'b1;
        if (slv_req_i.w_valid && slv_req_i.w.last) begin
          if (slv_resp_o.b_valid && !slv_req_i.b_ready) begin
            w_state_d = HOLD_B;
          end else begin
            w_state_d = INJECT_B;
          end
        end
      end

      HOLD_B: begin
        if (slv_resp_o.b_valid && slv_req_i.b_ready) begin
          w_state_d = INJECT_B;
        end
      end

      INJECT_B: begin
        mst_req_o.b_ready = 1'b0;
        slv_resp_o.b = '0;
        slv_resp_o.b.id = id_q;
        slv_resp_o.b.resp = axi_pkg::RESP_SLVERR;
        slv_resp_o.b_valid = 1'b1;
        if (slv_req_i.b_ready) begin
          if (r_resp_cmd_pop_valid && !r_resp_cmd_pop_ready) begin
            w_state_d = WAIT_R;
          end else begin
            w_state_d = W_FEEDTHROUGH;
          end
        end
      end

      WAIT_R: begin
        if (!r_resp_cmd_pop_valid) begin
          w_state_d = W_FEEDTHROUGH;
        end
      end

      default: w_state_d = W_RESET;
    endcase
  end
  always_comb begin
    mst_req_o.aw      = slv_req_i.aw;
    mst_req_o.aw.atop = '0;
  end
  assign mst_req_o.w = slv_req_i.w;

  always_comb begin
    slv_resp_o.r       = mst_resp_i.r;
    slv_resp_o.r_valid = mst_resp_i.r_valid;
    mst_req_o.r_ready  = slv_req_i.r_ready;
    r_resp_cmd_pop_ready = 1'b0;
    r_beats_d = r_beats_q;
    r_state_d = r_state_q;

    unique case (r_state_q)
      R_RESET: r_state_d = R_FEEDTHROUGH;

      R_FEEDTHROUGH: begin
        if (mst_resp_i.r_valid && !slv_req_i.r_ready) begin
          r_state_d = R_HOLD;
        end else if (r_resp_cmd_pop_valid) begin
          r_beats_d = r_resp_cmd_pop.len;
          r_state_d = INJECT_R;
        end
      end

      INJECT_R: begin
        mst_req_o.r_ready  = 1'b0;
        slv_resp_o.r       = '0;
        slv_resp_o.r.id    = id_q;
        slv_resp_o.r.resp  = axi_pkg::RESP_SLVERR;
        slv_resp_o.r.last  = (r_beats_q == '0);
        slv_resp_o.r_valid = 1'b1;
        if (slv_req_i.r_ready) begin
          if (slv_resp_o.r.last) begin
            r_resp_cmd_pop_ready = 1'b1;
            r_state_d = R_FEEDTHROUGH;
          end else begin
            r_beats_d -= 1;
          end
        end
      end

      R_HOLD: begin
        if (mst_resp_i.r_valid && slv_req_i.r_ready) begin
          r_state_d = R_FEEDTHROUGH;
        end
      end

      default: r_state_d = R_RESET;
    endcase
  end
  assign mst_req_o.ar        = slv_req_i.ar;
  assign mst_req_o.ar_valid  = slv_req_i.ar_valid;
  assign slv_resp_o.ar_ready = mst_resp_i.ar_ready;

  always_comb begin
    w_cnt_d = w_cnt_q;
    if (mst_req_o.aw_valid && mst_resp_i.aw_ready) begin
      w_cnt_d.cnt += 1;
    end
    if (mst_req_o.w_valid && mst_resp_i.w_ready && mst_req_o.w.last) begin
      w_cnt_d.cnt -= 1;
    end
    if (w_cnt_q.underflow && (w_cnt_d.cnt == '0)) begin
      w_cnt_d.underflow = 1'b0;
    end else if (w_cnt_q.cnt == '0 && &(w_cnt_d.cnt)) begin
      w_cnt_d.underflow = 1'b1;
    end
  end

  always_ff @(posedge clk_i, negedge rst_ni) begin
    if (!rst_ni) begin
      id_q <= '0;
      r_beats_q <= '0;
      r_state_q <= R_RESET;
      w_cnt_q <= '{default: '0};
      w_state_q <= W_RESET;
    end else begin
      id_q <= id_d;
      r_beats_q <= r_beats_d;
      r_state_q <= r_state_d;
      w_cnt_q <= w_cnt_d;
      w_state_q <= w_state_d;
    end
  end

  stream_register #(
    .T(r_resp_cmd_t)
  ) r_resp_cmd (
    .clk_i      (clk_i),
    .rst_ni     (rst_ni),
    .clr_i      (1'b0),
    .testmode_i (1'b0),
    .valid_i    (r_resp_cmd_push_valid),
    .ready_o    (r_resp_cmd_push_ready),
    .data_i     (r_resp_cmd_push),
    .valid_o    (r_resp_cmd_pop_valid),
    .ready_i    (r_resp_cmd_pop_ready),
    .data_o     (r_resp_cmd_pop)
  );
  assign r_resp_cmd_push.len = slv_req_i.aw.len;
endmodule"
"module full_adder 
(
    input a,
    input b,
    input cin,
    output sum,
    output cout
);

assign sum = a ^ b ^ cin;
assign cout = (a & b) | (a & cin) | (b & cin);
endmodule

module Ripple_Carry_Adder #(
	parameter DATA_WIDTH=8
)
(
    input [DATA_WIDTH-1:0] a,
    input [DATA_WIDTH-1:0] b,
    input clk,
    input rst,
    output logic [DATA_WIDTH-0:0] sum,
    output logic [DATA_WIDTH-1:0] cout_int
);

logic [DATA_WIDTH:0] carry;
assign carry[0] = 1'b0;

genvar x;
generate
	for( x = 0; x < DATA_WIDTH; x++ ) begin
		// instanciate adder module
		full_adder m_adder(
			.a( a[x] ),
			.b( b[x] ),
			.cin( carry[x]),
			.sum( sum[x] ),
			.cout( carry[x+1] )
		);
	end
endgenerate
// output
assign sum[DATA_WIDTH] = carry[DATA_WIDTH];
assign cout_int        = carry[DATA_WIDTH-1:0];

endmodule"	"// `include ""full_adder.sv""
module Ripple_Carry_Adder_sva #(
	parameter DATA_WIDTH=8
)
(
    input [DATA_WIDTH-1:0] a,
    input [DATA_WIDTH-1:0] b,
    input clk,
    input rst,
    input logic [DATA_WIDTH-0:0] sum,
    input logic [DATA_WIDTH-1:0] cout_int
);

default clocking cb @(posedge clk);
endclocking
default disable iff (~rst);

logic [DATA_WIDTH:0] res;
assign res = a + b;

sva_adder : assert property ( res == sum );

endmodule"	https://github.com/Essenceia/formal_experiements/tree/master/24_Ripple_Carry_Adder	"Assertion 1:
This assertion is to check that AXI_ADDR_WIDTH, the width of the AXI address signal, is at least 1 bit.
Assertion 2:
This assertion is to check that AXI_DATA_WIDTH, the width of the AXI data signal, is at least 1 bit.
Assertion 2:
This assertion is to check that AXI_USER_WIDTH, the width of the AXI data signal, is at least 1 bit.
"	"module axi_atop_filter_intf #(
  parameter int unsigned AXI_ID_WIDTH   = 0,
  parameter int unsigned AXI_ADDR_WIDTH = 0,
  parameter int unsigned AXI_DATA_WIDTH = 0,
  parameter int unsigned AXI_USER_WIDTH = 0,
  parameter int unsigned AXI_MAX_WRITE_TXNS = 0
) (
  input  logic    clk_i,
  input  logic    rst_ni,
  AXI_BUS.Slave   slv,
  AXI_BUS.Master  mst
);

  typedef logic [AXI_ID_WIDTH-1:0]     id_t;
  typedef logic [AXI_ADDR_WIDTH-1:0]   addr_t;
  typedef logic [AXI_DATA_WIDTH-1:0]   data_t;
  typedef logic [AXI_DATA_WIDTH/8-1:0] strb_t;
  typedef logic [AXI_USER_WIDTH-1:0]   user_t;

  `AXI_TYPEDEF_AW_CHAN_T(aw_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_W_CHAN_T(w_chan_t, data_t, strb_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(b_chan_t, id_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(ar_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(r_chan_t, data_t, id_t, user_t)
  `AXI_TYPEDEF_REQ_T(axi_req_t, aw_chan_t, w_chan_t, ar_chan_t)
  `AXI_TYPEDEF_RESP_T(axi_resp_t, b_chan_t, r_chan_t)

  axi_req_t  slv_req,  mst_req;
  axi_resp_t slv_resp, mst_resp;

  `AXI_ASSIGN_TO_REQ(slv_req, slv)
  `AXI_ASSIGN_FROM_RESP(slv, slv_resp)

  `AXI_ASSIGN_FROM_REQ(mst, mst_req)
  `AXI_ASSIGN_TO_RESP(mst_resp, mst)

  axi_atop_filter #(
    .AxiIdWidth      ( AXI_ID_WIDTH       ),
    .AxiMaxWriteTxns ( AXI_MAX_WRITE_TXNS ),
    .axi_req_t       ( axi_req_t          ),
    .axi_resp_t      ( axi_resp_t         )
  ) i_axi_atop_filter (
    .clk_i,
    .rst_ni,
    .slv_req_i  ( slv_req  ),
    .slv_resp_o ( slv_resp ),
    .mst_req_o  ( mst_req  ),
    .mst_resp_i ( mst_resp )
  );
endmodule"
"module Flip_Flop_Array #(
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

endmodule"	"module Flip_Flop_Array_sva #(
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

endmodule"	https://github.com/Essenceia/formal_experiements/tree/master/25_Flip-Flop_Array	"Assertion 1:
This assertion is to check that any AW (write address) transaction output by the master port (mst_req_o.aw_valid) has a length (mst_req_o.aw.len) of zero, indicating a single-beat transaction.
Assertion 2:
This assertion is to check that any AR (read address) transaction output by the master port (mst_req_o.ar_valid) has a length of zero, confirming a single-beat transaction.
"	"module axi_burst_splitter #(
  parameter int unsigned MaxReadTxns  = 32'd0,
  parameter int unsigned MaxWriteTxns = 32'd0,
  parameter bit          FullBW       = 0,
  parameter int unsigned AddrWidth    = 32'd0,
  parameter int unsigned DataWidth    = 32'd0,
  parameter int unsigned IdWidth      = 32'd0,
  parameter int unsigned UserWidth    = 32'd0,
  parameter type         axi_req_t    = logic,
  parameter type         axi_resp_t   = logic
) (
  input  logic  clk_i,
  input  logic  rst_ni,

  input  axi_req_t  slv_req_i,
  output axi_resp_t slv_resp_o,

  output axi_req_t  mst_req_o,
  input  axi_resp_t mst_resp_i
);

  typedef logic [AddrWidth-1:0]   addr_t;
  typedef logic [DataWidth-1:0]   data_t;
  typedef logic [IdWidth-1:0]     id_t;
  typedef logic [DataWidth/8-1:0] strb_t;
  typedef logic [UserWidth-1:0]   user_t;
  `AXI_TYPEDEF_AW_CHAN_T(aw_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_W_CHAN_T(w_chan_t, data_t, strb_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(b_chan_t, id_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(ar_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(r_chan_t, data_t, id_t, user_t)

  axi_req_t   act_req,  unsupported_req;
  axi_resp_t  act_resp, unsupported_resp;
  logic sel_aw_unsupported, sel_ar_unsupported;
  localparam int unsigned MaxTxns = (MaxReadTxns > MaxWriteTxns) ? MaxReadTxns : MaxWriteTxns;
  axi_demux #(
    .AxiIdWidth   ( IdWidth     ),
    .aw_chan_t    ( aw_chan_t   ),
    .w_chan_t     ( w_chan_t    ),
    .b_chan_t     ( b_chan_t    ),
    .ar_chan_t    ( ar_chan_t   ),
    .r_chan_t     ( r_chan_t    ),
    .axi_req_t    ( axi_req_t   ),
    .axi_resp_t   ( axi_resp_t  ),
    .NoMstPorts   ( 2           ),
    .MaxTrans     ( MaxTxns     ),
    .AxiLookBits  ( IdWidth     ),
    .SpillAw      ( 1'b0        ),
    .SpillW       ( 1'b0        ),
    .SpillB       ( 1'b0        ),
    .SpillAr      ( 1'b0        ),
    .SpillR       ( 1'b0        )
  ) i_demux_supported_vs_unsupported (
    .clk_i,
    .rst_ni,
    .test_i           ( 1'b0                          ),
    .slv_req_i,
    .slv_aw_select_i  ( sel_aw_unsupported            ),
    .slv_ar_select_i  ( sel_ar_unsupported            ),
    .slv_resp_o,
    .mst_reqs_o       ( {unsupported_req,  act_req}   ),
    .mst_resps_i      ( {unsupported_resp, act_resp}  )
  );
  function bit txn_supported(axi_pkg::atop_t atop, axi_pkg::burst_t burst, axi_pkg::cache_t cache,
      axi_pkg::len_t len);
    if (len == '0) return 1'b1;
    if (burst == axi_pkg::BURST_WRAP) return 1'b0;
    if (atop != '0) return 1'b0;
    if (!axi_pkg::modifiable(cache)) begin
      return (burst == axi_pkg::BURST_INCR) & (len > 16);
    end
    return 1'b1;
  endfunction
  assign sel_aw_unsupported = ~txn_supported(slv_req_i.aw.atop, slv_req_i.aw.burst,
                                              slv_req_i.aw.cache, slv_req_i.aw.len);
  assign sel_ar_unsupported = ~txn_supported('0, slv_req_i.ar.burst,
                                              slv_req_i.ar.cache, slv_req_i.ar.len);
  axi_err_slv #(
    .AxiIdWidth ( IdWidth               ),
    .axi_req_t  ( axi_req_t             ),
    .axi_resp_t ( axi_resp_t            ),
    .Resp       ( axi_pkg::RESP_SLVERR  ),
    .ATOPs      ( 1'b0                  ), 
    .MaxTrans   ( 1                     )  
  ) i_err_slv (
    .clk_i,
    .rst_ni,
    .test_i     ( 1'b0              ),
    .slv_req_i  ( unsupported_req   ),
    .slv_resp_o ( unsupported_resp  )
  );

  logic           w_cnt_dec, w_cnt_req, w_cnt_gnt, w_cnt_err;
  axi_pkg::len_t  w_cnt_len;
  axi_burst_splitter_ax_chan #(
    .chan_t   ( aw_chan_t    ),
    .IdWidth  ( IdWidth      ),
    .MaxTxns  ( MaxWriteTxns ),
    .FullBW   ( FullBW       )
  ) i_axi_burst_splitter_aw_chan (
    .clk_i,
    .rst_ni,
    .ax_i           ( act_req.aw           ),
    .ax_valid_i     ( act_req.aw_valid     ),
    .ax_ready_o     ( act_resp.aw_ready    ),
    .ax_o           ( mst_req_o.aw         ),
    .ax_valid_o     ( mst_req_o.aw_valid   ),
    .ax_ready_i     ( mst_resp_i.aw_ready  ),
    .cnt_id_i       ( mst_resp_i.b.id      ),
    .cnt_len_o      ( w_cnt_len            ),
    .cnt_set_err_i  ( mst_resp_i.b.resp[1] ),
    .cnt_err_o      ( w_cnt_err            ),
    .cnt_dec_i      ( w_cnt_dec            ),
    .cnt_req_i      ( w_cnt_req            ),
    .cnt_gnt_o      ( w_cnt_gnt            )
  );

  always_comb begin
    mst_req_o.w        = act_req.w;
    mst_req_o.w.last   = 1'b1; 
  end
  assign mst_req_o.w_valid  = act_req.w_valid;
  assign act_resp.w_ready   = mst_resp_i.w_ready;

  enum logic {BReady, BWait} b_state_d, b_state_q;
  logic b_err_d, b_err_q;
  always_comb begin
    mst_req_o.b_ready = 1'b0;
    act_resp.b        = '0;
    act_resp.b_valid  = 1'b0;
    w_cnt_dec         = 1'b0;
    w_cnt_req         = 1'b0;
    b_err_d           = b_err_q;
    b_state_d         = b_state_q;

    unique case (b_state_q)
      BReady: begin
        if (mst_resp_i.b_valid) begin
          w_cnt_req = 1'b1;
          if (w_cnt_gnt) begin
            if (w_cnt_len == 8'd0) begin
              act_resp.b = mst_resp_i.b;
              if (w_cnt_err) begin
                act_resp.b.resp = axi_pkg::RESP_SLVERR;
              end
              act_resp.b_valid  = 1'b1;
              w_cnt_dec         = 1'b1;
              if (act_req.b_ready) begin
                mst_req_o.b_ready = 1'b1;
              end else begin
                b_state_d = BWait;
                b_err_d   = w_cnt_err;
              end
            end else begin
              mst_req_o.b_ready = 1'b1;
              w_cnt_dec         = 1'b1;
            end
          end
        end
      end
      BWait: begin
        act_resp.b = mst_resp_i.b;
        if (b_err_q) begin
          act_resp.b.resp = axi_pkg::RESP_SLVERR;
        end
        act_resp.b_valid  = 1'b1;
        if (mst_resp_i.b_valid && act_req.b_ready) begin
          mst_req_o.b_ready = 1'b1;
          b_state_d         = BReady;
        end
      end
      default: /*do nothing*/;
    endcase
  end

  logic           r_cnt_dec, r_cnt_req, r_cnt_gnt;
  axi_pkg::len_t  r_cnt_len;
  axi_burst_splitter_ax_chan #(
    .chan_t   ( ar_chan_t   ),
    .IdWidth  ( IdWidth     ),
    .MaxTxns  ( MaxReadTxns ),
    .FullBW   ( FullBW      )
  ) i_axi_burst_splitter_ar_chan (
    .clk_i,
    .rst_ni,
    .ax_i           ( act_req.ar          ),
    .ax_valid_i     ( act_req.ar_valid    ),
    .ax_ready_o     ( act_resp.ar_ready   ),
    .ax_o           ( mst_req_o.ar        ),
    .ax_valid_o     ( mst_req_o.ar_valid  ),
    .ax_ready_i     ( mst_resp_i.ar_ready ),
    .cnt_id_i       ( mst_resp_i.r.id     ),
    .cnt_len_o      ( r_cnt_len           ),
    .cnt_set_err_i  ( 1'b0                ),
    .cnt_err_o      (                     ),
    .cnt_dec_i      ( r_cnt_dec           ),
    .cnt_req_i      ( r_cnt_req           ),
    .cnt_gnt_o      ( r_cnt_gnt           )
  );

  logic r_last_d, r_last_q;
  enum logic {RFeedthrough, RWait} r_state_d, r_state_q;
  always_comb begin
    r_cnt_dec         = 1'b0;
    r_cnt_req         = 1'b0;
    r_last_d          = r_last_q;
    r_state_d         = r_state_q;
    mst_req_o.r_ready = 1'b0;
    act_resp.r        = mst_resp_i.r;
    act_resp.r.last   = 1'b0;
    act_resp.r_valid  = 1'b0;

    unique case (r_state_q)
      RFeedthrough: begin
        if (mst_resp_i.r_valid) begin
          r_cnt_req = 1'b1;
          if (r_cnt_gnt) begin
            r_last_d = (r_cnt_len == 8'd0);
            act_resp.r.last   = r_last_d;
            r_cnt_dec         = 1'b1;
            act_resp.r_valid  = 1'b1;
            if (act_req.r_ready) begin
              mst_req_o.r_ready = 1'b1;
            end else begin
              r_state_d = RWait;
            end
          end
        end
      end
      RWait: begin
        act_resp.r.last   = r_last_q;
        act_resp.r_valid  = mst_resp_i.r_valid;
        if (mst_resp_i.r_valid && act_req.r_ready) begin
          mst_req_o.r_ready = 1'b1;
          r_state_d         = RFeedthrough;
        end
      end
      default: 
    endcase
  end

  `FFARN(b_err_q, b_err_d, 1'b0, clk_i, rst_ni)
  `FFARN(b_state_q, b_state_d, BReady, clk_i, rst_ni)
  `FFARN(r_last_q, r_last_d, 1'b0, clk_i, rst_ni)
  `FFARN(r_state_q, r_state_d, RFeedthrough, clk_i, rst_ni)

endmodule"
"module PWM #(parameter CBITS = 10) 
(input clk, input rst, input [3:0] sw, output reg pulse);
  
  wire [CBITS-1:0] pulse_wide;
  assign pulse_wide = {1'b0, sw[3:1], 6'd0};     // (CBTIS-4)

  reg [CBITS-1:0] cntR;

  always @(posedge clk) begin
    cntR <= cntR + 1;
    
    if (cntR < pulse_wide)
      pulse = 1'b1;
    else
      pulse = 1'b0;
  end

endmodule"	"module PWM_sva #(parameter CBITS = 10) 
(
          input clk,
          input rst, 
          input [3:0] sw, 
          input logic pulse
);

p1: assert property (@(posedge clk) (1 |-> s_eventually(~pulse)));

endmodule
"	https://github.com/diffblue/hw-cbmc/blob/main/examples/Benchmarks/PWM_1.sv	"Assertions 1-4:
These assertions are to check whether the basic width parameters (ADDR_WIDTH, DATA_WIDTH, ID_WIDTH, and USER_WIDTH) are greater than zero.
Assertions 5-8:
These assertions are to check whether the width parameters for the slave interface (in) match the expected values specified by ADDR_WIDTH, DATA_WIDTH, ID_WIDTH, and USER_WIDTH.
Assertions 9-12:
These assertions are to check whether the width parameters for the master interface (out) match the module parameters.
"	"module axi_cut_intf #(
  parameter bit          BYPASS     = 1'b0,
  parameter int unsigned ADDR_WIDTH = 0,
  parameter int unsigned DATA_WIDTH = 0,
  parameter int unsigned ID_WIDTH   = 0,
  parameter int unsigned USER_WIDTH = 0
) (
  input logic     clk_i  ,
  input logic     rst_ni ,
  AXI_BUS.Slave   in     ,
  AXI_BUS.Master  out
);

  typedef logic [ID_WIDTH-1:0]     id_t;
  typedef logic [ADDR_WIDTH-1:0]   addr_t;
  typedef logic [DATA_WIDTH-1:0]   data_t;
  typedef logic [DATA_WIDTH/8-1:0] strb_t;
  typedef logic [USER_WIDTH-1:0]   user_t;

  `AXI_TYPEDEF_AW_CHAN_T(aw_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_W_CHAN_T(w_chan_t, data_t, strb_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(b_chan_t, id_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(ar_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(r_chan_t, data_t, id_t, user_t)
  `AXI_TYPEDEF_REQ_T(axi_req_t, aw_chan_t, w_chan_t, ar_chan_t)
  `AXI_TYPEDEF_RESP_T(axi_resp_t, b_chan_t, r_chan_t)

  axi_req_t  slv_req,  mst_req;
  axi_resp_t slv_resp, mst_resp;

  `AXI_ASSIGN_TO_REQ(slv_req, in)
  `AXI_ASSIGN_FROM_RESP(in, slv_resp)

  `AXI_ASSIGN_FROM_REQ(out, mst_req)
  `AXI_ASSIGN_TO_RESP(mst_resp, out)

  axi_cut #(
    .Bypass     (     BYPASS ),
    .aw_chan_t  (  aw_chan_t ),
    .w_chan_t   (   w_chan_t ),
    .b_chan_t   (   b_chan_t ),
    .ar_chan_t  (  ar_chan_t ),
    .r_chan_t   (   r_chan_t ),
    .axi_req_t  (  axi_req_t ),
    .axi_resp_t ( axi_resp_t )
  ) i_axi_cut (
    .clk_i,
    .rst_ni,
    .slv_req_i  ( slv_req  ),
    .slv_resp_o ( slv_resp ),
    .mst_req_o  ( mst_req  ),
    .mst_resp_i ( mst_resp )
  );

endmodule"
"module Delay 
#(
          parameter N = 750, 
          parameter CBITS = 10
) 
(input clk, input rst, output reg sig);
  reg [CBITS-1 :0] cnt;
  always @(posedge clk) begin
    if (rst) cnt = 0;
    else cnt = cnt + 1;
    if (cnt > N) begin sig = 1;
      cnt = 0; end
    else sig = 0;
  end

endmodule"	"module Delay_sva
#(
          parameter N = 750, 
          parameter CBITS = 10
) 
(input clk, input rst, input logic sig);

p1: assert property (@(posedge clk) s_eventually (rst || sig == 1)) ;
endmodule"	https://github.com/diffblue/hw-cbmc/blob/main/examples/Benchmarks/delay_1.sv	"Assertions 1-2:
These assertions are to check whether the basic width parameters (ADDR_WIDTH, DATA_WIDTH) are greater than zero.
Assertions 3-4:
The two assertions are to check whether the address width (in.AXI_ADDR_WIDTH) and the data width (in.AXI_DATA_WIDTH) of the slave interface matches the module parameters ADDR_WIDTH, DATA_WIDTH.
Assertions 5-6:
The two assertions are to check whether the address width (out.AXI_ADDR_WIDTH) and the data width (out.AXI_DATA_WIDTH) of the master interface matches the module parameters ADDR_WIDTH, DATA_WIDTH.
"	"module axi_lite_cut_intf #(
  parameter bit          BYPASS     = 1'b0,
  parameter int unsigned ADDR_WIDTH = 0,
  parameter int unsigned DATA_WIDTH = 0
) (
  input logic     clk_i  ,
  input logic     rst_ni ,
  AXI_LITE.Slave  in     ,
  AXI_LITE.Master out
);

  typedef logic [ADDR_WIDTH-1:0]   addr_t;
  typedef logic [DATA_WIDTH-1:0]   data_t;
  typedef logic [DATA_WIDTH/8-1:0] strb_t;

  `AXI_LITE_TYPEDEF_AW_CHAN_T(aw_chan_t, addr_t)
  `AXI_LITE_TYPEDEF_W_CHAN_T(w_chan_t, data_t, strb_t)
  `AXI_LITE_TYPEDEF_B_CHAN_T(b_chan_t)
  `AXI_LITE_TYPEDEF_AR_CHAN_T(ar_chan_t, addr_t)
  `AXI_LITE_TYPEDEF_R_CHAN_T(r_chan_t, data_t)
  `AXI_LITE_TYPEDEF_REQ_T(axi_req_t, aw_chan_t, w_chan_t, ar_chan_t)
  `AXI_LITE_TYPEDEF_RESP_T(axi_resp_t, b_chan_t, r_chan_t)

  axi_req_t   slv_req,  mst_req;
  axi_resp_t  slv_resp, mst_resp;

  `AXI_LITE_ASSIGN_TO_REQ(slv_req, in)
  `AXI_LITE_ASSIGN_FROM_RESP(in, slv_resp)

  `AXI_LITE_ASSIGN_FROM_REQ(out, mst_req)
  `AXI_LITE_ASSIGN_TO_RESP(mst_resp, out)

  axi_cut #(
    .Bypass     (     BYPASS ),
    .aw_chan_t  (  aw_chan_t ),
    .w_chan_t   (   w_chan_t ),
    .b_chan_t   (   b_chan_t ),
    .ar_chan_t  (  ar_chan_t ),
    .r_chan_t   (   r_chan_t ),
    .axi_req_t  (  axi_req_t ),
    .axi_resp_t ( axi_resp_t )
  ) i_axi_cut (
    .clk_i,
    .rst_ni,
    .slv_req_i  ( slv_req  ),
    .slv_resp_o ( slv_resp ),
    .mst_req_o  ( mst_req  ),
    .mst_resp_i ( mst_resp )
  );

endmodule"
"module gray #(parameter CBITS = 8) (input clk, input rst, output reg [CBITS-1:0] gray_cnt, output reg sig);
  reg [CBITS-1:0] cnt;
  always@(posedge clk, posedge rst) begin
    if (rst) begin
      cnt = 0;
    end
    else begin
      cnt = cnt + 1;
      gray_cnt = (cnt) ^ ((cnt) >> 1);
      if(gray_cnt == 0)
        sig = 1;
      else
        sig = 0;
    end
  end
  // F G (rst = F) -> G F (sig = T)
endmodule"	"module gray_sva #(parameter CBITS = 8) (input clk, input rst, input logic [CBITS-1:0] gray_cnt, input logic sig);

  p1: assert property (@(posedge clk) s_eventually (rst || sig == 1));
  // F G (rst = F) -> G F (sig = T)
endmodule"	https://github.com/diffblue/hw-cbmc/blob/main/examples/Benchmarks/gray_1.sv	"Assertions 1-4: 
These assertions are to check whether the basic width parameters (AXI_ADDR_WIDTH, AXI_DATA_WIDTH, AXI_ID_WIDTH, and AXI_USER_WIDTH) are greater than zero."	"module axi_delayer_intf #(
  parameter int unsigned AXI_ID_WIDTH        = 0,
  parameter int unsigned AXI_ADDR_WIDTH      = 0,
  parameter int unsigned AXI_DATA_WIDTH      = 0,
  parameter int unsigned AXI_USER_WIDTH      = 0,
  parameter bit          STALL_RANDOM_INPUT  = 0,
  parameter bit          STALL_RANDOM_OUTPUT = 0,
  parameter int unsigned FIXED_DELAY_INPUT   = 1,
  parameter int unsigned FIXED_DELAY_OUTPUT  = 1
) (
  input  logic    clk_i,
  input  logic    rst_ni,
  AXI_BUS.Slave   slv,
  AXI_BUS.Master  mst
);

  typedef logic [AXI_ID_WIDTH-1:0]     id_t;
  typedef logic [AXI_ADDR_WIDTH-1:0]   addr_t;
  typedef logic [AXI_DATA_WIDTH-1:0]   data_t;
  typedef logic [AXI_DATA_WIDTH/8-1:0] strb_t;
  typedef logic [AXI_USER_WIDTH-1:0]   user_t;

  `AXI_TYPEDEF_AW_CHAN_T(aw_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_W_CHAN_T(w_chan_t, data_t, strb_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(b_chan_t, id_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(ar_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(r_chan_t, data_t, id_t, user_t)
  `AXI_TYPEDEF_REQ_T(axi_req_t, aw_chan_t, w_chan_t, ar_chan_t)
  `AXI_TYPEDEF_RESP_T(axi_resp_t, b_chan_t, r_chan_t)

  axi_req_t  slv_req,  mst_req;
  axi_resp_t slv_resp, mst_resp;

  `AXI_ASSIGN_TO_REQ(slv_req, slv)
  `AXI_ASSIGN_FROM_RESP(slv, slv_resp)

  `AXI_ASSIGN_FROM_REQ(mst, mst_req)
  `AXI_ASSIGN_TO_RESP(mst_resp, mst)

  axi_delayer #(
    .aw_chan_t         (           aw_chan_t ),
    .w_chan_t          (            w_chan_t ),
    .b_chan_t          (            b_chan_t ),
    .ar_chan_t         (           ar_chan_t ),
    .r_chan_t          (            r_chan_t ),
    .axi_req_t         (           axi_req_t ),
    .axi_resp_t        (          axi_resp_t ),
    .StallRandomInput  ( STALL_RANDOM_INPUT  ),
    .StallRandomOutput ( STALL_RANDOM_OUTPUT ),
    .FixedDelayInput   ( FIXED_DELAY_INPUT   ),
    .FixedDelayOutput  ( FIXED_DELAY_OUTPUT  )
  ) i_axi_delayer (
    .clk_i,   // Clock
    .rst_ni,  // Asynchronous reset active low
    .slv_req_i  ( slv_req  ),
    .slv_resp_o ( slv_resp ),
    .mst_req_o  ( mst_req  ),
    .mst_resp_i ( mst_resp )
  );

endmodule"
"module i2c #(parameter divider = 125, parameter CBITS = 9) (input clk, input rst, input scl_not_ena, output reg data_clk);
	reg [CBITS - 1:0] cnt;	//0 to 4*divider
	reg scl_clk;
	reg stretch;
	always @(posedge clk) begin
		if(rst == 1) begin
			stretch = 0;
			cnt = 0;
		end
		if(cnt >= divider*4 - 1)
			cnt = 0;
		else if(stretch == 0)
			cnt = cnt + 1;

		if( cnt <= divider - 1) begin
			scl_clk = 0;
			data_clk = 0;
		end
		else if( divider <= cnt && cnt <= 2*divider - 1) begin
			scl_clk = 0;
			data_clk = 1;
		end
		else if( 2*divider <= cnt && cnt <= 3*divider - 1) begin
			if(scl_clk == 0 & scl_not_ena == 0)
				stretch = 1;
			else
				stretch = 0;
			scl_clk = 1;
			data_clk = 1;
		end
		else begin
			scl_clk = 1;
			data_clk = 0;
		end
	end

endmodule"	"module i2c_sva #(parameter divider = 125, parameter CBITS = 9) (input clk, input rst, input scl_not_ena, input logic data_clk, input logic stretch);

	p1: assert property (@(posedge clk) s_eventually rst == 1 || scl_not_ena == 1 || stretch == 1);

endmodule"	https://github.com/diffblue/hw-cbmc/blob/main/examples/Benchmarks/i2c_1.sv	"Assertion 1:
This assertion is to check only when rst_ni is 0 whether no underflow occurs for each counter when a pop operation is attempted on the ID-specific counters (pop_en[i]).
"	"module axi_demux_id_counters #(
  parameter int unsigned AxiIdBits         = 2,
  parameter int unsigned CounterWidth      = 4,
  parameter type         mst_port_select_t = logic
) (
  input                        clk_i, 
  input                        rst_ni, 
  input  logic [AxiIdBits-1:0] lookup_axi_id_i,
  output mst_port_select_t     lookup_mst_select_o,
  output logic                 lookup_mst_select_occupied_o,
  output logic                 full_o,
  input  logic [AxiIdBits-1:0] push_axi_id_i,
  input  mst_port_select_t     push_mst_select_i,
  input  logic                 push_i,
  input  logic [AxiIdBits-1:0] inject_axi_id_i,
  input  logic                 inject_i,
  input  logic [AxiIdBits-1:0] pop_axi_id_i,
  input  logic                 pop_i
);
  localparam int unsigned NoCounters = 2**AxiIdBits;
  typedef logic [CounterWidth-1:0] cnt_t;

  mst_port_select_t [NoCounters-1:0] mst_select_q;

  logic [NoCounters-1:0] push_en, inject_en, pop_en, occupied, cnt_full;

  assign lookup_mst_select_o          = mst_select_q[lookup_axi_id_i];
  assign lookup_mst_select_occupied_o = occupied[lookup_axi_id_i];
  assign push_en   = (push_i)   ? (1 << push_axi_id_i)   : '0;
  assign inject_en = (inject_i) ? (1 << inject_axi_id_i) : '0;
  assign pop_en    = (pop_i)    ? (1 << pop_axi_id_i)    : '0;
  assign full_o    = |cnt_full;

  for (genvar i = 0; i < NoCounters; i++) begin : gen_counters
    logic cnt_en, cnt_down, overflow;
    cnt_t cnt_delta, in_flight;
    always_comb begin
      unique case ({push_en[i], inject_en[i], pop_en[i]})
        3'b001  : begin
          cnt_en    = 1'b1;
          cnt_down  = 1'b1;
          cnt_delta = cnt_t'(1);
        end
        3'b010  : begin
          cnt_en    = 1'b1;
          cnt_down  = 1'b0;
          cnt_delta = cnt_t'(1);
        end

        3'b100  : begin // push_i = +1
          cnt_en    = 1'b1;
          cnt_down  = 1'b0;
          cnt_delta = cnt_t'(1);
        end

        3'b110  : begin
          cnt_en    = 1'b1;
          cnt_down  = 1'b0;
          cnt_delta = cnt_t'(2);
        end
        3'b111  : begin
          cnt_en    = 1'b1;
          cnt_down  = 1'b0;
          cnt_delta = cnt_t'(1);
        end
        default : begin
          cnt_en    = 1'b0;
          cnt_down  = 1'b0;
          cnt_delta = cnt_t'(0);
        end
      endcase
    end

    delta_counter #(
      .WIDTH           ( CounterWidth ),
      .STICKY_OVERFLOW ( 1'b0         )
    ) i_in_flight_cnt (
      .clk_i      ( clk_i     ),
      .rst_ni     ( rst_ni    ),
      .clear_i    ( 1'b0      ),
      .en_i       ( cnt_en    ),
      .load_i     ( 1'b0      ),
      .down_i     ( cnt_down  ),
      .delta_i    ( cnt_delta ),
      .d_i        ( '0        ),
      .q_o        ( in_flight ),
      .overflow_o ( overflow  )
    );
    assign occupied[i] = |in_flight;
    assign cnt_full[i] = overflow | (&in_flight);


    `FFLARN(mst_select_q[i], push_mst_select_i, push_en[i], '0, clk_i, rst_ni)
  end
endmodule"
"module lcd #(parameter clk_freq = 1, parameter CBITS = 9) (input rst, input clk, input [6:0] in_data, input lcd_enable, input [9:0] lcd_bus, output reg e, output reg[7:0] lcd_data, output reg rw, output reg rs, output reg busy);
	reg [CBITS - 1:0] cnt;			// 0 to 500*clk_freg
	reg [1:0] state;

	always @(posedge clk) begin
		rw = 0;
		rs = 0;
		busy = 0;
		lcd_data = 0;
		e = 0;
		if(state == 0) begin
			busy = 1;
			if(cnt < 500*clk_freq)				// wait 500
				cnt = cnt + 1;
			else begin							// power-up completed
				cnt = 0;
				rs = 0;
				rw = 0;
				lcd_data = 8'b00110000;
				state = 1;
			end
		end
		if(state == 1) begin
			busy = 1;
			cnt = cnt + 1;
			if(cnt < (10*clk_freq))begin			//function set
				lcd_data = {4'b0011, in_data[6], in_data[5], 2'b00};
				e = 1;
			end
			else if(cnt < (60*clk_freq))begin		// wait 50
				lcd_data = 8'b00000000;
				e = 0;
			end
			else if(cnt < (70*clk_freq))begin		//display on/off control
				lcd_data = {5'b00001, in_data[4], in_data[3], in_data[2]};
				e = 1;
			end
			else if(cnt < (120*clk_freq))begin		// wait 50
				lcd_data = 8'b00000000;
				e = 0;
			end
			else if(cnt < (130*clk_freq))begin		// display clear
				lcd_data = 8'b00000001;
				e = 1;
			end
			else if(cnt < (330*clk_freq))begin		// wait 200
				lcd_data = 8'b00000000;
				e = 0;
			end
			else if(cnt < (340*clk_freq))begin		// entry mode set
				lcd_data = {6'b000001, in_data[1], in_data[0]};
				e = 1;
			end
			else if(cnt < (440*clk_freq))begin		// wait 100
				lcd_data = 8'b00000000;
				e = 0;
			end
			else begin								// initialization complete
				cnt = 0;
				busy = 0;
				state = 2;
			end
		end
		if(state == 2) begin
			if(lcd_enable == 1) begin
				busy = 1;
				rs = lcd_bus[9];
				rw = lcd_bus[8];
				lcd_data = lcd_bus[7:0];
				cnt = 0;
				state = 3;
			end
			else begin
				busy = 0;
				rs = 0;
				rw = 0;
				lcd_data = 8'b00000000;
				cnt = 0;
			end
		end
		if(state == 3) begin
			if(cnt < 50* clk_freq) begin 		// do not exit for 50
				if(cnt < clk_freq)
					e = 0;
				else if(cnt < 14*clk_freq)		// positive enable half-cycle
					e = 1;
				else if(cnt < 27*clk_freq)		// negative enable half-cycle
					e = 0;
				cnt = cnt + 1;
			end
			else begin
				cnt = 0;
				state = 2;
			end
		end
	end

endmodule"	"module lcd_sva #(parameter clk_freq = 1, parameter CBITS = 9) (input clk, input [6:0] in_data, input lcd_enable, input [9:0] lcd_bus, input logic e, input logic[7:0] lcd_data, input logic rw, input logic rs, input logic busy, input logic [1:0] state);
	p1: assert property (@(posedge clk) s_eventually (lcd_enable == 0 || state == 2));
endmodule"	https://github.com/diffblue/hw-cbmc/blob/main/examples/Benchmarks/lcd_1.sv	"Assertion 1:
This assertion is to check if aw_valid is high but aw_ready is low, aw_valid remains stable. This ensures that aw_valid does not deassert prematurely when it’s not acknowledged.
Assertion 2:
This assertion is to check ar_valid remains high until acknowledged by ar_ready, maintaining protocol compliance.
Assertion 3:
slv_req_i.aw remains stable when aw_valid is asserted but aw_ready is not.
Assertion 4:
This assertion is to check slv_aw_select_i remains stable under the same conditions.
Assertion 5:
This assertion is to check slv_req_i.ar remains stable when ar_valid is high and ar_ready is low.
Assertion 6:
This assertion is to check slv_ar_select_i remains stable in the same scenario.
Assertion 7:
This assertion is to check when ar_valid is high, slv_ar_select_i is within the valid range of master ports.
Assertion 8:
This assertion is to check when aw_valid is high, slv_aw_select_i should be valid.
Assertion 9:
This assertion is to check if w_open is zero, no w_cnt_down operation (decrement) occurs unless balanced by a w_cnt_up. This prevents an underflow in the write counter."	"module axi_demux_simple #(
  parameter int unsigned AxiIdWidth     = 32'd0,
  parameter bit          AtopSupport    = 1'b1,
  parameter type         axi_req_t      = logic,
  parameter type         axi_resp_t     = logic,
  parameter int unsigned NoMstPorts     = 32'd0,
  parameter int unsigned MaxTrans       = 32'd8,
  parameter int unsigned AxiLookBits    = 32'd3,
  parameter bit          UniqueIds      = 1'b0,

  parameter int unsigned SelectWidth    = (NoMstPorts > 32'd1) ? $clog2(NoMstPorts) : 32'd1,
  parameter type         select_t       = logic [SelectWidth-1:0]
) (
  input  logic                          clk_i,
  input  logic                          rst_ni,
  input  logic                          test_i,

  input  axi_req_t                      slv_req_i,
  input  select_t                       slv_aw_select_i,
  input  select_t                       slv_ar_select_i,
  output axi_resp_t                     slv_resp_o,

  output axi_req_t    [NoMstPorts-1:0]  mst_reqs_o,
  input  axi_resp_t   [NoMstPorts-1:0]  mst_resps_i
);

  localparam int unsigned IdCounterWidth = cf_math_pkg::idx_width(MaxTrans);
  typedef logic [IdCounterWidth-1:0] id_cnt_t;


  if (NoMstPorts == 32'h1) begin : gen_no_demux
    `AXI_ASSIGN_REQ_STRUCT(mst_reqs_o[0], slv_req_i)
    `AXI_ASSIGN_RESP_STRUCT(slv_resp_o, mst_resps_i[0])
  end else begin

    logic                     lock_aw_valid_d,    lock_aw_valid_q, load_aw_lock;
    logic                     aw_valid,           aw_ready;

    select_t                  lookup_aw_select;
    logic                     aw_select_occupied, aw_id_cnt_full;
    logic                     atop_inject;

    select_t                  w_select,           w_select_q;
    logic                     w_select_valid;
    id_cnt_t                  w_open;
    logic                     w_cnt_up,           w_cnt_down;

    logic    [NoMstPorts-1:0] mst_b_valids,       mst_b_readies;

    select_t                  lookup_ar_select;
    logic                     ar_select_occupied, ar_id_cnt_full;
    logic                     ar_push;

    logic                     lock_ar_valid_d,    lock_ar_valid_q, load_ar_lock;
    logic                     ar_valid,           ar_ready;

    logic    [NoMstPorts-1:0] mst_r_valids, mst_r_readies;







    always_comb begin
      slv_resp_o.aw_ready = 1'b0;
      aw_valid     = 1'b0;
      lock_aw_valid_d = lock_aw_valid_q;
      load_aw_lock    = 1'b0;
      w_cnt_up        = 1'b0;
      atop_inject     = 1'b0;
      if (lock_aw_valid_q) begin
        aw_valid = 1'b1;
        if (aw_ready) begin
          slv_resp_o.aw_ready    = 1'b1;
          lock_aw_valid_d = 1'b0;
          load_aw_lock    = 1'b1;
          atop_inject     = slv_req_i.aw.atop[axi_pkg::ATOP_R_RESP] & AtopSupport;
        end
      end else begin
        if (!aw_id_cnt_full && (w_open != {IdCounterWidth{1'b1}}) &&
            (!(ar_id_cnt_full && slv_req_i.aw.atop[axi_pkg::ATOP_R_RESP]) ||
             !AtopSupport)) begin
          if (slv_req_i.aw_valid &&
                ((w_open == '0) || (w_select == slv_aw_select_i)) &&
                (!aw_select_occupied || (slv_aw_select_i == lookup_aw_select))) begin
            aw_valid     = 1'b1;
            w_cnt_up     = 1'b1;
            if (aw_ready) begin
              slv_resp_o.aw_ready = 1'b1;
              atop_inject  = slv_req_i.aw.atop[axi_pkg::ATOP_R_RESP] & AtopSupport;
            end else begin
              lock_aw_valid_d = 1'b1;
              load_aw_lock    = 1'b1;
            end
          end
        end
      end
    end

    `FFLARN(lock_aw_valid_q, lock_aw_valid_d, load_aw_lock, '0, clk_i, rst_ni)

    if (UniqueIds) begin : gen_unique_ids_aw
      assign lookup_aw_select = slv_aw_select_i;
      assign aw_select_occupied = 1'b0;
      assign aw_id_cnt_full = 1'b0;
    end else begin : gen_aw_id_counter
      axi_demux_id_counters #(
        .AxiIdBits         ( AxiLookBits    ),
        .CounterWidth      ( IdCounterWidth ),
        .mst_port_select_t ( select_t       )
      ) i_aw_id_counter (
        .clk_i                        ( clk_i                          ),
        .rst_ni                       ( rst_ni                         ),
        .lookup_axi_id_i              ( slv_req_i.aw.id[0+:AxiLookBits] ),
        .lookup_mst_select_o          ( lookup_aw_select               ),
        .lookup_mst_select_occupied_o ( aw_select_occupied             ),
        .full_o                       ( aw_id_cnt_full                 ),
        .inject_axi_id_i              ( '0                             ),
        .inject_i                     ( 1'b0                           ),
        .push_axi_id_i                ( slv_req_i.aw.id[0+:AxiLookBits] ),
        .push_mst_select_i            ( slv_aw_select_i                ),
        .push_i                       ( w_cnt_up                       ),
        .pop_axi_id_i                 ( slv_resp_o.b.id[0+:AxiLookBits]  ),
        .pop_i                        ( slv_resp_o.b_valid & slv_req_i.b_ready      )
      );
    end

    counter #(
      .WIDTH           ( IdCounterWidth ),
      .STICKY_OVERFLOW ( 1'b0           )
    ) i_counter_open_w (
      .clk_i,
      .rst_ni,
      .clear_i    ( 1'b0                  ),
      .en_i       ( w_cnt_up ^ w_cnt_down ),
      .load_i     ( 1'b0                  ),
      .down_i     ( w_cnt_down            ),
      .d_i        ( '0                    ),
      .q_o        ( w_open                ),
      .overflow_o ( /*not used*/          )
    );

    `FFLARN(w_select_q, slv_aw_select_i, w_cnt_up, select_t'(0), clk_i, rst_ni)
    assign w_select       = (|w_open) ? w_select_q : slv_aw_select_i;
    assign w_select_valid = w_cnt_up | (|w_open);

    logic [cf_math_pkg::idx_width(NoMstPorts)-1:0] b_idx;

    rr_arb_tree #(
      .NumIn    ( NoMstPorts ),
      .DataType ( logic   ),
      .AxiVldRdy( 1'b1       ),
      .LockIn   ( 1'b1       )
    ) i_b_mux (
      .clk_i  ( clk_i         ),
      .rst_ni ( rst_ni        ),
      .flush_i( 1'b0          ),
      .rr_i   ( '0            ),
      .req_i  ( mst_b_valids  ),
      .gnt_o  ( mst_b_readies ),
      .data_i ( '0   ),
      .gnt_i  ( slv_req_i.b_ready  ),
      .req_o  ( slv_resp_o.b_valid ),
      .data_o (        ),
      .idx_o  ( b_idx              )
    );

    always_comb begin
      if (slv_resp_o.b_valid) begin
        `AXI_SET_B_STRUCT(slv_resp_o.b, mst_resps_i[b_idx].b)
      end else begin
        slv_resp_o.b = '0;
      end
    end


    always_comb begin
      slv_resp_o.ar_ready    = 1'b0;
      ar_valid        = 1'b0;
      lock_ar_valid_d = lock_ar_valid_q;
      load_ar_lock    = 1'b0;
      ar_push         = 1'b0;
      if (lock_ar_valid_q) begin
        ar_valid = 1'b1;
        if (ar_ready) begin
          slv_resp_o.ar_ready    = 1'b1;
          ar_push         = 1'b1;
          lock_ar_valid_d = 1'b0;
          load_ar_lock    = 1'b1;
        end
      end else begin
        if (!ar_id_cnt_full) begin
          if (slv_req_i.ar_valid && (!ar_select_occupied ||
             (slv_ar_select_i == lookup_ar_select))) begin
            ar_valid     = 1'b1;
            if (ar_ready) begin
              slv_resp_o.ar_ready = 1'b1;
              ar_push      = 1'b1;
            end else begin
              lock_ar_valid_d = 1'b1;
              load_ar_lock    = 1'b1;
            end
          end
        end
      end
    end

    `FFLARN(lock_ar_valid_q, lock_ar_valid_d, load_ar_lock, '0, clk_i, rst_ni)

    if (UniqueIds) begin : gen_unique_ids_ar
      assign lookup_ar_select = slv_ar_select_i;
      assign ar_select_occupied = 1'b0;
      assign ar_id_cnt_full = 1'b0;
    end else begin : gen_ar_id_counter
      axi_demux_id_counters #(
        .AxiIdBits         ( AxiLookBits    ),
        .CounterWidth      ( IdCounterWidth ),
        .mst_port_select_t ( select_t       )
      ) i_ar_id_counter (
        .clk_i                        ( clk_i                                       ),
        .rst_ni                       ( rst_ni                                      ),
        .lookup_axi_id_i              ( slv_req_i.ar.id[0+:AxiLookBits]             ),
        .lookup_mst_select_o          ( lookup_ar_select                            ),
        .lookup_mst_select_occupied_o ( ar_select_occupied                          ),
        .full_o                       ( ar_id_cnt_full                              ),
        .inject_axi_id_i              ( slv_req_i.aw.id[0+:AxiLookBits]             ),
        .inject_i                     ( atop_inject                                 ),
        .push_axi_id_i                ( slv_req_i.ar.id[0+:AxiLookBits]             ),
        .push_mst_select_i            ( slv_ar_select_i                             ),
        .push_i                       ( ar_push                                     ),
        .pop_axi_id_i                 ( slv_resp_o.r.id[0+:AxiLookBits]               ),
        .pop_i                        ( slv_resp_o.r_valid & slv_req_i.r_ready & slv_resp_o.r.last )
      );
    end


    logic [cf_math_pkg::idx_width(NoMstPorts)-1:0] r_idx;

    rr_arb_tree #(
      .NumIn    ( NoMstPorts ),
      .DataType ( logic   ),
      .AxiVldRdy( 1'b1       ),
      .LockIn   ( 1'b1       )
    ) i_r_mux (
      .clk_i  ( clk_i         ),
      .rst_ni ( rst_ni        ),
      .flush_i( 1'b0          ),
      .rr_i   ( '0            ),
      .req_i  ( mst_r_valids  ),
      .gnt_o  ( mst_r_readies ),
      .data_i ( '0            ),
      .gnt_i  ( slv_req_i.r_ready   ),
      .req_o  ( slv_resp_o.r_valid   ),
      .data_o (),
      .idx_o  ( r_idx              )
    );

    always_comb begin
      if (slv_resp_o.r_valid) begin
        `AXI_SET_R_STRUCT(slv_resp_o.r, mst_resps_i[r_idx].r)
      end else begin
        slv_resp_o.r = '0;
      end
    end

    assign ar_ready = ar_valid & mst_resps_i[slv_ar_select_i].ar_ready;
    assign aw_ready = aw_valid & mst_resps_i[slv_aw_select_i].aw_ready;

    always_comb begin
      mst_reqs_o  = '0;
      slv_resp_o.w_ready = 1'b0;
      w_cnt_down  = 1'b0;

      for (int unsigned i = 0; i < NoMstPorts; i++) begin
        mst_reqs_o[i].aw       = slv_req_i.aw;
        mst_reqs_o[i].aw_valid = 1'b0;
        if (aw_valid && (slv_aw_select_i == i)) begin
          mst_reqs_o[i].aw_valid = 1'b1;
        end

        mst_reqs_o[i].w       = slv_req_i.w;
        mst_reqs_o[i].w_valid = 1'b0;
        if (w_select_valid && (w_select == i)) begin
          mst_reqs_o[i].w_valid = slv_req_i.w_valid;
          slv_resp_o.w_ready           = mst_resps_i[i].w_ready;
          w_cnt_down            = slv_req_i.w_valid & mst_resps_i[i].w_ready & slv_req_i.w.last;
        end

        mst_reqs_o[i].b_ready = mst_b_readies[i];

        mst_reqs_o[i].ar       = slv_req_i.ar;
        mst_reqs_o[i].ar_valid = 1'b0;
        if (ar_valid && (slv_ar_select_i == i)) begin
          mst_reqs_o[i].ar_valid = 1'b1;
        end

        mst_reqs_o[i].r_ready = mst_r_readies[i];
      end
    end
    for (genvar i = 0; i < NoMstPorts; i++) begin : gen_b_channels
      assign mst_b_valids[i]       = mst_resps_i[i].b_valid;
      assign mst_r_valids[i]       = mst_resps_i[i].r_valid;
    end

  end
endmodule"
"module SEVEN #(parameter freq = 250, parameter CBITS = 8) (input clk, input rst, input [13:0] both7seg, output reg[6:0] segment);
	reg [CBITS-1:0] cnt;
	reg digit_select;

	always @(posedge clk) begin
		if(rst == 1) begin
			cnt = 0;
			digit_select = 0;
			segment = 0;
		end
		if(cnt < freq)
			cnt = cnt + 1;
		else begin
			cnt = 0;
			if(digit_select == 0) begin
				digit_select = 1;
				segment = both7seg[13:7];
			end
			else begin
				digit_select = 0;
				segment = both7seg[6:0];
			end
		end
	end
endmodule"	"module SEVEN_sva #(parameter freq = 250, parameter CBITS = 8) (input clk, input rst, input [13:0] both7seg, input logic[6:0] segment, input logic digit_select);
	p1: assert property (@(posedge clk) s_eventually rst == 1 || digit_select == 1);
	p2: assert property (@(posedge clk) s_eventually rst == 1 || digit_select == 0);
endmodule"	https://github.com/diffblue/hw-cbmc/blob/main/examples/Benchmarks/seven_seg_1.sv	"Assertion 1:
This assertion is to check the response type specified by the Resp parameter is one of the two valid error responses: RESP_DECERR (decode error) or RESP_SLVERR (slave error).
Assertion 2:
This assertion is to check that if ATOPs (atomic operation support) is disabled, all ATOP-related transactions received on slv_req_i.aw.atop are zero, meaning no ATOP transactions are allowed."	"module axi_err_slv #(
  parameter int unsigned          AxiIdWidth  = 0, 
  parameter type                  axi_req_t   = logic,
  parameter type                  axi_resp_t  = logic,
  parameter axi_pkg::resp_t       Resp        = axi_pkg::RESP_DECERR,
  parameter int unsigned          RespWidth   = 32'd64,       
  parameter logic [RespWidth-1:0] RespData    = 64'hCA11AB1EBADCAB1E,
  parameter bit                   ATOPs       = 1'b1,     
  parameter int unsigned          MaxTrans    = 1 
) (
  input  logic      clk_i, 
  input  logic      rst_ni,
  input  logic      test_i,

  input  axi_req_t  slv_req_i,
  output axi_resp_t slv_resp_o
);
  typedef logic [AxiIdWidth-1:0] id_t;
  typedef struct packed {
    id_t           id;
    axi_pkg::len_t len;
  } r_data_t;

  axi_req_t   err_req;
  axi_resp_t  err_resp;

  if (ATOPs) begin
    axi_atop_filter #(
      .AxiIdWidth       ( AxiIdWidth  ),
      .AxiMaxWriteTxns  ( MaxTrans    ),
      .axi_req_t        ( axi_req_t   ),
      .axi_resp_t       ( axi_resp_t  )
    ) i_atop_filter (
      .clk_i,
      .rst_ni,
      .slv_req_i  ( slv_req_i   ),
      .slv_resp_o ( slv_resp_o  ),
      .mst_req_o  ( err_req     ),
      .mst_resp_i ( err_resp    )
    );
  end else begin
    assign err_req    = slv_req_i;
    assign slv_resp_o = err_resp;
  end


  logic    w_fifo_full, w_fifo_empty;
  logic    w_fifo_push, w_fifo_pop;
  id_t     w_fifo_data;

  logic    b_fifo_full, b_fifo_empty;
  logic    b_fifo_push, b_fifo_pop;
  id_t     b_fifo_data;

  r_data_t r_fifo_inp;
  logic    r_fifo_full, r_fifo_empty;
  logic    r_fifo_push, r_fifo_pop;
  r_data_t r_fifo_data;

  logic    r_cnt_clear, r_cnt_en, r_cnt_load;
  axi_pkg::len_t r_current_beat;

  logic    r_busy_d, r_busy_q, r_busy_load;

  assign w_fifo_push        = err_req.aw_valid & ~w_fifo_full;
  assign err_resp.aw_ready  = ~w_fifo_full;

  fifo_v3 #(
    .FALL_THROUGH ( 1'b1      ),
    .DEPTH        ( MaxTrans  ),
    .dtype        ( id_t      )
  ) i_w_fifo (
    .clk_i      ( clk_i             ),
    .rst_ni     ( rst_ni            ),
    .flush_i    ( 1'b0              ),
    .testmode_i ( test_i            ),
    .full_o     ( w_fifo_full       ),
    .empty_o    ( w_fifo_empty      ),
    .usage_o    (                   ),
    .data_i     ( err_req.aw.id     ),
    .push_i     ( w_fifo_push       ),
    .data_o     ( w_fifo_data       ),
    .pop_i      ( w_fifo_pop        )
  );

  always_comb begin : proc_w_channel
    err_resp.w_ready  = 1'b0;
    w_fifo_pop        = 1'b0;
    b_fifo_push       = 1'b0;
    if (!w_fifo_empty && !b_fifo_full) begin
      
      err_resp.w_ready = 1'b1;
      
      if (err_req.w_valid && err_req.w.last) begin
        w_fifo_pop    = 1'b1;
        b_fifo_push   = 1'b1;
      end
    end
  end

  fifo_v3 #(
    .FALL_THROUGH ( 1'b0         ),
    .DEPTH        ( unsigned'(2) ), 
    .dtype        ( id_t         )
  ) i_b_fifo (
    .clk_i      ( clk_i        ),
    .rst_ni     ( rst_ni       ),
    .flush_i    ( 1'b0         ),
    .testmode_i ( test_i       ),
    .full_o     ( b_fifo_full  ),
    .empty_o    ( b_fifo_empty ),
    .usage_o    (              ),
    .data_i     ( w_fifo_data  ),
    .push_i     ( b_fifo_push  ),
    .data_o     ( b_fifo_data  ),
    .pop_i      ( b_fifo_pop   )
  );

  always_comb begin : proc_b_channel
    b_fifo_pop        = 1'b0;
    err_resp.b        = '0;
    err_resp.b.id     = b_fifo_data;
    err_resp.b.resp   = Resp;
    err_resp.b_valid  = 1'b0;
    if (!b_fifo_empty) begin
      err_resp.b_valid = 1'b1;
      b_fifo_pop = err_req.b_ready;
    end
  end

  assign r_fifo_push        = err_req.ar_valid & ~r_fifo_full;
  assign err_resp.ar_ready  = ~r_fifo_full;

  assign r_fifo_inp.id  = err_req.ar.id;
  assign r_fifo_inp.len = err_req.ar.len;

  fifo_v3 #(
    .FALL_THROUGH ( 1'b0      ),
    .DEPTH        ( MaxTrans  ),
    .dtype        ( r_data_t  )
  ) i_r_fifo (
    .clk_i     ( clk_i        ),
    .rst_ni    ( rst_ni       ),
    .flush_i   ( 1'b0         ),
    .testmode_i( test_i       ),
    .full_o    ( r_fifo_full  ),
    .empty_o   ( r_fifo_empty ),
    .usage_o   (              ),
    .data_i    ( r_fifo_inp   ),
    .push_i    ( r_fifo_push  ),
    .data_o    ( r_fifo_data  ),
    .pop_i     ( r_fifo_pop   )
  );

  always_comb begin : proc_r_channel
    r_busy_d    = r_busy_q;
    r_busy_load = 1'b0;
    r_fifo_pop  = 1'b0;
    r_cnt_clear = 1'b0;
    r_cnt_en    = 1'b0;
    r_cnt_load  = 1'b0;
    err_resp.r        = '0;
    err_resp.r.id     = r_fifo_data.id;
    err_resp.r.data   = RespData;
    err_resp.r.resp   = Resp;
    err_resp.r_valid  = 1'b0;
    if (r_busy_q) begin
      err_resp.r_valid = 1'b1;
      err_resp.r.last = (r_current_beat == '0);
      if (err_req.r_ready) begin
        r_cnt_en = 1'b1;
        if (r_current_beat == '0) begin
          r_busy_d    = 1'b0;
          r_busy_load = 1'b1;
          r_cnt_clear = 1'b1;
          r_fifo_pop  = 1'b1;
        end
      end
    end else begin
      if (!r_fifo_empty) begin
        r_busy_d    = 1'b1;
        r_busy_load = 1'b1;
        r_cnt_load  = 1'b1;
      end
    end
  end

  always_ff @(posedge clk_i, negedge rst_ni) begin
    if (!rst_ni) begin
      r_busy_q <= '0;
    end else if (r_busy_load) begin
      r_busy_q <= r_busy_d;
    end
  end

  counter #(
    .WIDTH     ($bits(axi_pkg::len_t))
  ) i_r_counter (
    .clk_i     ( clk_i           ),
    .rst_ni    ( rst_ni          ),
    .clear_i   ( r_cnt_clear     ),
    .en_i      ( r_cnt_en        ),
    .load_i    ( r_cnt_load      ),
    .down_i    ( 1'b1            ),
    .d_i       ( r_fifo_data.len ),
    .q_o       ( r_current_beat  ),
    .overflow_o(                 )
  );

endmodule"
"module uart_transmit #(localparam d_width = 4, localparam c_width = 3) (input clk, input rst, input tx_ena, input [d_width - 1: 0] tx_data, output reg tx, output reg tx_busy);
	reg [c_width-1:0] tx_cnt;
	reg tx_state;
	reg [d_width+1:0] tx_buffer;

	always @(posedge clk) begin
		if(rst == 1) begin
			tx_cnt = 0;
			tx = 1;
			tx_busy = 0;
			tx_state = 0;
		end
		if(tx_state == 0) begin
			if(tx_ena == 1) begin
				tx_buffer = {tx_data, 2'b01};
				tx_busy = 1;
				tx_cnt = 0;
				tx_state = 1;
			end
			else
				tx_busy = 0;
		end
		else if(tx_state == 1) begin
			if(tx_cnt < d_width+3) begin
				tx_state = 1;
				tx_cnt = tx_cnt + 1;
				tx_buffer = {1'b1, tx_buffer[d_width+1:1]};
			end
			else begin
				tx_cnt = 0;
				tx_state = 0;
			end
		end
		tx = tx_buffer[0];
	end
endmodule"	"module uart_transmit_sva #(localparam d_width = 4, localparam c_width = 3) (input clk, input rst, input tx_ena, input [d_width - 1: 0] tx_data, input reg tx, input reg tx_busy, input reg tx_state);
	
	p1: assert property (@(posedge clk) s_eventually rst == 1 ||  tx_state == 0);
  	// F G (rst = FALSE) -> G F (tx_state = FALSE)
endmodule"	https://github.com/diffblue/hw-cbmc/blob/main/examples/Benchmarks/uart_transmit_1.sv	"Assertion 1: 
This assertion is to check that the depth parameter, which specifies the number of FIFO slots, is a non-negative value.
"	"module axi_fifo #(
    parameter int unsigned Depth       = 32'd1,
    parameter bit          FallThrough = 1'b0,
    // AXI channel structs
    parameter type         aw_chan_t   = logic,
    parameter type         w_chan_t    = logic,
    parameter type         b_chan_t    = logic,
    parameter type         ar_chan_t   = logic,
    parameter type         r_chan_t    = logic,
    // AXI request & response structs
    parameter type         axi_req_t   = logic,
    parameter type         axi_resp_t  = logic
) (
    input  logic      clk_i, 
    input  logic      rst_ni,
    input  logic      test_i,
    input  axi_req_t  slv_req_i,
    output axi_resp_t slv_resp_o,
    output axi_req_t  mst_req_o,
    input  axi_resp_t mst_resp_i
);

  if (Depth == '0) begin : gen_no_fifo
    assign mst_req_o  = slv_req_i;
    assign slv_resp_o = mst_resp_i;
  end else begin : gen_axi_fifo
    logic aw_fifo_empty, ar_fifo_empty, w_fifo_empty, r_fifo_empty, b_fifo_empty;
    logic aw_fifo_full, ar_fifo_full, w_fifo_full, r_fifo_full, b_fifo_full;

    assign mst_req_o.aw_valid  = ~aw_fifo_empty;
    assign mst_req_o.ar_valid  = ~ar_fifo_empty;
    assign mst_req_o.w_valid   = ~w_fifo_empty;
    assign slv_resp_o.r_valid  = ~r_fifo_empty;
    assign slv_resp_o.b_valid  = ~b_fifo_empty;

    assign slv_resp_o.aw_ready = ~aw_fifo_full;
    assign slv_resp_o.ar_ready = ~ar_fifo_full;
    assign slv_resp_o.w_ready  = ~w_fifo_full;
    assign mst_req_o.r_ready   = ~r_fifo_full;
    assign mst_req_o.b_ready   = ~b_fifo_full;

    fifo_v3 #(
        .dtype(aw_chan_t),
        .DEPTH(Depth),
        .FALL_THROUGH(FallThrough)
    ) i_aw_fifo (
        .clk_i,
        .rst_ni,
        .flush_i   (1'b0),
        .testmode_i(test_i),
        .full_o    (aw_fifo_full),
        .empty_o   (aw_fifo_empty),
        .usage_o   (),
        .data_i    (slv_req_i.aw),
        .push_i    (slv_req_i.aw_valid && slv_resp_o.aw_ready),
        .data_o    (mst_req_o.aw),
        .pop_i     (mst_req_o.aw_valid && mst_resp_i.aw_ready)
    );
    fifo_v3 #(
        .dtype(ar_chan_t),
        .DEPTH(Depth),
        .FALL_THROUGH(FallThrough)
    ) i_ar_fifo (
        .clk_i,
        .rst_ni,
        .flush_i   (1'b0),
        .testmode_i(test_i),
        .full_o    (ar_fifo_full),
        .empty_o   (ar_fifo_empty),
        .usage_o   (),
        .data_i    (slv_req_i.ar),
        .push_i    (slv_req_i.ar_valid && slv_resp_o.ar_ready),
        .data_o    (mst_req_o.ar),
        .pop_i     (mst_req_o.ar_valid && mst_resp_i.ar_ready)
    );
    fifo_v3 #(
        .dtype(w_chan_t),
        .DEPTH(Depth),
        .FALL_THROUGH(FallThrough)
    ) i_w_fifo (
        .clk_i,
        .rst_ni,
        .flush_i   (1'b0),
        .testmode_i(test_i),
        .full_o    (w_fifo_full),
        .empty_o   (w_fifo_empty),
        .usage_o   (),
        .data_i    (slv_req_i.w),
        .push_i    (slv_req_i.w_valid && slv_resp_o.w_ready),
        .data_o    (mst_req_o.w),
        .pop_i     (mst_req_o.w_valid && mst_resp_i.w_ready)
    );
    fifo_v3 #(
        .dtype(r_chan_t),
        .DEPTH(Depth),
        .FALL_THROUGH(FallThrough)
    ) i_r_fifo (
        .clk_i,
        .rst_ni,
        .flush_i   (1'b0),
        .testmode_i(test_i),
        .full_o    (r_fifo_full),
        .empty_o   (r_fifo_empty),
        .usage_o   (),
        .data_i    (mst_resp_i.r),
        .push_i    (mst_resp_i.r_valid && mst_req_o.r_ready),
        .data_o    (slv_resp_o.r),
        .pop_i     (slv_resp_o.r_valid && slv_req_i.r_ready)
    );
    fifo_v3 #(
        .dtype(b_chan_t),
        .DEPTH(Depth),
        .FALL_THROUGH(FallThrough)
    ) i_b_fifo (
        .clk_i,
        .rst_ni,
        .flush_i   (1'b0),
        .testmode_i(test_i),
        .full_o    (b_fifo_full),
        .empty_o   (b_fifo_empty),
        .usage_o   (),
        .data_i    (mst_resp_i.b),
        .push_i    (mst_resp_i.b_valid && mst_req_o.b_ready),
        .data_o    (slv_resp_o.b),
        .pop_i     (slv_resp_o.b_valid && slv_req_i.b_ready)
    );
  end

endmodule"
"module VGA #(localparam  size = 1, localparam h_bits = 7, localparam v_bits = 5) (input clk, input rst, output reg disp_ena, output reg n_blank, output reg n_sync, output reg [h_bits-1:0] col, output reg [v_bits-1:0] row);

	localparam h_pixels = 50*size;
	localparam h_pulse = 5*size;
	localparam h_bp = 8*size;
	localparam h_fp = 3*size;
	localparam h_pol = 0;

	localparam v_pixels =  25*size;
	localparam v_pulse = size;
	localparam v_bp = 1*size;
	localparam v_fp = size;
	localparam v_pol = 1;

	localparam h_period = h_pulse + h_bp + h_pixels + h_fp;
	localparam v_period = v_pulse + v_bp + v_pixels + v_fp;

	reg [h_bits-1:0] h_cnt;
	reg [v_bits-1:0] v_cnt;
	reg h_sync;
	reg v_sync;
	always @(posedge clk) begin
		if(rst == 1) begin
			h_cnt = 0;
			v_cnt = 0;
			h_sync = ~h_sync;
			v_sync = ~v_sync;
			disp_ena = 0;
			col = 0;
			row = 0;
		end
		else begin
			if(h_cnt < h_period - 1)
				h_cnt = h_cnt + 1;
			else begin
				h_cnt = 0;
				if(v_cnt < v_period - 1)
					v_cnt = v_cnt + 1;
				else
					v_cnt = 0;
			end
			if((h_cnt < (h_pixels + h_fp)) | (h_cnt >= (h_pixels + h_fp + h_pulse)))
				h_sync = ~h_sync;
			else
				h_sync = h_pol;

			if((v_cnt < (v_pixels + v_fp)) | (v_cnt >= (v_pixels + v_fp + v_pulse)))
				v_sync = ~v_sync;
			else
				v_sync = v_pol;

			if(h_cnt < h_pixels)
				col = h_cnt;

			if(v_cnt < v_pixels)
				row = v_cnt;

			if(h_cnt < h_pixels & v_cnt < v_pixels)
				disp_ena = 1;
			else
				disp_ena = 0;
		end
	end
endmodule"	"module VGA_sva #(localparam  size = 1, localparam h_bits = 7, localparam v_bits = 5) (input clk, input rst, input reg disp_ena, input reg n_blank, input reg n_sync, input reg [h_bits-1:0] col, input reg [v_bits-1:0] row);

	
	p1: assert property  (@(posedge clk) s_eventually rst == 1 || disp_ena == 1);
  	// F G !rst -> G F disp_ena
endmodule"	https://github.com/diffblue/hw-cbmc/blob/main/examples/Benchmarks/vga_1.sv	"Assertion 1-4:
These assertions check that the ADDR_WIDTH, DATA_WIDTH, ID_WIDTH, and USER_WIDTH parameters are each greater than zero, ensuring they are properly defined.
Assertion 5-8:
These assertions ensure that the slave interface (slv) has the same width definitions as specified by the module parameters.
Assertion 9-12:
These assertions check that the master interface (mst) definitions match the module’s specified ADDR_WIDTH, DATA_WIDTH, ID_WIDTH, and USER_WIDTH parameters.
"	"module axi_fifo_intf #(
    parameter int unsigned ADDR_WIDTH = 0,  // The address width.
    parameter int unsigned DATA_WIDTH = 0,  // The data width.
    parameter int unsigned ID_WIDTH = 0,  // The ID width.
    parameter int unsigned USER_WIDTH = 0,  // The user data width.
    parameter int unsigned DEPTH = 0,  // The number of FiFo slots.
    parameter int unsigned FALL_THROUGH = 0  // FiFo in fall-through mode
) (
    input logic    clk_i,
    input logic    rst_ni,
    input logic    test_i,
    AXI_BUS.Slave  slv,
    AXI_BUS.Master mst
);

  typedef logic [ID_WIDTH-1:0] id_t;
  typedef logic [ADDR_WIDTH-1:0] addr_t;
  typedef logic [DATA_WIDTH-1:0] data_t;
  typedef logic [DATA_WIDTH/8-1:0] strb_t;
  typedef logic [USER_WIDTH-1:0] user_t;

  `AXI_TYPEDEF_AW_CHAN_T(aw_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_W_CHAN_T(w_chan_t, data_t, strb_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(b_chan_t, id_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(ar_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(r_chan_t, data_t, id_t, user_t)
  `AXI_TYPEDEF_REQ_T(axi_req_t, aw_chan_t, w_chan_t, ar_chan_t)
  `AXI_TYPEDEF_RESP_T(axi_resp_t, b_chan_t, r_chan_t)

  axi_req_t slv_req, mst_req;
  axi_resp_t slv_resp, mst_resp;

  `AXI_ASSIGN_TO_REQ(slv_req, slv)
  `AXI_ASSIGN_FROM_RESP(slv, slv_resp)

  `AXI_ASSIGN_FROM_REQ(mst, mst_req)
  `AXI_ASSIGN_TO_RESP(mst_resp, mst)

  axi_fifo #(
      .Depth      (DEPTH),
      .FallThrough(FALL_THROUGH),
      .aw_chan_t  (aw_chan_t),
      .w_chan_t   (w_chan_t),
      .b_chan_t   (b_chan_t),
      .ar_chan_t  (ar_chan_t),
      .r_chan_t   (r_chan_t),
      .axi_req_t  (axi_req_t),
      .axi_resp_t (axi_resp_t)
  ) i_axi_fifo (
      .clk_i,
      .rst_ni,
      .test_i,
      .slv_req_i (slv_req),
      .slv_resp_o(slv_resp),
      .mst_req_o (mst_req),
      .mst_resp_i(mst_resp)
  );

endmodule"
"module arb2(clk, rst, req1, req2, gnt1, gnt2);

input clk, rst;
input req1, req2;
output gnt1, gnt2;

reg state;
reg gnt1, gnt2;

always @ (posedge clk or posedge rst)
	if (rst)
		state <= 0;
	else
		state <= gnt1;

always @ (*)
	if (state)
	begin
		gnt1 = req1 & ~req2;
		gnt2 = req2;
	end
	else
	begin
		gnt1 = req1;
		gnt2 = req2 & ~req1;
	end

endmodule"	"module arb2_sva(
input gnt1, gnt2,
input state,
input clk, rst,
input req1,
input req2
);


property a3;
@(posedge clk) (state == 1 & req2 == 1) |-> (gnt1 == 0);
endproperty
assert_a3: assert property(a3);

property a1;
@(posedge clk) (req1 == 1 & state == 0) |-> (gnt1 == 1);
endproperty
assert_a1: assert property(a1);

property a2;
@(posedge clk) (req1 == 0) |-> (gnt1 == 0);
endproperty
assert_a2: assert property(a2);

property a0;
@(posedge clk) (req1 == 1 & req2 == 0) |-> (gnt1 == 1);
endproperty
assert_a0: assert property(a0);

property a5;
@(posedge clk) (req1 == 1 & state == 0) |-> (gnt2 == 0);
endproperty
assert_a5: assert property(a5);

property a7;
@(posedge clk) (req2 == 1 & state == 1) |-> (gnt2 == 1);
endproperty
assert_a7: assert property(a7);

property a4;
@(posedge clk) (req2 == 0) |-> (gnt2 == 0);
endproperty
assert_a4: assert property(a4);

property a6;
@(posedge clk) (req2 == 1 & req1 == 0) |-> (gnt2 == 1);
endproperty
assert_a6: assert property(a6);

endmodule"	https://github.com/achieve-lab/assertion_data_for_LLM/tree/NIPS_2024/Jasper_results/Arbiter	"Assertion 1:
NoBus > 0: Ensures there is at least one bus to process (NoBus should be greater than zero). If not, it stops the simulation with an error, as the module needs at least one input bus.
Assertion 2:
PreIdWidth Calculation: Checks that PreIdWidth (the number of bits added as a prefix to the ID) is correctly calculated as the difference between the master port's ID width and the slave port's ID width. If not, $fatal stops the simulation. This calculation is crucial to ensure proper ID prepending.
Assertion 3:
Master ID Width Validation: Ensures the master port’s ID width is greater than the slave port’s ID width, confirming there’s enough space to prepend the ID. This prevents configuration errors that could lead to truncated IDs.
Assertion 4-8:
Ensures the lower bits of mst_aw_chans_o[0].id match slv_aw_chans_i[0].id. This verifies that only the pre_id_i bits were prepended, leaving the original slave ID intact in the lower bits.
Assertion 9:
Ensures the lower bits of the mst_b_chans_i[0].id match slv_b_chans_o[0].id, verifying that the pre_id_i bits were correctly removed in the B channel.
Assertion 10:
Similar to the AW channel, this assertion ensures that only pre_id_i was prepended, leaving the original slave ID bits intact.
Assertion 11:
Confirms that the lower bits of mst_r_chans_i[0].id match slv_r_chans_o[0].id, indicating successful removal of the prepended ID.

"	"module axi_id_prepend #(
  parameter int unsigned NoBus             = 1,     // Can take multiple axi busses
  parameter int unsigned AxiIdWidthSlvPort = 4,     // AXI ID Width of the Slave Ports
  parameter int unsigned AxiIdWidthMstPort = 6,     // AXI ID Width of the Master Ports
  parameter type         slv_aw_chan_t     = logic, // AW Channel Type for slv port
  parameter type         slv_w_chan_t      = logic, //  W Channel Type for slv port
  parameter type         slv_b_chan_t      = logic, //  B Channel Type for slv port
  parameter type         slv_ar_chan_t     = logic, // AR Channel Type for slv port
  parameter type         slv_r_chan_t      = logic, //  R Channel Type for slv port
  parameter type         mst_aw_chan_t     = logic, // AW Channel Type for mst port
  parameter type         mst_w_chan_t      = logic, //  W Channel Type for mst port
  parameter type         mst_b_chan_t      = logic, //  B Channel Type for mst port
  parameter type         mst_ar_chan_t     = logic, // AR Channel Type for mst port
  parameter type         mst_r_chan_t      = logic, //  R Channel Type for mst port
  // DEPENDENT PARAMETER DO NOT OVERWRITE!
  parameter int unsigned PreIdWidth        = AxiIdWidthMstPort - AxiIdWidthSlvPort
) (
  input  logic [PreIdWidth-1:0] pre_id_i,
  input  slv_aw_chan_t [NoBus-1:0] slv_aw_chans_i,
  input  logic         [NoBus-1:0] slv_aw_valids_i,
  output logic         [NoBus-1:0] slv_aw_readies_o,
  input  slv_w_chan_t  [NoBus-1:0] slv_w_chans_i,
  input  logic         [NoBus-1:0] slv_w_valids_i,
  output logic         [NoBus-1:0] slv_w_readies_o,
  output slv_b_chan_t  [NoBus-1:0] slv_b_chans_o,
  output logic         [NoBus-1:0] slv_b_valids_o,
  input  logic         [NoBus-1:0] slv_b_readies_i,
  input  slv_ar_chan_t [NoBus-1:0] slv_ar_chans_i,
  input  logic         [NoBus-1:0] slv_ar_valids_i,
  output logic         [NoBus-1:0] slv_ar_readies_o,
  output slv_r_chan_t  [NoBus-1:0] slv_r_chans_o,
  output logic         [NoBus-1:0] slv_r_valids_o,
  input  logic         [NoBus-1:0] slv_r_readies_i,
  output mst_aw_chan_t [NoBus-1:0] mst_aw_chans_o,
  output logic         [NoBus-1:0] mst_aw_valids_o,
  input  logic         [NoBus-1:0] mst_aw_readies_i,
  output mst_w_chan_t  [NoBus-1:0] mst_w_chans_o,
  output logic         [NoBus-1:0] mst_w_valids_o,
  input  logic         [NoBus-1:0] mst_w_readies_i,
  input  mst_b_chan_t  [NoBus-1:0] mst_b_chans_i,
  input  logic         [NoBus-1:0] mst_b_valids_i,
  output logic         [NoBus-1:0] mst_b_readies_o,
  output mst_ar_chan_t [NoBus-1:0] mst_ar_chans_o,
  output logic         [NoBus-1:0] mst_ar_valids_o,
  input  logic         [NoBus-1:0] mst_ar_readies_i,
  input  mst_r_chan_t  [NoBus-1:0] mst_r_chans_i,
  input  logic         [NoBus-1:0] mst_r_valids_i,
  output logic         [NoBus-1:0] mst_r_readies_o
);

  for (genvar i = 0; i < NoBus; i++) begin : gen_id_prepend
    if (PreIdWidth == 0) begin : gen_no_prepend
      assign mst_aw_chans_o[i] = slv_aw_chans_i[i];
      assign mst_ar_chans_o[i] = slv_ar_chans_i[i];
    end else begin : gen_prepend
      always_comb begin
        mst_aw_chans_o[i] = slv_aw_chans_i[i];
        mst_ar_chans_o[i] = slv_ar_chans_i[i];
        mst_aw_chans_o[i].id = {pre_id_i, slv_aw_chans_i[i].id[AxiIdWidthSlvPort-1:0]};
        mst_ar_chans_o[i].id = {pre_id_i, slv_ar_chans_i[i].id[AxiIdWidthSlvPort-1:0]};
      end
    end
    assign slv_b_chans_o[i] = mst_b_chans_i[i];
    assign slv_r_chans_o[i] = mst_r_chans_i[i];
  end


  assign mst_w_chans_o    = slv_w_chans_i;
  assign mst_aw_valids_o  = slv_aw_valids_i;
  assign slv_aw_readies_o = mst_aw_readies_i;
  assign mst_w_valids_o   = slv_w_valids_i;
  assign slv_w_readies_o  = mst_w_readies_i;
  assign slv_b_valids_o   = mst_b_valids_i;
  assign mst_b_readies_o  = slv_b_readies_i;
  assign mst_ar_valids_o  = slv_ar_valids_i;
  assign slv_ar_readies_o = mst_ar_readies_i;
  assign slv_r_valids_o   = mst_r_valids_i;
  assign mst_r_readies_o  = slv_r_readies_i;


endmodule"
"//////////////////////////////////////////////////////////////////
////
////
//// 	AES CORE BLOCK
////
////
////
//// This file is part of the APB to I2C project
////
//// http://www.opencores.org/cores/apbi2c/
////
////
////
//// Description
////
//// Implementation of APB IP core according to
////
//// aes128_spec IP core specification document.
////
////
////
//// To Do: Things are right here but always all block can suffer changes
////
////
////
////
////
//// Author(s): - Felipe Fernandes Da Costa, fefe2560@gmail.com
////		  Julio Cesar 
////
///////////////////////////////////////////////////////////////// 
////
////
//// Copyright (C) 2009 Authors and OPENCORES.ORG
////
////
////
//// This source file may be used and distributed without
////
//// restriction provided that this copyright statement is not
////
//// removed from the file and that any derivative work contains
//// the original copyright notice and the associated disclaimer.
////
////
//// This source file is free software; you can redistribute it
////
//// and/or modify it under the terms of the GNU Lesser General
////
//// Public License as published by the Free Software Foundation;
//// either version 2.1 of the License, or (at your option) any
////
//// later version.
////
////
////
//// This source is distributed in the hope that it will be
////
//// useful, but WITHOUT ANY WARRANTY; without even the implied
////
//// warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR
////
//// PURPOSE. See the GNU Lesser General Public License for more
//// details.
////
////
////
//// You should have received a copy of the GNU Lesser General
////
//// Public License along with this source; if not, download it
////
//// from http://www.opencores.org/lgpl.shtml
////
////
///////////////////////////////////////////////////////////////////
module control_unit
(
	output reg [ 2:0] sbox_sel,
	output reg [ 1:0] rk_sel,
	output reg [ 1:0] key_out_sel,
	output reg [ 1:0] col_sel,
	output reg [ 3:0] key_en,
	output reg [ 3:0] col_en,
	output     [ 3:0] round,
	output reg bypass_rk,
	output reg bypass_key_en,
	output reg key_sel,
	output reg iv_cnt_en,
	output reg iv_cnt_sel,
	output reg key_derivation_en,
	output end_comp,
	output key_init,
	output key_gen,
	output mode_ctr,
	output mode_cbc,
	output last_round,
  output encrypt_decrypt,	
	input [1:0] operation_mode,
	input [1:0] aes_mode,
	input start,
	input disable_core,
	input clk,
	input rst_n
);
//`include ""include/host_interface.vh""
//`include ""include/control_unit_params.vh""

//=====================================================================================
// Memory Mapped Registers Address
//=====================================================================================
localparam AES_CR    = 4'd00;
localparam AES_SR    = 4'd01;
localparam AES_DINR  = 4'd02;
localparam AES_DOUTR = 4'd03;
localparam AES_KEYR0 = 4'd04;
localparam AES_KEYR1 = 4'd05;
localparam AES_KEYR2 = 4'd06;
localparam AES_KEYR3 = 4'd07;
localparam AES_IVR0  = 4'd08;
localparam AES_IVR1  = 4'd09;
localparam AES_IVR2  = 4'd10;
localparam AES_IVR3  = 4'd11;

//=============================================================================
// Operation Modes
//=============================================================================
localparam ENCRYPTION     = 2'b00;
localparam KEY_DERIVATION = 2'b01;
localparam DECRYPTION     = 2'b10;
localparam DECRYP_W_DERIV = 2'b11;

//=============================================================================
// AES Modes
//=============================================================================
localparam ECB = 2'b00;
localparam CBC = 2'b01;
localparam CTR = 2'b10;

//=============================================================================
// SBOX SEL
//=============================================================================
localparam COL_0 = 3'b000;
localparam COL_1 = 3'b001;
localparam COL_2 = 3'b010;
localparam COL_3 = 3'b011;
localparam G_FUNCTION = 3'b100;

//=============================================================================
// RK_SEL
//=============================================================================
localparam COL        = 2'b00;
localparam MIXCOL_IN  = 2'b01;
localparam MIXCOL_OUT = 2'b10;

//=============================================================================
// KEY_OUT_SEL
//=============================================================================
localparam KEY_0 = 2'b00;
localparam KEY_1 = 2'b01;
localparam KEY_2 = 2'b10;
localparam KEY_3 = 2'b11;

//=============================================================================
// COL_SEL
//=============================================================================
localparam SHIFT_ROWS = 2'b00;
localparam ADD_RK_OUT = 2'b01;
localparam INPUT      = 2'b10;

//=============================================================================
// KEY_SEL
//=============================================================================
localparam KEY_HOST = 1'b0;
localparam KEY_OUT  = 1'b1;

//=============================================================================
// KEY_EN
//=============================================================================
localparam KEY_DIS  = 4'b0000;
localparam EN_KEY_0 = 4'b0001;
localparam EN_KEY_1 = 4'b0010;
localparam EN_KEY_2 = 4'b0100;
localparam EN_KEY_3 = 4'b1000;
localparam KEY_ALL  = 4'b1111;

//=============================================================================
// COL_EN
//=============================================================================
localparam COL_DIS  = 4'b0000;
localparam EN_COL_0 = 4'b0001;
localparam EN_COL_1 = 4'b0010;
localparam EN_COL_2 = 4'b0100;
localparam EN_COL_3 = 4'b1000;
localparam COL_ALL  = 4'b1111;

//=============================================================================
// IV_CNT_SEL
//=============================================================================
localparam IV_CNT = 1'b1;
localparam IV_BUS = 1'b0;

//=============================================================================
// ENABLES
//=============================================================================
localparam ENABLE = 1'b1;
localparam DISABLE = 1'b0;

localparam NUMBER_ROUND      = 4'd10;
localparam NUMBER_ROUND_INC  = 4'd11;
localparam INITIAL_ROUND     = 4'd00;

//=============================================================================
// FSM STATES
//=============================================================================
localparam IDLE        = 4'd00;
localparam ROUND0_COL0 = 4'd01;
localparam ROUND0_COL1 = 4'd02;
localparam ROUND0_COL2 = 4'd03;
localparam ROUND0_COL3 = 4'd04;
localparam ROUND_KEY0  = 4'd05;
localparam ROUND_COL0  = 4'd06;
localparam ROUND_COL1  = 4'd07;
localparam ROUND_COL2  = 4'd08;
localparam ROUND_COL3  = 4'd09;
localparam READY       = 4'd10;
localparam GEN_KEY0    = 4'd11;
localparam GEN_KEY1    = 4'd12;
localparam GEN_KEY2    = 4'd13;
localparam GEN_KEY3    = 4'd14;
localparam NOP         = 4'd15;

reg [3:0] state, next_state;
reg [3:0] rd_count;

reg rd_count_en;
//reg end_aes_pp1, end_aes_pp2;
wire op_key_derivation;
wire first_round;
wire [1:0] op_mode;
wire enc_dec;

// State Flops Definition
always @(posedge clk or negedge rst_n)
	begin
		if(!rst_n)
			state <= IDLE;
		else
			if(disable_core)
				state <= IDLE;
			else
				state <= next_state;
	end

assign encrypt_decrypt = (op_mode == ENCRYPTION || op_mode == KEY_DERIVATION || state == GEN_KEY0   
			  ||   state == GEN_KEY1       ||state == GEN_KEY2   ||   state == GEN_KEY3       );

assign enc_dec = encrypt_decrypt | mode_ctr;
assign key_gen = (state == ROUND_KEY0);

assign op_key_derivation = (op_mode == KEY_DERIVATION);

assign mode_ctr = (aes_mode == CTR);
assign mode_cbc = (aes_mode == CBC);

assign key_init = start;

assign op_mode = (mode_ctr) ? ENCRYPTION : operation_mode;

// Next State Logic
always @(*)
	begin
		next_state = state;
		case(state)
			IDLE:
				begin
					if(!start)
						next_state = IDLE;
					else
						case(op_mode)
							ENCRYPTION    : next_state = ROUND0_COL0;
							DECRYPTION    : next_state = ROUND0_COL3;
							KEY_DERIVATION: next_state = GEN_KEY0;
							DECRYP_W_DERIV: next_state = GEN_KEY0;
							default       : next_state = IDLE;
						endcase
				end
			ROUND0_COL0:
				begin
					next_state = (enc_dec) ? ROUND0_COL1 : ROUND_KEY0; 
				end
			ROUND0_COL1:
				begin
					next_state = (enc_dec) ? ROUND0_COL2 : ROUND0_COL0;
				end
			ROUND0_COL2:
				begin
					next_state = (enc_dec) ? ROUND0_COL3 : ROUND0_COL1;
				end
			ROUND0_COL3:
				begin
					next_state = (enc_dec) ? ROUND_KEY0 : ROUND0_COL2;
				end
			ROUND_KEY0 :
				begin
					if(!first_round)
						begin
							next_state = (last_round) ? READY : NOP;
						end
					else
						begin
							next_state = (enc_dec) ? ROUND_COL0 : ROUND_COL3;
						end
				end
			NOP        :
				begin
					next_state = (enc_dec) ? ROUND_COL0 : ROUND_COL3;
				end
			ROUND_COL0 :
				begin
					next_state = (enc_dec) ? ROUND_COL1 : ROUND_KEY0;
				end
			ROUND_COL1 :
				begin
					next_state = (enc_dec) ? ROUND_COL2 : ROUND_COL0;
				end
			ROUND_COL2 :
				begin
					next_state = (enc_dec) ? ROUND_COL3 : ROUND_COL1;
				end
			ROUND_COL3 :
				begin
					if(last_round && enc_dec)
						next_state = READY;
					else
					next_state = (enc_dec) ? ROUND_KEY0 : ROUND_COL2;
				end
			GEN_KEY0   :
				begin
					next_state = GEN_KEY1;
				end
			GEN_KEY1   :
				begin
					next_state = GEN_KEY2;
				end
			GEN_KEY2   :
				begin
					next_state = GEN_KEY3;
				end
			GEN_KEY3   :
				begin
					if(last_round)
						next_state = (op_key_derivation) ? READY : ROUND0_COL3;
					else
						next_state = GEN_KEY0;
				end
			READY      :
				begin
					next_state = IDLE;
				end
		endcase
	end
 
       
// Output Logic
assign end_comp = (state == READY)?ENABLE:DISABLE;

/*
always @(posedge clk, negedge rst_n)
begin
		if(!rst_n)
		begin
			end_aes_pp1 <= 1'b0;
			end_aes_pp2 <= 1'b0; 
			end_comp <= 1'b0;
		end
		else
			if(state == READY)
			begin
				end_aes_pp1 <= ENABLE;
				//end_aes_pp2 <= end_aes_pp1;
				end_comp <= end_aes_pp1 ;
			end
			else
			begin
				end_aes_pp1 <= DISABLE;
				//end_aes_pp2 <= end_aes_pp1;
				end_comp <= end_aes_pp1 ;
			end

end
*/
always @(*)
	begin
		sbox_sel = COL_0;
		rk_sel = COL;
		bypass_rk = DISABLE;
		key_out_sel = KEY_0;
		col_sel = INPUT;
		key_sel = KEY_HOST;
		key_en = KEY_DIS;
		col_en = COL_DIS;
		rd_count_en = DISABLE;
		iv_cnt_en = DISABLE;
		iv_cnt_sel = IV_BUS;
		bypass_key_en = DISABLE;
		key_derivation_en = DISABLE;
		//end_comp = DISABLE;
		case(state)
			ROUND0_COL0:
				begin
					sbox_sel = COL_0;
					rk_sel   = COL;
					bypass_rk = ENABLE;
					bypass_key_en = ENABLE;
					key_out_sel = KEY_0;
					col_sel = (enc_dec) ? ADD_RK_OUT : SHIFT_ROWS;
					col_en =  (enc_dec) ? EN_COL_0 : COL_ALL;
				end
			ROUND0_COL1:
				begin
					sbox_sel = COL_1;
					rk_sel   = COL;
					bypass_rk = ENABLE;
					bypass_key_en = ENABLE;
					key_out_sel = KEY_1;
					col_sel = ADD_RK_OUT;
					col_en = EN_COL_1;
					if(!enc_dec)
						begin
							key_sel = KEY_OUT;
							key_en =  EN_KEY_1;
						end
				end
			ROUND0_COL2:
				begin
					sbox_sel = COL_2;
					rk_sel   = COL;
					bypass_rk = ENABLE;
					bypass_key_en = ENABLE;
					key_out_sel = KEY_2;
					col_sel = ADD_RK_OUT;
					col_en = EN_COL_2;
					if(!enc_dec)
						begin
							key_sel = KEY_OUT;
							key_en =  EN_KEY_2;
						end
				end
			ROUND0_COL3:
				begin
					sbox_sel = COL_3;
					rk_sel   = COL;
					bypass_key_en = ENABLE;
					key_out_sel = KEY_3;
					col_sel = (enc_dec) ? SHIFT_ROWS : ADD_RK_OUT;
					col_en =  (enc_dec) ? COL_ALL : EN_COL_3;
					bypass_rk = ENABLE;
					if(!enc_dec)
					begin
							key_sel = KEY_OUT;
							key_en =  EN_KEY_3;
					end
				end
			ROUND_KEY0:
				begin
					sbox_sel = G_FUNCTION;
					key_sel = KEY_OUT;
					key_en = EN_KEY_0;
					rd_count_en = ENABLE;
				end
			ROUND_COL0:
				begin
					sbox_sel = COL_0;
					rk_sel = (last_round) ? MIXCOL_IN : MIXCOL_OUT;
					key_out_sel = KEY_0;
					key_sel = KEY_OUT;

					if(enc_dec)
						key_en = EN_KEY_1;
					if((mode_cbc && last_round && !enc_dec) || (mode_ctr && last_round))
						col_sel = INPUT;
					else
						begin
							if(!enc_dec)
								col_sel = (last_round) ? ADD_RK_OUT : SHIFT_ROWS;
							else
								col_sel = ADD_RK_OUT;
						end
					if(enc_dec)
						col_en = EN_COL_0;
					else
						col_en = (last_round) ? EN_COL_0 : COL_ALL;
				end
			ROUND_COL1:
				begin
					sbox_sel = COL_1;
					rk_sel   = (last_round) ? MIXCOL_IN : MIXCOL_OUT;
					key_out_sel = KEY_1;
					key_sel = KEY_OUT;
					if(enc_dec)
						key_en = EN_KEY_2;
					else
						key_en = EN_KEY_1;
					if((mode_cbc && last_round && !enc_dec) || (mode_ctr && last_round))
						col_sel = INPUT;
					else
						col_sel = ADD_RK_OUT;
					col_en = EN_COL_1;
				end
			ROUND_COL2:
				begin
					sbox_sel = COL_2;
					rk_sel   = (last_round) ? MIXCOL_IN : MIXCOL_OUT;
					key_out_sel = KEY_2;
					key_sel = KEY_OUT;
					if(enc_dec)
						key_en = EN_KEY_3;
					else
						key_en = EN_KEY_2;
					if((mode_cbc && last_round && !enc_dec) || (mode_ctr && last_round))
						col_sel = INPUT;
					else
						col_sel = ADD_RK_OUT;
					col_en = EN_COL_2;
				end
			ROUND_COL3:
				begin
					sbox_sel = COL_3;
					rk_sel   = (last_round) ? MIXCOL_IN : MIXCOL_OUT;
					key_out_sel = KEY_3;
					key_sel = KEY_OUT;
					if(!enc_dec)
						key_en = EN_KEY_3;
					if((mode_cbc && last_round && !enc_dec) || (mode_ctr && last_round))
						col_sel = INPUT;
					else
						begin
							if(enc_dec)
								col_sel = (last_round) ? ADD_RK_OUT : SHIFT_ROWS;
							else
								col_sel = ADD_RK_OUT;
						end
					if(enc_dec)
						col_en = (last_round) ? EN_COL_3 : COL_ALL;
					else
						col_en = EN_COL_3;
					if(mode_ctr && last_round)
						begin
							iv_cnt_en = ENABLE;
							iv_cnt_sel = IV_CNT;
						end
				end
			GEN_KEY0:
				begin
					sbox_sel = G_FUNCTION;
					rd_count_en = ENABLE;
				end
			GEN_KEY1:
				begin
					key_en = EN_KEY_1 | EN_KEY_0; //Enable key 0 AND key 1
					key_sel = KEY_OUT;
					bypass_key_en = ENABLE;
				end
			GEN_KEY2:
				begin
					key_en = EN_KEY_2;
					key_sel = KEY_OUT;
					bypass_key_en = ENABLE;
				end
			GEN_KEY3:
				begin
					key_en = EN_KEY_3;
					key_sel = KEY_OUT;
					bypass_key_en = ENABLE;
				end
			READY:
				begin
					//end_comp = ENABLE;
					if(op_mode == KEY_DERIVATION)
						key_derivation_en = ENABLE;
				end
		endcase
	end

// Round Counter
always @(posedge clk or negedge rst_n)
	begin
		if(!rst_n)
			rd_count <= INITIAL_ROUND;
		else
			if(state == IDLE || (state == GEN_KEY3 && last_round))
				rd_count <= INITIAL_ROUND;
			else 
				if(rd_count_en)
					rd_count <= rd_count + 1'b1;
	end

assign round = rd_count;
assign first_round = (rd_count == INITIAL_ROUND);
assign last_round  = (rd_count == NUMBER_ROUND || rd_count == NUMBER_ROUND_INC);

endmodule"	"
module control_unit_sva(
        input  [2:0] sbox_sel,
        input  [1:0] rk_sel,
        input  [1:0] key_out_sel,
        input  [1:0] col_sel,
        input  [3:0] key_en,
        input  [3:0] col_en,
        input  [3:0] round,
        input  bypass_rk,
        input  bypass_key_en,
        input  key_sel,
        input  iv_cnt_en,
        input  iv_cnt_sel,
        input  key_derivation_en,
        input end_comp,
        input key_init,
        input key_gen,
        input mode_ctr,
        input mode_cbc,
        input last_round,
  	input encrypt_decrypt,
        input [1:0] operation_mode,
        input [1:0] aes_mode,
        input start,
        input disable_core,
        input clk,
        input rst_n,
	input first_round,
	input state,
	input op_mode,
	input rd_count_en,
	input next_state,
	input rd_count,
	input op_key_derivation,
	input enc_dec
);
property a3;
@(posedge clk) (aes_mode[0] == 1) |-> (mode_ctr == 0);
endproperty
assert_a3: assert property(a3);

property a2;
@(posedge clk) (aes_mode[0] == 0) |-> (mode_cbc == 0);
endproperty
assert_a2: assert property(a2);

property a1;
@(posedge clk) (start == 0) |-> (key_init == 0);
endproperty
assert_a1: assert property(a1);

property a0;
@(posedge clk) (start == 1) |-> (key_init == 1);
endproperty
assert_a0: assert property(a0);

endmodule"	https://github.com/achieve-lab/assertion_data_for_LLM/blob/NIPS_2024/Jasper_results/arithmetic_core_aes128/control_unit/FPV_control_unit.tcl	"Assertion 1:
AxiSlvPortIdWidth > 0: Ensures the slave port ID width is valid (non-zero).
Assertion 2:
AxiMstPortIdWidth >= IdxWidth: Ensures the master port ID width is sufficient to represent all unique IDs from the slave port.
Assertion 3:
AxiSlvPortMaxUniqIds > 0: Ensures there is at least one unique ID allowed in flight at the slave port.
Assertion 4:
AxiSlvPortMaxUniqIds <= 2**AxiSlvPortIdWidth: Ensures the number of unique IDs does not exceed what can be represented by the slave port ID width.
Assertion 5:
AxiMaxTxnsPerId > 0: Confirms that each unique ID can support at least one transaction in flight.
Assertion 6-10:
These assertions ensure that address (addr), data (data), and user (user) fields are of equal width on the master and slave ports for the AW, W, and AR channels. Inconsistent widths would cause protocol issues and data corruption.
Assertion 11-13:
Slave Port ID Width: Checks that aw.id, b.id, ar.id, and r.id fields on the slave port match AxiSlvPortIdWidth.
Assertion 14-16:
Master Port ID Width: Verifies that these ID fields on the master port match AxiMstPortIdWidth.
Assertion 17-20:
Write Address (AW) and Read Address (AR) Channels: Confirms that when the slave aw or ar handshake is valid and ready, the corresponding master handshake signals are also valid and ready.
Write Response (B) and Read Response (R) Channels: Ensures that a valid b or r response on the master port corresponds with a valid and ready response on the slave port.
Assertion 21:
last Signal: Confirms that the last flag for R responses (indicating the end of a burst) is consistent between master and slave ports. Any mismatch could indicate an incomplete or out-of-order transaction.
Assertion 22-23:
AR Channel ID Stability: Ensures that ar.id remains stable when ar_valid is asserted but ar_ready is not yet acknowledged.
AW Channel ID Stability: Verifies that aw.id does not change during an unacknowledged aw transaction.

"	"module axi_id_remap #(
  parameter int unsigned AxiSlvPortIdWidth = 32'd0,
  parameter int unsigned AxiSlvPortMaxUniqIds = 32'd0,
  parameter int unsigned AxiMaxTxnsPerId = 32'd0,
  parameter int unsigned AxiMstPortIdWidth = 32'd0,
  parameter type slv_req_t = logic,
  parameter type slv_resp_t = logic,
  parameter type mst_req_t = logic,
  parameter type mst_resp_t = logic
) (
  input  logic      clk_i,
  input  logic      rst_ni,
  input  slv_req_t  slv_req_i,
  output slv_resp_t slv_resp_o,
  output mst_req_t  mst_req_o,
  input  mst_resp_t mst_resp_i
);

  assign mst_req_o.aw.addr   = slv_req_i.aw.addr;
  assign mst_req_o.aw.len    = slv_req_i.aw.len;
  assign mst_req_o.aw.size   = slv_req_i.aw.size;
  assign mst_req_o.aw.burst  = slv_req_i.aw.burst;
  assign mst_req_o.aw.lock   = slv_req_i.aw.lock;
  assign mst_req_o.aw.cache  = slv_req_i.aw.cache;
  assign mst_req_o.aw.prot   = slv_req_i.aw.prot;
  assign mst_req_o.aw.qos    = slv_req_i.aw.qos;
  assign mst_req_o.aw.region = slv_req_i.aw.region;
  assign mst_req_o.aw.atop   = slv_req_i.aw.atop;
  assign mst_req_o.aw.user   = slv_req_i.aw.user;

  assign mst_req_o.w         = slv_req_i.w;
  assign mst_req_o.w_valid   = slv_req_i.w_valid;
  assign slv_resp_o.w_ready  = mst_resp_i.w_ready;

  assign slv_resp_o.b.resp   = mst_resp_i.b.resp;
  assign slv_resp_o.b.user   = mst_resp_i.b.user;
  assign slv_resp_o.b_valid  = mst_resp_i.b_valid;
  assign mst_req_o.b_ready   = slv_req_i.b_ready;

  assign mst_req_o.ar.addr   = slv_req_i.ar.addr;
  assign mst_req_o.ar.len    = slv_req_i.ar.len;
  assign mst_req_o.ar.size   = slv_req_i.ar.size;
  assign mst_req_o.ar.burst  = slv_req_i.ar.burst;
  assign mst_req_o.ar.lock   = slv_req_i.ar.lock;
  assign mst_req_o.ar.cache  = slv_req_i.ar.cache;
  assign mst_req_o.ar.prot   = slv_req_i.ar.prot;
  assign mst_req_o.ar.qos    = slv_req_i.ar.qos;
  assign mst_req_o.ar.region = slv_req_i.ar.region;
  assign mst_req_o.ar.user   = slv_req_i.ar.user;

  assign slv_resp_o.r.data   = mst_resp_i.r.data;
  assign slv_resp_o.r.resp   = mst_resp_i.r.resp;
  assign slv_resp_o.r.last   = mst_resp_i.r.last;
  assign slv_resp_o.r.user   = mst_resp_i.r.user;
  assign slv_resp_o.r_valid  = mst_resp_i.r_valid;
  assign mst_req_o.r_ready   = slv_req_i.r_ready;

  localparam int unsigned IdxWidth = cf_math_pkg::idx_width(AxiSlvPortMaxUniqIds);
  typedef logic [AxiSlvPortMaxUniqIds-1:0]  field_t;
  typedef logic [AxiSlvPortIdWidth-1:0]     id_inp_t;
  typedef logic [IdxWidth-1:0]              idx_t;
  field_t   wr_free,          rd_free,          both_free;
  id_inp_t                    rd_push_inp_id;
  idx_t     wr_free_oup_id,   rd_free_oup_id,   both_free_oup_id,
            wr_push_oup_id,   rd_push_oup_id,
            wr_exists_id,     rd_exists_id;
  logic     wr_exists,        rd_exists,
            wr_exists_full,   rd_exists_full,
            wr_full,          rd_full,
            wr_push,          rd_push;

  axi_id_remap_table #(
    .InpIdWidth     ( AxiSlvPortIdWidth     ),
    .MaxUniqInpIds  ( AxiSlvPortMaxUniqIds  ),
    .MaxTxnsPerId   ( AxiMaxTxnsPerId       )
  ) i_wr_table (
    .clk_i,
    .rst_ni,
    .free_o          ( wr_free                                 ),
    .free_oup_id_o   ( wr_free_oup_id                          ),
    .full_o          ( wr_full                                 ),
    .push_i          ( wr_push                                 ),
    .push_inp_id_i   ( slv_req_i.aw.id                         ),
    .push_oup_id_i   ( wr_push_oup_id                          ),
    .exists_inp_id_i ( slv_req_i.aw.id                         ),
    .exists_o        ( wr_exists                               ),
    .exists_oup_id_o ( wr_exists_id                            ),
    .exists_full_o   ( wr_exists_full                          ),
    .pop_i           ( slv_resp_o.b_valid && slv_req_i.b_ready ),
    .pop_oup_id_i    ( mst_resp_i.b.id[IdxWidth-1:0]           ),
    .pop_inp_id_o    ( slv_resp_o.b.id                         )
  );
  axi_id_remap_table #(
    .InpIdWidth     ( AxiSlvPortIdWidth     ),
    .MaxUniqInpIds  ( AxiSlvPortMaxUniqIds  ),
    .MaxTxnsPerId   ( AxiMaxTxnsPerId       )
  ) i_rd_table (
    .clk_i,
    .rst_ni,
    .free_o           ( rd_free                                                      ),
    .free_oup_id_o    ( rd_free_oup_id                                               ),
    .full_o           ( rd_full                                                      ),
    .push_i           ( rd_push                                                      ),
    .push_inp_id_i    ( rd_push_inp_id                                               ),
    .push_oup_id_i    ( rd_push_oup_id                                               ),
    .exists_inp_id_i  ( slv_req_i.ar.id                                              ),
    .exists_o         ( rd_exists                                                    ),
    .exists_oup_id_o  ( rd_exists_id                                                 ),
    .exists_full_o    ( rd_exists_full                                               ),
    .pop_i            ( slv_resp_o.r_valid && slv_req_i.r_ready && slv_resp_o.r.last ),
    .pop_oup_id_i     ( mst_resp_i.r.id[IdxWidth-1:0]                                ),
    .pop_inp_id_o     ( slv_resp_o.r.id                                              )
  );
  assign both_free = wr_free & rd_free;
  lzc #(
    .WIDTH  ( AxiSlvPortMaxUniqIds  ),
    .MODE   ( 1'b0                  )
  ) i_lzc (
    .in_i     ( both_free        ),
    .cnt_o    ( both_free_oup_id ),
    .empty_o  ( /* unused */     )
  );

  localparam ZeroWidth = AxiMstPortIdWidth - IdxWidth;
  assign mst_req_o.ar.id = {{ZeroWidth{1'b0}}, rd_push_oup_id};
  assign mst_req_o.aw.id = {{ZeroWidth{1'b0}}, wr_push_oup_id};

  enum logic [1:0] {Ready, HoldAR, HoldAW, HoldAx} state_d, state_q;
  idx_t ar_id_d, ar_id_q,
        aw_id_d, aw_id_q;
  logic ar_prio_d, ar_prio_q;
  always_comb begin
    mst_req_o.aw_valid  = 1'b0;
    slv_resp_o.aw_ready = 1'b0;
    wr_push             = 1'b0;
    wr_push_oup_id      =   '0;
    mst_req_o.ar_valid  = 1'b0;
    slv_resp_o.ar_ready = 1'b0;
    rd_push             = 1'b0;
    rd_push_inp_id      =   '0;
    rd_push_oup_id      =   '0;
    ar_id_d             = ar_id_q;
    aw_id_d             = aw_id_q;
    ar_prio_d           = ar_prio_q;
    state_d             = state_q;

    unique case (state_q)
      Ready: begin
        if (slv_req_i.ar_valid) begin
          if ((rd_exists && !rd_exists_full) || (!rd_exists && !rd_full)) begin
            rd_push_inp_id     = slv_req_i.ar.id;
            rd_push_oup_id     = rd_exists ? rd_exists_id : rd_free_oup_id;
            mst_req_o.ar_valid = 1'b1;
            rd_push            = 1'b1;
          end
        end

        if (slv_req_i.aw_valid) begin
          if (!slv_req_i.aw.atop[axi_pkg::ATOP_R_RESP]) begin
            if ((wr_exists && !wr_exists_full) || (!wr_exists && !wr_full)) begin
              wr_push_oup_id     = wr_exists ? wr_exists_id : wr_free_oup_id;
              mst_req_o.aw_valid = 1'b1;
              wr_push            = 1'b1;
            end
          end else if (!(ar_prio_q && mst_req_o.ar_valid)) begin
            mst_req_o.ar_valid  = 1'b0;
            slv_resp_o.ar_ready = 1'b0;
            rd_push             = 1'b0;
            if ((|both_free)) begin
              wr_push_oup_id = both_free_oup_id;
              rd_push_inp_id = slv_req_i.aw.id;
              rd_push_oup_id = both_free_oup_id;
              mst_req_o.aw_valid = 1'b1;
              rd_push            = 1'b1;
              wr_push            = 1'b1;
              ar_prio_d = 1'b1;
            end
          end
        end

        if (mst_req_o.ar_valid) begin
          slv_resp_o.ar_ready = mst_resp_i.ar_ready;
          if (!mst_resp_i.ar_ready) begin
            ar_id_d = rd_push_oup_id;
          end
        end
        if (mst_req_o.aw_valid) begin
          slv_resp_o.aw_ready = mst_resp_i.aw_ready;
          if (!mst_resp_i.aw_ready) begin
            aw_id_d = wr_push_oup_id;
          end
        end
        if ({mst_req_o.ar_valid, mst_resp_i.ar_ready,
             mst_req_o.aw_valid, mst_resp_i.aw_ready} == 4'b1010) begin
          state_d = HoldAx;
        end else if ({mst_req_o.ar_valid, mst_resp_i.ar_ready} == 2'b10) begin
          state_d = HoldAR;
        end else if ({mst_req_o.aw_valid, mst_resp_i.aw_ready} == 2'b10) begin
          state_d = HoldAW;
        end else begin
          state_d = Ready;
        end

        if (mst_req_o.ar_valid && mst_resp_i.ar_ready) begin
          ar_prio_d = 1'b0;
        end
      end

      HoldAR: begin
        rd_push_oup_id      = ar_id_q;
        mst_req_o.ar_valid  = 1'b1;
        slv_resp_o.ar_ready = mst_resp_i.ar_ready;
        if (mst_resp_i.ar_ready) begin
          state_d = Ready;
          ar_prio_d = 1'b0;
        end
      end

      HoldAW: begin
        wr_push_oup_id      = aw_id_q;
        mst_req_o.aw_valid  = 1'b1;
        slv_resp_o.aw_ready = mst_resp_i.aw_ready;
        if (mst_resp_i.aw_ready) begin
          state_d = Ready;
        end
      end

      HoldAx: begin
        rd_push_oup_id      = ar_id_q;
        mst_req_o.ar_valid  = 1'b1;
        slv_resp_o.ar_ready = mst_resp_i.ar_ready;
        wr_push_oup_id      = aw_id_q;
        mst_req_o.aw_valid  = 1'b1;
        slv_resp_o.aw_ready = mst_resp_i.aw_ready;
        unique case ({mst_resp_i.ar_ready, mst_resp_i.aw_ready})
          2'b01:   state_d = HoldAR;
          2'b10:   state_d = HoldAW;
          2'b11:   state_d = Ready;
          default: /*do nothing / stay in this state*/;
        endcase
        if (mst_resp_i.ar_ready) begin
          ar_prio_d = 1'b0;
        end
      end

      default: state_d = Ready;
    endcase
  end

  `FFARN(ar_id_q, ar_id_d, '0, clk_i, rst_ni)
  `FFARN(ar_prio_q, ar_prio_d, 1'b0, clk_i, rst_ni)
  `FFARN(aw_id_q, aw_id_d, '0, clk_i, rst_ni)
  `FFARN(state_q, state_d, Ready, clk_i, rst_ni)

endmodule"
"//////////////////////////////////////////////////////////////////
////
////
//// 	CRCAHB CORE BLOCK
////
////
////
//// This file is part of the APB to I2C project
////
//// http://www.opencores.org/cores/apbi2c/
////
////
////
//// Description
////
//// Implementation of APB IP core according to
////
//// crcahb IP core specification document.
////
////
////
//// To Do: Things are right here but always all block can suffer changes
////
////
////
////
////
//// Author(s): -  Julio Cesar 
////
///////////////////////////////////////////////////////////////// 
////
////
//// Copyright (C) 2009 Authors and OPENCORES.ORG
////
////
////
//// This source file may be used and distributed without
////
//// restriction provided that this copyright statement is not
////
//// removed from the file and that any derivative work contains
//// the original copyright notice and the associated disclaimer.
////
////
//// This source file is free software; you can redistribute it
////
//// and/or modify it under the terms of the GNU Lesser General
////
//// Public License as published by the Free Software Foundation;
//// either version 2.1 of the License, or (at your option) any
////
//// later version.
////
////
////
//// This source is distributed in the hope that it will be
////
//// useful, but WITHOUT ANY WARRANTY; without even the implied
////
//// warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR
////
//// PURPOSE. See the GNU Lesser General Public License for more
//// details.
////
////
////
//// You should have received a copy of the GNU Lesser General
////
//// Public License along with this source; if not, download it
////
//// from http://www.opencores.org/lgpl.shtml
////
////
///////////////////////////////////////////////////////////////////
module host_interface
(
	//OUTPUTS
	output [31:0] HRDATA,
	output HREADYOUT,
	output HRESP,
	output [31:0] bus_wr,
	output [ 1:0] crc_poly_size,
	output [ 1:0] bus_size,
	output [ 1:0] rev_in_type,
	output rev_out_type,
	output crc_init_en,
	output crc_idr_en,
	output crc_poly_en,
	output buffer_write_en,
	output reset_chain,
	//INPUTS
	input [31:0] HWDATA,
	input [31:0] HADDR,
	input [ 2:0] HSIZE,
	input [ 1:0] HTRANS,
	input HWRITE,
	input HSElx,
	input HREADY,
	input HRESETn,
	input HCLK,
	input [31:0] crc_poly_out,
	input [31:0] crc_out,
	input [31:0] crc_init_out,
	input [ 7:0] crc_idr_out,
	input buffer_full,
	input reset_pending,
	input read_wait
);

//Reset Values
localparam RESET_CRC_CR = 6'h00;

//CRC Register Map
localparam CRC_DR   = 3'h0;
localparam CRC_IDR  = 3'h1;
localparam CRC_CR   = 3'h2;
localparam CRC_INIT = 3'h4;
localparam CRC_POL  = 3'h5;

//Transfer Type Encoding
localparam IDLE    = 2'b00;
localparam BUSY    = 2'b01;
localparam NON_SEQ = 2'b10;
localparam SEQ     = 2'b11;

//HRESP Encoding
localparam OK    = 1'b0;
localparam ERROR = 1'b1;

//Pipeline flops
reg [2:0] haddr_pp;
reg [2:0] hsize_pp;
reg [1:0] htrans_pp;
reg hwrite_pp;
reg hselx_pp;

//Flops
reg [4:0] crc_cr_ff;

//Internal Signals
wire [31:0] crc_cr_rd;
wire crc_dr_sel;
wire crc_init_sel;
wire crc_idr_sel;
wire crc_poly_sel;
wire crc_cr_sel;
wire ahb_enable;
wire write_en;
wire read_en;
wire crc_cr_en;
wire sample_bus;
wire buffer_read_en;

//Pipeline Registers for Address Phase of AHB Protocol
always @(posedge HCLK)
	begin
		if(!HRESETn)
			begin
				hselx_pp <= 1'b0;
			end
		else
			if(sample_bus)
				begin
					haddr_pp  <= HADDR[4:2];
					hsize_pp  <= HSIZE;
					htrans_pp <= HTRANS;
					hwrite_pp <= HWRITE;
					hselx_pp  <= HSElx;
				end
	end

//Enable Signals
assign ahb_enable = (htrans_pp == NON_SEQ);
assign write_en = hselx_pp &&  hwrite_pp && ahb_enable;
assign read_en  = hselx_pp && !hwrite_pp && ahb_enable;

//Registers decoding
assign crc_dr_sel   = (haddr_pp == CRC_DR  );
assign crc_init_sel = (haddr_pp == CRC_INIT);
assign crc_idr_sel  = (haddr_pp == CRC_IDR );
assign crc_poly_sel = (haddr_pp == CRC_POL );
assign crc_cr_sel   = (haddr_pp == CRC_CR  );

//Write Esnables Signals for Registers
assign buffer_write_en = crc_dr_sel   && write_en;
assign crc_init_en     = crc_init_sel && write_en;
assign crc_idr_en      = crc_idr_sel  && write_en;
assign crc_poly_en     = crc_poly_sel && write_en;
assign crc_cr_en       = crc_cr_sel   && write_en;

//Indicates reading operation request to crc_dr register
assign buffer_read_en = crc_dr_sel && read_en;

//Bus Size is the output of HSIZE pipeline register
assign bus_size = hsize_pp;

//The Write Bus is not pipelined
assign bus_wr = HWDATA;

//HREADY Signal outputed to Master
assign HREADYOUT = !((buffer_write_en && buffer_full   ) ||
                     (buffer_read_en  && read_wait     ) ||
                     (crc_init_en     && reset_pending ) );

//Signal to control sampling of bus
assign sample_bus = HREADYOUT && HREADY;

//HRESP Signal outputed to Master
//This implementation never signalize bus error to master
assign HRESP = OK;

//CRC_CR Data Read
assign crc_cr_rd = {24'h0, crc_cr_ff[4:0], 3'h0};

//Mux to HRDATA
assign HRDATA = ({32{crc_dr_sel  }} & crc_out             ) |
                ({32{crc_init_sel}} & crc_init_out        ) |
                ({32{crc_idr_sel }} & {24'h0, crc_idr_out}) |
                ({32{crc_poly_sel}} & crc_poly_out        ) |
                ({32{crc_cr_sel  }} & crc_cr_rd           ) ;

//Control Register
always @(posedge HCLK)
	begin
		if(!HRESETn)
			crc_cr_ff <= RESET_CRC_CR;
		else
			if(crc_cr_en)
				crc_cr_ff <= {HWDATA[7], HWDATA[6:5], HWDATA[4:3]};
	end

//Configuration Signals
assign reset_chain   = (crc_cr_en && HWDATA[0]);
assign crc_poly_size = crc_cr_ff[1:0];
assign rev_in_type   = crc_cr_ff[3:2];
assign rev_out_type  = crc_cr_ff[4];

endmodule"	"
module host_interface_sva(
	input HSElx,
	input buffer_write_en,
	input HREADYOUT,
	input HRESP,
	input rev_out_type,
	input [31:0] HRDATA,
	input [31:0] crc_poly_out,
	input buffer_full,
	input read_wait,
input crc_idr_sel,
input crc_poly_sel,
	input [31:0] HADDR,
	input HCLK,
	input [ 1:0] crc_poly_size,
input buffer_read_en,
input crc_cr_sel,
input ahb_enable,
input write_en,
	input [31:0] crc_init_out,
	input crc_poly_en,
	input reset_pending,
	input [ 1:0] bus_size,
input crc_init_sel,
	input [ 1:0] rev_in_type,
input [2:0] hsize_pp,
input sample_bus,
	input [ 7:0] crc_idr_out,
	input [31:0] HWDATA,
input crc_dr_sel,
	input HREADY,
	input [31:0] bus_wr,
	input [ 2:0] HSIZE,
	input [31:0] crc_out,
	input crc_idr_en,
	input crc_init_en,
	input HRESETn,
input hselx_pp,
input read_en,
input [4:0] crc_cr_ff,
input [1:0] htrans_pp,
	input [ 1:0] HTRANS,
input [2:0] haddr_pp,
input hwrite_pp,
	input HWRITE,
	input reset_chain,
input crc_cr_en,
input DEFAULT_CLOCK,
input DEFAULT_RESET,
input [31:0] crc_cr_rd
);



property a1;
@(posedge DEFAULT_CLOCK) (buffer_read_en == 0) |-> (HREADYOUT == 1);
endproperty
// assert_a1: assert property(a1);

property a3;
@(posedge DEFAULT_CLOCK) (sample_bus == 1) |-> (HREADYOUT == 1);
endproperty
assert_a3: assert property(a3);

property a5;
@(posedge DEFAULT_CLOCK) (buffer_read_en == 1 & read_wait == 1) |-> (HREADYOUT == 0);
endproperty
assert_a5: assert property(a5);

property a2;
@(posedge DEFAULT_CLOCK) (reset_pending == 0) |-> (HREADYOUT == 1);
endproperty
// assert_a2: assert property(a2);

property a4;
@(posedge DEFAULT_CLOCK) (read_wait == 0) |-> (HREADYOUT == 1);
endproperty
// assert_a4: assert property(a4);

property a0;
@(posedge DEFAULT_CLOCK) (ahb_enable == 0) |-> (HREADYOUT == 1);
endproperty
assert_a0: assert property(a0);

property a8;
@(posedge DEFAULT_CLOCK) (write_en == 0) |-> (crc_idr_en == 0);
endproperty
assert_a8: assert property(a8);

property a11;
@(posedge DEFAULT_CLOCK) (write_en == 1 & crc_idr_sel == 1) |-> (crc_idr_en == 1);
endproperty
assert_a11: assert property(a11);

property a10;
@(posedge DEFAULT_CLOCK) (crc_idr_sel == 0) |-> (crc_idr_en == 0);
endproperty
assert_a10: assert property(a10);

property a13;
@(posedge DEFAULT_CLOCK) (hselx_pp == 0) |-> (crc_idr_en == 0);
endproperty
assert_a13: assert property(a13);

property a12;
@(posedge DEFAULT_CLOCK) (hwrite_pp == 0) |-> (crc_idr_en == 0);
endproperty
assert_a12: assert property(a12);

property a9;
@(posedge DEFAULT_CLOCK) (haddr_pp[1] == 0) |-> (crc_idr_en == 0);
endproperty
// assert_a9: assert property(a9);

property a16;
@(posedge DEFAULT_CLOCK) (write_en == 0) |-> (crc_poly_en == 0);
endproperty
assert_a16: assert property(a16);

property a18;
@(posedge DEFAULT_CLOCK) (write_en == 1 & haddr_pp[1] == 0) |-> (crc_poly_en == 1);
endproperty
// assert_a18: assert property(a18);

property a15;
@(posedge DEFAULT_CLOCK) (hselx_pp == 0) |-> (crc_poly_en == 0);
endproperty
assert_a15: assert property(a15);

property a14;
@(posedge DEFAULT_CLOCK) (hwrite_pp == 0) |-> (crc_poly_en == 0);
endproperty
assert_a14: assert property(a14);

property a17;
@(posedge DEFAULT_CLOCK) (haddr_pp[1] == 1) |-> (crc_poly_en == 0);
endproperty
assert_a17: assert property(a17);

endmodule"	https://github.com/achieve-lab/assertion_data_for_LLM/blob/NIPS_2024/Jasper_results/arithmetic_core_crcahb/host_interface/property_goldmine.sva	"Assertion 1:
This assertion checks that the width of the input ID (InpIdWidth) is positive, confirming that IDs have a valid width.
Assertion 2:
This assertion ensures that MaxUniqInpIds, the maximum number of unique input IDs that can be in-flight, is greater than zero, meaning the table can hold at least one unique ID.
Assertion 3:
This assertion verifies that MaxUniqInpIds does not exceed the number of unique IDs representable by InpIdWidth. It ensures that the table’s size is within the range allowed by the input ID width.
Assertion 4:
This assertion checks that MaxTxnsPerId, the maximum number of in-flight transactions per ID, is greater than zero, confirming that there is a non-zero limit for tracking transactions.
Assertion 5:
This assertion ensures that IdxWidth, the width of the index into the remap table, is at least one bit wide, which is necessary to uniquely address entries in the table."	"module axi_id_remap_table #(
  parameter int unsigned InpIdWidth = 32'd0,
  parameter int unsigned MaxUniqInpIds = 32'd0,
  parameter int unsigned MaxTxnsPerId = 32'd0,
  localparam type id_inp_t = logic [InpIdWidth-1:0],
  localparam int unsigned IdxWidth = cf_math_pkg::idx_width(MaxUniqInpIds),
  localparam type idx_t = logic [IdxWidth-1:0],
  localparam type field_t = logic [MaxUniqInpIds-1:0]
) (
  input  logic    clk_i,
  input  logic    rst_ni,
  output field_t  free_o,
  output idx_t    free_oup_id_o,
  output logic    full_o,
  input  logic    push_i,
  input  id_inp_t push_inp_id_i,
  input  idx_t    push_oup_id_i,
  input  id_inp_t exists_inp_id_i,
  output logic    exists_o,
  output idx_t    exists_oup_id_o,
  output logic    exists_full_o,
  input  logic    pop_i,
  input  idx_t    pop_oup_id_i,
  output id_inp_t pop_inp_id_o
);

  localparam int unsigned CntWidth = $clog2(MaxTxnsPerId+1);
  typedef logic [CntWidth-1:0] cnt_t;
  typedef struct packed {
    id_inp_t  inp_id;
    cnt_t     cnt;
  } entry_t;

  entry_t [MaxUniqInpIds-1:0] table_d, table_q;

  for (genvar i = 0; i < MaxUniqInpIds; i++) begin : gen_free_o
    assign free_o[i] = table_q[i].cnt == '0;
  end
  lzc #(
    .WIDTH ( MaxUniqInpIds  ),
    .MODE  ( 1'b0           )
  ) i_lzc_free (
    .in_i    ( free_o        ),
    .cnt_o   ( free_oup_id_o ),
    .empty_o ( full_o        )
  );

  if (MaxUniqInpIds == 1) begin : gen_pop_for_single_unique_inp_id
    assign pop_inp_id_o = table_q[0].inp_id;
  end else begin : gen_pop_for_multiple_unique_inp_ids
    assign pop_inp_id_o = table_q[pop_oup_id_i].inp_id;
  end

  field_t match;
  for (genvar i = 0; i < MaxUniqInpIds; i++) begin : gen_match
    assign match[i] = table_q[i].cnt > 0 && table_q[i].inp_id == exists_inp_id_i;
  end
  logic no_match;
  lzc #(
      .WIDTH ( MaxUniqInpIds  ),
      .MODE  ( 1'b0           )
  ) i_lzc_match (
      .in_i     ( match           ),
      .cnt_o    ( exists_oup_id_o ),
      .empty_o  ( no_match        )
  );
  assign exists_o      = ~no_match;
  if (MaxUniqInpIds == 1) begin : gen_exists_full_for_single_unique_inp_id
    assign exists_full_o = table_q[0].cnt == MaxTxnsPerId;
  end else begin : gen_exists_full_for_multiple_unique_inp_ids
    assign exists_full_o = table_q[exists_oup_id_o].cnt == MaxTxnsPerId;
  end

  always_comb begin
    table_d = table_q;
    if (push_i) begin
      table_d[push_oup_id_i].inp_id  = push_inp_id_i;
      table_d[push_oup_id_i].cnt    += 1;
    end
    if (pop_i) begin
      table_d[pop_oup_id_i].cnt -= 1;
    end
  end

  `FFARN(table_q, table_d, '0, clk_i, rst_ni)

endmodule"
"`timescale 1ns / 1ps
//=============================================================================
//	(C) 2007,2012  Robert Finch
//  robfinch<remove>@opencores.org
//	All rights reserved.
//
//	PSGBusArb.v
//
// This source file is free software: you can redistribute it and/or modify 
// it under the terms of the GNU Lesser General Public License as published 
// by the Free Software Foundation, either version 3 of the License, or     
// (at your option) any later version.                                      
//                                                                          
// This source file is distributed in the hope that it will be useful,      
// but WITHOUT ANY WARRANTY; without even the implied warranty of           
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the            
// GNU General Public License for more details.                             
//                                                                          
// You should have received a copy of the GNU General Public License        
// along with this program.  If not, see <http://www.gnu.org/licenses/>.    
//
//		Arbitrates access to the system bus among up to eight
//	wave table channels for the PSG. This arbitrator is part
//	of a tree that ends up looking like a single arbitration
//	request to the system.
//
//	Spartan3
//	19 LUTs / 11 slices
//=============================================================================

module PSGBusArb(rst, clk, ce, ack,
	req0, req1, req2, req3, req4, req5, req6, req7,
	sel0, sel1, sel2, sel3, sel4, sel5, sel6, sel7, seln);
input rst;		// reset
input clk;		// clock (eg 100MHz)
input ce;		// clock enable (eg 25MHz)
input ack;		// bus transfer completed
input req0;		// requester 0 wants the bus
input req1;		// requester 1 wants the bus
input req2;		// ...
input req3;
input req4;
input req5;
input req6;
input req7;
output sel0;	// requester 0 granted the bus
reg sel0;
output sel1;
reg sel1;
output sel2;
reg sel2;
output sel3;
reg sel3;
output sel4;
reg sel4;
output sel5;
reg sel5;
output sel6;
reg sel6;
output sel7;
reg sel7;
output [2:0] seln;	// who has the bus
reg [2:0] seln;

always @(posedge clk) begin
	if (rst) begin
		sel0 <= 1'b0;
		sel1 <= 1'b0;
		sel2 <= 1'b0;
		sel3 <= 1'b0;
		sel4 <= 1'b0;
		sel5 <= 1'b0;
		sel6 <= 1'b0;
		sel7 <= 1'b0;
		seln <= 3'd0;
	end
	else begin
		if (ce&ack) begin
			if (req0) begin
				sel0 <= 1'b1;
				sel1 <= 1'b0;
				sel2 <= 1'b0;
				sel3 <= 1'b0;
				sel4 <= 1'b0;
				sel5 <= 1'b0;
				sel6 <= 1'b0;
				sel7 <= 1'b0;
				seln <= 3'd0;
			end
			else if (req1) begin
				sel1 <= 1'b1;
				sel0 <= 1'b0;
				sel2 <= 1'b0;
				sel3 <= 1'b0;
				sel4 <= 1'b0;
				sel5 <= 1'b0;
				sel6 <= 1'b0;
				sel7 <= 1'b0;
				seln <= 3'd1;
			end
			else if (req2) begin
				sel2 <= 1'b1;
				sel0 <= 1'b0;
				sel1 <= 1'b0;
				sel3 <= 1'b0;
				sel4 <= 1'b0;
				sel5 <= 1'b0;
				sel6 <= 1'b0;
				sel7 <= 1'b0;
				seln <= 3'd2;
			end
			else if (req3) begin
				sel3 <= 1'b1;
				sel0 <= 1'b0;
				sel1 <= 1'b0;
				sel2 <= 1'b0;
				sel4 <= 1'b0;
				sel5 <= 1'b0;
				sel6 <= 1'b0;
				sel7 <= 1'b0;
				seln <= 3'd3;
			end
			else if (req4) begin
				sel4 <= 1'b1;
				sel0 <= 1'b0;
				sel1 <= 1'b0;
				sel2 <= 1'b0;
				sel3 <= 1'b0;
				sel5 <= 1'b0;
				sel6 <= 1'b0;
				sel7 <= 1'b0;
				seln <= 3'd4;
			end
			else if (req5) begin
				sel5 <= 1'b1;
				sel0 <= 1'b0;
				sel1 <= 1'b0;
				sel2 <= 1'b0;
				sel3 <= 1'b0;
				sel4 <= 1'b0;
				sel6 <= 1'b0;
				sel7 <= 1'b0;
				seln <= 3'd5;
			end
			else if (req6) begin
				sel6 <= 1'b1;
				sel0 <= 1'b0;+A29
				sel1 <= 1'b0;
				sel2 <= 1'b0;
				sel3 <= 1'b0;
				sel4 <= 1'b0;
				sel5 <= 1'b0;
				sel7 <= 1'b0;
				seln <= 3'd6;
			end
			else if (req7) begin
				sel7 <= 1'b1;
				sel0 <= 1'b0;
				sel1 <= 1'b0;
				sel2 <= 1'b0;
				sel3 <= 1'b0;
				sel4 <= 1'b0;
				sel5 <= 1'b0;
				sel6 <= 1'b0;
				seln <= 3'd7;
			end
			// otherwise, hold onto last owner
			else begin
				sel0 <= sel0;
				sel1 <= sel1;
				sel2 <= sel2;
				sel3 <= sel3;
				sel4 <= sel4;
				sel5 <= sel5;
				sel6 <= sel6;
				sel7 <= sel7;
				seln <= seln;
			end
		end
	end
end

endmodule"	"module PSGBusArb_sva(
input req3,
input sel4,
input sel3,
input sel6,
input sel1,
input req4,
input req2,		// ...
input req6,
input ack,		// bus transfer completed
input req1,		// requester 1 wants the bus
input sel7,
input req0,		// requester 0 wants the bus
input sel2,
input req5,
input rst,		// reset
input req7,
input ce,		// clock enable (eg 25MHz)
input clk,		// clock (eg 100MHz)
input sel5,
input [2:0] seln,
input sel0
);

property a10;
@(posedge clk) (ce == 1 & req1 == 1) |=> (sel7 == 0);
endproperty
// assert_a10: assert property(a10);

property a0;
@(posedge clk) (req4 == 1 & req1 == 1) |=> (sel7 == 0);
endproperty
// assert_a0: assert property(a0);

property a5;
@(posedge clk) (req4 == 1 & ce == 1) |=> (sel7 == 0);
endproperty
// assert_a5: assert property(a5);

property a14;
@(posedge clk) (req2 == 0 & req6 == 0 & req4 == 0 & req0 == 0 & ack == 1 & ce == 1 & req5 == 0 & req1 == 0 & req7 == 1) |=> (sel7 == 1);
endproperty
// assert_a14: assert property(a14);

property a7;
@(posedge clk) (sel7 == 0 & req0 == 1) |=> (sel7 == 0);
endproperty
assert_a7: assert property(a7);

property a1;
@(posedge clk) (sel7 == 0 & req1 == 1) |=> (sel7 == 0);
endproperty
assert_a1: assert property(a1);

property a13;
@(posedge clk) (sel7 == 1 & ack == 0) |=> (sel7 == 1);
endproperty
assert_a13: assert property(a13);

property a12;
@(posedge clk) (sel7 == 1 & ce == 0) |=> (sel7 == 1);
endproperty
assert_a12: assert property(a12);

property a3;
@(posedge clk) (sel7 == 0 & ack == 0) |=> (sel7 == 0);
endproperty
assert_a3: assert property(a3);

property a2;
@(posedge clk) (sel7 == 0 & ce == 0) |=> (sel7 == 0);
endproperty
// assert_a2: assert property(a2);

property a4;
@(posedge clk) (sel7 == 0 & req2 == 1) |=> (sel7 == 0);
endproperty
assert_a4: assert property(a4);

property a6;
@(posedge clk) (sel7 == 0 & req3 == 1) |=> (sel7 == 0);
endproperty
assert_a6: assert property(a6);

property a11;
@(posedge clk) (sel7 == 0 & req5 == 1) |=> (sel7 == 0);
endproperty
assert_a11: assert property(a11);

property a8;
@(posedge clk) (sel7 == 0 & req6 == 1) |=> (sel7 == 0);
endproperty
assert_a8: assert property(a8);

property a19;
@(posedge clk) (sel5 == 0 & req0 == 1) |=> (sel5 == 0);
endproperty
assert_a19: assert property(a19);

property a20;
@(posedge clk) (sel5 == 0 & req1 == 1) |=> (sel5 == 0);
endproperty
assert_a20: assert property(a20);

property a26;
@(posedge clk) (sel5 == 1 & ce == 0) |=> (sel5 == 1);
endproperty
assert_a26: assert property(a26);

property a27;
@(posedge clk) (sel5 == 1 & ack == 0) |=> (sel5 == 1);
endproperty
assert_a27: assert property(a27);

property a16;
@(posedge clk) (sel5 == 0 & ack == 0) |=> (sel5 == 0);
endproperty
assert_a16: assert property(a16);

property a15;
@(posedge clk) (sel5 == 0 & ce == 0) |=> (sel5 == 0);
endproperty
assert_a15: assert property(a15);

property a18;
@(posedge clk) (sel5 == 0 & req2 == 1) |=> (sel5 == 0);
endproperty
assert_a18: assert property(a18);

property a17;
@(posedge clk) (sel5 == 0 & req3 == 1) |=> (sel5 == 0);
endproperty
assert_a17: assert property(a17);

property a21;
@(posedge clk) (sel5 == 0 & req4 == 1) |=> (sel5 == 0);
endproperty
assert_a21: assert property(a21);

property a23;
@(posedge clk) (sel5 == 0 & req5 == 0) |=> (sel5 == 0);
endproperty
assert_a23: assert property(a23);

property a35;
@(posedge clk) (sel4 == 0 & req1 == 1) |=> (sel4 == 0);
endproperty
assert_a35: assert property(a35);

property a40;
@(posedge clk) (sel4 == 1 & ack == 0) |=> (sel4 == 1);
endproperty
assert_a40: assert property(a40);

property a31;
@(posedge clk) (sel4 == 0 & ack == 0) |=> (sel4 == 0);
endproperty
assert_a31: assert property(a31);

property a30;
@(posedge clk) (sel4 == 0 & ce == 0) |=> (sel4 == 0);
endproperty
assert_a30: assert property(a30);

property a39;
@(posedge clk) (sel4 == 1 & ce == 0) |=> (sel4 == 1);
endproperty
assert_a39: assert property(a39);

property a32;
@(posedge clk) (sel4 == 0 & req2 == 1) |=> (sel4 == 0);
endproperty
assert_a32: assert property(a32);

property a33;
@(posedge clk) (sel4 == 0 & req3 == 1) |=> (sel4 == 0);
endproperty
assert_a33: assert property(a33);

property a37;
@(posedge clk) (sel4 == 0 & req4 == 0) |=> (sel4 == 0);
endproperty
assert_a37: assert property(a37);

endmodule"	https://github.com/achieve-lab/assertion_data_for_LLM/tree/NIPS_2024/Jasper_results/arithmetic_core_common_files/PSGBusArb	"Assertion 1:
Ensures that the AXI_ID_WIDTH of the slave port (slv) matches the expected AXI_SLV_PORT_ID_WIDTH parameter. This verification is crucial because the ID width needs to be consistent with the configured ID width for slave requests and responses.
Assertion 2:
Confirms that the address width (AXI_ADDR_WIDTH) of the slave port matches the specified parameter AXI_ADDR_WIDTH. This check ensures that the width of address signals is as expected, avoiding mismatches that could lead to data misinterpretation.
Assertion 3:
Verifies that the data width (AXI_DATA_WIDTH) of the slave port is equal to the expected data width parameter. This check ensures that the data signals are aligned correctly, which is crucial for data integrity during transactions.
Assertion 4:
Ensures that the user data width (AXI_USER_WIDTH) in the slave port matches the specified parameter. This verification is necessary for consistency in user-defined fields associated with the AXI protocol.
Assertion 5:
Checks that the AXI_ID_WIDTH of the master port (mst) is equal to the AXI_MST_PORT_ID_WIDTH. This ensures that the master port ID width is correctly configured to handle IDs remapped by the module.
Assertion 6:
Confirms that the address width of the master port (AXI_ADDR_WIDTH) is consistent with the parameter for address width. This ensures that both slave and master ports are compatible in terms of address signal width.
Assertion 7:
Validates that the master port’s data width matches the AXI_DATA_WIDTH parameter, ensuring compatibility for data transactions.
Assertion 8:
Ensures that the user width on the master port is consistent with the AXI_USER_WIDTH parameter. This check guarantees that user-defined signal fields are compatible between the master and slave interfaces."	"module axi_id_remap_intf #(
  parameter int unsigned AXI_SLV_PORT_ID_WIDTH = 32'd0,
  parameter int unsigned AXI_SLV_PORT_MAX_UNIQ_IDS = 32'd0,
  parameter int unsigned AXI_MAX_TXNS_PER_ID = 32'd0,
  parameter int unsigned AXI_MST_PORT_ID_WIDTH = 32'd0,
  parameter int unsigned AXI_ADDR_WIDTH = 32'd0,
  parameter int unsigned AXI_DATA_WIDTH = 32'd0,
  parameter int unsigned AXI_USER_WIDTH = 32'd0
) (
  input logic     clk_i,
  input logic     rst_ni,
  AXI_BUS.Slave   slv,
  AXI_BUS.Master  mst
);

  typedef logic [AXI_SLV_PORT_ID_WIDTH-1:0] slv_id_t;
  typedef logic [AXI_MST_PORT_ID_WIDTH-1:0] mst_id_t;
  typedef logic [AXI_ADDR_WIDTH-1:0]        axi_addr_t;
  typedef logic [AXI_DATA_WIDTH-1:0]        axi_data_t;
  typedef logic [AXI_DATA_WIDTH/8-1:0]      axi_strb_t;
  typedef logic [AXI_USER_WIDTH-1:0]        axi_user_t;

  `AXI_TYPEDEF_AW_CHAN_T(slv_aw_chan_t, axi_addr_t, slv_id_t, axi_user_t)
  `AXI_TYPEDEF_W_CHAN_T(slv_w_chan_t, axi_data_t, axi_strb_t, axi_user_t)
  `AXI_TYPEDEF_B_CHAN_T(slv_b_chan_t, slv_id_t, axi_user_t)
  `AXI_TYPEDEF_AR_CHAN_T(slv_ar_chan_t, axi_addr_t, slv_id_t, axi_user_t)
  `AXI_TYPEDEF_R_CHAN_T(slv_r_chan_t, axi_data_t, slv_id_t, axi_user_t)
  `AXI_TYPEDEF_REQ_T(slv_req_t, slv_aw_chan_t, slv_w_chan_t, slv_ar_chan_t)
  `AXI_TYPEDEF_RESP_T(slv_resp_t, slv_b_chan_t, slv_r_chan_t)

  `AXI_TYPEDEF_AW_CHAN_T(mst_aw_chan_t, axi_addr_t, mst_id_t, axi_user_t)
  `AXI_TYPEDEF_W_CHAN_T(mst_w_chan_t, axi_data_t, axi_strb_t, axi_user_t)
  `AXI_TYPEDEF_B_CHAN_T(mst_b_chan_t, mst_id_t, axi_user_t)
  `AXI_TYPEDEF_AR_CHAN_T(mst_ar_chan_t, axi_addr_t, mst_id_t, axi_user_t)
  `AXI_TYPEDEF_R_CHAN_T(mst_r_chan_t, axi_data_t, mst_id_t, axi_user_t)
  `AXI_TYPEDEF_REQ_T(mst_req_t, mst_aw_chan_t, mst_w_chan_t, mst_ar_chan_t)
  `AXI_TYPEDEF_RESP_T(mst_resp_t, mst_b_chan_t, mst_r_chan_t)

  slv_req_t  slv_req;
  slv_resp_t slv_resp;
  mst_req_t  mst_req;
  mst_resp_t mst_resp;

  `AXI_ASSIGN_TO_REQ(slv_req, slv)
  `AXI_ASSIGN_FROM_RESP(slv, slv_resp)
  `AXI_ASSIGN_FROM_REQ(mst, mst_req)
  `AXI_ASSIGN_TO_RESP(mst_resp, mst)

  axi_id_remap #(
    .AxiSlvPortIdWidth    ( AXI_SLV_PORT_ID_WIDTH     ),
    .AxiSlvPortMaxUniqIds ( AXI_SLV_PORT_MAX_UNIQ_IDS ),
    .AxiMaxTxnsPerId      ( AXI_MAX_TXNS_PER_ID       ),
    .AxiMstPortIdWidth    ( AXI_MST_PORT_ID_WIDTH     ),
    .slv_req_t            ( slv_req_t                 ),
    .slv_resp_t           ( slv_resp_t                ),
    .mst_req_t            ( mst_req_t                 ),
    .mst_resp_t           ( mst_resp_t                )
  ) i_axi_id_remap (
    .clk_i,
    .rst_ni,
    .slv_req_i  ( slv_req  ),
    .slv_resp_o ( slv_resp ),
    .mst_req_o  ( mst_req  ),
    .mst_resp_i ( mst_resp )
  );

  
endmodule"
"module simple_req_ack (
	input  clk,
	input  rst_n,

	input  req,
	output ack
);
	logic req_ff, ack_ff;

	always_ff @(negedge rst_n, posedge clk)
		if (!rst_n)
			req_ff <= '0;
		else
			if (req_ff)
				req_ff <= '0;
			else
				req_ff <= req;

	always_ff @(negedge rst_n, posedge clk)
		if (!rst_n)
			ack_ff <= '0;
		else
		if (ack_ff)
			ack_ff <= '0;
		else
		if (req_ff)
			ack_ff <= '1;

	assign ack = ack_ff;

endmodule"	"module simple_req_ack_sva (input clk, rst_n, req, ack);

	// PROPERTY 
	property sva_req_ack1 (clk, rst_n, req, ack);
		@(posedge clk) disable iff(!rst_n)
		req |-> ##2 ack;
	endproperty

	property sva_req_ack2 (clk, rst_n, req, ack);
		@(posedge clk) disable iff(!rst_n)
		$rose(req) |-> ##2 $rose(ack);
	endproperty

	property sva_req_ack3 (clk, rst_n, req, ack);
		@(posedge clk) disable iff(!rst_n)
		$rose(req) |-> ##1 $fell(req) ##1 $rose(ack) ##1 $fell(ack);
	endproperty

	property sva_req_ack4 (clk, rst_n, req, ack);
		@(posedge clk) disable iff(!rst_n)
		$rose(req) |->
			!ack ##1 ($fell(req) & !ack) ##1 ($rose(ack) & !req) ##1 ($fell(ack) & !req);
	endproperty

	// ASSERT PROPERTY
	// assert_sva_req_ack1 : assert property( sva_req_ack1(clk, rst_n, req, ack) );
	assert_sva_req_ack2 : assert property( sva_req_ack2(clk, rst_n, req, ack) );
	// assert_sva_req_ack3 : assert property( sva_req_ack3(clk, rst_n, req, ack) );
	// assert_sva_req_ack4 : assert property( sva_req_ack4(clk, rst_n, req, ack) );

endmodule"	https://github.com/hassyy/systemverilog-assertion/blob/master/simple-req-ack/sva_req_ack.sv		
"//////////////////////////////////////////////////////////////////
////
////
//// 	APB module to I2C Core
////
////
////
//// This file is part of the APB to I2C project
////
//// http://www.opencores.org/cores/apbi2c/
////
////
////
//// Description
////
//// Implementation of APB IP core according to
////
//// apbi2c_spec IP core specification document.
////
////
////
//// To Do: Things are right here but always all block can suffer changes
////
////
////
////
////
//// Author(s): - Felipe Fernandes Da Costa, fefe2560@gmail.com
////		  Ronal Dario Celaya
////
///////////////////////////////////////////////////////////////// 
////
////
//// Copyright (C) 2009 Authors and OPENCORES.ORG
////
////
////
//// This source file may be used and distributed without
////
//// restriction provided that this copyright statement is not
////
//// removed from the file and that any derivative work contains
//// the original copyright notice and the associated disclaimer.
////
////
//// This source file is free software; you can redistribute it
////
//// and/or modify it under the terms of the GNU Lesser General
////
//// Public License as published by the Free Software Foundation;
//// either version 2.1 of the License, or (at your option) any
////
//// later version.
////
////
////
//// This source is distributed in the hope that it will be
////
//// useful, but WITHOUT ANY WARRANTY; without even the implied
////
//// warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR
////
//// PURPOSE. See the GNU Lesser General Public License for more
//// details.
////
////
////
//// You should have received a copy of the GNU Lesser General
////
//// Public License along with this source; if not, download it
////
//// from http://www.opencores.org/lgpl.shtml
////
////
///////////////////////////////////////////////////////////////////

`timescale 1ns/1ps //timescale 

module apb(
			//standard ARM
	    		input PCLK,
			input PRESETn,
			input PSELx,
			input PWRITE,
			input PENABLE,
			input [31:0] PADDR,
			input [31:0] PWDATA,

			//internal pin
			input [31:0] READ_DATA_ON_RX,
			input ERROR,
			input TX_EMPTY,
			input RX_EMPTY,
			
			//external pin
			output [31:0] PRDATA,

			//internal pin 
			output reg [13:0] INTERNAL_I2C_REGISTER_CONFIG,
			output reg [13:0] INTERNAL_I2C_REGISTER_TIMEOUT,
			output [31:0] WRITE_DATA_ON_TX,
			output  WR_ENA,
			output  RD_ENA,
			
			//outside port 
			output PREADY,
			output PSLVERR,

			//interruption
			output INT_RX,
			output INT_TX
	   

	  );

//ENABLE WRITE ON TX FIFO
assign WR_ENA = (PWRITE == 1'b1 & PENABLE == 1'b1 & PADDR == 32'd0 & PSELx == 1'b1)?  1'b1:1'b0;

//ENABLE READ ON RX FIFO
assign RD_ENA = (PWRITE == 1'b0 & PENABLE == 1'b1  & PADDR == 32'd4 & PSELx == 1'b1)?  1'b1:1'b0;

//WRITE ON I2C MODULE
assign PREADY = ((WR_ENA == 1'b1 | RD_ENA == 1'b1 | PADDR == 32'd8 | PADDR == 32'd12) &  (PENABLE == 1'b1 & PSELx == 1'b1))? 1'b1:1'b0;

//INPUT TO WRITE ON TX FIFO
assign WRITE_DATA_ON_TX = (PADDR == 32'd0)? PWDATA:PWDATA;

//OUTPUT DATA FROM RX TO PRDATA
assign PRDATA = (PADDR == 32'd4)? READ_DATA_ON_RX:READ_DATA_ON_RX;

//ERROR FROM I2C CORE
assign PSLVERR = ERROR; 

//INTERRUPTION FROM I2C
assign INT_TX = TX_EMPTY;

//INTERRUPTION FROM I2C
assign INT_RX = RX_EMPTY;

//This is sequential logic used only to register configuration
always@(posedge PCLK)
begin

	if(!PRESETn)
	begin
		INTERNAL_I2C_REGISTER_CONFIG <= 14'd0;
		INTERNAL_I2C_REGISTER_TIMEOUT <= 14'd0;
	end
	else
	begin

		// Set configuration to i2c
		if(PADDR == 32'd8 && PSELx == 1'b1 && PWRITE == 1'b1 && PREADY == 1'b1)
		begin
			INTERNAL_I2C_REGISTER_CONFIG <= PWDATA[13:0];
		end
		else if(PADDR == 32'd12 && PSELx == 1'b1 && PWRITE == 1'b1 && PREADY == 1'b1)
		begin
			INTERNAL_I2C_REGISTER_TIMEOUT <= PWDATA[13:0];
		end
		else
		begin
			INTERNAL_I2C_REGISTER_CONFIG <= INTERNAL_I2C_REGISTER_CONFIG;
		end
		
	end

end 


endmodule"	"module apb_sva(
			input PRESETn,
			input [31:0] READ_DATA_ON_RX,
			input ERROR,
	    		input PCLK,
			input [13:0] INTERNAL_I2C_REGISTER_TIMEOUT,
			input [31:0] PWDATA,
			input INT_TX,
			input [31:0] WRITE_DATA_ON_TX,
			input  WR_ENA,
			input [31:0] PRDATA,
			input  RD_ENA,
			input [13:0] INTERNAL_I2C_REGISTER_CONFIG,
			input RX_EMPTY,
			input PREADY,
			input [31:0] PADDR,
			input PWRITE,
			input PENABLE,
			input INT_RX,
			input PSELx,
			input TX_EMPTY,
			input PSLVERR
);
property a5;
@(posedge PCLK) (ERROR == 0) |-> (PSLVERR == 0);
endproperty
assert_a5: assert property(a5);

property a4;
@(posedge PCLK) (ERROR == 1) |-> (PSLVERR == 1);
endproperty
assert_a4: assert property(a4);
property a3;
@(posedge PCLK) (TX_EMPTY == 1) |-> (INT_TX == 1);
endproperty
assert_a3: assert property(a3);

property a2;
@(posedge PCLK) (TX_EMPTY == 0) |-> (INT_TX == 0);
endproperty
assert_a2: assert property(a2);

property a1;
@(posedge PCLK) (RX_EMPTY == 0) |-> (INT_RX == 0);
endproperty
assert_a1: assert property(a1);

property a0;
@(posedge PCLK) (RX_EMPTY == 1) |-> (INT_RX == 1);
endproperty
assert_a0: assert property(a0);


endmodule"	https://github.com/achieve-lab/assertion_data_for_LLM/blob/NIPS_2024/Jasper_results/communication_controller_apb_to_i2c/apb/FPV_apb.tcl		
"////////////////////////////////////////////////////////////////////////////////////////////////
////                                                              							////
////                                                              							////
////  	This file is part of the project                 									////
////	""instruction_list_pipelined_processor_with_peripherals""								////
////                                                              							////
////  http://opencores.org/project,instruction_list_pipelined_processor_with_peripherals	////
////                                                              							////
////                                                              							////
//// 				 Author:                                                  				////
////      			- Mahesh Sukhdeo Palve													////
////																						////
////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////
////																						////
//// 											                 							////
////                                                              							////
//// 					This source file may be used and distributed without         		////
//// 					restriction provided that this copyright statement is not    		////
//// 					removed from the file and that any derivative work contains  		////
//// 					the original copyright notice and the associated disclaimer. 		////
////                                                              							////
//// 					This source file is free software; you can redistribute it   		////
//// 					and/or modify it under the terms of the GNU Lesser General   		////
//// 					Public License as published by the Free Software Foundation; 		////
////					either version 2.1 of the License, or (at your option) any   		////
//// 					later version.                                               		////
////                                                             							////
//// 					This source is distributed in the hope that it will be       		////
//// 					useful, but WITHOUT ANY WARRANTY; without even the implied   		////
//// 					warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR      		////
//// 					PURPOSE.  See the GNU Lesser General Public License for more 		////
//// 					details.                                                     		////
////                                                              							////
//// 					You should have received a copy of the GNU Lesser General    		////
//// 					Public License along with this source; if not, download it   		////
//// 					from http://www.opencores.org/lgpl.shtml                     		////
////                                                              							////
////////////////////////////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////////////////////////////
////                                                              							////
////                                                              							////
////  	This file is part of the project                 									////
////	""instruction_list_pipelined_processor_with_peripherals""								////
////                                                              							////
////  http://opencores.org/project,instruction_list_pipelined_processor_with_peripherals	////
////                                                              							////
////                                                              							////
//// 				 Author:                                                  				////
////      			- Mahesh Sukhdeo Palve													////
////																						////
////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////
////																						////
//// 											                 							////
////                                                              							////
//// 					This source file may be used and distributed without         		////
//// 					restriction provided that this copyright statement is not    		////
//// 					removed from the file and that any derivative work contains  		////
//// 					the original copyright notice and the associated disclaimer. 		////
////                                                              							////
//// 					This source file is free software; you can redistribute it   		////
//// 					and/or modify it under the terms of the GNU Lesser General   		////
//// 					Public License as published by the Free Software Foundation; 		////
////					either version 2.1 of the License, or (at your option) any   		////
//// 					later version.                                               		////
////                                                             							////
//// 					This source is distributed in the hope that it will be       		////
//// 					useful, but WITHOUT ANY WARRANTY; without even the implied   		////
//// 					warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR      		////
//// 					PURPOSE.  See the GNU Lesser General Public License for more 		////
//// 					details.                                                     		////
////                                                              							////
//// 					You should have received a copy of the GNU Lesser General    		////
//// 					Public License along with this source; if not, download it   		////
//// 					from http://www.opencores.org/lgpl.shtml                     		////
////                                                              							////
////////////////////////////////////////////////////////////////////////////////////////////////

// 8-bit Pipelined Processor defines

`define		immDataLen			8

// program counter & instruction register
`define		instAddrLen			10			// 10-bit address => 1024 inst in rom
`define		instLen				15			// 15-bit fixed-length instructions
`define		instOpCodeLen		5
`define		instFieldLen		10


// control unit
`define		cuStateLen			4		// max 16 states
`define		END					`instOpCodeLen'b0
`define		JMP					`instOpCodeLen'b1
`define		Ld						`instOpCodeLen'b10
`define		Ldi					`instOpCodeLen'b11
`define		ST						`instOpCodeLen'b100
`define		ADD					`instOpCodeLen'b101
`define		SUB					`instOpCodeLen'b110
`define		MUL					`instOpCodeLen'b111
`define		DIV					`instOpCodeLen'b1000
`define		AND					`instOpCodeLen'b1001
`define		OR						`instOpCodeLen'b1010
`define		XOR					`instOpCodeLen'b1011
`define		GrT					`instOpCodeLen'b1100
`define		GE						`instOpCodeLen'b1101
`define		EQ						`instOpCodeLen'b1110
`define		LE						`instOpCodeLen'b1111
`define		LT						`instOpCodeLen'b10000
`define		PRE					`instOpCodeLen'b10001
`define		ETY					`instOpCodeLen'b10010
`define		RST					`instOpCodeLen'b10011
`define		LdTC					`instOpCodeLen'b10100
`define		LdACC					`instOpCodeLen'b10101
`define		UARTrd				`instOpCodeLen'b10110
`define		UARTwr				`instOpCodeLen'b10111
`define		UARTstat				`instOpCodeLen'b11000
//`define		SPIxFER				`instOpCodeLen'b11001
//`define		SPIstat				`instOpCodeLen'b11010
//`define		SPIwBUF				`instOpCodeLen'b11011
//`define		SPIrBUF				`instOpCodeLen'b11100

// alu opcodes
`define		aluOpcodeLen		4
`define		AND_alu				`aluOpcodeLen'b0
`define		OR_alu				`aluOpcodeLen'b1
`define		XOR_alu				`aluOpcodeLen'b10
`define		GT_alu				`aluOpcodeLen'b11
`define		GE_alu				`aluOpcodeLen'b100
`define		EQ_alu				`aluOpcodeLen'b101
`define		LE_alu				`aluOpcodeLen'b110
`define		LT_alu				`aluOpcodeLen'b111
`define		ADD_alu				`aluOpcodeLen'b1000
`define		SUB_alu				`aluOpcodeLen'b1001
`define		MUL_alu				`aluOpcodeLen'b1010
`define		DIV_alu				`aluOpcodeLen'b1011
`define		LD_data				`aluOpcodeLen'b1100

// bit RAM
`define		bitRamAddrLen		7		// 7-bit address
`define		bitRamDepth			128	// 2^7 = 128 locations

// byte RAM
`define		byteRamLen			8		// 8-bit input
`define		byteRamAddrLen		7		// 7-bit address
`define		byteRamDepth		128	// 2^7 = 128 locations

// input register
`define		inputNumber			128	// 128 inputs
`define		inputAddrLen		7		// 7-bit address

// output register
`define		outputNumber		128	// 128 outputs
`define		outputAddrLen		7		// 7-bit address

// accumulator multiplexer
`define		accMuxSelLen			4		// 2^4 = 16 selections available for accumulator
`define		accMuxSelImmData		`accMuxSelLen'b0
`define		accMuxSelAluOut		`accMuxSelLen'b1
`define		accMuxSelTcLoad		`accMuxSelLen'b10
`define		accMuxSelTcAcc			`accMuxSelLen'b11
`define		accMuxSelUartData		`accMuxSelLen'b100
`define		accMuxSelUartStat		`accMuxSelLen'b101

// operand2 multiplexer
`define		op2MuxSelLen			4		// 2^4 = 16 selections available for op2
`define		op2MuxSelInput			`op2MuxSelLen'b0
`define		op2MuxSelOutput		`op2MuxSelLen'b1
`define		op2MuxSelBitRam		`op2MuxSelLen'b10
`define		op2MuxSelByteRam		`op2MuxSelLen'b11
`define		op2MuxSel4			`op2MuxSelLen'b100
`define		op2MuxSel5			`op2MuxSelLen'b101
`define		op2MuxSel6			`op2MuxSelLen'b110

//-----------------------------------------------------------------------------------------------------

// peripheral defines
`define		timerAndCounter_peripheral
`define		UART_peripheral


//-----------------------------------------------------------------------------------------------------

// Timer-Counter
`define		tcAccLen				8		// 8-bit accumulated value
`define		tcPresetLen			8		// 8-bit preset value
`define		tcAddrLen			4
`define		tcTypeLen			2		// max 4-types
`define		tcNumbers			8		// total 8 modules (4-timers, 4-counters)

`define		timerType1			`tcTypeLen'b0
`define		timerType2			`tcTypeLen'b1
`define		timerType3			`tcTypeLen'b10

`define		counterType1		`tcTypeLen'b1
`define		counterType2		`tcTypeLen'b10


//-----------------------------------------------------------------------------------------------------

// UART
`define		dataBits 			8
`define		sbTick 				16	// ticks for stop bits (16 for 1-stopBit)
`define		fifoWidth 			4
`define 		number_fifo_regs 	16
`define 		fifoCntrWidth 		5
`define 		fifoDepth 			16


module uartTrans (clk, reset, sTick, txDoneTick, din, tx, txStart);

		parameter dataBits = `dataBits;
		parameter sbTick = `sbTick;
		
		input [dataBits-1 :0] din;
		input clk, reset, sTick, txStart;
		output tx, txDoneTick;
		
		reg txDoneTick;
		
/*
should be impleneted as a 4-state FSM : idle, start, data, stop;

*/

	localparam [1:0] idle = 2'b00, start = 2'b01, data = 2'b10, stop = 2'b11;
	
		reg [1:0] stateReg, stateNext;	// current and next states
		reg [3:0] sReg, sNext;		//	counter
		reg [2:0] nReg, nNext;		// counter
		reg [7:0] bReg, bNext;		// perhaps keeps data to be sent
		reg		 txReg, txNext;	// current bit being transferred
		
		
		//	reset and non-reset conditions:
		
		always @ (posedge clk or posedge reset)
		begin
			if (reset)
			begin
				stateReg <= idle;
				sReg <= 1'b0;
				bReg <= 1'b0;
				nReg <= 1'b0;
				txReg <= 1'b1;
			end	// end if
			
			else
			begin
				stateReg <= stateNext;
				sReg <= sNext;
				bReg <= bNext;
				nReg <= nNext;
				txReg <= txNext;
			end	// end else
		
		end	// end always
		
		// FSM:
		
		always @ *
		begin
				stateNext = stateReg;
				sNext = sReg;
				bNext = bReg;
				nNext = nReg;
				txNext = txReg;
				
				txDoneTick = 1'b0;		// not done yet!
				
			case	(stateReg)
			
				idle	:	begin
								txNext = 1'b1;	// start bit '0'; thus, send '1' in idle
								
								if (txStart)
								begin
									txDoneTick = 1'b1;	// generate rd for fifo **
									stateNext = start;	// should go into start state
									sNext = 0;
								end	// end if txStart
							// in idle state unless txStart...
							end	// end idle case
							
				start	:	begin
								txNext = 0;
								txDoneTick = 1'b0;		// **
								bNext = din;		// take din into bReg
								if (sTick)
									if (sReg == 15)
									begin
										stateNext = data;
										sNext = 1'b0;
										nNext = 1'b0;
									end	// end if sReg==15
									
									else
										sNext = sReg + 1;	// keep incrementing sNext (sReg)
										// sReg = sNext on each clk edge !!
							end	// end start case
							
				data	:	begin
								txNext = bReg[0];	// keep sending LSB of bReg
								
								if (sTick)
									if (sReg == 15)
									begin
										sNext = 0;	// reset counter
										bNext = bReg >> 1;	// shift word to be sent
										
										if (nReg == (dataBits-1))
											stateNext = stop;
										else
											nNext = nReg +1;
									end	// end if sReg==15
								else
									sNext = sReg + 1;
				
							end	// end data state
							
				stop	:	begin
								txNext = 1'b1;
								
								if (sTick)
									if (sReg == sbTick-1)
									begin
										stateNext = idle;
										//txDoneTick = 1'b1; it's working as read signal to
										// fifo, so, used at starting . . .
									end //end if sReg==15
									else
										sNext = sReg + 1;
							end	// end stop state
			
			endcase
		
		end	// end always combinatorial

		
		// output bit-stream
		
		assign tx = txReg;

endmodule"	"
////////////////////////////////////////////////////////////////////////////////////////////////
////                                                              							////
////                                                              							////
////  	This file is part of the project                 									////
////	""instruction_list_pipelined_processor_with_peripherals""								////
////                                                              							////
////  http://opencores.org/project,instruction_list_pipelined_processor_with_peripherals	////
////                                                              							////
////                                                              							////
//// 				 Author:                                                  				////
////      			- Mahesh Sukhdeo Palve													////
////																						////
////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////
////																						////
//// 											                 							////
////                                                              							////
//// 					This source file may be used and distributed without         		////
//// 					restriction provided that this copyright statement is not    		////
//// 					removed from the file and that any derivative work contains  		////
//// 					the original copyright notice and the associated disclaimer. 		////
////                                                              							////
//// 					This source file is free software; you can redistribute it   		////
//// 					and/or modify it under the terms of the GNU Lesser General   		////
//// 					Public License as published by the Free Software Foundation; 		////
////					either version 2.1 of the License, or (at your option) any   		////
//// 					later version.                                               		////
////                                                             							////
//// 					This source is distributed in the hope that it will be       		////
//// 					useful, but WITHOUT ANY WARRANTY; without even the implied   		////
//// 					warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR      		////
//// 					PURPOSE.  See the GNU Lesser General Public License for more 		////
//// 					details.                                                     		////
////                                                              							////
//// 					You should have received a copy of the GNU Lesser General    		////
//// 					Public License along with this source; if not, download it   		////
//// 					from http://www.opencores.org/lgpl.shtml                     		////
////                                                              							////
////////////////////////////////////////////////////////////////////////////////////////////////

// 8-bit Pipelined Processor defines

`define		immDataLen			8

// program counter & instruction register
`define		instAddrLen			10			// 10-bit address => 1024 inst in rom
`define		instLen				15			// 15-bit fixed-length instructions
`define		instOpCodeLen		5
`define		instFieldLen		10


// control unit
`define		cuStateLen			4		// max 16 states
`define		END					`instOpCodeLen'b0
`define		JMP					`instOpCodeLen'b1
`define		Ld						`instOpCodeLen'b10
`define		Ldi					`instOpCodeLen'b11
`define		ST						`instOpCodeLen'b100
`define		ADD					`instOpCodeLen'b101
`define		SUB					`instOpCodeLen'b110
`define		MUL					`instOpCodeLen'b111
`define		DIV					`instOpCodeLen'b1000
`define		AND					`instOpCodeLen'b1001
`define		OR						`instOpCodeLen'b1010
`define		XOR					`instOpCodeLen'b1011
`define		GrT					`instOpCodeLen'b1100
`define		GE						`instOpCodeLen'b1101
`define		EQ						`instOpCodeLen'b1110
`define		LE						`instOpCodeLen'b1111
`define		LT						`instOpCodeLen'b10000
`define		PRE					`instOpCodeLen'b10001
`define		ETY					`instOpCodeLen'b10010
`define		RST					`instOpCodeLen'b10011
`define		LdTC					`instOpCodeLen'b10100
`define		LdACC					`instOpCodeLen'b10101
`define		UARTrd				`instOpCodeLen'b10110
`define		UARTwr				`instOpCodeLen'b10111
`define		UARTstat				`instOpCodeLen'b11000
//`define		SPIxFER				`instOpCodeLen'b11001
//`define		SPIstat				`instOpCodeLen'b11010
//`define		SPIwBUF				`instOpCodeLen'b11011
//`define		SPIrBUF				`instOpCodeLen'b11100

// alu opcodes
`define		aluOpcodeLen		4
`define		AND_alu				`aluOpcodeLen'b0
`define		OR_alu				`aluOpcodeLen'b1
`define		XOR_alu				`aluOpcodeLen'b10
`define		GT_alu				`aluOpcodeLen'b11
`define		GE_alu				`aluOpcodeLen'b100
`define		EQ_alu				`aluOpcodeLen'b101
`define		LE_alu				`aluOpcodeLen'b110
`define		LT_alu				`aluOpcodeLen'b111
`define		ADD_alu				`aluOpcodeLen'b1000
`define		SUB_alu				`aluOpcodeLen'b1001
`define		MUL_alu				`aluOpcodeLen'b1010
`define		DIV_alu				`aluOpcodeLen'b1011
`define		LD_data				`aluOpcodeLen'b1100

// bit RAM
`define		bitRamAddrLen		7		// 7-bit address
`define		bitRamDepth			128	// 2^7 = 128 locations

// byte RAM
`define		byteRamLen			8		// 8-bit input
`define		byteRamAddrLen		7		// 7-bit address
`define		byteRamDepth		128	// 2^7 = 128 locations

// input register
`define		inputNumber			128	// 128 inputs
`define		inputAddrLen		7		// 7-bit address

// output register
`define		outputNumber		128	// 128 outputs
`define		outputAddrLen		7		// 7-bit address

// accumulator multiplexer
`define		accMuxSelLen			4		// 2^4 = 16 selections available for accumulator
`define		accMuxSelImmData		`accMuxSelLen'b0
`define		accMuxSelAluOut		`accMuxSelLen'b1
`define		accMuxSelTcLoad		`accMuxSelLen'b10
`define		accMuxSelTcAcc			`accMuxSelLen'b11
`define		accMuxSelUartData		`accMuxSelLen'b100
`define		accMuxSelUartStat		`accMuxSelLen'b101

// operand2 multiplexer
`define		op2MuxSelLen			4		// 2^4 = 16 selections available for op2
`define		op2MuxSelInput			`op2MuxSelLen'b0
`define		op2MuxSelOutput		`op2MuxSelLen'b1
`define		op2MuxSelBitRam		`op2MuxSelLen'b10
`define		op2MuxSelByteRam		`op2MuxSelLen'b11
`define		op2MuxSel4			`op2MuxSelLen'b100
`define		op2MuxSel5			`op2MuxSelLen'b101
`define		op2MuxSel6			`op2MuxSelLen'b110

//-----------------------------------------------------------------------------------------------------

// peripheral defines
`define		timerAndCounter_peripheral
`define		UART_peripheral


//-----------------------------------------------------------------------------------------------------

// Timer-Counter
`define		tcAccLen				8		// 8-bit accumulated value
`define		tcPresetLen			8		// 8-bit preset value
`define		tcAddrLen			4
`define		tcTypeLen			2		// max 4-types
`define		tcNumbers			8		// total 8 modules (4-timers, 4-counters)

`define		timerType1			`tcTypeLen'b0
`define		timerType2			`tcTypeLen'b1
`define		timerType3			`tcTypeLen'b10

`define		counterType1		`tcTypeLen'b1
`define		counterType2		`tcTypeLen'b10


//-----------------------------------------------------------------------------------------------------

// UART
`define		dataBits 			8
`define		sbTick 				16	// ticks for stop bits (16 for 1-stopBit)
`define		fifoWidth 			4
`define 		number_fifo_regs 	16
`define 		fifoCntrWidth 		5
`define 		fifoDepth 			16

module uartTrans_sva(
		// input bit-stream
		input [1:0] stateReg, stateNext,	// current and next states
		input [2:0] nReg, nNext,		// counter
		input tx, txDoneTick,
		input		 txReg, txNext,	// current bit being transferred
		input [3:0] sReg, sNext,		//	counter
		input clk, reset, sTick, txStart,
		input [7:0] bReg, bNext,		// perhaps keeps data to be sent
		input [`dataBits-1 :0] din
);
property a10;
@(posedge clk) (txNext == 0) |=> (tx == 0);
endproperty
assert_a10: assert property(a10);

property a9;
@(posedge clk) (txNext == 1) |=> (tx == 1);
endproperty
assert_a9: assert property(a9);


property a6;
@(posedge clk) (stateReg[0] == 1) |-> (txDoneTick == 0);
endproperty
assert_a6: assert property(a6);

property a0;
@(posedge clk) (txStart == 0) |-> (txDoneTick == 0);
endproperty
assert_a0: assert property(a0);
endmodule"	https://github.com/achieve-lab/assertion_data_for_LLM/blob/NIPS_2024/Jasper_results/arithmetic_core_8-bit_piepelined_processor/uartTrans/FPV_uartTrans.tcl		
"////////////////////////////////////////////////////////////////////////////////////////////////
////                                                              							////
////                                                              							////
////  	This file is part of the project                 									////
////	""instruction_list_pipelined_processor_with_peripherals""								////
////                                                              							////
////  http://opencores.org/project,instruction_list_pipelined_processor_with_peripherals	////
////                                                              							////
////                                                              							////
//// 				 Author:                                                  				////
////      			- Mahesh Sukhdeo Palve													////
////																						////
////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////
////																						////
//// 											                 							////
////                                                              							////
//// 					This source file may be used and distributed without         		////
//// 					restriction provided that this copyright statement is not    		////
//// 					removed from the file and that any derivative work contains  		////
//// 					the original copyright notice and the associated disclaimer. 		////
////                                                              							////
//// 					This source file is free software; you can redistribute it   		////
//// 					and/or modify it under the terms of the GNU Lesser General   		////
//// 					Public License as published by the Free Software Foundation; 		////
////					either version 2.1 of the License, or (at your option) any   		////
//// 					later version.                                               		////
////                                                             							////
//// 					This source is distributed in the hope that it will be       		////
//// 					useful, but WITHOUT ANY WARRANTY; without even the implied   		////
//// 					warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR      		////
//// 					PURPOSE.  See the GNU Lesser General Public License for more 		////
//// 					details.                                                     		////
////                                                              							////
//// 					You should have received a copy of the GNU Lesser General    		////
//// 					Public License along with this source; if not, download it   		////
//// 					from http://www.opencores.org/lgpl.shtml                     		////
////                                                              							////
////////////////////////////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////////////////////////////
////                                                              							////
////                                                              							////
////  	This file is part of the project                 									////
////	""instruction_list_pipelined_processor_with_peripherals""								////
////                                                              							////
////  http://opencores.org/project,instruction_list_pipelined_processor_with_peripherals	////
////                                                              							////
////                                                              							////
//// 				 Author:                                                  				////
////      			- Mahesh Sukhdeo Palve													////
////																						////
////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////
////																						////
//// 											                 							////
////                                                              							////
//// 					This source file may be used and distributed without         		////
//// 					restriction provided that this copyright statement is not    		////
//// 					removed from the file and that any derivative work contains  		////
//// 					the original copyright notice and the associated disclaimer. 		////
////                                                              							////
//// 					This source file is free software; you can redistribute it   		////
//// 					and/or modify it under the terms of the GNU Lesser General   		////
//// 					Public License as published by the Free Software Foundation; 		////
////					either version 2.1 of the License, or (at your option) any   		////
//// 					later version.                                               		////
////                                                             							////
//// 					This source is distributed in the hope that it will be       		////
//// 					useful, but WITHOUT ANY WARRANTY; without even the implied   		////
//// 					warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR      		////
//// 					PURPOSE.  See the GNU Lesser General Public License for more 		////
//// 					details.                                                     		////
////                                                              							////
//// 					You should have received a copy of the GNU Lesser General    		////
//// 					Public License along with this source; if not, download it   		////
//// 					from http://www.opencores.org/lgpl.shtml                     		////
////                                                              							////
////////////////////////////////////////////////////////////////////////////////////////////////

// 8-bit Pipelined Processor defines

`define		immDataLen			8

// program counter & instruction register
`define		instAddrLen			10			// 10-bit address => 1024 inst in rom
`define		instLen				15			// 15-bit fixed-length instructions
`define		instOpCodeLen		5
`define		instFieldLen		10


// control unit
`define		cuStateLen			4		// max 16 states
`define		END					`instOpCodeLen'b0
`define		JMP					`instOpCodeLen'b1
`define		Ld						`instOpCodeLen'b10
`define		Ldi					`instOpCodeLen'b11
`define		ST						`instOpCodeLen'b100
`define		ADD					`instOpCodeLen'b101
`define		SUB					`instOpCodeLen'b110
`define		MUL					`instOpCodeLen'b111
`define		DIV					`instOpCodeLen'b1000
`define		AND					`instOpCodeLen'b1001
`define		OR						`instOpCodeLen'b1010
`define		XOR					`instOpCodeLen'b1011
`define		GrT					`instOpCodeLen'b1100
`define		GE						`instOpCodeLen'b1101
`define		EQ						`instOpCodeLen'b1110
`define		LE						`instOpCodeLen'b1111
`define		LT						`instOpCodeLen'b10000
`define		PRE					`instOpCodeLen'b10001
`define		ETY					`instOpCodeLen'b10010
`define		RST					`instOpCodeLen'b10011
`define		LdTC					`instOpCodeLen'b10100
`define		LdACC					`instOpCodeLen'b10101
`define		UARTrd				`instOpCodeLen'b10110
`define		UARTwr				`instOpCodeLen'b10111
`define		UARTstat				`instOpCodeLen'b11000
//`define		SPIxFER				`instOpCodeLen'b11001
//`define		SPIstat				`instOpCodeLen'b11010
//`define		SPIwBUF				`instOpCodeLen'b11011
//`define		SPIrBUF				`instOpCodeLen'b11100

// alu opcodes
`define		aluOpcodeLen		4
`define		AND_alu				`aluOpcodeLen'b0
`define		OR_alu				`aluOpcodeLen'b1
`define		XOR_alu				`aluOpcodeLen'b10
`define		GT_alu				`aluOpcodeLen'b11
`define		GE_alu				`aluOpcodeLen'b100
`define		EQ_alu				`aluOpcodeLen'b101
`define		LE_alu				`aluOpcodeLen'b110
`define		LT_alu				`aluOpcodeLen'b111
`define		ADD_alu				`aluOpcodeLen'b1000
`define		SUB_alu				`aluOpcodeLen'b1001
`define		MUL_alu				`aluOpcodeLen'b1010
`define		DIV_alu				`aluOpcodeLen'b1011
`define		LD_data				`aluOpcodeLen'b1100

// bit RAM
`define		bitRamAddrLen		7		// 7-bit address
`define		bitRamDepth			128	// 2^7 = 128 locations

// byte RAM
`define		byteRamLen			8		// 8-bit input
`define		byteRamAddrLen		7		// 7-bit address
`define		byteRamDepth		128	// 2^7 = 128 locations

// input register
`define		inputNumber			128	// 128 inputs
`define		inputAddrLen		7		// 7-bit address

// output register
`define		outputNumber		128	// 128 outputs
`define		outputAddrLen		7		// 7-bit address

// accumulator multiplexer
`define		accMuxSelLen			4		// 2^4 = 16 selections available for accumulator
`define		accMuxSelImmData		`accMuxSelLen'b0
`define		accMuxSelAluOut		`accMuxSelLen'b1
`define		accMuxSelTcLoad		`accMuxSelLen'b10
`define		accMuxSelTcAcc			`accMuxSelLen'b11
`define		accMuxSelUartData		`accMuxSelLen'b100
`define		accMuxSelUartStat		`accMuxSelLen'b101

// operand2 multiplexer
`define		op2MuxSelLen			4		// 2^4 = 16 selections available for op2
`define		op2MuxSelInput			`op2MuxSelLen'b0
`define		op2MuxSelOutput		`op2MuxSelLen'b1
`define		op2MuxSelBitRam		`op2MuxSelLen'b10
`define		op2MuxSelByteRam		`op2MuxSelLen'b11
`define		op2MuxSel4			`op2MuxSelLen'b100
`define		op2MuxSel5			`op2MuxSelLen'b101
`define		op2MuxSel6			`op2MuxSelLen'b110

//-----------------------------------------------------------------------------------------------------

// peripheral defines
`define		timerAndCounter_peripheral
`define		UART_peripheral


//-----------------------------------------------------------------------------------------------------

// Timer-Counter
`define		tcAccLen				8		// 8-bit accumulated value
`define		tcPresetLen			8		// 8-bit preset value
`define		tcAddrLen			4
`define		tcTypeLen			2		// max 4-types
`define		tcNumbers			8		// total 8 modules (4-timers, 4-counters)

`define		timerType1			`tcTypeLen'b0
`define		timerType2			`tcTypeLen'b1
`define		timerType3			`tcTypeLen'b10

`define		counterType1		`tcTypeLen'b1
`define		counterType2		`tcTypeLen'b10


//-----------------------------------------------------------------------------------------------------

// UART
`define		dataBits 			8
`define		sbTick 				16	// ticks for stop bits (16 for 1-stopBit)
`define		fifoWidth 			4
`define 		number_fifo_regs 	16
`define 		fifoCntrWidth 		5
`define 		fifoDepth 			16


module uartRec(clk, reset, sTick, rx, rxDoneTick, dOut);

		parameter dataBits = `dataBits;
		parameter sbTick = `sbTick;
		
		input clk, reset, sTick, rx;
		output rxDoneTick;
		output [dataBits-1:0] dOut;
		
		reg rxDoneTick;
		// states:
		
	localparam idle = 2'b00, start = 2'b01, data = 2'b10, stop = 2'b11;
	
		reg [1:0] stateReg, stateNext;	// current and next states
		reg [3:0] sReg, sNext;		//	counter
		reg [2:0] nReg, nNext;		// counter
		reg [7:0] bReg, bNext;		// data recieved in this..
		
		
		always @ (posedge clk or posedge reset)
		begin
			if (reset)
			begin
				stateReg <= idle;
				sReg <= 1'b0;
				bReg <= 1'b0;
				nReg <= 1'b0;
			end	// end if
			
			else
			begin
				stateReg <= stateNext;
				sReg <= sNext;
				bReg <= bNext;
				nReg <= nNext;
			end	// end else
		
		end	// end always
		
		
		
		// FSM next state logic:
		
		always @ *
		begin
		
				stateNext = stateReg;
				sNext = sReg;
				bNext = bReg;
				nNext = nReg;
				rxDoneTick = 1'b0;
				
			case (stateReg)
			
			idle	:	if (~rx)
						begin
							stateNext = start;	// start when rx is activated
							sNext = 0;	// initialize sampling counter
						end	// end if rx
						
			start	:	if (sTick)
							if (sReg == 7)
							begin
								stateNext = data;		// at middle of oversampled start
													// bit, go to data state
								sNext = 0;
								nNext = 0;
							end	// end if sReg==7
							
							else
								sNext = sReg + 1;	// otherwise keep increment sReg upto 7
			
			data	:	if (sTick)
							if (sReg == 15)	// if reached middle of next bit
							begin
								sNext = 0;	// reset counter
								bNext = {rx, bReg[7:1]};	// LSB first, and the
														//data recieved in bReg
								if (nReg == (dataBits-1))	// if all data recvd,
									stateNext = stop;	// go to stop bit(s) state
								else
									nNext = nReg + 1;
							end	// end if sReg==15
							
							else
								sNext = sReg + 1;	// otherwise keep increment sReg upto 15
							
			stop	:	if (sTick)
							if (sReg == (sbTick-1))
							begin
								stateNext = idle;		// done reception, go to idle state
								rxDoneTick = 1'b1;	// raise done tick!
							end	// end if sReg==sbTick-1
							
							else
								sNext = sReg + 1;		// otherwise keep increment sReg 
															//upto (sbTick-1)
			endcase
		
		end	// end always combinatorial
		
		
		// recvd data output
		
		assign dOut = bReg;


endmodule"	"////////////////////////////////////////////////////////////////////////////////////////////////
////                                                              							////
////                                                              							////
////  	This file is part of the project                 									////
////	""instruction_list_pipelined_processor_with_peripherals""								////
////                                                              							////
////  http://opencores.org/project,instruction_list_pipelined_processor_with_peripherals	////
////                                                              							////
////                                                              							////
//// 				 Author:                                                  				////
////      			- Mahesh Sukhdeo Palve													////
////																						////
////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////
////																						////
//// 											                 							////
////                                                              							////
//// 					This source file may be used and distributed without         		////
//// 					restriction provided that this copyright statement is not    		////
//// 					removed from the file and that any derivative work contains  		////
//// 					the original copyright notice and the associated disclaimer. 		////
////                                                              							////
//// 					This source file is free software; you can redistribute it   		////
//// 					and/or modify it under the terms of the GNU Lesser General   		////
//// 					Public License as published by the Free Software Foundation; 		////
////					either version 2.1 of the License, or (at your option) any   		////
//// 					later version.                                               		////
////                                                             							////
//// 					This source is distributed in the hope that it will be       		////
//// 					useful, but WITHOUT ANY WARRANTY; without even the implied   		////
//// 					warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR      		////
//// 					PURPOSE.  See the GNU Lesser General Public License for more 		////
//// 					details.                                                     		////
////                                                              							////
//// 					You should have received a copy of the GNU Lesser General    		////
//// 					Public License along with this source; if not, download it   		////
//// 					from http://www.opencores.org/lgpl.shtml                     		////
////                                                              							////
////////////////////////////////////////////////////////////////////////////////////////////////

// 8-bit Pipelined Processor defines

`define		immDataLen			8

// program counter & instruction register
`define		instAddrLen			10			// 10-bit address => 1024 inst in rom
`define		instLen				15			// 15-bit fixed-length instructions
`define		instOpCodeLen		5
`define		instFieldLen		10


// control unit
`define		cuStateLen			4		// max 16 states
`define		END					`instOpCodeLen'b0
`define		JMP					`instOpCodeLen'b1
`define		Ld						`instOpCodeLen'b10
`define		Ldi					`instOpCodeLen'b11
`define		ST						`instOpCodeLen'b100
`define		ADD					`instOpCodeLen'b101
`define		SUB					`instOpCodeLen'b110
`define		MUL					`instOpCodeLen'b111
`define		DIV					`instOpCodeLen'b1000
`define		AND					`instOpCodeLen'b1001
`define		OR						`instOpCodeLen'b1010
`define		XOR					`instOpCodeLen'b1011
`define		GrT					`instOpCodeLen'b1100
`define		GE						`instOpCodeLen'b1101
`define		EQ						`instOpCodeLen'b1110
`define		LE						`instOpCodeLen'b1111
`define		LT						`instOpCodeLen'b10000
`define		PRE					`instOpCodeLen'b10001
`define		ETY					`instOpCodeLen'b10010
`define		RST					`instOpCodeLen'b10011
`define		LdTC					`instOpCodeLen'b10100
`define		LdACC					`instOpCodeLen'b10101
`define		UARTrd				`instOpCodeLen'b10110
`define		UARTwr				`instOpCodeLen'b10111
`define		UARTstat				`instOpCodeLen'b11000
//`define		SPIxFER				`instOpCodeLen'b11001
//`define		SPIstat				`instOpCodeLen'b11010
//`define		SPIwBUF				`instOpCodeLen'b11011
//`define		SPIrBUF				`instOpCodeLen'b11100

// alu opcodes
`define		aluOpcodeLen		4
`define		AND_alu				`aluOpcodeLen'b0
`define		OR_alu				`aluOpcodeLen'b1
`define		XOR_alu				`aluOpcodeLen'b10
`define		GT_alu				`aluOpcodeLen'b11
`define		GE_alu				`aluOpcodeLen'b100
`define		EQ_alu				`aluOpcodeLen'b101
`define		LE_alu				`aluOpcodeLen'b110
`define		LT_alu				`aluOpcodeLen'b111
`define		ADD_alu				`aluOpcodeLen'b1000
`define		SUB_alu				`aluOpcodeLen'b1001
`define		MUL_alu				`aluOpcodeLen'b1010
`define		DIV_alu				`aluOpcodeLen'b1011
`define		LD_data				`aluOpcodeLen'b1100

// bit RAM
`define		bitRamAddrLen		7		// 7-bit address
`define		bitRamDepth			128	// 2^7 = 128 locations

// byte RAM
`define		byteRamLen			8		// 8-bit input
`define		byteRamAddrLen		7		// 7-bit address
`define		byteRamDepth		128	// 2^7 = 128 locations

// input register
`define		inputNumber			128	// 128 inputs
`define		inputAddrLen		7		// 7-bit address

// output register
`define		outputNumber		128	// 128 outputs
`define		outputAddrLen		7		// 7-bit address

// accumulator multiplexer
`define		accMuxSelLen			4		// 2^4 = 16 selections available for accumulator
`define		accMuxSelImmData		`accMuxSelLen'b0
`define		accMuxSelAluOut		`accMuxSelLen'b1
`define		accMuxSelTcLoad		`accMuxSelLen'b10
`define		accMuxSelTcAcc			`accMuxSelLen'b11
`define		accMuxSelUartData		`accMuxSelLen'b100
`define		accMuxSelUartStat		`accMuxSelLen'b101

// operand2 multiplexer
`define		op2MuxSelLen			4		// 2^4 = 16 selections available for op2
`define		op2MuxSelInput			`op2MuxSelLen'b0
`define		op2MuxSelOutput		`op2MuxSelLen'b1
`define		op2MuxSelBitRam		`op2MuxSelLen'b10
`define		op2MuxSelByteRam		`op2MuxSelLen'b11
`define		op2MuxSel4			`op2MuxSelLen'b100
`define		op2MuxSel5			`op2MuxSelLen'b101
`define		op2MuxSel6			`op2MuxSelLen'b110

//-----------------------------------------------------------------------------------------------------

// peripheral defines
`define		timerAndCounter_peripheral
`define		UART_peripheral


//-----------------------------------------------------------------------------------------------------

// Timer-Counter
`define		tcAccLen				8		// 8-bit accumulated value
`define		tcPresetLen			8		// 8-bit preset value
`define		tcAddrLen			4
`define		tcTypeLen			2		// max 4-types
`define		tcNumbers			8		// total 8 modules (4-timers, 4-counters)

`define		timerType1			`tcTypeLen'b0
`define		timerType2			`tcTypeLen'b1
`define		timerType3			`tcTypeLen'b10

`define		counterType1		`tcTypeLen'b1
`define		counterType2		`tcTypeLen'b10


//-----------------------------------------------------------------------------------------------------

// UART
`define		dataBits 			8
`define		sbTick 				16	// ticks for stop bits (16 for 1-stopBit)
`define		fifoWidth 			4
`define 		number_fifo_regs 	16
`define 		fifoCntrWidth 		5
`define 		fifoDepth 			16

module uartRec_sva(
		input [7:0] bReg, bNext,		// data recieved in this..
		// recvd data input
		input [1:0] stateReg, stateNext,	// current and next states
		input rxDoneTick,
		input [3:0] sReg, sNext,		//	counter
		input clk, reset, sTick, rx,
		input [`dataBits-1:0] dOut,
		input [2:0] nReg,
		input [2:0] nNext		// counter
);
property a4;
@(posedge clk) (stateReg[0] == 0) |-> (rxDoneTick == 0);
endproperty
assert_a4: assert property(a4);

property a1;
@(posedge clk) (sReg[2] == 0) |=> (rxDoneTick == 0);
endproperty
assert_a1: assert property(a1);

property a0;
@(posedge clk) (sReg[1] == 0) |=> (rxDoneTick == 0);
endproperty
assert_a0: assert property(a0);

property a3;
@(posedge clk) (nReg[1] == 0) |=> (rxDoneTick == 0);
endproperty
assert_a3: assert property(a3);

property a2;
@(posedge clk) (nReg[0] == 0) |=> (rxDoneTick == 0);
endproperty
assert_a2: assert property(a2);

property a5;
@(posedge clk) (sTick == 0) |-> (rxDoneTick == 0);
endproperty
assert_a5: assert property(a5);

property a6;
@(posedge clk) (sNext[0] == 0) |=> (rxDoneTick == 0);
endproperty
assert_a6: assert property(a6);

endmodule"	https://github.com/achieve-lab/assertion_data_for_LLM/blob/NIPS_2024/Jasper_llama_results/arithmetic_core_8-bit_piepelined_processor/uartRec/FPV_uartRec.tcl		
"//////////////////////////////////////////////////////////////////
////
////
//// 	TOP I2C BLOCK to I2C Core
////
////
////
//// This file is part of the APB to I2C project
////
//// http://www.opencores.org/cores/apbi2c/
////
////
////
//// Description
////
//// Implementation of APB IP core according to
////
//// apbi2c_spec IP core specification document.
////
////
////
//// To Do: Things are right here but always all block can suffer changes
////
////
////
////
////
//// Author(s): - Felipe Fernandes Da Costa, fefe2560@gmail.com
////		  Ronal Dario Celaya ,rcelaya.dario@gmail.com
////
///////////////////////////////////////////////////////////////// 
////
////
//// Copyright (C) 2009 Authors and OPENCORES.ORG
////
////
////
//// This source file may be used and distributed without
////
//// restriction provided that this copyright statement is not
////
//// removed from the file and that any derivative work contains
//// the original copyright notice and the associated disclaimer.
////
////
//// This source file is free software; you can redistribute it
////
//// and/or modify it under the terms of the GNU Lesser General
////
//// Public License as published by the Free Software Foundation;
//// either version 2.1 of the License, or (at your option) any
////
//// later version.
////
////
////
//// This source is distributed in the hope that it will be
////
//// useful, but WITHOUT ANY WARRANTY; without even the implied
////
//// warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR
////
//// PURPOSE. See the GNU Lesser General Public License for more
//// details.
////
////
////
//// You should have received a copy of the GNU Lesser General
////
//// Public License along with this source; if not, download it
////
//// from http://www.opencores.org/lgpl.shtml
////
////
///////////////////////////////////////////////////////////////////


`timescale 1ns/1ps //timescale 

module module_i2c#(
			//THIS IS USED ONLY LIKE PARAMETER TO BEM CONFIGURABLE
			parameter integer DWIDTH = 32,
			parameter integer AWIDTH = 14
		)
		(
		//I2C INTERFACE WITH ANOTHER BLOCKS
		 input PCLK,
		 input PRESETn,
		 
		//INTERFACE WITH FIFO TRANSMISSION
		 input fifo_tx_f_full,
		 input fifo_tx_f_empty,
		 input [DWIDTH-1:0] fifo_tx_data_out,

		//INTERFACE WITH FIFO RECEIVER
		 input fifo_rx_f_full,
		 input fifo_rx_f_empty,
		 output reg fifo_rx_wr_en,
		 output reg [DWIDTH-1:0] fifo_rx_data_in, 

		//INTERFACE WITH REGISTER CONFIGURATION
		 input [AWIDTH-1:0] DATA_CONFIG_REG,
 		 input [AWIDTH-1:0] TIMEOUT_TX,
		
		//INTERFACE TO APB AND READ FOR FIFO   
		 output reg fifo_tx_rd_en,
		 output   TX_EMPTY,
		 output   RX_EMPTY,
		 output ERROR,
		 output ENABLE_SDA,
		 output ENABLE_SCL,

		//I2C BI DIRETIONAL PORTS
		inout SDA,
		inout SCL
		 

		 );

//THIS IS USED TO GENERATE INTERRUPTIONS
assign TX_EMPTY = (fifo_tx_f_empty == 1'b1)? 1'b1:1'b0;
assign RX_EMPTY = (fifo_rx_f_empty == 1'b1)? 1'b1:1'b0;

	//THIS COUNT IS USED TO CONTROL DATA ACCROSS FSM	
	reg [1:0] count_tx;
	reg [1:0] count_rx;
	//CONTROL CLOCK AND COUNTER
	reg [11:0] count_send_data;
	reg [11:0] count_receive_data;
	reg [11:0] count_timeout;
	reg BR_CLK_O;
	reg SDA_OUT;

	reg BR_CLK_O_RX;
	reg SDA_OUT_RX;

	//RESPONSE USED TO HOLD SIGNAL TO ACK OR NACK
	reg RESPONSE;

//    PARAMETERS USED TO STATE MACHINE

localparam [5:0] IDLE = 6'd0, //IDLE

	   START = 6'd1,//START BIT

	     CONTROLIN_1 = 6'd2, //START BYTE
	     CONTROLIN_2 = 6'd3,
	     CONTROLIN_3 = 6'd4,
             CONTROLIN_4 = 6'd5,
	     CONTROLIN_5 = 6'd6,
	     CONTROLIN_6 = 6'd7,
             CONTROLIN_7 = 6'd8,
             CONTROLIN_8 = 6'd9, //END FIRST BYTE

	     RESPONSE_CIN =6'd10, //RESPONSE

	     ADDRESS_1 = 6'd11,//START BYTE
	     ADDRESS_2 = 6'd12,
	     ADDRESS_3 = 6'd13,
             ADDRESS_4 = 6'd14,
	     ADDRESS_5 = 6'd15,
	     ADDRESS_6 = 6'd16,
             ADDRESS_7 = 6'd17,
             ADDRESS_8 = 6'd18,//END FIRST BYTE

	     RESPONSE_ADDRESS =6'd19, //RESPONSE

	     DATA0_1 = 6'd20,//START BYTE
	     DATA0_2 = 6'd21,
	     DATA0_3 = 6'd22,
             DATA0_4 = 6'd23,
	     DATA0_5 = 6'd24,
	     DATA0_6 = 6'd25,
             DATA0_7 = 6'd26,
             DATA0_8 = 6'd27,//END FIRST BYTE

	     RESPONSE_DATA0_1 = 6'd28,  //RESPONSE
	   
	     DATA1_1 = 6'd29,//START BYTE
	     DATA1_2 = 6'd30,
	     DATA1_3 = 6'd31,
             DATA1_4 = 6'd32,
	     DATA1_5 = 6'd33,
	     DATA1_6 = 6'd34,
             DATA1_7 = 6'd35,
             DATA1_8 = 6'd36,//END FIRST BYTE

	     RESPONSE_DATA1_1 = 6'd37,//RESPONSE

	     DELAY_BYTES = 6'd38,//USED ONLY IN ACK TO DELAY BETWEEN
	     NACK = 6'd39,//USED ONLY IN ACK TO DELAY BETWEEN BYTES
	     STOP = 6'd40;//USED TO SEND STOP BIT

	//STATE CONTROL 
	reg [5:0] state_tx;
	reg [5:0] next_state_tx;

//ASSIGN REGISTERS TO BIDIRETIONAL PORTS
assign SDA =(DATA_CONFIG_REG[0] == 1'b1 & DATA_CONFIG_REG[1] == 1'b0 & state_tx != RESPONSE_CIN & state_tx != RESPONSE_ADDRESS & state_tx != RESPONSE_DATA0_1 & state_tx != RESPONSE_DATA1_1)?SDA_OUT:SDA_OUT_RX;


assign SCL = (DATA_CONFIG_REG[0] == 1'b1 & DATA_CONFIG_REG[1] == 1'b0)?BR_CLK_O:BR_CLK_O_RX;

//STANDARD ERROR
assign ERROR = (DATA_CONFIG_REG[0] == 1'b1 & DATA_CONFIG_REG[1] == 1'b1)?1'b1:1'b0;


//COMBINATIONAL BLOCK TO   
always@(*)
begin

	//THE FUN START HERE :-)
	//COMBINATIONAL UPDATE STATE BE CAREFUL WITH WHAT YOU MAKE HERE
	next_state_tx=state_tx;

	case(state_tx)//state_   IS MORE SECURE CHANGE ONLY IF YOU KNOW WHAT ARE YOU DOING 
	IDLE:
	begin
		//OBEYING SPEC
		if(DATA_CONFIG_REG[0] == 1'b0 && (fifo_tx_f_full == 1'b1 || fifo_tx_f_empty == 1'b0) && DATA_CONFIG_REG[1] == 1'b0)
		begin
			next_state_tx   = IDLE;
		end
		else if(DATA_CONFIG_REG[0] == 1'b1 && (fifo_tx_f_full == 1'b1 || fifo_tx_f_empty == 1'b0) && DATA_CONFIG_REG[1] == 1'b1)
		begin
			next_state_tx   = IDLE;
		end
		else if(DATA_CONFIG_REG[0] == 1'b1 && ((fifo_tx_f_full == 1'b0 && fifo_tx_f_empty == 1'b0) || fifo_tx_f_full == 1'b1) && DATA_CONFIG_REG[1] == 1'b0 && count_timeout < TIMEOUT_TX)
		begin
			next_state_tx   = START;
		end


	end
	START://THIS IS USED TOO ALL STATE MACHINES THE COUNTER_SEND_DATA
	begin
		if(count_send_data != DATA_CONFIG_REG[13:2])
		begin
			next_state_tx   = START;
		end
		else
		begin
			next_state_tx   = CONTROLIN_1;
		end
		
	end
	CONTROLIN_1:
	begin
		if(count_send_data != DATA_CONFIG_REG[13:2])
		begin
			next_state_tx  = CONTROLIN_1;
		end
		else
		begin
			next_state_tx  =  CONTROLIN_2;
		end

	end
	CONTROLIN_2:
	begin

		if(count_send_data != DATA_CONFIG_REG[13:2])
		begin
			next_state_tx   = CONTROLIN_2;
		end
		else
		begin
			next_state_tx   = CONTROLIN_3;
		end

	end
	CONTROLIN_3:
	begin

		if(count_send_data != DATA_CONFIG_REG[13:2])
		begin
			next_state_tx  =  CONTROLIN_3;
		end
		else
		begin
			next_state_tx   = CONTROLIN_4;
		end		
	end
	CONTROLIN_4:
	begin

		if(count_send_data != DATA_CONFIG_REG[13:2])
		begin
			next_state_tx   = CONTROLIN_4;
		end
		else
		begin
			next_state_tx   = CONTROLIN_5;
		end		
	end
	CONTROLIN_5:
	begin

		if(count_send_data != DATA_CONFIG_REG[13:2])
		begin
			next_state_tx = CONTROLIN_5;
		end
		else
		begin
			next_state_tx = CONTROLIN_6;
		end		
	end
	CONTROLIN_6:
	begin

		if(count_send_data != DATA_CONFIG_REG[13:2])
		begin
			next_state_tx = CONTROLIN_6;
		end
		else
		begin
			next_state_tx = CONTROLIN_7;
		end		
	end
	CONTROLIN_7:
	begin

		if(count_send_data != DATA_CONFIG_REG[13:2])
		begin
			next_state_tx = CONTROLIN_7;
		end
		else
		begin
			next_state_tx = CONTROLIN_8;
		end		
	end
	CONTROLIN_8:
	begin

		if(count_send_data != DATA_CONFIG_REG[13:2])
		begin
			next_state_tx  = CONTROLIN_8;
		end
		else 
		begin
			next_state_tx  = RESPONSE_CIN;
		end		
	end
	RESPONSE_CIN:
	begin

		if(count_send_data != DATA_CONFIG_REG[13:2])
		begin
			next_state_tx = RESPONSE_CIN;
		end
		else if(RESPONSE == 1'b0)//ACK
		begin 
			next_state_tx = DELAY_BYTES;
		end
		else if(RESPONSE == 1'b1)//NACK
		begin
			next_state_tx = NACK;
		end	
		
	end

	//NOW SENDING ADDRESS
	ADDRESS_1:
	begin
		if(count_send_data != DATA_CONFIG_REG[13:2])
		begin
			next_state_tx  = ADDRESS_1;
		end
		else
		begin
			next_state_tx  =  ADDRESS_2;
		end	
	end
	ADDRESS_2:
	begin
		if(count_send_data != DATA_CONFIG_REG[13:2])
		begin
			next_state_tx = ADDRESS_2;
		end
		else
		begin
			next_state_tx = ADDRESS_3;
		end	
	end
	ADDRESS_3:
	begin
		if(count_send_data != DATA_CONFIG_REG[13:2])
		begin
			next_state_tx = ADDRESS_3;
		end
		else
		begin
			next_state_tx = ADDRESS_4;
		end	
	end
	ADDRESS_4:
	begin
		if(count_send_data != DATA_CONFIG_REG[13:2])
		begin
			next_state_tx = ADDRESS_4;
		end
		else
		begin
			next_state_tx = ADDRESS_5;
		end	
	end
	ADDRESS_5:
	begin
		if(count_send_data != DATA_CONFIG_REG[13:2])
		begin
			next_state_tx = ADDRESS_5;
		end
		else
		begin
			next_state_tx = ADDRESS_6;
		end	
	end
	ADDRESS_6:
	begin
		if(count_send_data != DATA_CONFIG_REG[13:2])
		begin
			next_state_tx = ADDRESS_6;
		end
		else
		begin
			next_state_tx = ADDRESS_7;
		end	
	end
	ADDRESS_7:
	begin
		if(count_send_data != DATA_CONFIG_REG[13:2])
		begin
			next_state_tx = ADDRESS_7;
		end
		else
		begin
			next_state_tx = ADDRESS_8;
		end	
	end
	ADDRESS_8:
	begin
		if(count_send_data != DATA_CONFIG_REG[13:2])
		begin
			next_state_tx = ADDRESS_8;
		end
		else
		begin
			next_state_tx = RESPONSE_ADDRESS;
		end	
	end
	RESPONSE_ADDRESS:
	begin
		if(count_send_data != DATA_CONFIG_REG[13:2])
		begin
			next_state_tx = RESPONSE_ADDRESS;
		end
		else if(RESPONSE == 1'b0)//ACK
		begin 
			next_state_tx = DELAY_BYTES;
		end
		else if(RESPONSE == 1'b1)//NACK --> RESTART CONDITION AND BACK TO START BYTE AGAIN
		begin
			next_state_tx = NACK;
		end	
	end
	
	//data in
	DATA0_1:
	begin
		if(count_send_data != DATA_CONFIG_REG[13:2])
		begin
			next_state_tx = DATA0_1;
		end
		else
		begin
			next_state_tx = DATA0_2;
		end
	end
	DATA0_2:
	begin
		if(count_send_data != DATA_CONFIG_REG[13:2])
		begin
			next_state_tx = DATA0_2;
		end
		else
		begin
			next_state_tx = DATA0_3;
		end
	end
	DATA0_3:
	begin
		if(count_send_data != DATA_CONFIG_REG[13:2])
		begin
			next_state_tx = DATA0_3;
		end
		else
		begin
			next_state_tx = DATA0_4;
		end
	end
	DATA0_4:
	begin
		if(count_send_data != DATA_CONFIG_REG[13:2])
		begin
			next_state_tx = DATA0_4;
		end
		else
		begin
			next_state_tx = DATA0_5;
		end
	end
	DATA0_5:
	begin
		if(count_send_data != DATA_CONFIG_REG[13:2])
		begin
			next_state_tx = DATA0_5;
		end
		else
		begin
			next_state_tx   = DATA0_6;
		end
	end
	DATA0_6:
	begin
		if(count_send_data != DATA_CONFIG_REG[13:2])
		begin
			next_state_tx  = DATA0_6;
		end
		else
		begin
			next_state_tx  = DATA0_7;
		end
	end
	DATA0_7:
	begin
		if(count_send_data != DATA_CONFIG_REG[13:2])
		begin
			next_state_tx  = DATA0_7;
		end
		else
		begin
			next_state_tx  = DATA0_8;
		end
	end
	DATA0_8:
	begin
		if(count_send_data != DATA_CONFIG_REG[13:2])
		begin
			next_state_tx  = DATA0_8;
		end
		else
		begin
			next_state_tx  =  RESPONSE_DATA0_1;
		end
	end
	RESPONSE_DATA0_1:
	begin
		if(count_send_data != DATA_CONFIG_REG[13:2])
		begin
			next_state_tx  =  RESPONSE_DATA0_1;
		end
		else if(RESPONSE == 1'b0)//ACK
		begin 
			next_state_tx  =   DELAY_BYTES;
		end
		else if(RESPONSE == 1'b1)//NACK
		begin
			next_state_tx  =   NACK;
		end	
	end

	//second byte
	DATA1_1:
	begin
		if(count_send_data != DATA_CONFIG_REG[13:2])
		begin
			next_state_tx  = DATA1_1;
		end
		else
		begin
			next_state_tx  = DATA1_2;
		end
	end
	DATA1_2:
	begin
		if(count_send_data != DATA_CONFIG_REG[13:2])
		begin
			next_state_tx = DATA1_2;
		end
		else
		begin
			next_state_tx = DATA1_3;
		end
	end
	DATA1_3:
	begin
		if(count_send_data != DATA_CONFIG_REG[13:2])
		begin
			next_state_tx  = DATA1_3;
		end
		else
		begin
			next_state_tx  =  DATA1_4;
		end
	end
	DATA1_4:
	begin
		if(count_send_data != DATA_CONFIG_REG[13:2])
		begin
			next_state_tx  = DATA1_4;
		end
		else
		begin
			next_state_tx  = DATA1_5;
		end
	end
	DATA1_5:
	begin
		if(count_send_data != DATA_CONFIG_REG[13:2])
		begin
			next_state_tx = DATA1_5;
		end
		else
		begin
			next_state_tx = DATA1_6;
		end
	end
	DATA1_6:
	begin
		if(count_send_data != DATA_CONFIG_REG[13:2])
		begin
			next_state_tx  =  DATA1_6;
		end
		else
		begin
			next_state_tx  =  DATA1_7;
		end
	end
	DATA1_7:
	begin
		if(count_send_data != DATA_CONFIG_REG[13:2])
		begin
			next_state_tx =  DATA1_7;
		end
		else
		begin
			next_state_tx =  DATA1_8;
		end
	end
	DATA1_8:
	begin
		if(count_send_data != DATA_CONFIG_REG[13:2])
		begin
			next_state_tx = DATA1_8;
		end
		else
		begin
			next_state_tx = RESPONSE_DATA1_1;
		end
	end
	RESPONSE_DATA1_1:
	begin
		if(count_send_data != DATA_CONFIG_REG[13:2])
		begin
			next_state_tx   =  RESPONSE_DATA1_1;
		end
		else if(RESPONSE == 1'b0)//ACK
		begin 
			next_state_tx   =  DELAY_BYTES;
		end
		else if(RESPONSE == 1'b1)//NACK
		begin
			next_state_tx   =  NACK;
		end	
	end
	DELAY_BYTES://THIS FORM WORKS 
	begin

		
		if(count_send_data != DATA_CONFIG_REG[13:2])
		begin
			next_state_tx =  DELAY_BYTES;
		end
		else
		begin

			if(count_tx == 2'd0)
			begin
				next_state_tx = ADDRESS_1;
			end
			else if(count_tx   == 2'd1)
			begin
				next_state_tx = DATA0_1;
			end
			else if(count_tx   == 2'd2)
			begin
				next_state_tx = DATA1_1;
			end
			else if(count_tx   == 2'd3)
			begin
				next_state_tx = STOP;
			end
			
		end

	end
	NACK://NOT TESTED YET !!!!
	begin
		if(count_send_data != DATA_CONFIG_REG[13:2]*2'd2)
		begin
			next_state_tx  = NACK;
		end
		else
		begin
			if(count_tx == 2'd0)
			begin
				next_state_tx = CONTROLIN_1;
			end
			else if(count_tx == 2'd1)
			begin
				next_state_tx = ADDRESS_1;
			end
			else if(count_tx  == 2'd2)
			begin
				next_state_tx   = DATA0_1;
			end
			else if(count_tx == 2'd3)
			begin
				next_state_tx = DATA1_1;
			end
		end
	end
	STOP://THIS WORK
	begin
		if(count_send_data != DATA_CONFIG_REG[13:2])
		begin
			next_state_tx = STOP;
		end
		else
		begin
			next_state_tx = IDLE;
		end
	end
	default:
	begin
		next_state_tx =  IDLE;
	end
	endcase


end



//SEQUENTIAL   
always@(posedge PCLK)
begin

	//RESET SYNC
	if(!PRESETn)
	begin
		//SIGNALS MUST BE RESETED
		count_send_data <= 12'd0;
		state_tx   <= IDLE;	
		SDA_OUT<= 1'b1;
		fifo_tx_rd_en <= 1'b0;
		count_tx   <= 2'd0;
		BR_CLK_O <= 1'b1;
		RESPONSE<= 1'b0;	
	end
	else
	begin
		
		// SEQUENTIAL FUN START
		state_tx  <= next_state_tx;

		case(state_tx)
		IDLE:
		begin

			fifo_tx_rd_en <= 1'b0;
			
 
			if(DATA_CONFIG_REG[0] == 1'b0 && (fifo_tx_f_full == 1'b1 ||fifo_tx_f_empty == 1'b0) && DATA_CONFIG_REG[1] == 1'b0)
			begin
				count_send_data <= 12'd0;
				SDA_OUT<= 1'b1;
				BR_CLK_O <= 1'b1;
			end
			else if(DATA_CONFIG_REG[0] == 1'b1 && ((fifo_tx_f_empty == 1'b0 && fifo_tx_f_full == 1'b0 )|| fifo_tx_f_full == 1'b1 ) && DATA_CONFIG_REG[1] == 1'b0)
			begin
				count_send_data <= count_send_data + 12'd1;
				SDA_OUT<=1'b0;			
			end
			else if(DATA_CONFIG_REG[0] == 1'b1 && (fifo_tx_f_full == 1'b1 ||fifo_tx_f_empty == 1'b0) && DATA_CONFIG_REG[1] == 1'b1)
			begin
				count_send_data <= 12'd0;
				SDA_OUT<= 1'b1;
				BR_CLK_O <= 1'b1;
			end			

		end
		START:
		begin

			if(count_send_data < DATA_CONFIG_REG[13:2])
			begin
				count_send_data <= count_send_data + 12'd1;
				BR_CLK_O <= 1'b0;
			end
			else
			begin
				count_send_data <= 12'd0;					
			end	

			if(count_send_data == DATA_CONFIG_REG[13:2]- 12'd1)
			begin
				SDA_OUT<=fifo_tx_data_out[0:0];
				count_tx   <= 2'd0;
			end

		end
		CONTROLIN_1:
		begin

			

			if(count_send_data < DATA_CONFIG_REG[13:2])
			begin
				
				count_send_data <= count_send_data + 12'd1;
				SDA_OUT<=fifo_tx_data_out[0:0];	

								
				if(count_send_data < DATA_CONFIG_REG[13:2]/12'd4)
				begin
					BR_CLK_O <= 1'b0;
				end
				else if(count_send_data >= DATA_CONFIG_REG[13:2]/12'd4 && count_send_data < (DATA_CONFIG_REG[13:2]-(DATA_CONFIG_REG[13:2]/12'd4))-12'd1)
				begin
					BR_CLK_O <= 1'b1;
				end
				else
				begin
					BR_CLK_O <= 1'b0;
				end			
			end
			else
			begin
				count_send_data <= 12'd0;
				SDA_OUT<=fifo_tx_data_out[1:1];
			end

				
		end
		
		CONTROLIN_2:
		begin

			

			if(count_send_data < DATA_CONFIG_REG[13:2])
			begin
				count_send_data <= count_send_data + 12'd1;
				SDA_OUT<=fifo_tx_data_out[1:1];

				if(count_send_data < DATA_CONFIG_REG[13:2]/12'd4)
				begin
					BR_CLK_O <= 1'b0;
				end
				else if(count_send_data >= DATA_CONFIG_REG[13:2]/12'd4 && count_send_data < (DATA_CONFIG_REG[13:2]-(DATA_CONFIG_REG[13:2]/12'd4))-12'd1)
				begin
					BR_CLK_O <= 1'b1;
				end
				else
				begin
					BR_CLK_O <= 1'b0;
				end		
			end
			else
			begin
				count_send_data <= 12'd0;
				SDA_OUT<=fifo_tx_data_out[2:2];
			end
				
		end

		CONTROLIN_3:
		begin

			

			if(count_send_data < DATA_CONFIG_REG[13:2])
			begin
				count_send_data <= count_send_data + 12'd1;
				SDA_OUT<=fifo_tx_data_out[2:2];

				if(count_send_data < DATA_CONFIG_REG[13:2]/12'd4)
				begin
					BR_CLK_O <= 1'b0;
				end
				else if(count_send_data >= DATA_CONFIG_REG[13:2]/12'd4 && count_send_data < (DATA_CONFIG_REG[13:2]-(DATA_CONFIG_REG[13:2]/12'd4))-12'd1)
				begin
					BR_CLK_O <= 1'b1;
				end
				else
				begin
					BR_CLK_O <= 1'b0;
				end		
			end
			else
			begin
				count_send_data <= 12'd0;
				SDA_OUT<=fifo_tx_data_out[3:3];
			end	


				
		end
		CONTROLIN_4:
		begin

			if(count_send_data < DATA_CONFIG_REG[13:2])
			begin
				count_send_data <= count_send_data + 12'd1;
				SDA_OUT<=fifo_tx_data_out[3:3];

				if(count_send_data < DATA_CONFIG_REG[13:2]/12'd4)
				begin
					BR_CLK_O <= 1'b0;
				end
				else if(count_send_data >= DATA_CONFIG_REG[13:2]/12'd4 && count_send_data < (DATA_CONFIG_REG[13:2]-(DATA_CONFIG_REG[13:2]/12'd4))-12'd1)
				begin
					BR_CLK_O <= 1'b1;
				end
				else
				begin
					BR_CLK_O <= 1'b0;
				end				
			end
			else
			begin
				count_send_data <= 12'd0;
				SDA_OUT<=fifo_tx_data_out[4:4];
			end
				
		end

		CONTROLIN_5:
		begin

			

			if(count_send_data < DATA_CONFIG_REG[13:2])
			begin
				count_send_data <= count_send_data + 12'd1;
				SDA_OUT<=fifo_tx_data_out[4:4];

				if(count_send_data < DATA_CONFIG_REG[13:2]/12'd4)
				begin
					BR_CLK_O <= 1'b0;
				end
				else if(count_send_data >= DATA_CONFIG_REG[13:2]/12'd4 && count_send_data < (DATA_CONFIG_REG[13:2]-(DATA_CONFIG_REG[13:2]/12'd4))-12'd1)
				begin
					BR_CLK_O <= 1'b1;
				end
				else
				begin
					BR_CLK_O <= 1'b0;
				end			
			end
			else
			begin
				count_send_data <= 12'd0;
				SDA_OUT<=fifo_tx_data_out[5:5];
			end	

		end
		CONTROLIN_6:
		begin

			if(count_send_data < DATA_CONFIG_REG[13:2])
			begin
				count_send_data <= count_send_data + 12'd1;
				SDA_OUT<=fifo_tx_data_out[5:5];

				if(count_send_data < DATA_CONFIG_REG[13:2]/12'd4)
				begin
					BR_CLK_O <= 1'b0;
				end
				else if(count_send_data >= DATA_CONFIG_REG[13:2]/12'd4 && count_send_data < (DATA_CONFIG_REG[13:2]-(DATA_CONFIG_REG[13:2]/12'd4))-12'd1)
				begin
					BR_CLK_O <= 1'b1;
				end
				else
				begin
					BR_CLK_O <= 1'b0;
				end	
			end
			else
			begin
				count_send_data <= 12'd0;
				SDA_OUT<=fifo_tx_data_out[6:6];
			end	

				
		end

		CONTROLIN_7:
		begin

			if(count_send_data < DATA_CONFIG_REG[13:2])
			begin
				count_send_data <= count_send_data + 12'd1;
				SDA_OUT<=fifo_tx_data_out[6:6];

				if(count_send_data < DATA_CONFIG_REG[13:2]/12'd4)
				begin
					BR_CLK_O <= 1'b0;
				end
				else if(count_send_data >= DATA_CONFIG_REG[13:2]/12'd4 && count_send_data < (DATA_CONFIG_REG[13:2]-(DATA_CONFIG_REG[13:2]/12'd4))-12'd1)
				begin
					BR_CLK_O <= 1'b1;
				end
				else
				begin
					BR_CLK_O <= 1'b0;
				end	
			end
			else
			begin
				count_send_data <= 12'd0;
				SDA_OUT<=fifo_tx_data_out[7:7];
			end	

				
		end
		CONTROLIN_8:
		begin

			if(count_send_data < DATA_CONFIG_REG[13:2])
			begin
				count_send_data <= count_send_data + 12'd1;
				SDA_OUT<=fifo_tx_data_out[7:7];

				if(count_send_data < DATA_CONFIG_REG[13:2]/12'd4)
				begin
					BR_CLK_O <= 1'b0;
				end
				else if(count_send_data >= DATA_CONFIG_REG[13:2]/12'd4 && count_send_data < (DATA_CONFIG_REG[13:2]-(DATA_CONFIG_REG[13:2]/12'd4))-12'd1)
				begin
					BR_CLK_O <= 1'b1;
				end
				else
				begin
					BR_CLK_O <= 1'b0;
				end		
			end
			else
			begin
				count_send_data <= 12'd0;
				SDA_OUT<= 1'b0;
			end

				
		end
		RESPONSE_CIN:
		begin

			if(count_send_data < DATA_CONFIG_REG[13:2])
			begin
				count_send_data <= count_send_data + 12'd1;

				//LETS TRY USE THIS BUT I DONT THINK IF WORKS  
				RESPONSE<= SDA;

				if(count_send_data < DATA_CONFIG_REG[13:2]/12'd4)
				begin
					BR_CLK_O <= 1'b0;
				end
				else if(count_send_data >= DATA_CONFIG_REG[13:2]/12'd4 && count_send_data < (DATA_CONFIG_REG[13:2]-(DATA_CONFIG_REG[13:2]/12'd4))-12'd1)
				begin
					BR_CLK_O <= 1'b1;
				end
				else
				begin
					BR_CLK_O <= 1'b0;
				end		
			end
			else
			begin
				count_send_data <= 12'd0;
			end	


		end
		ADDRESS_1:
		begin

			if(count_send_data < DATA_CONFIG_REG[13:2])
			begin
				count_send_data <= count_send_data + 12'd1;
				SDA_OUT<=fifo_tx_data_out[8:8];

				if(count_send_data < DATA_CONFIG_REG[13:2]/12'd4)
				begin
					BR_CLK_O <= 1'b0;
				end
				else if(count_send_data >= DATA_CONFIG_REG[13:2]/12'd4 && count_send_data < (DATA_CONFIG_REG[13:2]-(DATA_CONFIG_REG[13:2]/12'd4))-12'd1)
				begin
					BR_CLK_O <= 1'b1;
				end
				else
				begin
					BR_CLK_O <= 1'b0;
				end		
			end
			else
			begin
				count_send_data <= 12'd0;
				SDA_OUT<=fifo_tx_data_out[9:9];
			end	
				
		end		
		ADDRESS_2:
		begin

			if(count_send_data < DATA_CONFIG_REG[13:2])
			begin
				count_send_data <= count_send_data + 12'd1;
				SDA_OUT<=fifo_tx_data_out[9:9];

				if(count_send_data < DATA_CONFIG_REG[13:2]/12'd4)
				begin
					BR_CLK_O <= 1'b0;
				end
				else if(count_send_data >= DATA_CONFIG_REG[13:2]/12'd4 && count_send_data < (DATA_CONFIG_REG[13:2]-(DATA_CONFIG_REG[13:2]/12'd4))-12'd1)
				begin
					BR_CLK_O <= 1'b1;
				end
				else
				begin
					BR_CLK_O <= 1'b0;
				end		
			end
			else
			begin
				count_send_data <= 12'd0;
				SDA_OUT<=fifo_tx_data_out[10:10];
			end	

		end
		ADDRESS_3:
		begin

			if(count_send_data < DATA_CONFIG_REG[13:2])
			begin
				count_send_data <= count_send_data + 12'd1;
				SDA_OUT<=fifo_tx_data_out[10:10];

				if(count_send_data < DATA_CONFIG_REG[13:2]/12'd4)
				begin
					BR_CLK_O <= 1'b0;
				end
				else if(count_send_data >= DATA_CONFIG_REG[13:2]/12'd4 && count_send_data < (DATA_CONFIG_REG[13:2]-(DATA_CONFIG_REG[13:2]/12'd4))-12'd1)
				begin
					BR_CLK_O <= 1'b1;
				end
				else
				begin
					BR_CLK_O <= 1'b0;
				end			
			end
			else
			begin
				count_send_data <= 12'd0;
				SDA_OUT<=fifo_tx_data_out[11:11];
			end	

		end
		ADDRESS_4:
		begin

			if(count_send_data < DATA_CONFIG_REG[13:2])
			begin
				count_send_data <= count_send_data + 12'd1;
				SDA_OUT<=fifo_tx_data_out[11:11];

				if(count_send_data < DATA_CONFIG_REG[13:2]/12'd4)
				begin
					BR_CLK_O <= 1'b0;
				end
				else if(count_send_data >= DATA_CONFIG_REG[13:2]/12'd4 && count_send_data < (DATA_CONFIG_REG[13:2]-(DATA_CONFIG_REG[13:2]/12'd4))-12'd1)
				begin
					BR_CLK_O <= 1'b1;
				end
				else
				begin
					BR_CLK_O <= 1'b0;
				end			
			end
			else
			begin
				count_send_data <= 12'd0;
				SDA_OUT<=fifo_tx_data_out[12:12];
			end	
		end
		ADDRESS_5:
		begin

			if(count_send_data < DATA_CONFIG_REG[13:2])
			begin
				count_send_data <= count_send_data + 12'd1;
				SDA_OUT<=fifo_tx_data_out[12:12];

				if(count_send_data < DATA_CONFIG_REG[13:2]/12'd4)
				begin
					BR_CLK_O <= 1'b0;
				end
				else if(count_send_data >= DATA_CONFIG_REG[13:2]/12'd4 && count_send_data < (DATA_CONFIG_REG[13:2]-(DATA_CONFIG_REG[13:2]/12'd4))-12'd1)
				begin
					BR_CLK_O <= 1'b1;
				end
				else
				begin
					BR_CLK_O <= 1'b0;
				end				
			end
			else
			begin
				count_send_data <= 12'd0;
				SDA_OUT<=fifo_tx_data_out[13:13];
			end	

				
		end
		ADDRESS_6:
		begin

			if(count_send_data < DATA_CONFIG_REG[13:2])
			begin
				count_send_data <= count_send_data + 12'd1;
				SDA_OUT<=fifo_tx_data_out[13:13];

				if(count_send_data < DATA_CONFIG_REG[13:2]/12'd4)
				begin
					BR_CLK_O <= 1'b0;
				end
				else if(count_send_data >= DATA_CONFIG_REG[13:2]/12'd4 && count_send_data < (DATA_CONFIG_REG[13:2]-(DATA_CONFIG_REG[13:2]/12'd4))-12'd1)
				begin
					BR_CLK_O <= 1'b1;
				end
				else
				begin
					BR_CLK_O <= 1'b0;
				end		
			end
			else
			begin
				count_send_data <= 12'd0;		
				SDA_OUT<=fifo_tx_data_out[14:14];
			end	
				
		end
		ADDRESS_7:
		begin

			if(count_send_data < DATA_CONFIG_REG[13:2])
			begin
				count_send_data <= count_send_data + 12'd1;
				SDA_OUT<=fifo_tx_data_out[14:14];

				if(count_send_data < DATA_CONFIG_REG[13:2]/12'd4)
				begin
					BR_CLK_O <= 1'b0;
				end
				else if(count_send_data >= DATA_CONFIG_REG[13:2]/12'd4 && count_send_data < (DATA_CONFIG_REG[13:2]-(DATA_CONFIG_REG[13:2]/12'd4))-12'd1)
				begin
					BR_CLK_O <= 1'b1;
				end
				else
				begin
					BR_CLK_O <= 1'b0;
				end		
			end
			else
			begin
				count_send_data <= 12'd0;
				SDA_OUT<=fifo_tx_data_out[15:15];
			end	

				
		end
		ADDRESS_8:
		begin

			if(count_send_data < DATA_CONFIG_REG[13:2])
			begin
				count_send_data <= count_send_data + 12'd1;
				SDA_OUT<=fifo_tx_data_out[15:15];

				if(count_send_data < DATA_CONFIG_REG[13:2]/12'd4)
				begin
					BR_CLK_O <= 1'b0;
				end
				else if(count_send_data >= DATA_CONFIG_REG[13:2]/12'd4 && count_send_data < (DATA_CONFIG_REG[13:2]-(DATA_CONFIG_REG[13:2]/12'd4))-12'd1)
				begin
					BR_CLK_O <= 1'b1;
				end
				else
				begin
					BR_CLK_O <= 1'b0;
				end		
			end
			else
			begin
				count_send_data <= 12'd0;
				SDA_OUT<=1'b0;
			end	
				
		end
		RESPONSE_ADDRESS:
		begin
			if(count_send_data < DATA_CONFIG_REG[13:2])
			begin
				count_send_data <= count_send_data + 12'd1;

				//LETS TRY USE THIS BUT I DONT THINK IF WORKS  
				RESPONSE<= SDA;

				if(count_send_data < DATA_CONFIG_REG[13:2]/12'd4)
				begin
					BR_CLK_O <= 1'b0;
				end
				else if(count_send_data >= DATA_CONFIG_REG[13:2]/12'd4 && count_send_data < (DATA_CONFIG_REG[13:2]-(DATA_CONFIG_REG[13:2]/12'd4))-12'd1)
				begin
					BR_CLK_O <= 1'b1;
				end
				else
				begin
					BR_CLK_O <= 1'b0;
				end		
			end
			else
			begin
				count_send_data <= 12'd0;
			end

		end
		DATA0_1:
		begin

			if(count_send_data < DATA_CONFIG_REG[13:2])
			begin
				count_send_data <= count_send_data + 12'd1;
				SDA_OUT<=fifo_tx_data_out[16:16];

				if(count_send_data < DATA_CONFIG_REG[13:2]/12'd4)
				begin
					BR_CLK_O <= 1'b0;
				end
				else if(count_send_data >= DATA_CONFIG_REG[13:2]/12'd4 && count_send_data < (DATA_CONFIG_REG[13:2]-(DATA_CONFIG_REG[13:2]/12'd4))-12'd1)
				begin
					BR_CLK_O <= 1'b1;
				end
				else
				begin
					BR_CLK_O <= 1'b0;
				end		
			end
			else
			begin
				count_send_data <= 12'd0;				
				SDA_OUT<=fifo_tx_data_out[17:17];
			end	

				
		end
		DATA0_2:
		begin

			if(count_send_data < DATA_CONFIG_REG[13:2])
			begin
				count_send_data <= count_send_data + 12'd1;
				SDA_OUT<=fifo_tx_data_out[17:17];

				if(count_send_data < DATA_CONFIG_REG[13:2]/12'd4)
				begin
					BR_CLK_O <= 1'b0;
				end
				else if(count_send_data >= DATA_CONFIG_REG[13:2]/12'd4 && count_send_data < (DATA_CONFIG_REG[13:2]-(DATA_CONFIG_REG[13:2]/12'd4))-12'd1)
				begin
					BR_CLK_O <= 1'b1;
				end
				else
				begin
					BR_CLK_O <= 1'b0;
				end		
			end
			else
			begin
				count_send_data <= 12'd0;
				SDA_OUT<=fifo_tx_data_out[18:18];
			end	

				
		end		
		DATA0_3:
		begin

			if(count_send_data < DATA_CONFIG_REG[13:2])
			begin
				count_send_data <= count_send_data + 12'd1;
				SDA_OUT<=fifo_tx_data_out[18:18];

				if(count_send_data < DATA_CONFIG_REG[13:2]/12'd4)
				begin
					BR_CLK_O <= 1'b0;
				end
				else if(count_send_data >= DATA_CONFIG_REG[13:2]/12'd4 && count_send_data < (DATA_CONFIG_REG[13:2]-(DATA_CONFIG_REG[13:2]/12'd4))-12'd1)
				begin
					BR_CLK_O <= 1'b1;
				end
				else
				begin
					BR_CLK_O <= 1'b0;
				end		
			end
			else
			begin
				count_send_data <= 12'd0;
				SDA_OUT<=fifo_tx_data_out[19:19];
			end	
				
		end
		DATA0_4:
		begin

			if(count_send_data < DATA_CONFIG_REG[13:2])
			begin
				count_send_data <= count_send_data + 12'd1;
				SDA_OUT<=fifo_tx_data_out[19:19];

				if(count_send_data < DATA_CONFIG_REG[13:2]/12'd4)
				begin
					BR_CLK_O <= 1'b0;
				end
				else if(count_send_data >= DATA_CONFIG_REG[13:2]/12'd4 && count_send_data < (DATA_CONFIG_REG[13:2]-(DATA_CONFIG_REG[13:2]/12'd4))-12'd1)
				begin
					BR_CLK_O <= 1'b1;
				end
				else
				begin
					BR_CLK_O <= 1'b0;
				end		
			end
			else
			begin
				count_send_data <= 12'd0;
				SDA_OUT<=fifo_tx_data_out[20:20];
			end	
				
		end
		DATA0_5:
		begin

			if(count_send_data < DATA_CONFIG_REG[13:2])
			begin
				count_send_data <= count_send_data + 12'd1;
				SDA_OUT<=fifo_tx_data_out[20:20];

				if(count_send_data < DATA_CONFIG_REG[13:2]/12'd4)
				begin
					BR_CLK_O <= 1'b0;
				end
				else if(count_send_data >= DATA_CONFIG_REG[13:2]/12'd4 && count_send_data < (DATA_CONFIG_REG[13:2]-(DATA_CONFIG_REG[13:2]/12'd4))-12'd1)
				begin
					BR_CLK_O <= 1'b1;
				end
				else
				begin
					BR_CLK_O <= 1'b0;
				end			
			end
			else
			begin
				count_send_data <= 12'd0;
				SDA_OUT<=fifo_tx_data_out[21:21];
			end

		end
		DATA0_6:
		begin

			if(count_send_data < DATA_CONFIG_REG[13:2])
			begin
				count_send_data <= count_send_data + 12'd1;
				SDA_OUT<=fifo_tx_data_out[21:21];

				if(count_send_data < DATA_CONFIG_REG[13:2]/12'd4)
				begin
					BR_CLK_O <= 1'b0;
				end
				else if(count_send_data >= DATA_CONFIG_REG[13:2]/12'd4 && count_send_data < (DATA_CONFIG_REG[13:2]-(DATA_CONFIG_REG[13:2]/12'd4))-12'd1)
				begin
					BR_CLK_O <= 1'b1;
				end
				else
				begin
					BR_CLK_O <= 1'b0;
				end			
			end
			else
			begin
				count_send_data <= 12'd0;
				SDA_OUT<=fifo_tx_data_out[22:22];
			end
				
		end
		DATA0_7:
		begin

			if(count_send_data < DATA_CONFIG_REG[13:2])
			begin
				count_send_data <= count_send_data + 12'd1;
				SDA_OUT<=fifo_tx_data_out[22:22];

				if(count_send_data < DATA_CONFIG_REG[13:2]/12'd4)
				begin
					BR_CLK_O <= 1'b0;
				end
				else if(count_send_data >= DATA_CONFIG_REG[13:2]/12'd4 && count_send_data < (DATA_CONFIG_REG[13:2]-(DATA_CONFIG_REG[13:2]/12'd4))-12'd1)
				begin
					BR_CLK_O <= 1'b1;
				end
				else
				begin
					BR_CLK_O <= 1'b0;
				end		
			end
			else
			begin
				count_send_data <= 12'd0;
				SDA_OUT<=fifo_tx_data_out[23:23];
			end	
				
		end
		DATA0_8:
		begin

			if(count_send_data < DATA_CONFIG_REG[13:2])
			begin
				count_send_data <= count_send_data + 12'd1;
				SDA_OUT<=fifo_tx_data_out[23:23];

				if(count_send_data < DATA_CONFIG_REG[13:2]/12'd4)
				begin
					BR_CLK_O <= 1'b0;
				end
				else if(count_send_data >= DATA_CONFIG_REG[13:2]/12'd4 && count_send_data < (DATA_CONFIG_REG[13:2]-(DATA_CONFIG_REG[13:2]/12'd4))-12'd1)
				begin
					BR_CLK_O <= 1'b1;
				end
				else
				begin
					BR_CLK_O <= 1'b0;
				end		

			end
			else
			begin
				count_send_data <= 12'd0;
				SDA_OUT<=1'b0;
			end	
				
		end
		RESPONSE_DATA0_1:
		begin

			if(count_send_data < DATA_CONFIG_REG[13:2])
			begin
				count_send_data <= count_send_data + 12'd1;

				//LETS TRY USE THIS BUT I DONT THINK IF WORKS  
				RESPONSE<= SDA;

				if(count_send_data < DATA_CONFIG_REG[13:2]/12'd4)
				begin
					BR_CLK_O <= 1'b0;
				end
				else if(count_send_data >= DATA_CONFIG_REG[13:2]/12'd4 && count_send_data < (DATA_CONFIG_REG[13:2]-(DATA_CONFIG_REG[13:2]/12'd4))-12'd1)
				begin
					BR_CLK_O <= 1'b1;
				end
				else
				begin
					BR_CLK_O <= 1'b0;
				end				
			end
			else
			begin
				count_send_data <= 12'd0;
			end

		end
		DATA1_1:
		begin

			if(count_send_data < DATA_CONFIG_REG[13:2])
			begin
				count_send_data <= count_send_data + 12'd1;
				SDA_OUT<=fifo_tx_data_out[24:24];

				if(count_send_data < DATA_CONFIG_REG[13:2]/12'd4)
				begin
					BR_CLK_O <= 1'b0;
				end
				else if(count_send_data >= DATA_CONFIG_REG[13:2]/12'd4 && count_send_data < (DATA_CONFIG_REG[13:2]-(DATA_CONFIG_REG[13:2]/12'd4))-12'd1)
				begin
					BR_CLK_O <= 1'b1;
				end
				else
				begin
					BR_CLK_O <= 1'b0;
				end				
			end
			else
			begin
				count_send_data <= 12'd0;
				SDA_OUT<=fifo_tx_data_out[25:25];

			end

				
		end
		DATA1_2:
		begin

			if(count_send_data < DATA_CONFIG_REG[13:2])
			begin
				count_send_data <= count_send_data + 12'd1;
				SDA_OUT<=fifo_tx_data_out[25:25];

				if(count_send_data < DATA_CONFIG_REG[13:2]/12'd4)
				begin
					BR_CLK_O <= 1'b0;
				end
				else if(count_send_data >= DATA_CONFIG_REG[13:2]/12'd4 && count_send_data < (DATA_CONFIG_REG[13:2]-(DATA_CONFIG_REG[13:2]/12'd4))-12'd1)
				begin
					BR_CLK"	"
module module_i2c_sva(PCLK,PRESETn,fifo_tx_f_full,fifo_tx_f_empty,fifo_tx_data_out,fifo_rx_data_in,fifo_rx_f_full,fifo_rx_f_empty,fifo_rx_wr_en,
fifo_tx_rd_en,RX_EMPTY,TX_EMPTY,ERROR,ENABLE_SCL,ENABLE_SDA,SDA,SCL,DATA_CONFIG_REG,TIMEOUT_TX,state_tx,count_receive_data,RESPONSE,SDA_OUT,count_timeout,count_send_data,next_state_rx,BR_CLK_O,next_state_tx, count_tx,count_rx,BR_CLK_O_RX,SDA_OUT_RX,state_rx);

input PCLK;
input PRESETn;

//INTERFACE WITH FIFO TRANSMISSION
input fifo_tx_f_full;
input fifo_tx_f_empty;
input [32-1:0] fifo_tx_data_out;

//INTERFACE WITH FIFO RECEIVER
input fifo_rx_f_full;
input fifo_rx_f_empty;
input fifo_rx_wr_en;
input [32-1:0] fifo_rx_data_in; 

//INTERFACE WITH REGISTER CONFIGURATION
input [14-1:0] DATA_CONFIG_REG;
input [14-1:0] TIMEOUT_TX;

//INTERFACE TO APB AND READ FOR FIFO   
input fifo_tx_rd_en;
input   TX_EMPTY;
input   RX_EMPTY;
input ERROR;
input ENABLE_SDA;
input ENABLE_SCL;


//I2C BI DIRETIONAL PORTS
input SDA;
input SCL;
//registers
input state_tx;
input state_rx;
input count_receive_data;
input SDA_OUT;
input RESPONSE;
input count_timeout;
input count_send_data;
input next_state_rx;
input BR_CLK_O;
input next_state_tx;
input SDA_OUT_RX;
input count_tx;
input count_rx;
input BR_CLK_O_RX;

property a1;
@(posedge PCLK) (fifo_rx_f_empty == 1) |-> (RX_EMPTY == 1);
endproperty
assert_a1: assert property(a1);

property a0;
@(posedge PCLK) (fifo_rx_f_empty == 0) |-> (RX_EMPTY == 0);
endproperty
assert_a0: assert property(a0);

property a3;
@(posedge PCLK) (fifo_rx_f_empty == 1) |-> (RX_EMPTY == 1);
endproperty
assert_a3: assert property(a3);

property a2;
@(posedge PCLK) (fifo_rx_f_empty == 0) |-> (RX_EMPTY == 0);
endproperty
assert_a2: assert property(a2);

property a5;
@(posedge PCLK) (DATA_CONFIG_REG[1] == 0) |-> (ERROR == 0);
endproperty
assert_a5: assert property(a5);

property a4;
@(posedge PCLK) (DATA_CONFIG_REG[0] == 0) |-> (ERROR == 0);
endproperty
assert_a4: assert property(a4);

property a6;
@(posedge PCLK) (DATA_CONFIG_REG[0] == 1 & DATA_CONFIG_REG[1] == 1) |-> (ERROR == 1);
endproperty
assert_a6: assert property(a6);

endmodule"	https://github.com/achieve-lab/assertion_data_for_LLM/blob/NIPS_2024/Jasper_llama_results/communication_controller_apb_to_i2c/module_i2c/FPV_module_i2c.tcl		
"//////////////////////////////////////////////////////////////////////
////                                                              ////
////  eth_rxstatem.v                                              ////
////                                                              ////
////  This file is part of the Ethernet IP core project           ////
////  http://www.opencores.org/project,ethmac                     ////
////                                                              ////
////  Author(s):                                                  ////
////      - Igor Mohor (igorM@opencores.org)                      ////
////      - Novan Hartadi (novan@vlsi.itb.ac.id)                  ////
////      - Mahmud Galela (mgalela@vlsi.itb.ac.id)                ////
////                                                              ////
////  All additional information is avaliable in the Readme.txt   ////
////  file.                                                       ////
////                                                              ////
//////////////////////////////////////////////////////////////////////
////                                                              ////
//// Copyright (C) 2001 Authors                                   ////
////                                                              ////
//// This source file may be used and distributed without         ////
//// restriction provided that this copyright statement is not    ////
//// removed from the file and that any derivative work contains  ////
//// the original copyright notice and the associated disclaimer. ////
////                                                              ////
//// This source file is free software; you can redistribute it   ////
//// and/or modify it under the terms of the GNU Lesser General   ////
//// Public License as published by the Free Software Foundation; ////
//// either version 2.1 of the License, or (at your option) any   ////
//// later version.                                               ////
////                                                              ////
//// This source is distributed in the hope that it will be       ////
//// useful, but WITHOUT ANY WARRANTY; without even the implied   ////
//// warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR      ////
//// PURPOSE.  See the GNU Lesser General Public License for more ////
//// details.                                                     ////
////                                                              ////
//// You should have received a copy of the GNU Lesser General    ////
//// Public License along with this source; if not, download it   ////
//// from http://www.opencores.org/lgpl.shtml                     ////
////                                                              ////
//////////////////////////////////////////////////////////////////////
//
// CVS Revision History
//
// $Log: not supported by cvs2svn $
// Revision 1.5  2002/01/23 10:28:16  mohor
// Link in the header changed.
//
// Revision 1.4  2001/10/19 08:43:51  mohor
// eth_timescale.v changed to timescale.v This is done because of the
// simulation of the few cores in a one joined project.
//
// Revision 1.3  2001/10/18 12:07:11  mohor
// Status signals changed, Adress decoding changed, interrupt controller
// added.
//
// Revision 1.2  2001/09/11 14:17:00  mohor
// Few little NCSIM warnings fixed.
//
// Revision 1.1  2001/08/06 14:44:29  mohor
// A define FPGA added to select between Artisan RAM (for ASIC) and Block Ram (For Virtex).
// Include files fixed to contain no path.
// File names and module names changed ta have a eth_ prologue in the name.
// File eth_timescale.v is used to define timescale
// All pin names on the top module are changed to contain _I, _O or _OE at the end.
// Bidirectional signal MDIO is changed to three signals (Mdc_O, Mdi_I, Mdo_O
// and Mdo_OE. The bidirectional signal must be created on the top level. This
// is done due to the ASIC tools.
//
// Revision 1.1  2001/07/30 21:23:42  mohor
// Directory structure changed. Files checked and joind together.
//
// Revision 1.2  2001/07/03 12:55:41  mohor
// Minor changes because of the synthesys warnings.
//
//
// Revision 1.1  2001/06/27 21:26:19  mohor
// Initial release of the RxEthMAC module.
//
//
//
//

module eth_rxstatem (MRxClk, Reset, MRxDV, ByteCntEq0, ByteCntGreat2, Transmitting, MRxDEq5, MRxDEqD, 
                     IFGCounterEq24, ByteCntMaxFrame, StateData, StateIdle, StatePreamble, StateSFD, 
                     StateDrop
                    );

input         MRxClk;
input         Reset;
input         MRxDV;
input         ByteCntEq0;
input         ByteCntGreat2;
input         MRxDEq5;
input         Transmitting;
input         MRxDEqD;
input         IFGCounterEq24;
input         ByteCntMaxFrame;

output [1:0]  StateData;
output        StateIdle;
output        StateDrop;
output        StatePreamble;
output        StateSFD;

reg           StateData0;
reg           StateData1;
reg           StateIdle;
reg           StateDrop;
reg           StatePreamble;
reg           StateSFD;

wire          StartIdle;
wire          StartDrop;
wire          StartData0;
wire          StartData1;
wire          StartPreamble;
wire          StartSFD;


// Defining the next state
assign StartIdle = ~MRxDV & (StateDrop | StatePreamble | StateSFD | (|StateData));

assign StartPreamble = MRxDV & ~MRxDEq5 & (StateIdle & ~Transmitting);

assign StartSFD = MRxDV & MRxDEq5 & (StateIdle & ~Transmitting | StatePreamble);

assign StartData0 = MRxDV & (StateSFD & MRxDEqD & IFGCounterEq24 | StateData1);

assign StartData1 = MRxDV & StateData0 & (~ByteCntMaxFrame);

assign StartDrop = MRxDV & (StateIdle & Transmitting | StateSFD & ~IFGCounterEq24 &
                   MRxDEqD |  StateData0 &  ByteCntMaxFrame);

// Rx State Machine
always @ (posedge MRxClk or posedge Reset)
begin
  if(Reset)
    begin
      StateIdle     <=  1'b0;
      StateDrop     <=  1'b1;
      StatePreamble <=  1'b0;
      StateSFD      <=  1'b0;
      StateData0    <=  1'b0;
      StateData1    <=  1'b0;
    end
  else
    begin
      if(StartPreamble | StartSFD | StartDrop)
        StateIdle <=  1'b0;
      else
      if(StartIdle)
        StateIdle <=  1'b1;

      if(StartIdle)
        StateDrop <=  1'b0;
      else
      if(StartDrop)
        StateDrop <=  1'b1;

      if(StartSFD | StartIdle | StartDrop)
        StatePreamble <=  1'b0;
      else
      if(StartPreamble)
        StatePreamble <=  1'b1;

      if(StartPreamble | StartIdle | StartData0 | StartDrop)
        StateSFD <=  1'b0;
      else
      if(StartSFD)
        StateSFD <=  1'b1;

      if(StartIdle | StartData1 | StartDrop)
        StateData0 <=  1'b0;
      else
      if(StartData0)
        StateData0 <=  1'b1;

      if(StartIdle | StartData0 | StartDrop)
        StateData1 <=  1'b0;
      else
      if(StartData1)
        StateData1 <=  1'b1;
    end
end

assign StateData[1:0] = {StateData1, StateData0};

endmodule"	"
module eth_rxstate_sva(
input         MRxDV,
input        StateDrop,
input         MRxDEqD,
input          StartPreamble,
input         ByteCntMaxFrame,
input           StateData0,
input           StateData1,
input          StartData1,
input         ByteCntGreat2,
input [1:0]  StateData,
input         MRxDEq5,
input         MRxClk,
input           StatePreamble,
input        StateIdle,
input          StartSFD,
input         Transmitting,
input         IFGCounterEq24,
input         ByteCntEq0,
input        StateSFD,
input          StartDrop,
input         Reset,
input          StartData0,
input          StartIdle
);


property a7;
@(posedge MRxClk) (StartPreamble == 1) |=> (StatePreamble == 1);
endproperty
assert_a7: assert property(a7);

property a0;
@(posedge MRxClk) (StartDrop == 1) |=> (StatePreamble == 0);
endproperty
assert_a0: assert property(a0);

property a6;
@(posedge MRxClk) (StateSFD == 1) |=> (StatePreamble == 0);
endproperty
assert_a6: assert property(a6);

property a3;
@(posedge MRxClk) (StateData[0] == 1) |=> (StatePreamble == 0);
endproperty
assert_a3: assert property(a3);

property a2;
@(posedge MRxClk) (StateDrop == 1) |=> (StatePreamble == 0);
endproperty
assert_a2: assert property(a2);

property a5;
@(posedge MRxClk) (StateData1 == 1) |=> (StatePreamble == 0);
endproperty
assert_a5: assert property(a5);

property a8;
@(posedge MRxClk) (StatePreamble == 1 & MRxDEq5 == 0 & MRxDV == 1) |=> (StatePreamble == 1);
endproperty
assert_a8: assert property(a8);

property a1;
@(posedge MRxClk) (MRxDEq5 == 1) |=> (StatePreamble == 0);
endproperty
assert_a1: assert property(a1);

property a4;
@(posedge MRxClk) (MRxDV == 0) |=> (StatePreamble == 0);
endproperty
assert_a4: assert property(a4);


property a17;
@(posedge MRxClk) (StartSFD == 1) |=> (StateSFD == 1);
endproperty
assert_a17: assert property(a17);

property a14;
@(posedge MRxClk) (StartIdle == 1) |=> (StateSFD == 0);
endproperty
assert_a14: assert property(a14);

property a9;
@(posedge MRxClk) (StartDrop == 1) |=> (StateSFD == 0);
endproperty
assert_a9: assert property(a9);

property a12;
@(posedge MRxClk) (StartData0 == 1) |=> (StateSFD == 0);
endproperty
assert_a12: assert property(a12);

property a10;
@(posedge MRxClk) (StartPreamble == 1) |=> (StateSFD == 0);
endproperty
assert_a10: assert property(a10);

property a18;
@(posedge MRxClk) (StateSFD == 1 & StartIdle == 0 & MRxDEqD == 0) |=> (StateSFD == 1);
endproperty
assert_a18: assert property(a18);

property a11;
@(posedge MRxClk) (StateData[0] == 1) |=> (StateSFD == 0);
endproperty
assert_a11: assert property(a11);

property a13;
@(posedge MRxClk) (StateDrop == 1) |=> (StateSFD == 0);
endproperty
assert_a13: assert property(a13);

property a16;
@(posedge MRxClk) (MRxDEq5 == 0 & StatePreamble == 1) |=> (StateSFD == 0);
endproperty
assert_a16: assert property(a16);

property a15;
@(posedge MRxClk) (MRxDV == 0) |=> (StateSFD == 0);
endproperty
assert_a15: assert property(a15);

property a20;
@(posedge MRxClk) (StartIdle == 1) |=> (StateDrop == 0);
endproperty
assert_a20: assert property(a20);

property a26;
@(posedge MRxClk) (StartDrop == 1) |=> (StateDrop == 1);
endproperty
assert_a26: assert property(a26);

property a27;
@(posedge MRxClk) (StateDrop == 1 & StartIdle == 0) |=> (StateDrop == 1);
endproperty
assert_a27: assert property(a27);

property a23;
@(posedge MRxClk) (StateSFD == 1 & StartDrop == 0) |=> (StateDrop == 0);
endproperty
assert_a23: assert property(a23);

property a24;
@(posedge MRxClk) (StateData[0] == 1 & StartDrop == 0) |=> (StateDrop == 0);
endproperty
assert_a24: assert property(a24);

property a28;
@(posedge MRxClk) (StatePreamble == 1) |=> (StateDrop == 0);
endproperty
assert_a28: assert property(a28);

property a21;
@(posedge MRxClk) (StateData1 == 1) |=> (StateDrop == 0);
endproperty
assert_a21: assert property(a21);

property a22;
@(posedge MRxClk) (MRxDV == 0) |=> (StateDrop == 0);
endproperty
assert_a22: assert property(a22);

property a25;
@(posedge MRxClk) (Transmitting == 0 & StateIdle == 1) |=> (StateDrop == 0);
endproperty
assert_a25: assert property(a25);

property a33;
@(posedge MRxClk) (StartIdle == 1) |=> (StateIdle == 1);
endproperty
assert_a33: assert property(a33);

property a29;
@(posedge MRxClk) (StartDrop == 1) |=> (StateIdle == 0);
endproperty
assert_a29: assert property(a29);

property a30;
@(posedge MRxClk) (StartSFD == 1) |=> (StateIdle == 0);
endproperty
assert_a30: assert property(a30);

property a31;
@(posedge MRxClk) (StartPreamble == 1) |=> (StateIdle == 0);
endproperty
assert_a31: assert property(a31);

property a32;
@(posedge MRxClk) (MRxDV == 1) |=> (StateIdle == 0);
endproperty
assert_a32: assert property(a32);

property a34;
@(posedge MRxClk) (MRxDV == 0) |=> (StateIdle == 1);
endproperty
assert_a34: assert property(a34);

endmodule"	https://github.com/achieve-lab/assertion_data_for_LLM/blob/66da64e4274e8571ffcdd9d6645ed898a1a23f83/Jasper_results/communication_controller_100_mb-s_ethernet_mac_layer_switch/eth_rxstatem/FPV_eth_rxstatem.tcl		
