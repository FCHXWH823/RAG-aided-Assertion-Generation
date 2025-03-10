`timescale 1ns / 1ps
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
				sel0 <= 1'b0;
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


assert property(@(posedge clk) (sel7 == 0 & req0 == 1) |=> (sel7 == 0));
assert property(@(posedge clk) (sel7 == 0 & req1 == 1) |=> (sel7 == 0));
assert property(@(posedge clk) (sel7 == 1 & ack == 0) |=> (sel7 == 1));
assert property(@(posedge clk) (sel7 == 1 & ce == 0) |=> (sel7 == 1));
assert property(@(posedge clk) (sel7 == 0 & ack == 0) |=> (sel7 == 0));
assert property(@(posedge clk) (sel7 == 0 & req2 == 1) |=> (sel7 == 0));
assert property(@(posedge clk) (sel7 == 0 & req3 == 1) |=> (sel7 == 0));
assert property(@(posedge clk) (sel7 == 0 & req5 == 1) |=> (sel7 == 0));
assert property(@(posedge clk) (sel7 == 0 & req6 == 1) |=> (sel7 == 0));
assert property(@(posedge clk) (sel5 == 0 & req0 == 1) |=> (sel5 == 0));
assert property(@(posedge clk) (sel5 == 0 & req1 == 1) |=> (sel5 == 0));
assert property(@(posedge clk) (sel5 == 1 & ce == 0) |=> (sel5 == 1));
assert property(@(posedge clk) (sel5 == 1 & ack == 0) |=> (sel5 == 1));
assert property(@(posedge clk) (sel5 == 0 & ack == 0) |=> (sel5 == 0));
assert property(@(posedge clk) (sel5 == 0 & ce == 0) |=> (sel5 == 0));
assert property(@(posedge clk) (sel5 == 0 & req2 == 1) |=> (sel5 == 0));
assert property(@(posedge clk) (sel5 == 0 & req3 == 1) |=> (sel5 == 0));
assert property(@(posedge clk) (sel5 == 0 & req4 == 1) |=> (sel5 == 0));
assert property(@(posedge clk) (sel5 == 0 & req5 == 0) |=> (sel5 == 0));
assert property(@(posedge clk) (sel4 == 0 & req1 == 1) |=> (sel4 == 0));
assert property(@(posedge clk) (sel4 == 1 & ack == 0) |=> (sel4 == 1));
assert property(@(posedge clk) (sel4 == 0 & ack == 0) |=> (sel4 == 0));
assert property(@(posedge clk) (sel4 == 0 & ce == 0) |=> (sel4 == 0));
assert property(@(posedge clk) (sel4 == 1 & ce == 0) |=> (sel4 == 1));
assert property(@(posedge clk) (sel4 == 0 & req2 == 1) |=> (sel4 == 0));
assert property(@(posedge clk) (sel4 == 0 & req3 == 1) |=> (sel4 == 0));
assert property(@(posedge clk) (sel4 == 0 & req4 == 0) |=> (sel4 == 0));

assert property (@(posedge clk)  (translate_sentence(sentence) == words |-> translated_sentence |=> "s_eventually" $past translated_word));
assert property (@(posedge clk)  ((sel7 == 0 & req0 == 1) |=> (sel7 == 0)) iff (translate_sentence(sentence) == words |-> translated_sentence |=> "s_eventually" $past translated_word));
assert property (@(posedge clk)  (if s_eventually $past(signal) == expected_value |=> response_signal));
assert property (@(posedge clk)  ((sel7 == 0 & req1 == 1) |=> (sel7 == 0)) iff (if s_eventually $past(signal) == expected_value |=> response_signal));
assert property (@(posedge clk)  (in == 1 |=> out == 0));
assert property (@(posedge clk)  ((sel7 == 1 & ack == 0) |=> (sel7 == 1)) iff (in == 1 |=> out == 0));
assert property (@(posedge clk)  (translate_sentence(sentence) == "ON NEXT THE CLOCK THEN HOLD =>>"));
assert property (@(posedge clk)  ((sel7 == 1 & ce == 0) |=> (sel7 == 1)) iff (translate_sentence(sentence) == "ON NEXT THE CLOCK THEN HOLD =>>"));
assert property (@(posedge clk)  (s_eventually (condition1 == $past(condition2)) |=> response));
assert property (@(posedge clk)  ((sel7 == 0 & ack == 0) |=> (sel7 == 0)) iff (s_eventually (condition1 == $past(condition2)) |=> response));
assert property (@(posedge clk)  (request |-> (grant && !reset)));
assert property (@(posedge clk)  ((sel7 == 0 & req2 == 1) |=> (sel7 == 0)) iff (request |-> (grant && !reset)));
assert property (@(posedge clk)  (sel7==0 && req3==1 |=> sel7==0));
assert property (@(posedge clk)  ((sel7 == 0 & req3 == 1) |=> (sel7 == 0)) iff (sel7==0 && req3==1 |=> sel7==0));
assert property (@(posedge clk)  (s_eventually (request ##1 (ack |=> grant))));
assert property (@(posedge clk)  ((sel7 == 0 & req5 == 1) |=> (sel7 == 0)) iff (s_eventually (request ##1 (ack |=> grant))));
assert property (@(posedge clk)  (s_eventually signal1 |=> signal2));
assert property (@(posedge clk)  ((sel7 == 0 & req6 == 1) |=> (sel7 == 0)) iff (s_eventually signal1 |=> signal2));
assert property (@(posedge clk)  (s_eventually (signal1 && $past(signal2)) |-> (signal3 |=> (signal4 && !signal5))));
assert property (@(posedge clk)  ((sel5 == 0 & req0 == 1) |=> (sel5 == 0)) iff (s_eventually (signal1 && $past(signal2)) |-> (signal3 |=> (signal4 && !signal5))));
assert property (@(posedge clk)  ((selection_signal_5 == 0 && bus_request_signal_1 == 1) |-> $past(selection_signal_5) == 0));
assert property (@(posedge clk)  ((sel5 == 0 & req1 == 1) |=> (sel5 == 0)) iff ((selection_signal_5 == 0 && bus_request_signal_1 == 1) |-> $past(selection_signal_5) == 0));
assert property (@(posedge clk)  (iff |=> s_eventually $past));
assert property (@(posedge clk)  ((sel5 == 1 & ce == 0) |=> (sel5 == 1)) iff (iff |=> s_eventually $past));
assert property (@(posedge clk)  (translate_sentence(sentence)));
assert property (@(posedge clk)  ((sel5 == 1 & ack == 0) |=> (sel5 == 1)) iff (translate_sentence(sentence)));
assert property (@(posedge clk)  (sig_xfr_cmpltd));
assert property (@(posedge clk)  ((sel5 == 0 & ack == 0) |=> (sel5 == 0)) iff (sig_xfr_cmpltd));
assert property (@(posedge clk)  (translate_sentence(sentence) == |=> $past()));
assert property (@(posedge clk)  ((sel5 == 0 & ce == 0) |=> (sel5 == 0)) iff (translate_sentence(sentence) == |=> $past()));
assert property (@(posedge clk)  (sel[4] == 0 && req[1] == 1 |=> sel[4] == 0));
assert property (@(posedge clk)  ((sel5 == 0 & req2 == 1) |=> (sel5 == 0)) iff (sel[4] == 0 && req[1] == 1 |=> sel[4] == 0));
assert property (@(posedge clk)  (always s_eventually ($past(signal) |=> (signal1 == signal2 && signal3 || !signal4))));
assert property (@(posedge clk)  ((sel5 == 0 & req3 == 1) |=> (sel5 == 0)) iff (always s_eventually ($past(signal) |=> (signal1 == signal2 && signal3 || !signal4))));
assert property (@(posedge clk)  (s_eventually sel5 == 0 and busreq4 == 1 |=> s_eventually sel5 == 0));
assert property (@(posedge clk)  ((sel5 == 0 & req4 == 1) |=> (sel5 == 0)) iff (s_eventually sel5 == 0 and busreq4 == 1 |=> s_eventually sel5 == 0));
assert property (@(posedge clk)  (translate_sentence(sentence) |=> translated_sentence));
assert property (@(posedge clk)  ((sel5 == 0 & req5 == 0) |=> (sel5 == 0)) iff (translate_sentence(sentence) |=> translated_sentence));
assert property (@(posedge clk)  ($past(condition1) |=> (condition2)));
assert property (@(posedge clk)  ((sel4 == 0 & req1 == 1) |=> (sel4 == 0)) iff ($past(condition1) |=> (condition2)));
assert property (@(posedge clk)  (!(a && b) | (c && d)));
assert property (@(posedge clk)  ((sel4 == 1 & ack == 0) |=> (sel4 == 1)) iff (!(a && b) | (c && d)));
assert property (@(posedge clk)  (sel_req4 == 0 & compl_bus == 0 |=> sel_req4 == 0));
assert property (@(posedge clk)  ((sel4 == 0 & ack == 0) |=> (sel4 == 0)) iff (sel_req4 == 0 & compl_bus == 0 |=> sel_req4 == 0));
assert property (@(posedge clk)  (s_eventually (condition1 |-> condition2 |=> $past(condition3))));
assert property (@(posedge clk)  ((sel4 == 0 & ce == 0) |=> (sel4 == 0)) iff (s_eventually (condition1 |-> condition2 |=> $past(condition3))));
assert property (@(posedge clk)  (|->));
assert property (@(posedge clk)  ((sel4 == 1 & ce == 0) |=> (sel4 == 1)) iff (|->));
assert property (@(posedge clk)  (s_eventually (A) |=> $past(B)));
assert property (@(posedge clk)  ((sel4 == 0 & req2 == 1) |=> (sel4 == 0)) iff (s_eventually (A) |=> $past(B)));
assert property (@(posedge clk)  (req |-> s_eventually (gnt && $past(rst_n))));
assert property (@(posedge clk)  ((sel4 == 0 & req3 == 1) |=> (sel4 == 0)) iff (req |-> s_eventually (gnt && $past(rst_n))));
assert property (@(posedge clk)  (a > b && c == d || e <= f));
assert property (@(posedge clk)  ((sel4 == 0 & req4 == 0) |=> (sel4 == 0)) iff (a > b && c == d || e <= f));

endmodule
