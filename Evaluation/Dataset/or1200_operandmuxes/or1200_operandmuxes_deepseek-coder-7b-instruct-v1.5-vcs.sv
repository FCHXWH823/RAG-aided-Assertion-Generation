//////////////////////////////////////////////////////////////////////
////                                                              ////
////  OR1200's register file read operands mux                    ////
////                                                              ////
////  This file is part of the OpenRISC 1200 project              ////
////  http://www.opencores.org/project,or1k                       ////
////                                                              ////
////  Description                                                 ////
////  Mux for two register file read operands.                    ////
////                                                              ////
////  To Do:                                                      ////
////   - make it smaller and faster                               ////
////                                                              ////
////  Author(s):                                                  ////
////      - Damjan Lampret, lampret@opencores.org                 ////
////                                                              ////
//////////////////////////////////////////////////////////////////////
////                                                              ////
//// Copyright (C) 2000 Authors and OPENCORES.ORG                 ////
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
// $Log: or1200_operandmuxes.v,v $
// Revision 2.0  2010/06/30 11:00:00  ORSoC
// Minor update: 
// Bugs fixed. 

// synopsys translate_off
`include "timescale.v"
// synopsys translate_on
`include "or1200_defines.v"

module or1200_operandmuxes(
	// Clock and rst
	clk, rst,

	// Internal i/f
	id_freeze, ex_freeze, rf_dataa, rf_datab, ex_forw, wb_forw,
	simm, sel_a, sel_b, operand_a, operand_b, muxed_a, muxed_b
);

parameter width = `OR1200_OPERAND_WIDTH;

//
// I/O
//
input				clk;
input				rst;
input				id_freeze;
input				ex_freeze;
input	[width-1:0]		rf_dataa;
input	[width-1:0]		rf_datab;
input	[width-1:0]		ex_forw;
input	[width-1:0]		wb_forw;
input	[width-1:0]		simm;
input	[`OR1200_SEL_WIDTH-1:0]	sel_a;
input	[`OR1200_SEL_WIDTH-1:0]	sel_b;
output	[width-1:0]		operand_a;
output	[width-1:0]		operand_b;
output	[width-1:0]		muxed_a;
output	[width-1:0]		muxed_b;

//
// Internal wires and regs
//
reg	[width-1:0]		operand_a;
reg	[width-1:0]		operand_b;
reg	[width-1:0]		muxed_a;
reg	[width-1:0]		muxed_b;
reg				saved_a;
reg				saved_b;

//
// Operand A register
//
always @(posedge clk or `OR1200_RST_EVENT rst) begin
	if (rst == `OR1200_RST_VALUE) begin
		operand_a <=  32'd0;
		saved_a <=  1'b0;
	end else if (!ex_freeze && id_freeze && !saved_a) begin
		operand_a <=  muxed_a;
		saved_a <=  1'b1;
	end else if (!ex_freeze && !saved_a) begin
		operand_a <=  muxed_a;
	end else if (!ex_freeze && !id_freeze)
		saved_a <=  1'b0;
end

//
// Operand B register
//
always @(posedge clk or `OR1200_RST_EVENT rst) begin
	if (rst == `OR1200_RST_VALUE) begin
		operand_b <=  32'd0;
		saved_b <=  1'b0;
	end else if (!ex_freeze && id_freeze && !saved_b) begin
		operand_b <=  muxed_b;
		saved_b <=  1'b1;
	end else if (!ex_freeze && !saved_b) begin
		operand_b <=  muxed_b;
	end else if (!ex_freeze && !id_freeze)
		saved_b <=  1'b0;
end

//
// Forwarding logic for operand A register
//
always @(ex_forw or wb_forw or rf_dataa or sel_a) begin
`ifdef OR1200_ADDITIONAL_SYNOPSYS_DIRECTIVES
	casez (sel_a)	// synopsys parallel_case infer_mux
`else
	casez (sel_a)	// synopsys parallel_case
`endif
		`OR1200_SEL_EX_FORW:
			muxed_a = ex_forw;
		`OR1200_SEL_WB_FORW:
			muxed_a = wb_forw;
		default:
			muxed_a = rf_dataa;
	endcase
end

//
// Forwarding logic for operand B register
//
always @(simm or ex_forw or wb_forw or rf_datab or sel_b) begin
`ifdef OR1200_ADDITIONAL_SYNOPSYS_DIRECTIVES
	casez (sel_b)	// synopsys parallel_case infer_mux
`else
	casez (sel_b)	// synopsys parallel_case
`endif
		`OR1200_SEL_IMM:
			muxed_b = simm;
		`OR1200_SEL_EX_FORW:
			muxed_b = ex_forw;
		`OR1200_SEL_WB_FORW:
			muxed_b = wb_forw;
		default:
			muxed_b = rf_datab;
	endcase
end


assert property (@(posedge clk) disable iff(rst) $rose(!ex_freeze && !id_freeze) ##1 (!ex_freeze && !id_freeze && sel_a == 2'd2 && $stable(ex_forw) && $stable(sel_a)) |-> muxed_a == ex_forw);
assert property (@(posedge clk) disable iff(rst) $rose(!ex_freeze && !id_freeze) ##1 (!ex_freeze && !id_freeze && sel_a == 2'd3 && $stable(wb_forw) && $stable(sel_a)) |-> muxed_a == wb_forw);
assert property (@(posedge clk) disable iff(rst) $rose(!ex_freeze && !id_freeze) ##1 ( !ex_freeze && !id_freeze & !(sel_a == 2'd2 || sel_a == 2'd3) && $stable(rf_dataa) && $stable(sel_a) && !$isunknown(operand_a) ) |-> muxed_a == rf_dataa);
assert property (@(posedge clk) disable iff(rst) $rose(!ex_freeze && !id_freeze) ##1 (!ex_freeze && !id_freeze && sel_b == 2'd1 && $stable(simm) && $stable(sel_b)) |->  muxed_b == simm);
assert property (@(posedge clk) disable iff(rst) $rose(!ex_freeze && !id_freeze) ##1 (!ex_freeze && !id_freeze && sel_b == 2'd2 && $stable(ex_forw) && $stable(sel_b)) |-> muxed_b == ex_forw);
assert property (@(posedge clk) disable iff(rst) $rose(!ex_freeze && !id_freeze) ##1 (!ex_freeze && !id_freeze && sel_b == 2'd3 && $stable(wb_forw) && $stable(sel_b)) |-> muxed_b == wb_forw);
assert property (@(posedge clk) disable iff(rst) $rose(!ex_freeze && !id_freeze) ##1 (!ex_freeze && !id_freeze && !(sel_b == 2'd1 || sel_b == 2'd2 || sel_b == 2'd3) && $stable(rf_datab) && $stable(sel_b)) |-> muxed_b == rf_datab);

// assert property (@(posedge clk) disable iff(rst) ((!ex_freeze && !id_freeze) |-> (sel_a == 2'd2 && ex_forw == muxed_a && id_freeze == ##1 ex_freeze)));
// assert property (@(posedge clk) disable iff(rst) ($rose(!ex_freeze && !id_freeze) ##1 (!ex_freeze && !id_freeze && sel_a == 2'd2 && $stable(ex_forw) && $stable(sel_a)) |-> muxed_a == ex_forw) iff ((!ex_freeze && !id_freeze) |-> (sel_a == 2'd2 && ex_forw == muxed_a && id_freeze == ##1 ex_freeze)));
// assert property (@(posedge clk) disable iff(rst) ((!ex_freeze && !id_freeze) |-> ((#1 !$changed(ex_freeze) && !$changed(id_freeze)) && (sel_a == 2'd3) && (!$changed(wb_forw[1]) && !$changed(sel_a)))));
// assert property (@(posedge clk) disable iff(rst) ($rose(!ex_freeze && !id_freeze) ##1 (!ex_freeze && !id_freeze && sel_a == 2'd3 && $stable(wb_forw) && $stable(sel_a)) |-> muxed_a == wb_forw) iff ((!ex_freeze && !id_freeze) |-> ((#1 !$changed(ex_freeze) && !$changed(id_freeze)) && (sel_a == 2'd3) && (!$changed(wb_forw[1]) && !$changed(sel_a)))));
// assert property (@(posedge clk) disable iff(rst) ((!ex_freeze && !id_freeze) |=> (!ex_freeze && !id_freeze && sel_a != 2'd2 && sel_a != 2'd3 && rf_dataa == operand_a && sel_a == muxed_a) && ##1 (!ex_freeze && !id_freeze)));
// assert property (@(posedge clk) disable iff(rst) ($rose(!ex_freeze && !id_freeze) ##1 (!ex_freeze && !id_freeze && !(sel_a == 2'd2 || sel_a == 2'd3) && $stable(rf_dataa) && $stable(sel_a) && !$isunknown(operand_a)) |-> muxed_a == rf_dataa) iff ((!ex_freeze && !id_freeze) |=> (!ex_freeze && !id_freeze && sel_a != 2'd2 && sel_a != 2'd3 && rf_dataa == operand_a && sel_a == muxed_a) && ##1 (!ex_freeze && !id_freeze)));
assert property (@(posedge clk) disable iff(rst) (!$rose(ex_freeze) && !$rose(id_freeze) && $fell(sel_b) && $stable(simm) && $stable(muxed_b) |-> ($fell(ex_freeze) && $fell(id_freeze) && sel_b == 2'd1 && $stable(simm) && $stable(muxed_b) |=> muxed_b == simm)));
assert property (@(posedge clk) disable iff(rst) ($rose(!ex_freeze && !id_freeze) ##1 (!ex_freeze && !id_freeze && sel_b == 2'd1 && $stable(simm) && $stable(sel_b)) |-> muxed_b == simm) iff (!$rose(ex_freeze) && !$rose(id_freeze) && $fell(sel_b) && $stable(simm) && $stable(muxed_b) |-> ($fell(ex_freeze) && $fell(id_freeze) && sel_b == 2'd1 && $stable(simm) && $stable(muxed_b) |=> muxed_b == simm)));
assert property (@(posedge clk) disable iff(rst) ((ex_freeze == 0) && (id_freeze == 0) && (sel_b == 2'd2) && (ex_forw == muxed_b) && (sel_b == ex_forw)));
assert property (@(posedge clk) disable iff(rst) ($rose(!ex_freeze && !id_freeze) ##1 (!ex_freeze && !id_freeze && sel_b == 2'd2 && $stable(ex_forw) && $stable(sel_b)) |-> muxed_b == ex_forw) iff ((ex_freeze == 0) && (id_freeze == 0) && (sel_b == 2'd2) && (ex_forw == muxed_b) && (sel_b == ex_forw)));
assert property (@(posedge clk) disable iff(rst) ((!ex_freeze && !id_freeze) |-> ##1 (!ex_freeze && !id_freeze && sel_b == 2'd3 && muxed_b == sel_b)));
assert property (@(posedge clk) disable iff(rst) ($rose(!ex_freeze && !id_freeze) ##1 (!ex_freeze && !id_freeze && sel_b == 2'd3 && $stable(wb_forw) && $stable(sel_b)) |-> muxed_b == wb_forw) iff ((!ex_freeze && !id_freeze) |-> ##1 (!ex_freeze && !id_freeze && sel_b == 2'd3 && muxed_b == sel_b)));
// assert property (@(posedge clk) disable iff(rst) ((ex_freeze !== 1'b1 && id_freeze !== 1'b1) &&                   ##1 (ex_freeze !== 1'b1 && id_freeze !== 1'b1) &&                   (sel_b !== 2'd1 && sel_b !== 2'd2 && sel_b !== 2'd3) &&                   $stable(rf_datab) && $stable(sel_b) &&                   $past(rf_datab) == muxed_b));
// assert property (@(posedge clk) disable iff(rst) ($rose(!ex_freeze && !id_freeze) ##1 (!ex_freeze && !id_freeze && !(sel_b == 2'd1 || sel_b == 2'd2 || sel_b == 2'd3) && $stable(rf_datab) && $stable(sel_b)) |-> muxed_b == rf_datab) iff ((ex_freeze !== 1'b1 && id_freeze !== 1'b1) &&                   ##1 (ex_freeze !== 1'b1 && id_freeze !== 1'b1) &&                   (sel_b !== 2'd1 && sel_b !== 2'd2 && sel_b !== 2'd3) &&                   $stable(rf_datab) && $stable(sel_b) &&                   $past(rf_datab) == muxed_b));

endmodule
