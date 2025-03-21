////////////////////////////////////////////////////////////////////////////////////////////////
////                                                              							////
////                                                              							////
////  	This file is part of the project                 									////
////	"instruction_list_pipelined_processor_with_peripherals"								////
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
////	"instruction_list_pipelined_processor_with_peripherals"								////
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


assert property(@(posedge clk) (txNext == 0) |=> (tx == 0));  
assert property(@(posedge clk) (txNext == 1) |=> (tx == 1));  
assert property(@(posedge clk) (stateReg[0] == 1) |-> (txDoneTick == 0));  
assert property(@(posedge clk) (txStart == 0) |-> (txDoneTick == 0));

assert property (@(posedge clk)  ((txNext == 0) |=> (tx == 0)));
assert property (@(posedge clk)  ((txNext == 0) |=> (tx == 0)) iff ((txNext == 0) |=> (tx == 0)));
assert property (@(posedge clk)  (txNext == 1'b1 |=> tx == 1'b1));
assert property (@(posedge clk)  ((txNext == 1) |=> (tx == 1)) iff (txNext == 1'b1 |=> tx == 1'b1));
assert property (@(posedge clk)  (stateReg[1] == 1'b1 |-> txDoneTick == 1'b0));
assert property (@(posedge clk)  ((stateReg[0] == 1) |-> (txDoneTick == 0)) iff (stateReg[1] == 1'b1 |-> txDoneTick == 1'b0));
assert property (@(posedge clk)  (!txStart |-> !txDoneTick));
assert property (@(posedge clk)  ((txStart == 0) |-> (txDoneTick == 0)) iff (!txStart |-> !txDoneTick));

endmodule
