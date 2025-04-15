//////////////////////////////////////////////////////////////////////
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


assert property(@(posedge MRxClk)  (StartPreamble == 1) |=> (StatePreamble == 1));  
assert property(@(posedge MRxClk)  (StartDrop == 1) |=> (StatePreamble == 0));  
assert property(@(posedge MRxClk)  (StateSFD == 1) |=> (StatePreamble == 0));  
assert property(@(posedge MRxClk)  (StateData[0] == 1) |=> (StatePreamble == 0));  
assert property(@(posedge MRxClk)  (StateDrop == 1) |=> (StatePreamble == 0));  
assert property(@(posedge MRxClk)  (StateData1 == 1) |=> (StatePreamble == 0));  
assert property(@(posedge MRxClk)  (StatePreamble == 1 & MRxDEq5 == 0 & MRxDV == 1) |=> (StatePreamble == 1));  
assert property(@(posedge MRxClk)  (MRxDEq5 == 1) |=> (StatePreamble == 0));  
assert property(@(posedge MRxClk)  (MRxDV == 0) |=> (StatePreamble == 0));  
assert property(@(posedge MRxClk)  (StartSFD == 1) |=> (StateSFD == 1));  
assert property(@(posedge MRxClk)  (StartIdle == 1) |=> (StateSFD == 0));  
assert property(@(posedge MRxClk)  (StartDrop == 1) |=> (StateSFD == 0));  
assert property(@(posedge MRxClk)  (StartData0 == 1) |=> (StateSFD == 0));  
assert property(@(posedge MRxClk)  (StartPreamble == 1) |=> (StateSFD == 0));  
assert property(@(posedge MRxClk)  (StateSFD == 1 & StartIdle == 0 & MRxDEqD == 0) |=> (StateSFD == 1));  
assert property(@(posedge MRxClk)  (StateData[0] == 1) |=> (StateSFD == 0));  
assert property(@(posedge MRxClk)  (StateDrop == 1) |=> (StateSFD == 0));  
assert property(@(posedge MRxClk)  (MRxDEq5 == 0 & StatePreamble == 1) |=> (StateSFD == 0));  
assert property(@(posedge MRxClk)  (MRxDV == 0) |=> (StateSFD == 0));  
assert property(@(posedge MRxClk)  (StartIdle == 1) |=> (StateDrop == 0));  
assert property(@(posedge MRxClk)  (StartDrop == 1) |=> (StateDrop == 1));  
assert property(@(posedge MRxClk)  (StateDrop == 1 & StartIdle == 0) |=> (StateDrop == 1));  
assert property(@(posedge MRxClk)  (StateSFD == 1 & StartDrop == 0) |=> (StateDrop == 0));  
assert property(@(posedge MRxClk)  (StateData[0] == 1 & StartDrop == 0) |=> (StateDrop == 0));  
assert property(@(posedge MRxClk)  (StatePreamble == 1) |=> (StateDrop == 0));  
assert property(@(posedge MRxClk)  (StateData1 == 1) |=> (StateDrop == 0));  
assert property(@(posedge MRxClk)  (MRxDV == 0) |=> (StateDrop == 0));  
assert property(@(posedge MRxClk)  (Transmitting == 0 & StateIdle == 1) |=> (StateDrop == 0));  
assert property(@(posedge MRxClk)  (StartIdle == 1) |=> (StateIdle == 1));  
assert property(@(posedge MRxClk)  (StartDrop == 1) |=> (StateIdle == 0));  
assert property(@(posedge MRxClk)  (StartSFD == 1) |=> (StateIdle == 0));  
assert property(@(posedge MRxClk)  (StartPreamble == 1) |=> (StateIdle == 0));  
assert property(@(posedge MRxClk)  (MRxDV == 1) |=> (StateIdle == 0));  
assert property(@(posedge MRxClk)  (MRxDV == 0) |=> (StateIdle == 1));

assert property (@(posedge MRxClk)  (StartPreamble |=> StatePreamble));
assert property (@(posedge MRxClk)  ((StartPreamble == 1) |=> (StatePreamble == 1)) iff (StartPreamble |=> StatePreamble));
assert property (@(posedge MRxClk)  (StartDrop |=> !StatePreamble));
assert property (@(posedge MRxClk)  ((StartDrop == 1) |=> (StatePreamble == 0)) iff (StartDrop |=> !StatePreamble));
assert property (@(posedge MRxClk)  (StateSFD |=> !StatePreamble));
assert property (@(posedge MRxClk)  ((StateSFD == 1) |=> (StatePreamble == 0)) iff (StateSFD |=> !StatePreamble));
assert property (@(posedge MRxClk)  (StateData0 == 1'b1 |=> StatePreamble == 1'b0));
assert property (@(posedge MRxClk)  ((StateData[0] == 1) |=> (StatePreamble == 0)) iff (StateData0 == 1'b1 |=> StatePreamble == 1'b0));
assert property (@(posedge MRxClk)  (StateDrop |=> !StatePreamble));
assert property (@(posedge MRxClk)  ((StateDrop == 1) |=> (StatePreamble == 0)) iff (StateDrop |=> !StatePreamble));
assert property (@(posedge MRxClk)  (!StateData1 || !$past(StatePreamble)));
assert property (@(posedge MRxClk)  ((StateData1 == 1) |=> (StatePreamble == 0)) iff (!StateData1 || !$past(StatePreamble)));
assert property (@(posedge MRxClk)  ((StatePreamble == 1'b1 && MRxDEq5 == 1'b0 && MRxDV == 1'b1) |=> (StatePreamble == 1'b1)));
assert property (@(posedge MRxClk)  ((StatePreamble == 1 & MRxDEq5 == 0 & MRxDV == 1) |=> (StatePreamble == 1)) iff ((StatePreamble == 1'b1 && MRxDEq5 == 1'b0 && MRxDV == 1'b1) |=> (StatePreamble == 1'b1)));
assert property (@(posedge MRxClk)  (MRxDEq5 |=> !StatePreamble));
assert property (@(posedge MRxClk)  ((MRxDEq5 == 1) |=> (StatePreamble == 0)) iff (MRxDEq5 |=> !StatePreamble));
assert property (@(posedge MRxClk)  ((~MRxDV) |=> ~StatePreamble));
assert property (@(posedge MRxClk)  ((MRxDV == 0) |=> (StatePreamble == 0)) iff ((~MRxDV) |=> ~StatePreamble));
assert property (@(posedge MRxClk)  (StartSFD |=> StateSFD));
assert property (@(posedge MRxClk)  ((StartSFD == 1) |=> (StateSFD == 1)) iff (StartSFD |=> StateSFD));
assert property (@(posedge MRxClk)  (a |=> b));
assert property (@(posedge MRxClk)  ((StartIdle == 1) |=> (StateSFD == 0)) iff (a |=> b));
assert property (@(posedge MRxClk)  (StartDrop |=> !StateSFD));
assert property (@(posedge MRxClk)  ((StartDrop == 1) |=> (StateSFD == 0)) iff (StartDrop |=> !StateSFD));
assert property (@(posedge MRxClk)  (StartData0 |=> !StateSFD));
assert property (@(posedge MRxClk)  ((StartData0 == 1) |=> (StateSFD == 0)) iff (StartData0 |=> !StateSFD));
assert property (@(posedge MRxClk)  (StartPreamble |=> !StateSFD));
assert property (@(posedge MRxClk)  ((StartPreamble == 1) |=> (StateSFD == 0)) iff (StartPreamble |=> !StateSFD));
assert property (@(posedge MRxClk)  (StateSFD && !StartIdle && !MRxDEqD |=> StateSFD));
assert property (@(posedge MRxClk)  ((StateSFD == 1 & StartIdle == 0 & MRxDEqD == 0) |=> (StateSFD == 1)) iff (StateSFD && !StartIdle && !MRxDEqD |=> StateSFD));
assert property (@(posedge MRxClk)  (StateData0 |=> !StateSFD));
assert property (@(posedge MRxClk)  ((StateData[0] == 1) |=> (StateSFD == 0)) iff (StateData0 |=> !StateSFD));
assert property (@(posedge MRxClk)  (StateDrop |=> !StateSFD));
assert property (@(posedge MRxClk)  ((StateDrop == 1) |=> (StateSFD == 0)) iff (StateDrop |=> !StateSFD));
assert property (@(posedge MRxClk)  ((~MRxDEq5 & StatePreamble) |=> ~StateSFD));
assert property (@(posedge MRxClk)  ((MRxDEq5 == 0 & StatePreamble == 1) |=> (StateSFD == 0)) iff ((~MRxDEq5 & StatePreamble) |=> ~StateSFD));
assert property (@(posedge MRxClk)  (~MRxDV |=> ~StateSFD));
assert property (@(posedge MRxClk)  ((MRxDV == 0) |=> (StateSFD == 0)) iff (~MRxDV |=> ~StateSFD));
assert property (@(posedge MRxClk)  ((StartIdle) |-> (StateDrop == 1'b0)));
assert property (@(posedge MRxClk)  ((StartIdle == 1) |=> (StateDrop == 0)) iff ((StartIdle) |-> (StateDrop == 1'b0)));
assert property (@(posedge MRxClk)  (StartDrop |-> StateDrop));
assert property (@(posedge MRxClk)  ((StartDrop == 1) |=> (StateDrop == 1)) iff (StartDrop |-> StateDrop));
assert property (@(posedge MRxClk)  (StateDrop && !StartIdle |=> StateDrop));
assert property (@(posedge MRxClk)  ((StateDrop == 1 & StartIdle == 0) |=> (StateDrop == 1)) iff (StateDrop && !StartIdle |=> StateDrop));
assert property (@(posedge MRxClk)  ((StateSFD && !StartDrop) |=> !StateDrop));
assert property (@(posedge MRxClk)  ((StateSFD == 1 & StartDrop == 0) |=> (StateDrop == 0)) iff ((StateSFD && !StartDrop) |=> !StateDrop));
assert property (@(posedge MRxClk)  ((StateData[0] == 1'b1 && StartDrop == 1'b0) |=> (StateDrop == 1'b0)));
assert property (@(posedge MRxClk)  ((StateData[0] == 1 & StartDrop == 0) |=> (StateDrop == 0)) iff ((StateData[0] == 1'b1 && StartDrop == 1'b0) |=> (StateDrop == 1'b0)));
assert property (@(posedge MRxClk)  (!StatePreamble || !$past(StateDrop)));
assert property (@(posedge MRxClk)  ((StatePreamble == 1) |=> (StateDrop == 0)) iff (!StatePreamble || !$past(StateDrop)));
assert property (@(posedge MRxClk)  (StateData1 |=> !StateDrop));
assert property (@(posedge MRxClk)  ((StateData1 == 1) |=> (StateDrop == 0)) iff (StateData1 |=> !StateDrop));
assert property (@(posedge MRxClk)  (!MRxDV |=> !StateDrop));
assert property (@(posedge MRxClk)  ((MRxDV == 0) |=> (StateDrop == 0)) iff (!MRxDV |=> !StateDrop));
assert property (@(posedge MRxClk)  ((~Transmitting & StateIdle) |=> ~StateDrop));
assert property (@(posedge MRxClk)  ((Transmitting == 0 & StateIdle == 1) |=> (StateDrop == 0)) iff ((~Transmitting & StateIdle) |=> ~StateDrop));
assert property (@(posedge MRxClk)  (StartIdle |=> StateIdle));
assert property (@(posedge MRxClk)  ((StartIdle == 1) |=> (StateIdle == 1)) iff (StartIdle |=> StateIdle));
assert property (@(posedge MRxClk)  (StartDrop |=> !StateIdle));
assert property (@(posedge MRxClk)  ((StartDrop == 1) |=> (StateIdle == 0)) iff (StartDrop |=> !StateIdle));
assert property (@(posedge MRxClk)  (StartSFD |=> !StateIdle));
assert property (@(posedge MRxClk)  ((StartSFD == 1) |=> (StateIdle == 0)) iff (StartSFD |=> !StateIdle));
assert property (@(posedge MRxClk)  (StartPreamble |=> !StateIdle));
assert property (@(posedge MRxClk)  ((StartPreamble == 1) |=> (StateIdle == 0)) iff (StartPreamble |=> !StateIdle));
assert property (@(posedge MRxClk)  (MRxDV |=> !StateIdle));
assert property (@(posedge MRxClk)  ((MRxDV == 1) |=> (StateIdle == 0)) iff (MRxDV |=> !StateIdle));
assert property (@(posedge MRxClk)  ((~MRxDV) |=> StateIdle));
assert property (@(posedge MRxClk)  ((MRxDV == 0) |=> (StateIdle == 1)) iff ((~MRxDV) |=> StateIdle));

endmodule
