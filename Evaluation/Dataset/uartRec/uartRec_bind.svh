bind uartRec
 uartRec_sva u_uartRec_sva(
.bNext(bNext),
.stateReg(stateReg),
.nNext(nNext),
.clk(clk),
.sTick(sTick),
.rxDoneTick(rxDoneTick),
.nReg(nReg),
.bReg(bReg),
.rx(rx),
.sReg(sReg),
.dOut(dOut),
.reset(reset),
.stateNext(stateNext),
.sNext(sNext)
);