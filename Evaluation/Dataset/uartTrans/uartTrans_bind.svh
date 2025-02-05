bind uartTrans
 uartTrans_sva u_uartTrans_sva(
.reset(reset),
.stateNext(stateNext),
.tx(tx),
.nReg(nReg),
.clk(clk),
.sNext(sNext),
.txReg(txReg),
.bNext(bNext),
.sReg(sReg),
.txDoneTick(txDoneTick),
.nNext(nNext),
.bReg(bReg),
.sTick(sTick),
.txStart(txStart),
.txNext(txNext),
.stateReg(stateReg),
.din(din)
);