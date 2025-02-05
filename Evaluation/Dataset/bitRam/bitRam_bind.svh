bind bitRam bitRam_sva u_bitRam_sva(
.clk(clk),
.reset(reset),
.bitRamEn(bitRamEn),
.bitRamRw(bitRamRw),
.bitRamIn(bitRamIn), 
.bitRamAddr(bitRamAddr),
.bitRamOut(bitRamOut)
);