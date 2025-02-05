bind fifo fifo_sva 
#(.WIDTH(WIDTH),.DEPTH(DEPTH)) 
u_fifo_sva (.*,.valid_wr(valid_wr),.valid_rd(valid_rd));
