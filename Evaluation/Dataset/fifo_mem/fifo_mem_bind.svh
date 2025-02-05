bind fifo_mem
 fifo_mem_sva u_fifo_mem_sva(
.empty(empty),
.r_en(r_en),
.rclk(rclk),
.w_en(w_en),
.data_out(data_out),
.data_in(data_in),
.b_wptr(b_wptr),
.full(full),
.wclk(wclk),
.b_rptr(b_rptr)
);