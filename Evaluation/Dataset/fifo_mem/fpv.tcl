analyze -clear
analyze -sv12 ./fifo_mem.sv
analyze -sv12 ./fifo_mem_sva.sv
analyze -sv12 ./fifo_mem_bind.svh

elaborate -top fifo_mem

clock -infer
reset -none
prove -all
report -summary -force -result -file fpv.rpt
exit

