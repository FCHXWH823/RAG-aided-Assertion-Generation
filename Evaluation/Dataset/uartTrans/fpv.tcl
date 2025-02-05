analyze -clear
analyze -sv12 ./uartTrans.sv
analyze -sv12 ./uartTrans_sva.sv
analyze -sv12 ./uartTrans_bind.svh

elaborate -top uartTrans

clock clk
reset reset
prove -all
report -summary -force -result -file fpv.rpt
exit

