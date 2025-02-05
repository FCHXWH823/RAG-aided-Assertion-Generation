analyze -clear
analyze -sv12 ./uartRec.sv
analyze -sv12 ./uartRec_sva.sv
analyze -sv12 ./uartRec_bind.svh

elaborate -top uartRec

clock clk
reset reset
prove -all
report -summary -force -result -file fpv.rpt
exit

