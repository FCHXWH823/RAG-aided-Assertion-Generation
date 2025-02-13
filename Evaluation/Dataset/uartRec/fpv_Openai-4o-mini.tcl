analyze -clear
analyze -sv12 ./uartRec_Openai-4o-mini.sv

elaborate -top uartRec

clock clk
reset reset
prove -all
report -summary -force -result -file fpv_Openai-4o-mini.rpt
exit

