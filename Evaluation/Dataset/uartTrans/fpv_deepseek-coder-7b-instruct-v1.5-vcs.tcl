analyze -clear
analyze -sv12 ./uartTrans_deepseek-coder-7b-instruct-v1.5-vcs.sv

elaborate -top uartTrans

clock clk
reset reset
prove -all
report -summary -force -result -file fpv_deepseek-coder-7b-instruct-v1.5-vcs.rpt
exit

