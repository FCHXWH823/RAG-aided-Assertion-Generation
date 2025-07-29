analyze -clear
analyze -sv12 ./lcd_deepseek-coder-7b-instruct-v1.5-vcs.sv

elaborate -top lcd

clock clk
reset -none
prove -all
report -summary -force -result -file fpv_deepseek-coder-7b-instruct-v1.5-vcs.rpt
exit

