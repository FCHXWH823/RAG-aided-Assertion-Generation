analyze -clear
analyze -sv12 ./Flip_Flop_Array_deepseek-coder-7b-instruct-v1.5-vcs.sv

elaborate -top Flip_Flop_Array

clock clk
reset -expression ~resetn
prove -all
report -summary -force -result -file fpv_deepseek-coder-7b-instruct-v1.5-vcs.rpt
exit

