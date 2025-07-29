analyze -clear
analyze -sv12 ./Gray_Code_Counter_deepseek-coder-7b-instruct-v1.5-vcs.sv

elaborate -top Gray_Code_Counter

clock clk
reset -expression ~resetn
prove -all
report -summary -force -result -file fpv_deepseek-coder-7b-instruct-v1.5-vcs.rpt
exit

