analyze -clear
analyze -sv12 ./second_largest_deepseek-coder-7b-instruct-v1.5-vcs.sv

elaborate -top second_largest

clock clk
reset -expression ~resetn
prove -all
report -summary -force -result -file fpv_deepseek-coder-7b-instruct-v1.5-vcs.rpt
exit

