analyze -clear
analyze -sv12 ./control_unit_deepseek-coder-7b-instruct-v1.5-vcs.sv

elaborate -top control_unit

clock clk
reset -expression rst_n
prove -all
report -summary -force -result -file fpv_deepseek-coder-7b-instruct-v1.5-vcs.rpt
exit

