analyze -clear
analyze -sv12 ./register_deepseek-coder-7b-instruct-v1.5-vcs.sv

elaborate -top register

clock clk
reset -expression rst
prove -all
report -summary -force -result -file fpv_deepseek-coder-7b-instruct-v1.5-vcs.rpt
