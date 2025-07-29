analyze -clear
analyze -sv12 ./module_i2c_deepseek-coder-7b-instruct-v1.5-vcs.sv

elaborate -top module_i2c

clock PCLK
reset PRESETn
prove -all
report -summary -force -result -file fpv_deepseek-coder-7b-instruct-v1.5-vcs.rpt
exit

