analyze -clear
analyze -sv12 ./or1200_defines.v
analyze -sv12 ./or1200_ctrl_deepseek-coder-7b-instruct-v1.5-vcs.sv

elaborate -top or1200_ctrl

clock clk
reset -expression rst
prove -all
report -summary -force -result -file fpv_deepseek-coder-7b-instruct-v1.5-vcs.rpt
exit

