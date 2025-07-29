analyze -clear
analyze -sv12 ./BusArbiter_assertion.sv

elaborate -top busarbiter

clock clk
reset -expression reset
prove -all
report -summary -force -result -file fpv_deepseek-coder-7b-instruct-v1.5-vcs.rpt
exit
