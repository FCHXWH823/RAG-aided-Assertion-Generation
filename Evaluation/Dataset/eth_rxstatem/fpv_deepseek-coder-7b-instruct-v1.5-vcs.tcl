analyze -clear
analyze -sv12 ./eth_rxstatem_deepseek-coder-7b-instruct-v1.5-vcs.sv

elaborate -top eth_rxstatem

clock MRxClk
reset Reset
prove -all
report -summary -force -result -file fpv_deepseek-coder-7b-instruct-v1.5-vcs.rpt
exit

