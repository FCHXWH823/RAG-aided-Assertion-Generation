analyze -clear
analyze -sv12 ./apb_deepseek-coder-7b-instruct-v1.5-vcs.sv

elaborate -top apb

clock PCLK
reset PRESETn
prove -all
report -summary -force -result -file fpv_deepseek-coder-7b-instruct-v1.5-vcs.rpt
exit

