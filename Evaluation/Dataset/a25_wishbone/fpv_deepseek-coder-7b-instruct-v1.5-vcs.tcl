analyze -clear
analyze -sv12 ./a25_wishbone_deepseek-coder-7b-instruct-v1.5-vcs.sv

elaborate -top a25_wishbone

clock i_clk
reset -expression ~quick_n_reset
prove -all
report -summary -force -result -file fpv_deepseek-coder-7b-instruct-v1.5-vcs.rpt
exit

