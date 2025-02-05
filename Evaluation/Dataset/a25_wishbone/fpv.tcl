analyze -clear
analyze -sv12 ./a25_wishbone.sv

elaborate -top a25_wishbone

clock i_clk
reset -expression ~quick_n_reset
prove -all
report -summary -force -result -file fpv.rpt
exit

