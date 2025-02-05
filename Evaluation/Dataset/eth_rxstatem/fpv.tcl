analyze -clear
analyze -sv12 ./eth_rxstatem_assertion.sv

elaborate -top eth_rxstatem

clock MRxClk
reset Reset
prove -all
report -summary -force -result -file fpv.rpt
exit

