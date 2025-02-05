analyze -clear
analyze -sv12 ./eth_rxstatem.sv
analyze -sv12 ./eth_rxstatem_sva.sv
analyze -sv12 ./eth_rxstatem_bind.svh

elaborate -top eth_rxstatem

clock MRxClk
reset Reset
prove -all
report -summary -force -result -file fpv.rpt
exit

