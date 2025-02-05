analyze -clear
analyze -sv12 ./apb_assertion.sv

elaborate -top apb

clock PCLK
reset PRESETn
prove -all
report -summary -force -result -file fpv.rpt
exit

