analyze -clear
analyze -sv12 ./apb.sv
analyze -sv12 ./apb_sva.sv
analyze -sv12 ./apb_bind.svh

elaborate -top apb

clock PCLK
reset PRESETn
prove -all
report -summary -force -result -file fpv.rpt
exit

