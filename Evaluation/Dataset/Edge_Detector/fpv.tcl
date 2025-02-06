analyze -clear
analyze -sv12 ./Edge_Detector_assertion.sv

elaborate -top Edge_Detector

clock clk
reset -expression ~resetn
prove -all
report -summary -force -result -file fpv.rpt
exit

