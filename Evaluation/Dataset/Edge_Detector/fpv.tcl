analyze -clear
analyze -sv ./Edge_Detector.sv
analyze -sv ./Edge_Detector_sva.sv
analyze -sv ./Edge_Detector_bind.svh

elaborate -top Edge_Detector

clock clk
reset -expression ~resetn
prove -all
report -summary -force -result -file fpv.rpt
exit

