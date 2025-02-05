analyze -clear
analyze -sv ./Programmable_Sequence_Detector.sv
analyze -sv ./Programmable_Sequence_Detector_sva.sv
analyze -sv ./Programmable_Sequence_Detector_bind.svh

elaborate -top Programmable_Sequence_Detector

clock clk
reset -expression ~resetn
prove -all
report -summary -force -result -file fpv.rpt
exit

