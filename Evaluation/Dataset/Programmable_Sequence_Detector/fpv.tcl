analyze -clear
analyze -sv12 ./Programmable_Sequence_Detector_assertion.sv

elaborate -top Programmable_Sequence_Detector

clock clk
reset -expression ~resetn
prove -all
report -summary -force -result -file fpv.rpt
exit

