analyze -clear
analyze -sv12 ./Programmable_Sequence_Detector_Openai-4o-mini.sv

elaborate -top Programmable_Sequence_Detector

clock clk
reset -expression ~resetn
prove -all
report -summary -force -result -file fpv_Openai-4o-mini.rpt
exit

