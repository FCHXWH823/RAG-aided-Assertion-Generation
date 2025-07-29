analyze -clear
analyze -sv12 ./Programmable_Sequence_Detector_deepseek-coder-7b-instruct-v1.5-vcs.sv

elaborate -top Programmable_Sequence_Detector

clock clk
reset -expression ~resetn
prove -all
report -summary -force -result -file fpv_deepseek-coder-7b-instruct-v1.5-vcs.rpt
exit

