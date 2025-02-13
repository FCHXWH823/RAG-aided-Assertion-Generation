analyze -clear
analyze -sv12 ./Edge_Detector_RAG-Openai-4o-mini.sv

elaborate -top Edge_Detector

clock clk
reset -expression ~resetn
prove -all
report -summary -force -result -file fpv_RAG-Openai-4o-mini.rpt
exit

