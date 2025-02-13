analyze -clear
analyze -sv12 ./SEVEN_RAG-Openai-4o-mini.sv

elaborate -top SEVEN

clock clk
reset -expression rst
prove -all
report -summary -force -result -file fpv_RAG-Openai-4o-mini.rpt
exit

