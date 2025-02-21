analyze -clear
analyze -sv12 ./reversing_bits_QueryExpand-Dynamic-RAG-Openai-4o-mini.sv

elaborate -top reversing_bits

clock clk
reset -expression rst
prove -all
report -summary -force -result -file fpv__QueryExpand-Dynamic-RAG-Openai-4o-mini.rpt
exit

