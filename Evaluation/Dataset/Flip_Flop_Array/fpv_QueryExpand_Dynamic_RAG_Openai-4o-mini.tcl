analyze -clear
analyze -sv12 ./Flip_Flop_Array_QueryExpand-Dynamic-RAG-Openai-4o-mini.sv

elaborate -top Flip_Flop_Array

clock clk
reset -expression ~resetn
prove -all
report -summary -force -result -file fpv__QueryExpand-Dynamic-RAG-Openai-4o-mini.rpt
exit

