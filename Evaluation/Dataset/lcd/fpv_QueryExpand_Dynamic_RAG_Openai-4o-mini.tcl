analyze -clear
analyze -sv12 ./lcd_QueryExpand-Dynamic-RAG-Openai-4o-mini.sv

elaborate -top lcd

clock clk
reset -none
prove -all
report -summary -force -result -file fpv_QueryExpand-Dynamic-RAG-Openai-4o-mini.rpt
exit

