analyze -clear
analyze -sv12 ./a25_wishbone_CoT-Dynamic-RAG-Openai-4o-mini.sv

elaborate -top a25_wishbone

clock i_clk
reset -expression ~quick_n_reset
prove -all
report -summary -force -result -file fpv_CoT-Dynamic-RAG-Openai-4o-mini.rpt
exit

