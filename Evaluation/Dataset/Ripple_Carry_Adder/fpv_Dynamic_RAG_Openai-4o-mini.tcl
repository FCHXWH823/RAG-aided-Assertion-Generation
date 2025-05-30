analyze -clear
analyze -sv12 ./Ripple_Carry_Adder_Dynamic-RAG-Openai-4o-mini.sv

elaborate -top Ripple_Carry_Adder

clock clk
reset -expression ~rst
prove -all
report -summary -force -result -file fpv_Dynamic-RAG-Openai-4o-mini.rpt
exit

