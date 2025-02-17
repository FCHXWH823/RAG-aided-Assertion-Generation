analyze -clear
analyze -sv12 ./or1200_operandmuxes_Dynamic-RAG-Openai-4o-mini.sv
analyze -sv12 ./or1200_defines.v

elaborate -top or1200_operandmuxes

clock clk
reset -expression rst
prove -all
report -summary -force -result -file fpv_Dynamic-RAG-Openai-4o-mini.rpt
exit

