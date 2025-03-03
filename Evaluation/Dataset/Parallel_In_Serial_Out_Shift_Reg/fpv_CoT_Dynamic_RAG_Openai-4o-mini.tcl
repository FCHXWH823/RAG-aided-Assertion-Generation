analyze -clear
analyze -sv12 ./Parallel_In_Serial_Out_Shift_Reg_CoT-Dynamic-RAG-Openai-4o-mini.sv

elaborate -top Parallel_In_Serial_Out_Shift_Reg

clock clk
reset -expression ~resetn
prove -all
report -summary -force -result -file fpv_CoT-Dynamic-RAG-Openai-4o-mini.rpt
exit

