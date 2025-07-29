analyze -clear
analyze -sv12 ./Parallel_In_Serial_Out_Shift_Reg_deepseek-coder-7b-instruct-v1.5-vcs.sv

elaborate -top Parallel_In_Serial_Out_Shift_Reg

clock clk
reset -expression ~resetn
prove -all
report -summary -force -result -file fpv_deepseek-coder-7b-instruct-v1.5-vcs.rpt
exit

