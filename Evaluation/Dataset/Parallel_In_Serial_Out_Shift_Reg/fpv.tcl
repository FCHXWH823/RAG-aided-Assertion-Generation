analyze -clear
analyze -sv ./Parallel_In_Serial_Out_Shift_Reg.sv
analyze -sv ./Parallel_In_Serial_Out_Shift_Reg_sva.sv
analyze -sv ./Parallel_In_Serial_Out_Shift_Reg_bind.svh

elaborate -top Parallel_In_Serial_Out_Shift_Reg

clock clk
reset -expression ~resetn
prove -all
report -summary -force -result -file fpv.rpt
exit

