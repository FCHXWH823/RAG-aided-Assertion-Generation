# ----------------------------------------
# Jasper Version Info
# tool      : Jasper 2022.09
# platform  : Linux 3.10.0-1160.el7.x86_64
# version   : 2022.09p001 64 bits
# build date: 2022.10.25 11:32:28 UTC
# ----------------------------------------
# started   : 2025-01-27 15:53:26 CST
# hostname  : icpc.(none)
# pid       : 47657
# arguments : '-label' 'session_0' '-console' '//127.0.0.1:35320' '-nowindow' '-style' 'windows' '-data' 'AAAA5nicbY7BCoJQFETPS9xGP6L9gDtpZ0QF1U7ENALRSItoU5/an7zGF0JBA/fOzGXuu88A0cNai4N3V5uQMGfFTH3BRgw7phTcONFwppNbS5VSWzJNCk1iqb1UTe58xdGpmvaPD5XNtO9gXh8mMnzDLJ8/DP4QVI1UYwI92JBy4KID/aTUN6860Olc1YffgRsgGg==' '-proj' '/home/master/Dataset/Parallel_In_Serial_Out_Shift_Reg/jgproject/sessionLogs/session_0' '-init' '-hidden' '/home/master/Dataset/Parallel_In_Serial_Out_Shift_Reg/jgproject/.tmp/.initCmds.tcl' 'fpv.tcl'
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
