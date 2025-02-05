# ----------------------------------------
# Jasper Version Info
# tool      : Jasper 2022.09
# platform  : Linux 3.10.0-1160.el7.x86_64
# version   : 2022.09p001 64 bits
# build date: 2022.10.25 11:32:28 UTC
# ----------------------------------------
# started   : 2025-01-27 14:49:59 CST
# hostname  : icpc.(none)
# pid       : 37735
# arguments : '-label' 'session_0' '-console' '//127.0.0.1:43296' '-nowindow' '-style' 'windows' '-data' 'AAAA5nicbY7BCoJQFETPS9xGP6L9gDtpZ0QF1U7ENALRSItoU5/an7zGF0JBA/fOzGXuu88A0cNai4N3V5uQMGfFTH3BRgw7phTcONFwppNbS5VSWzJNCk1iqb1UTe58xdGpmvaPD5XNtO9gXh8mMnzDLJ8/DP4QVI1UYwI92JBy4KID/aTUN6860Olc1YffgRsgGg==' '-proj' '/home/master/Dataset/reversing_bits/jgproject/sessionLogs/session_0' '-init' '-hidden' '/home/master/Dataset/reversing_bits/jgproject/.tmp/.initCmds.tcl' 'fpv.tcl'
analyze -clear
analyze -sv ./reversing_bits.sv
analyze -sv ./reversing_bits_sva.sv
analyze -sv ./reversing_bits_bind.svh

elaborate -top reversing_bits

clock clk
reset -expression rst
prove -all
report -summary -force -result -file fpv.rpt
exit
