# ----------------------------------------
# Jasper Version Info
# tool      : Jasper 2022.09
# platform  : Linux 3.10.0-1160.el7.x86_64
# version   : 2022.09p001 64 bits
# build date: 2022.10.25 11:32:28 UTC
# ----------------------------------------
# started   : 2025-01-26 05:44:44 CST
# hostname  : icpc.(none)
# pid       : 89292
# arguments : '-label' 'session_0' '-console' '//127.0.0.1:45479' '-nowindow' '-style' 'windows' '-data' 'AAAA5nicbY7BCoJQFETPS9xGP6L9gDtpZ0QF1U7ENALRSItoU5/an7zGF0JBA/fOzGXuu88A0cNai4N3V5uQMGfFTH3BRgw7phTcONFwppNbS5VSWzJNCk1iqb1UTe58xdGpmvaPD5XNtO9gXh8mMnzDLJ8/DP4QVI1UYwI92JBy4KID/aTUN6860Olc1YffgRsgGg==' '-proj' '/home/master/Dataset/fifo/jgproject/sessionLogs/session_0' '-init' '-hidden' '/home/master/Dataset/fifo/jgproject/.tmp/.initCmds.tcl' 'fpv.tcl'
analyze -clear
analyze -sv ./fifo.sv
analyze -sv ./fifo_sva.sv
analyze -sv ./fifo_bind.svh

elaborate -top fifo

clock clk
reset -expression rst
prove -all
report -summary -force -result -file fpv.rpt
exit
