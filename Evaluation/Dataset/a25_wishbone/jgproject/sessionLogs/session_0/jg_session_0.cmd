# ----------------------------------------
# Jasper Version Info
# tool      : Jasper 2022.09
# platform  : Linux 3.10.0-1160.el7.x86_64
# version   : 2022.09p001 64 bits
# build date: 2022.10.25 11:32:28 UTC
# ----------------------------------------
# started   : 2025-02-05 17:21:38 CST
# hostname  : icpc.(none)
# pid       : 48142
# arguments : '-label' 'session_0' '-console' '//127.0.0.1:40559' '-nowindow' '-style' 'windows' '-data' 'AAAA5nicbY7BCoJQFETPS9xGP6L9gDtpZ0QF1U7ENALRSItoU5/an7zGF0JBA/fOzGXuu88A0cNai4N3V5uQMGfFTH3BRgw7phTcONFwppNbS5VSWzJNCk1iqb1UTe58xdGpmvaPD5XNtO9gXh8mMnzDLJ8/DP4QVI1UYwI92JBy4KID/aTUN6860Olc1YffgRsgGg==' '-proj' '/home/master/Dataset/a25_wishbone/jgproject/sessionLogs/session_0' '-init' '-hidden' '/home/master/Dataset/a25_wishbone/jgproject/.tmp/.initCmds.tcl' 'fpv.tcl'
analyze -clear
analyze -sv12 ./a25_wishbone.sv

elaborate -top a25_wishbone

clock i_clk
reset -expression ~quick_n_reset
prove -all
report -summary -force -result -file fpv.rpt
exit
