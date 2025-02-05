# ----------------------------------------
# Jasper Version Info
# tool      : Jasper 2022.09
# platform  : Linux 3.10.0-1160.el7.x86_64
# version   : 2022.09p001 64 bits
# build date: 2022.10.25 11:32:28 UTC
# ----------------------------------------
# started   : 2025-01-23 06:05:23 CST
# hostname  : icpc.(none)
# pid       : 25983
# arguments : '-label' 'session_0' '-console' '//127.0.0.1:39115' '-style' 'windows' '-data' 'AAAA1HicbY7dCoJAEIW/JboNn6ReYO+iu0QsyG6lDITFxESkm3pU32Q7rgQJHZg5Pzs7jAHsy3tPwOKpFrEn5sBOPeEkhjMbCnpq7jS0ckepm1RGrqRQspW6SlVcgneUQVU8/vi1ZnP9DzDDxFjDL0z6njEsv4NjqlrpiJpO61otd+PTB1RIHV0=' '-proj' '/home/master/Dataset/ff/jgproject/sessionLogs/session_0' '-init' '-hidden' '/home/master/Dataset/ff/jgproject/.tmp/.initCmds.tcl' 'fpv.tcl'
analyze -clear
analyze -sv ./ff.sv
analyze -sv ./ff_sva.sv
analyze -sv ./ff_bind.svh

elaborate -top ff

clock clk
reset -expression rst
prove -all
report -summary -force -result -file ff.fpv.rpt
