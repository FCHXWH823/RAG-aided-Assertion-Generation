analyze -clear
analyze -sv12 ./apb_deepseek-coder-7b-finetune-nl2sva-prompt-guided-vcs.sv

elaborate -top apb

clock PCLK
reset PRESETn
prove -all
report -summary -force -result -file fpv_deepseek-coder-7b-finetune-nl2sva-prompt-guided-vcs.rpt
exit

