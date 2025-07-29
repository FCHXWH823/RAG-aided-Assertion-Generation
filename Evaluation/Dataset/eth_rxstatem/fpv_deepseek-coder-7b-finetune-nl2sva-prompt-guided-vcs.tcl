analyze -clear
analyze -sv12 ./eth_rxstatem_deepseek-coder-7b-finetune-nl2sva-prompt-guided-vcs.sv

elaborate -top eth_rxstatem

clock MRxClk
reset Reset
prove -all
report -summary -force -result -file fpv_deepseek-coder-7b-finetune-nl2sva-prompt-guided-vcs.rpt
exit

