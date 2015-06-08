#! /bin/bash
# files=( "2bitcomp_5.cnf" "C215_FC.cnf" "par16-1-c.cnf" "qg7-09.cnf" "2bitmax_6.cnf"
# "C230_FR.cnf" "par16-2-c.cnf" "ra.cnf" "4blocksb.cnf"    "C250_FW.cnf" 
# "par16-2.cnf" "ssa7552-038.cnf" "ais10.cnf" "C638_FKA.cnf"  "par16-3.cnf"
# "tire-2.cnf" "bw_large.a.cnf" "C638_FVK.cnf" "par16-5-c.cnf" "tire-3.cnf" 
# "bw_large.b.cnf" "cnt06.shuffled.cnf"  "par16-5.cnf" "tire-4.cnf" "C163_FW.cnf"
# "huge.cnf" "prob004-log-a.cnf" "uf250-017.cnf" "C169_FW.cnf"    "log-1.cnf")
# "qg1-07.cnf" "uf250-026.cnf" "C171_FR.cnf"   "log-2.cnf" "qg2-07.cnf"
files=("C210_FVF.cnf" "log-3.cnf" "qg3-08.cnf" "C211_FS.cnf" "medium.cnf" "qg6-09.cnf")

for i in "${files[@]}"
do
	echo "Test $i" >> "$i.result"&&
	./c2Dgiven -c $i -W  >> "$i.result" &&
	echo "==============================="  >> "$i.result" &&
	./c2D -c $i -W >> "$i.result"
done
