#!/bin/sh

for i in examples/*.lrat
do
    base=`basename $i .lrat`
    if ./lrat2dk.opt examples/$base.cnf $i
    then
	echo "$i succeeded"
	mv dedukti_out.dk examples/$base.dk
    else
	echo "$i failed"
    fi
done
