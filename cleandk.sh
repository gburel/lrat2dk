#!/bin/sh
final=`dirname $1`/`basename $1 .dk`_cleaned.dk
temp=`tempfile`
if ./cleandk $1 > $final
then
    echo -n "."
    while ./cleandk $final > $temp
    do
	echo -n "."
	mv $temp $final
    done
    rm $temp
else
    cp $1 $final
fi
