#!/bin/sh

./holtcp.d > dtrace.out

cat dtrace.out | \
    sed -e 's/IP \([0-9]*\)\.\([0-9]*\)\.\([0-9]*\)\.\([0-9]*\)/IP \1 \2 \3 \4/g' \
    -e 's/SOME(IP 0 0 0 0)/NONE/g' \
    -e 's/SOME(Port 0)/NONE/g' \
    -e 's/SOME(-42, 0)/NONE/g' \
    -e 's/t_rttseg := SOME(ts_seq(n2w 0).*/t_rttseg := NONE;/g' \
    -e 's/ts_recent := TimeWindow(ts_seq(n2w 0).*/ts_recent := TimeWindowClosed;/g' >> trace.out

rm dtrace.out

./hextotrace.native trace.out
mv trace.out.tmp trace.out
