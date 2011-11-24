#!/bin/bash
mydir=`pwd`
currdir=`dirname $0`
finaldir="$mydir/$currdir"

echo "finaldir = $finaldir"

export PATH="$finaldir/src/:$PATH"
export PYTHONPATH="$finaldir/src/pylib/:$PYTHONPATH"
export PYTHONPATH="$finaldir/src/ib/lib/:$PYTHONPATH"