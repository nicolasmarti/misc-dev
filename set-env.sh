#!/bin/bash
mydir=`pwd`
currdir=`dirname $0`
finaldir="$mydir/$currdir"

echo "finaldir = $finaldir"

export PATH="$finaldir/src/:$PATH"

export PATH="$finaldir/src/_build/app/:$PATH"

export PYTHONPATH="$finaldir/src/lib/python/gui/:$PYTHONPATH"
export PYTHONPATH="$finaldir/src/app/ib/lib/:$PYTHONPATH"
export PYTHONPATH="$finaldir/src/app/lib/:$PYTHONPATH"