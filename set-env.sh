#!/bin/bash
mydir=`pwd`
currdir=`dirname $0`
finaldir="$mydir/$currdir"

echo "finaldir = $finaldir"

export PATH="$finaldir/src/:$PATH"

export PATH="$finaldir/src/_build/lib/core/app/:$PATH"
export PATH="$finaldir/src/_build/lib/lisp/:$PATH"

export PYTHONPATH="$finaldir/src/app/lib/:$PYTHONPATH"
export PYTHONPATH="$finaldir/src/app/ib/lib/:$PYTHONPATH"