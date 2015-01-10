#!/bin/bash

mkdir -p data

for x in `seq 1 1`
do
echo nonrefl-skips$x...
(cd ../../../; coqc -noglob -R src "" -R bin ""  -R ../Charge "" -R ../coq-ext-lib/theories ExtLib -R ../mirror-core/theories MirrorCore -R ../Java "" -R ../mirror-core/src "" -R ../mirror-core/examples McExamples "src/MirrorCharge/Imp/NonRefl_NoMem_Skips.v" > src/MirrorCharge/Imp/data/nonrefl-skips$x.data)

echo nonrefl-assign$x...
(cd ../../../; coqc -noglob -R src "" -R bin ""  -R ../Charge "" -R ../coq-ext-lib/theories ExtLib -R ../mirror-core/theories MirrorCore -R ../Java "" -R ../mirror-core/src "" -R ../mirror-core/examples McExamples "src/MirrorCharge/Imp/NonRefl_NoMem_Assigns.v" > src/MirrorCharge/Imp/data/nonrefl-assign$x.data)

echo refl-skip$x...
(cd ../../../; coqc -noglob -R src "" -R bin ""  -R ../Charge "" -R ../coq-ext-lib/theories ExtLib -R ../mirror-core/theories MirrorCore -R ../Java "" -R ../mirror-core/src "" -R ../mirror-core/examples McExamples "src/MirrorCharge/Imp/Refl_NoMem_Skips.v" > src/MirrorCharge/Imp/data/refl-skips$x.data)

echo refl-assign$x...
(cd ../../../; coqc -noglob -R src "" -R bin ""  -R ../Charge "" -R ../coq-ext-lib/theories ExtLib -R ../mirror-core/theories MirrorCore -R ../Java "" -R ../mirror-core/src "" -R ../mirror-core/examples McExamples "src/MirrorCharge/Imp/Refl_NoMem_Assigns.v" > src/MirrorCharge/Imp/data/refl-assign$x.data)
done
