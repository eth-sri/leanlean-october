import RequestProject.AttCycle


/-!
# The concrete attaching map and the loop along which it spells the prescribed word

`RequestProject/AttCycle.lean` produced the labelled cycle.  This file turns it into the actual
attaching map

    `attCyc : NeSpx (cycA l hl) →o PresPos w`

of the chamber construction, and produces the **geometric loop of the cut surface**: the edge
path `sigLoop` which goes once around the cycle, based at the vertex `0`.  The computation
`mapPath_sigLoop_full` says that the image of that loop under the attaching map is *literally*
the loop `wordLoop w l` of the presentation complex which spells the word `l`.  This is the
reading hypothesis `hread` of `FiniteChains.Davis.injective_substHomF_of_spine`, on the nose.
-/
