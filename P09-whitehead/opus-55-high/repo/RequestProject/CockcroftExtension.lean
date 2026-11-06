import RequestProject.Cockcroft
import RequestProject.Pi2Dictionary
import RequestProject.Tac


/-!
# Cockcroft complexes and two-dimensional extensions killing `π₂`

The introduction of the paper records the following characterization: a connected
two-complex `K` admits at least one two-dimensional extension inducing zero on `π₂` if and
only if `K` is Cockcroft.  The argument given there is:

* for an inclusion `i : K ⊂ L` of two-complexes the map `H₂(i)` is injective, since there
  are no three-cells; hence `π₂(i) = 0` forces the Hurewicz map of `K` to vanish;
* conversely, attaching disks along a generating set of `π₁(K)` produces a simply connected
  `L`, and the inclusion is then zero on `π₂`.

This file proves both halves in the combinatorial model of the project, for a complex of a
finite presentation: `π₂` is the module of Fox cycles, the Hurewicz map is the augmentation
(see `RequestProject/Cockcroft.lean`), and an extension is a presentation containing the
generators and the two-cells of `K`, with the old cells attached along the old words.

The result is `FiniteChains.isCockcroft_iff_nonempty_zeroPi2Ext`: the presentation complex
of `ρ` is Cockcroft if and only if it admits a two-dimensional extension which is zero on
`π₂`.  The extension produced in the proof is the one from the paper: adjoin one disk along
each generator.
-/

bwd
