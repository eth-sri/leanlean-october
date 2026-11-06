import RequestProject.BlockCockcroft


/-!
# A wedge of Cockcroft complexes is Cockcroft

Lemma 3.10 finishes with: "A wedge of Cockcroft complexes is Cockcroft: its `H₂` is the
direct sum of those of the factors, and the factor retractions detect every coordinate of a
Hurewicz image."

In the combinatorial model the wedge of the presentation complexes of `⟨x_i | r_j⟩` and
`⟨y_a | s_k⟩` is the presentation complex of the disjoint union of the generators and of the
relators.  Each factor is a retract block of the wedge in the sense of
`RequestProject/BlockCockcroft.lean` — the retraction kills the generators of the other
factor — so every coordinate of a Fox cycle of the wedge has zero augmentation:

`FiniteChains.isCockcroft_wedgeRel`.
-/
