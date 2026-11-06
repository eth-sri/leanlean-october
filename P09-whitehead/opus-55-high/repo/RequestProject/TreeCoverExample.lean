import RequestProject.TreeCoverTheoremA


/-!
# Non-vacuity of the tree-collapse form of Theorem A

The statement `FiniteChains.Comb.SpanningTree.hasAcyclicRegularCover_of_topChains` is applied
here to a complex whose spanning tree is not trivial: the *interval*, two vertices joined by an
edge.  Its spanning tree consists of that edge, so the collapse is the empty presentation, the
chains of condition (1) exist in every length (take all of them empty), and the theorem yields
a connected acyclic regular cover of the interval.
-/
