module

public import Mathlib.Tactic

@[expose] public section

namespace HordijkSteelThreshold

/-- A cut in a finite graph with separately indexed edges, including parallel
edges. Its definition never identifies edges with equal endpoints. -/
def booleanEdgeCut {V E : Type*} (edges : Finset E) (a b : E → V)
    (label : V → Bool) : Finset E := edges.filter $ fun e => label (a e) ≠ label (b e)

end HordijkSteelThreshold
