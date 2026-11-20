module

public import RequestProject.SurfaceCells
public import RequestProject.NerveDegree

@[expose] public section

/-! Explicit oriented chains of the polygon's triangulation, before identifying its sides. -/

namespace FiniteChains.Davis
open FreeAbelianGroup

variable {P : Type}

def flagEdge (a b e : P) := of [a, e] - of [b, e]

variable (a b c ab bc ca t : P)

def triangleFlagChain :=
  (of [a, ab, t] - of [b, ab, t]) +
  (of [b, bc, t] - of [c, bc, t]) +
  (of [c, ca, t] - of [a, ca, t])

theorem bdry_triangleFlagChain :
    Nerve.bdry (triangleFlagChain a b c ab bc ca t) =
      flagEdge a b ab + flagEdge b c bc + flagEdge c a ca := by
  simp only [triangleFlagChain, map_add, map_sub, Nerve.bdry_of,
    Nerve.bdryOn_cons, Nerve.bdryOn_nil, map_zero, sub_zero, Nerve.consMap_of]
  abel

section

variable [Preorder P]

theorem flagTriangle_mem_inc {a e t : P}
    (hae : a ≤ e) (het : e ≤ t) : of [a, e, t] ∈ Nerve.Inc P :=
  Nerve.of_mem_inc (by simp_all)

theorem triangleFlagChain_mem_inc {a b c ab bc ca t : P}
    (ha : a ≤ ab) (hb : b ≤ ab) (hb' : b ≤ bc) (hc : c ≤ bc)
    (hc' : c ≤ ca) (ha' : a ≤ ca) (hab : ab ≤ t) (hbc : bc ≤ t) (hca : ca ≤ t) :
    triangleFlagChain a b c ab bc ca t ∈ Nerve.Inc P := (Nerve.Inc P).add_mem
    ((Nerve.Inc P).add_mem
      ((Nerve.Inc P).sub_mem (flagTriangle_mem_inc ha hab) (flagTriangle_mem_inc hb hab))
      ((Nerve.Inc P).sub_mem (flagTriangle_mem_inc hb' hbc) (flagTriangle_mem_inc hc hbc)))
    ((Nerve.Inc P).sub_mem (flagTriangle_mem_inc hc' hca) (flagTriangle_mem_inc ha' hca))

end

variable {κ ι : Type} {M : ℕ} [NeZero M]
  {vc : Fin M → κ} {ec : Fin M → ι} (hc : Compat vc ec)

end FiniteChains.Davis
