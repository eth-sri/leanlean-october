import Mathlib.Tactic

import RequestProject.SurfaceCells
import RequestProject.NerveDegree

/-! Explicit oriented chains of the polygon's triangulation, before identifying its sides. -/

set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis
open FreeAbelianGroup

variable {P : Type}
def flagEdge  (a b e : P)  := of [a, e] - of [b, e]

variable (a b c ab bc ca t : P)
def triangleFlagChain    :=
  (of [a, ab, t] - of [b, ab, t]) +
  (of [b, bc, t] - of [c, bc, t]) +
  (of [c, ca, t] - of [a, ca, t])

theorem bdry_triangleFlagChain   :
    Nerve.bdry (triangleFlagChain a b c ab bc ca t) =
      flagEdge a b ab + flagEdge b c bc + flagEdge c a ca := by
  simp only [triangleFlagChain, map_add, map_sub, Nerve.bdry_of,
    Nerve.bdryOn_cons, Nerve.bdryOn_nil, map_zero, sub_zero, Nerve.consMap_of]
  unfold flagEdge
  abel

theorem flagTriangle_mem_inc  [Preorder P] {a e t : P}
    (hae : a ≤ e) (het : e ≤ t) : of [a, e, t] ∈ Nerve.Inc P :=
  Nerve.of_mem_inc (by simp [*])

abbrev triangleFlagChain_mem_inc  [Preorder P] {a b c ab bc ca t : P}
    (ha : a ≤ ab) (hb : b ≤ ab) (hb' : b ≤ bc) (hc : c ≤ bc)
    (hc' : c ≤ ca) (ha' : a ≤ ca) (hab : ab ≤ t) (hbc : bc ≤ t) (hca : ca ≤ t)  :=
  AddSubgroup.add_mem (FiniteChains.Nerve.Inc P)
    (AddSubgroup.add_mem (FiniteChains.Nerve.Inc P)
      (AddSubgroup.sub_mem (FiniteChains.Nerve.Inc P) (FiniteChains.Davis.flagTriangle_mem_inc ha hab)
        (FiniteChains.Davis.flagTriangle_mem_inc hb hab))
      (AddSubgroup.sub_mem (FiniteChains.Nerve.Inc P) (FiniteChains.Davis.flagTriangle_mem_inc hb' hbc)
        (FiniteChains.Davis.flagTriangle_mem_inc hc hbc)))
    (AddSubgroup.sub_mem (FiniteChains.Nerve.Inc P) (FiniteChains.Davis.flagTriangle_mem_inc hc' hca)
      (FiniteChains.Davis.flagTriangle_mem_inc ha' hca))



end FiniteChains.Davis
