import RequestProject.SurfaceCells
import RequestProject.NerveDegree
import RequestProject.Tac


/-! Explicit oriented chains of the polygon's triangulation, before identifying its sides. -/

bwd

namespace FiniteChains.Davis
open FreeAbelianGroup

def flagEdge {P : Type} (a b e : P) : Nerve.Ch P := of [a, e] - of [b, e]

def triangleFlagChain {P : Type} (a b c ab bc ca t : P) : Nerve.Ch P :=
  (of [a, ab, t] - of [b, ab, t]) +
  (of [b, bc, t] - of [c, bc, t]) +
  (of [c, ca, t] - of [a, ca, t])

theorem bdry_triangleFlagChain (a b c ab bc ca t : P) :
    Nerve.bdry (triangleFlagChain a b c ab bc ca t) =
      flagEdge a b ab + flagEdge b c bc + flagEdge c a ca := by
  simp [triangleFlagChain, map_add, map_sub, Nerve.bdry_of,
    Nerve.bdryOn_cons, Nerve.bdryOn_nil, map_zero, sub_zero, Nerve.consMap_of]
  unfold flagEdge
  abel

theorem flagTriangle_mem_inc {P : Type} [Preorder P] {a e t}
    (hae : a ≤ e) (het : e ≤ t) : of [a, e, t] ∈ Nerve.Inc P :=
  Nerve.of_mem_inc (by simp_all)

theorem triangleFlagChain_mem_inc {P} [Preorder P] {a b c ab bc ca t}
    (ha : a ≤ ab) (hb : b ≤ ab) (hb' : b ≤ bc) (hc : c ≤ bc)
    (hc' : c ≤ ca) (ha' : a ≤ ca) (hab : ab ≤ t) (hbc : bc ≤ t) (hca : ca ≤ t) :
    triangleFlagChain a b c ab bc ca t ∈ Nerve.Inc P := (Nerve.Inc P).add_mem
    ((Nerve.Inc P).add_mem
      ((Nerve.Inc P).sub_mem (flagTriangle_mem_inc ha hab) (flagTriangle_mem_inc hb hab))
      ((Nerve.Inc P).sub_mem (flagTriangle_mem_inc hb' hbc) (flagTriangle_mem_inc hc hbc)))
    ((Nerve.Inc P).sub_mem (flagTriangle_mem_inc hc' hca) (flagTriangle_mem_inc ha' hca))

variable {κ ι : Type} {M : ℕ} [NeZero M]
  {vc : Fin M → κ} {ec : Fin M → ι} (hc : Compat vc ec)
