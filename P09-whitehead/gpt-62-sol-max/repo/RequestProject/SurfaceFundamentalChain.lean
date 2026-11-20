module

public import RequestProject.SurfaceCells

@[expose] public section

/-! Explicit oriented chains of the polygon's triangulation, before identifying its sides. -/


namespace FiniteChains.Davis
open Comb
universe u
variable {P : Type u} [Preorder P]

noncomputable def flagEdge {a b e : P} (ha : a ≤ e) (hb : b ≤ e) : OrdEdge P →₀ ℤ :=
  Finsupp.single ⟨(a, e), ha⟩ 1 - Finsupp.single ⟨(b, e), hb⟩ 1

noncomputable def triangleFlagChain {a b c ab bc ca t : P}
    (ha : a ≤ ab) (hb : b ≤ ab) (hb' : b ≤ bc) (hc : c ≤ bc)
    (hc' : c ≤ ca) (ha' : a ≤ ca) (hab : ab ≤ t) (hbc : bc ≤ t) (hca : ca ≤ t) : OrdTri P →₀ ℤ :=
  (Finsupp.single ⟨(a, ab, t), ha, hab⟩ 1 - Finsupp.single ⟨(b, ab, t), hb, hab⟩ 1) +
  (Finsupp.single ⟨(b, bc, t), hb', hbc⟩ 1 - Finsupp.single ⟨(c, bc, t), hc, hbc⟩ 1) +
  (Finsupp.single ⟨(c, ca, t), hc', hca⟩ 1 - Finsupp.single ⟨(a, ca, t), ha', hca⟩ 1)

set_option backward.isDefEq.respectTransparency false in
theorem bdry_triangleFlagChain {a b c ab bc ca t : P}
    (ha : a ≤ ab) (hb : b ≤ ab) (hb' : b ≤ bc) (hc : c ≤ bc)
    (hc' : c ≤ ca) (ha' : a ≤ ca) (hab : ab ≤ t) (hbc : bc ≤ t) (hca : ca ≤ t) :
    Comb.bdry2 (orderCx P) (triangleFlagChain ha hb hb' hc hc' ha' hab hbc hca) =
      flagEdge ha hb + flagEdge hb' hc + flagEdge hc' ha' := by
  unfold triangleFlagChain flagEdge
  erw [map_add, map_add, map_sub, map_sub, map_sub]
  repeat erw [Comb.bdry2_single]
  simp [orderCx, pathChain] <;> abel

end FiniteChains.Davis
