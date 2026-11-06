import Mathlib.Tactic

import RequestProject.StrictTopLinkCoefficients
import RequestProject.PosetCoverLowerInterval
import RequestProject.OrderNerveRealizationPosetCover

/-! The actual upper link of a minimal vertex, including relative boundaries.

This is the bottom-vertex counterpart of `StrictTopLinkChains`.  In particular,
the two-chain need not be a cycle: its boundary only has to vanish on edges
starting at the selected vertex.
-/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
variable {P : Type u} [PartialOrder P]

  (v : P)
def StrictAbove  := {p : P // v < p}

instance (v : P) : PartialOrder (StrictAbove v) := Subtype.partialOrder _

noncomputable def strictSourceRayEdge  (e : StrictOrdEdge P) :
    StrictAbove v →₀ ℤ := by
  classical
  exact if h : e.1.1 = v then Finsupp.single ⟨e.1.2, h ▸ e.2⟩ 1 else 0

noncomputable def strictSourceRayChain   :=
  Finsupp.linearCombination ℤ (strictSourceRayEdge v)

noncomputable def strictBottomLinkTriangle  (t : StrictOrdTri P) :
    StrictOrdEdge (StrictAbove v) →₀ ℤ := by
  classical
  exact if h : t.1.1 = v then Finsupp.single
    ⟨(⟨t.1.2.1, h ▸ t.2.1⟩, ⟨t.1.2.2, h ▸ t.2.1.trans t.2.2⟩), t.2.2⟩ 1 else 0

noncomputable def strictBottomLinkChain   :=
  Finsupp.linearCombination ℤ (strictBottomLinkTriangle v)

def strictBottomConeTriangle  (e : StrictOrdEdge (StrictAbove v)) :
    StrictOrdTri P :=
  ⟨(v, e.1.1.val, e.1.2.val), e.1.1.property, e.2⟩

theorem strictBottomLinkChain_apply  (c : StrictOrdTri P →₀ ℤ)
    (e : StrictOrdEdge (StrictAbove v)) :
    strictBottomLinkChain v c e = c (strictBottomConeTriangle v e) := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp_all
  | single t n =>
    rcases t with ⟨⟨z, a, b⟩, hza, hab⟩
    rcases e with ⟨⟨⟨x, hx⟩, ⟨y, hy⟩⟩, hxy⟩
    by_cases ht : z = v
    · simp_all [strictBottomLinkChain, strictBottomLinkTriangle, strictBottomConeTriangle, Finsupp.single_apply, StrictOrdTri, StrictOrdEdge, StrictAbove]
    · simp [strictBottomLinkChain, strictBottomLinkTriangle, ht, strictBottomConeTriangle,
        StrictOrdTri, StrictOrdEdge, StrictAbove]

theorem strictSourceRayChain_apply  (c : StrictOrdEdge P →₀ ℤ)
    (x : StrictAbove v) :
    strictSourceRayChain v c x = c ⟨(v, x.val), x.property⟩ := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp_all
  | single e n =>
    rcases e with ⟨⟨a, b⟩, hab⟩
    aesop (add simp [strictSourceRayChain, strictSourceRayEdge, Finsupp.single_apply, StrictOrdEdge])

variable (hm : ∀ p, p ≤ v → p = v)
include hm in
/-- At a minimal vertex the extracted upper link has the negative source-ray
boundary.  This identity applies to every finite chain, including relative chains. -/
theorem strictBottomLink_boundary  
    (c : StrictOrdTri P →₀ ℤ) :
    bdry1 (strictOrderCx (StrictAbove v)) (strictBottomLinkChain v c) =
      -strictSourceRayChain v (bdry2 (strictOrderCx P) c) := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd, neg_add]
  | single t n =>
    have hmid : t.1.2.1 ≠ v := by
      intro he
      have ht := hm t.1.1 (he ▸ t.2.1.le)
      exact (ne_of_lt t.2.1) (ht.trans he.symm)
    rw  [strictTriangle_bdry2_single, map_sub, map_add]
    by_cases ht : t.1.1 = v
    · simp [strictSourceRayChain, strictSourceRayEdge, strictBottomLinkChain,
        strictBottomLinkTriangle, strictTriangleEdge01, strictTriangleEdge12,
        strictTriangleEdge02, hmid, ht, bdry1, strictOrderCx, smul_sub,
        neg_sub]
    simp_all [strictSourceRayChain, strictSourceRayEdge, strictBottomLinkChain, strictBottomLinkTriangle, strictTriangleEdge01, strictTriangleEdge12, strictTriangleEdge02]

include hm in
/-- Only source-edge boundary vanishing is used; no absolute cycle premise is
introduced when extracting the link of a relative two-chain. -/
theorem strictBottomLink_relative_cycle  
    (c : StrictOrdTri P →₀ ℤ)
    (hc : ∀ e : StrictOrdEdge P, e.1.1 = v → bdry2 (strictOrderCx P) c e = 0) :
    bdry1 (strictOrderCx (StrictAbove v)) (strictBottomLinkChain v c) = 0 := by
  rw  [strictBottomLink_boundary v hm]
  have hz : strictSourceRayChain v (bdry2 (strictOrderCx P) c) = 0 := by
    aesop (add simp [strictSourceRayChain_apply])
  rw  [hz, neg_zero]

namespace IsPosetCover
variable {Q : Type u} [PartialOrder Q] {f : P → Q} (hf : IsPosetCover f)

include hf in
theorem upperInterval_le_reflect {a b v : P} (ha : v ≤ a) (hb : v ≤ b)
    (h : f a ≤ f b) : a ≤ b := by
  obtain ⟨c, ⟨hac, hfc⟩, _⟩ := hf.up a (f b) h
  have hc  := hf.up_inj (ha.trans hac) hb hfc
  exact hc ▸ hac

variable (v : P)
variable (q : StrictAbove (f v))
include q in
noncomputable def upperIntervalLift   :
    StrictAbove v := by
  let a := Classical.choose (hf.up v q.1 q.2.le)
  have hs  := (Classical.choose_spec (hf.up v q.1 q.2.le)).1
  exact ⟨a, lt_of_le_of_ne hs.1 (by
    grind)⟩

include q in
abbrev upperIntervalLift_projection    :=
  (Classical.choose_spec (hf.up v q.1 q.2.le)).1.2

/-- An actual cover identifies each upper link with the actual upper link in
the base.  Distinct pole lifts are not identified by this construction. -/
noncomputable def upperIntervalOrderIso  :
    StrictAbove v ≃o StrictAbove (f v) where
  toFun p := ⟨f p.1, hf.strictMono p.2⟩
  invFun := hf.upperIntervalLift v
  left_inv p := Subtype.ext (hf.up_inj (hf.upperIntervalLift v _).2.le p.2.le
    (hf.upperIntervalLift_projection v _))
  right_inv q := Subtype.ext (hf.upperIntervalLift_projection v q)
  map_rel_iff' {a b} := ⟨fun h => upperInterval_le_reflect hf a.2.le b.2.le h,
    fun h => hf.mono h⟩

end IsPosetCover

def strictAboveCongr {a b : P} (h : a = b) : StrictAbove a ≃o StrictAbove b := by
  cases h
  exact OrderIso.refl _

theorem strictAboveCongr_val {a b : P} (h : a = b) (x : StrictAbove a) :
    (strictAboveCongr h x).val = x.val := by
  cases h
  rfl

end FiniteChains.Comb
