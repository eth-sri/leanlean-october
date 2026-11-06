import RequestProject.StrictTopLinkCoefficients
import RequestProject.PosetCoverLowerInterval
import RequestProject.OrderNerveRealizationPosetCover
import RequestProject.Tac
noncomputable section


/-! The actual upper link of a minimal vertex, including relative boundaries.

This is the bottom-vertex counterpart of `StrictTopLinkChains`.  In particular,
the two-chain need not be a cycle: its boundary only has to vanish on edges
starting at the selected vertex.
-/
bwd

namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P]

def StrictAbove (v : P) := {p : P // v < p}

instance (v : P) : PartialOrder (StrictAbove v) := Subtype.partialOrder _

def strictSourceRayEdge (v : P) (e : StrictOrdEdge P) :
    StrictAbove v →₀ ℤ := by
  classical
  exact if h : e.1.1 = v then Finsupp.single ⟨e.1.2, h ▸ e.2⟩ 1 else 0

def strictSourceRayChain (v : P) :
    (StrictOrdEdge P →₀ ℤ) →ₗ[ℤ] (StrictAbove v →₀ ℤ) :=
  Finsupp.linearCombination ℤ (strictSourceRayEdge v)

def strictBottomLinkTriangle (v : P) (t : StrictOrdTri P) :
    StrictOrdEdge (StrictAbove v) →₀ ℤ := by
  classical
  exact if h : t.1.1 = v then Finsupp.single
    ⟨(⟨t.1.2.1, h ▸ t.2.1⟩, ⟨t.1.2.2, h ▸ t.2.1.trans t.2.2⟩), t.2.2⟩ 1 else 0

def strictBottomLinkChain (v : P) :
    (StrictOrdTri P →₀ ℤ) →ₗ[ℤ] (StrictOrdEdge (StrictAbove v) →₀ ℤ) :=
  Finsupp.linearCombination ℤ (strictBottomLinkTriangle v)

def strictBottomConeTriangle (v : P) (e : StrictOrdEdge (StrictAbove v)) :
    StrictOrdTri P :=
  ⟨(v, e.1.1.val, e.1.2.val), e.1.1.property, e.2⟩

theorem strictBottomLinkChain_apply v (c : StrictOrdTri P →₀ ℤ)
    e :
    strictBottomLinkChain v c e = c (strictBottomConeTriangle v e) := by
  classical
  lin_ind c t n =>
    rcases t with ⟨⟨z, a, b⟩, hza, hab⟩
    rcases e with ⟨⟨⟨x, hx⟩, ⟨y, hy⟩⟩, hxy⟩
    by_cases ht : z = v
    · subst z
      simp [strictBottomLinkChain, strictBottomLinkTriangle, strictBottomConeTriangle,
        Finsupp.single_apply, StrictOrdTri, StrictOrdEdge, StrictAbove,
        Subtype.mk.injEq, Prod.mk.injEq]
    · simp [strictBottomLinkChain, strictBottomLinkTriangle, ht, strictBottomConeTriangle,
        StrictOrdTri, StrictOrdEdge, StrictAbove]

theorem strictSourceRayChain_apply v (c : StrictOrdEdge P →₀ ℤ)
    x :
    strictSourceRayChain v c x = c ⟨(v, x.val), x.property⟩ := by
  classical
  lin_ind c e n =>
    rcases e with ⟨⟨a, b⟩, hab⟩
    cases' x with x hx
    by_cases ha : a = v
    · subst a
      simp [strictSourceRayChain, strictSourceRayEdge, Finsupp.single_apply,
        StrictOrdEdge, StrictAbove, Subtype.mk.injEq, Prod.mk.injEq]
    · simp [strictSourceRayChain, strictSourceRayEdge, ha, StrictOrdEdge, StrictAbove]

/-- At a minimal vertex the extracted upper link has the negative source-ray
boundary.  This identity applies to every finite chain, including relative chains. -/
theorem strictBottomLink_boundary v (hm : ∀ p, p ≤ v → p = v)
    c :
    bdry1 (strictOrderCx (StrictAbove v)) (strictBottomLinkChain v c) =
      -strictSourceRayChain v (bdry2 (strictOrderCx P) c) := by
  classical
  lin_ind c with c d hc hd => simp only [map_add, hc, hd, neg_add]
  | t n =>
    have hmid : t.1.2.1 ≠ v := by
      intro he
      have ht := hm t.1.1 (he ▸ t.2.1.le)
      grind
    rwd [strictTriangle_bdry2_single, map_sub, map_add]
    by_cases ht : t.1.1 = v
    · simp [strictSourceRayChain, strictSourceRayEdge, strictBottomLinkChain,
        strictBottomLinkTriangle, strictTriangleEdge01, strictTriangleEdge12,
        strictTriangleEdge02, hmid, ht, bdry1, strictOrderCx, smul_sub,
        neg_sub]
    · simp [strictSourceRayChain, strictSourceRayEdge, strictBottomLinkChain,
        strictBottomLinkTriangle, strictTriangleEdge01, strictTriangleEdge12,
        strictTriangleEdge02, hmid, ht]

/-- Only source-edge boundary vanishing is used; no absolute cycle premise is
introduced when extracting the link of a relative two-chain. -/
theorem strictBottomLink_relative_cycle v (hm : ∀ p, p ≤ v → p = v)
    (c : StrictOrdTri P →₀ ℤ)
    (hc : ∀ e : StrictOrdEdge P, e.1.1 = v → bdry2 (strictOrderCx P) c e = 0) :
    bdry1 (strictOrderCx (StrictAbove v)) (strictBottomLinkChain v c) = 0 := by
  rwd [strictBottomLink_boundary v hm]
  have hz : strictSourceRayChain v (bdry2 (strictOrderCx P) c) = 0 := by
    ext x
    rwd [strictSourceRayChain_apply]
    tauto
  simp_all

namespace IsPosetCover
variable {Q : Type u} [PartialOrder Q] {f : P → Q} (hf : IsPosetCover f)

include hf in
theorem upperInterval_le_reflect {a b v : P} (ha : v ≤ a) (hb : v ≤ b)
    (h : f a ≤ f b) : a ≤ b := by
  obtain ⟨c, ⟨hac, hfc⟩, _⟩ := hf.up a _ h
  have hc := hf.up_inj (ha.trans hac) hb hfc
  simp_all

def upperIntervalLift (v : P) (q : StrictAbove (f v)) :
    StrictAbove v := by
  let a := Classical.choose (hf.up v q.1 q.2.le)
  have hs : v ≤ a ∧ f a = q.1 := by grind
  exact ⟨a, lt_of_le_of_ne hs.1 (by
    grind)⟩

theorem upperIntervalLift_projection v q :
    f (hf.upperIntervalLift v q).1 = q.1 :=
  (Classical.choose_spec (hf.up v q.1 q.2.le)).1.2

/-- An actual cover identifies each upper link with the actual upper link in
the base.  Distinct pole lifts are not identified by this construction. -/
def upperIntervalOrderIso (v : P) :
    StrictAbove v ≃o StrictAbove (f v) where
  toFun p := ⟨f p.1, hf.strictMono p.2⟩
  invFun := hf.upperIntervalLift v
  left_inv p := Subtype.ext (hf.up_inj (hf.upperIntervalLift v _).2.le p.2.le
    (hf.upperIntervalLift_projection v _))
  right_inv q := Subtype.ext (hf.upperIntervalLift_projection v q)
  map_rel_iff' {a b} := ⟨(upperInterval_le_reflect hf a.2.le b.2.le),
    fun h => hf.mono h⟩

end IsPosetCover

def strictAboveCongr {a b : P} (h : a = b) : StrictAbove a ≃o StrictAbove b := by
  cases h
  exact OrderIso.refl _

theorem strictAboveCongr_val {a b : P} (h : a = b) x :
    (strictAboveCongr h x).val = x.val := by
  cases h
  rfl
