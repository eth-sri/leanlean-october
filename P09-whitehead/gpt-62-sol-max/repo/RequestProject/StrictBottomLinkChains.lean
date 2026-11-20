module

public import RequestProject.StrictTopLinkCoefficients
public import RequestProject.PosetCoverLowerInterval
public import RequestProject.OrderNerveRealizationPosetCover

@[expose] public section

/-! The actual upper link of a minimal vertex, including relative boundaries.

This is the bottom-vertex counterpart of `StrictTopLinkChains`.  In particular,
the two-chain need not be a cycle: its boundary only has to vanish on edges
starting at the selected vertex.
-/
set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P]

def strictSourceRay (v : P) (x : StrictAbove v) : StrictOrdEdge P :=
  ⟨(v, x.val), x.property⟩

def strictBottomConeTriangle (v : P) (e : StrictOrdEdge (StrictAbove v)) : StrictOrdTri P :=
  ⟨(v, e.1.1.val, e.1.2.val), e.1.1.property, e.2⟩

noncomputable def strictSourceRayChain (v : P) :
    (StrictOrdEdge P →₀ ℤ) →ₗ[ℤ] (StrictAbove v →₀ ℤ) :=
  Finsupp.lcomapDomain (strictSourceRay v) (fun _ _ h => Subtype.ext (congrArg (·.1.2) h))

noncomputable def strictBottomLinkChain (v : P) :
    (StrictOrdTri P →₀ ℤ) →ₗ[ℤ] (StrictOrdEdge (StrictAbove v) →₀ ℤ) :=
  Finsupp.lcomapDomain (strictBottomConeTriangle v) (fun _ _ h => Subtype.ext (Prod.ext
    (Subtype.ext (congrArg (·.1.2.1) h)) (Subtype.ext (congrArg (·.1.2.2) h))))

theorem strictBottomLinkChain_apply (v : P) (c : StrictOrdTri P →₀ ℤ)
    (e : StrictOrdEdge (StrictAbove v)) :
    strictBottomLinkChain v c e = c (strictBottomConeTriangle v e) := rfl

/-- At a minimal vertex the extracted upper link has the negative source-ray
boundary. This identity also applies to relative chains. -/
theorem strictBottomLink_boundary (v : P) (hm : ∀ p, p ≤ v → p = v)
    (c : StrictOrdTri P →₀ ℤ) :
    bdry1 (strictOrderCx (StrictAbove v)) (strictBottomLinkChain v c) =
      -strictSourceRayChain v (bdry2 (strictOrderCx P) c) := by
  classical
  have hz (e : StrictOrdEdge P) (he : e.1.1 ≠ v) :
      strictSourceRayChain v (Finsupp.single e 1) = 0 :=
    Finsupp.comapDomain_single_of_not_mem_range (f := strictSourceRay v)
      (fun ⟨_, h⟩ => he (congrArg (·.1.1) h.symm)) _ _
  finsupp_basis c
  rintro ⟨⟨a, b, c⟩, hab, hbc⟩
  have hb : b ≠ v := fun h => hab.ne ((hm a (h ▸ hab.le)).trans h.symm)
  erw [strictTriangle_bdry2_single, map_sub, map_add, hz ⟨(b, c), hbc⟩ hb, add_zero]
  by_cases h : a = v
  · subst a
    let e : StrictOrdEdge (StrictAbove v) := ⟨(⟨b, hab⟩, ⟨c, hab.trans hbc⟩), hbc⟩
    change bdry1 (strictOrderCx (StrictAbove v)) (strictBottomLinkChain v (Finsupp.single (strictBottomConeTriangle v e) 1)) =
      -(strictSourceRayChain v (Finsupp.single (strictSourceRay v e.1.1) 1) -
      strictSourceRayChain v (Finsupp.single (strictSourceRay v e.1.2) 1))
    simp [strictSourceRayChain, strictBottomLinkChain, Finsupp.comapDomain_single, neg_sub]
    rw [bdry1_single, one_smul]
    rfl
  · erw [hz _ h, hz _ h, sub_zero, neg_zero]
    have hs : strictBottomLinkChain v (Finsupp.single ⟨(a, b, c), hab, hbc⟩ 1) = 0 :=
      Finsupp.comapDomain_single_of_not_mem_range (f := strictBottomConeTriangle v)
        (fun ⟨_, he⟩ => h (congrArg (·.1.1) he.symm)) _ _
    erw [hs, map_zero]

/-- Only source-edge boundary vanishing is used; no absolute cycle premise is
introduced when extracting the link of a relative two-chain. -/
theorem strictBottomLink_relative_cycle (v : P) (hm : ∀ p, p ≤ v → p = v)
    (c : StrictOrdTri P →₀ ℤ)
    (hc : ∀ e : StrictOrdEdge P, e.1.1 = v → bdry2 (strictOrderCx P) c e = 0) :
    bdry1 (strictOrderCx (StrictAbove v)) (strictBottomLinkChain v c) = 0 := by
  erw [strictBottomLink_boundary v hm]
  have hz : strictSourceRayChain v (bdry2 (strictOrderCx P) c) = 0 := by
    ext x
    exact hc (strictSourceRay v x) rfl
  erw [hz, neg_zero]

def strictAboveCongr {a b : P} (h : a = b) : StrictAbove a ≃o StrictAbove b := by
  cases h
  exact OrderIso.refl _

theorem strictAboveCongr_val {a b : P} (h : a = b) (x : StrictAbove a) :
    (strictAboveCongr h x).val = x.val := by
  cases h
  rfl

end FiniteChains.Comb
