import Mathlib.Tactic

import RequestProject.PosetCoverComparableLifts
import RequestProject.OrderComparableCycleHomotopy
import RequestProject.OrderComparableOneHomotopy

/-! Actual cycle fillings in every cover of a poset with a three-leg contraction. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q] {f : P → Q}

  (hf : IsPosetCover f)
  (l r : Q → Q)
include hf in
theorem exists_cover_zigzag_contraction 
     (hl : Monotone l) (hr : Monotone r)
    (hir : ∀ x, x ≤ r x) (hlr : ∀ x, l x ≤ r x) (b : Q) (hlb : ∀ x, l x ≤ b) :
    ∃ L R E : P → P, Monotone L ∧ Monotone R ∧ Monotone E ∧
      (∀ x, x ≤ R x) ∧ (∀ x, L x ≤ R x) ∧ (∀ x, L x ≤ E x) ∧
      (∀ {x y}, x ≤ y → E x = E y) := by
  let R := hf.upTransform r hir
  have hR  := hf.upTransform_monotone r hr hir
  have hlR : ∀ x, l (f x) ≤ f (R x) := by
    classical aesop (add simp [FiniteChains.Comb.IsPosetCover.upTransform_spec])
  let L := hf.lowerMapLift R (l ∘ f) hlR
  have hL  := hf.lowerMapLift_monotone R (l ∘ f) hR (hl.comp hf.mono) hlR
  have hLb : ∀ x, f (L x) ≤ b := by
    classical aesop (add simp [FiniteChains.Comb.IsPosetCover.lowerMapLift_spec])
  let E := hf.upperMapLift L (fun _ => b) hLb
  refine ⟨L, R, E, hL, hR,
    hf.upperMapLift_monotone L (fun _ => b) hL (fun _ _ _ => le_refl _) hLb,
    hf.le_upTransform r hir, ?_, ?_, ?_⟩
  · classical aesop (add simp [FiniteChains.Comb.IsPosetCover.lowerMapLift_spec])
  · classical aesop (add simp [FiniteChains.Comb.IsPosetCover.upperMapLift_spec])
  · intro x y hxy
    exact hf.upperMapLift_constant_comparable L hL b hLb hxy

include hf in
theorem strict_oneCycle_cover_zigzag 
     (hl : Monotone l) (hr : Monotone r)
    (hir : ∀ x, x ≤ r x) (hlr : ∀ x, l x ≤ r x) (b : Q) (hlb : ∀ x, l x ≤ b)
    (c : StrictOrdEdge P →₀ ℤ) (hc : bdry1 (strictOrderCx P) c = 0) :
    ∃ d : StrictOrdTri P →₀ ℤ, bdry2 (strictOrderCx P) d = c := by
  obtain ⟨L, R, E, hL, hR, hE, hiR, hLR, hLE, hconst⟩ :=
    exists_cover_zigzag_contraction hf l r hl hr hir hlr b hlb
  obtain ⟨y, hy⟩ := strict_oneCycle_comparable_boundary id R monotone_id hR hiR c hc
  obtain ⟨z, hz⟩ := strict_oneCycle_comparable_boundary L R hL hR hLR c hc
  obtain ⟨w, hw⟩ := strict_oneCycle_comparable_boundary L E hL hE hLE c hc
  refine ⟨z - y - w, ?_⟩
  rw [map_sub, map_sub, hz, hy, hw, normalizedStrictChain1_id,
    normalizedStrictChain1_zero_of_comparable_equal E hE hconst]
  abel_nf
  simp

include hf in
theorem strict_twoCycle_cover_zigzag 
     (hl : Monotone l) (hr : Monotone r)
    (hir : ∀ x, x ≤ r x) (hlr : ∀ x, l x ≤ r x) (b : Q) (hlb : ∀ x, l x ≤ b)
    (c : StrictOrdTri P →₀ ℤ) (hc : bdry2 (strictOrderCx P) c = 0) :
    ∃ d : StrictOrdTet P →₀ ℤ, strictOrdBoundary3 d = c := by
  obtain ⟨L, R, E, hL, hR, hE, hiR, hLR, hLE, hconst⟩ :=
    exists_cover_zigzag_contraction hf l r hl hr hir hlr b hlb
  obtain ⟨y, hy⟩ := strict_cycle_comparable_boundary id R monotone_id hR hiR c hc
  obtain ⟨z, hz⟩ := strict_cycle_comparable_boundary L R hL hR hLR c hc
  obtain ⟨w, hw⟩ := strict_cycle_comparable_boundary L E hL hE hLE c hc
  refine ⟨z - y - w, ?_⟩
  rw [map_sub, map_sub, hz, hy, hw, normalizedStrictChain2_id,
    normalizedStrictChain2_zero_of_comparable_equal E hE hconst]
  abel

end FiniteChains.Comb
