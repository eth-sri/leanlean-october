import RequestProject.PosetCoverComparableLifts
import RequestProject.OrderComparableCycleHomotopy
import RequestProject.OrderComparableOneHomotopy
import RequestProject.Tac


/-! Actual cycle fillings in every cover of a poset with a three-leg contraction. -/
bwd

namespace FiniteChains.Comb
universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q] {f : P → Q}

theorem exists_cover_zigzag_contraction (hf : IsPosetCover f)
    l r (hl : Monotone l) (hr : Monotone r)
    (hir : ∀ x, x ≤ r x) (hlr : ∀ x, l x ≤ r x) (b : Q) (hlb : ∀ x, l x ≤ b) :
    ∃ L R E : P → P, Monotone L ∧ Monotone R ∧ Monotone E ∧
      (∀ x, x ≤ R x) ∧ (∀ x, L x ≤ R x) ∧ (∀ x, L x ≤ E x) ∧
      (∀ {x y}, x ≤ y → E x = E y) := by
  let R := hf.upTransform r hir
  have hR := hf.upTransform_monotone r hr hir
  have hlR : ∀ x, l (f x) ≤ f (R x) := by
    intro x
    rw [(hf.upTransform_spec r hir x).2]
    simp_all
  let L := hf.lowerMapLift R _ hlR
  have hL := hf.lowerMapLift_monotone R _ hR (hl.comp hf.mono) hlR
  have hLb : ∀ x, f (L x) ≤ b := by
    intro x
    rw [(hf.lowerMapLift_spec R _ hlR x).2]
    simp_all
  let E := hf.upperMapLift L _ hLb
  refine ⟨L, R, E, hL, hR,
    hf.upperMapLift_monotone L _ hL (by tauto) hLb,
    hf.le_upTransform r hir, ?_, ?_, ?_⟩
  · intro x
    exact (hf.lowerMapLift_spec R _ hlR x).1
  · intro x
    exact (hf.upperMapLift_spec L _ hLb x).1
  · intro x y hxy
    exact hf.upperMapLift_constant_comparable L hL b hLb hxy

theorem strict_oneCycle_cover_zigzag (hf : IsPosetCover f)
    l r (hl : Monotone l) (hr : Monotone r)
    (hir : ∀ x, x ≤ r x) (hlr : ∀ x, l x ≤ r x) (b : Q) (hlb : ∀ x, l x ≤ b)
    (c : StrictOrdEdge P →₀ ℤ) (hc : bdry1 (strictOrderCx P) c = 0) :
    ∃ d : StrictOrdTri P →₀ ℤ, bdry2 (strictOrderCx P) d = c := by
  obtain ⟨L, R, E, hL, hR, hE, hiR, hLR, hLE, hconst⟩ :=
    exists_cover_zigzag_contraction hf l r hl hr hir hlr b hlb
  cases' strict_oneCycle_comparable_boundary id R monotone_id hR hiR c hc with y hy
  cases' strict_oneCycle_comparable_boundary L R hL hR hLR c hc with z hz
  cases' strict_oneCycle_comparable_boundary L E hL hE hLE c hc with w hw
  refine ⟨z - y - w, ?_⟩
  simp [map_sub, hz, hy, hw, normalizedStrictChain1_id, normalizedStrictChain1_zero_of_comparable_equal E hE hconst]

theorem strict_twoCycle_cover_zigzag (hf : IsPosetCover f)
    l r (hl : Monotone l) (hr : Monotone r)
    (hir : ∀ x, x ≤ r x) (hlr : ∀ x, l x ≤ r x) (b : Q) (hlb : ∀ x, l x ≤ b)
    (c : StrictOrdTri P →₀ ℤ) (hc : bdry2 (strictOrderCx P) c = 0) :
    ∃ d, strictOrdBoundary3 d = c := by
  obtain ⟨L, R, E, hL, hR, hE, hiR, hLR, hLE, hconst⟩ :=
    exists_cover_zigzag_contraction hf l r hl hr hir hlr b hlb
  cases' strict_cycle_comparable_boundary id R monotone_id hR hiR c hc with y hy
  cases' strict_cycle_comparable_boundary L R hL hR hLR c hc with z hz
  cases' strict_cycle_comparable_boundary L E hL hE hLE c hc with w hw
  refine ⟨z - y - w, ?_⟩
  simp [map_sub, hz, hy, hw, normalizedStrictChain2_id, normalizedStrictChain2_zero_of_comparable_equal E hE hconst]
