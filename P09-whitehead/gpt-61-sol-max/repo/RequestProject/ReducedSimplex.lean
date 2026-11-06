import Mathlib.Tactic

import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Convex.GaugeRescale

namespace FiniteChains

variable (n : ℕ)
/-- The standard simplex in its actual dimension, obtained by omitting the first barycentric coordinate. -/
def reducedSimplex  : Set (Fin n → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1}

/-- Reinsert the first barycentric coordinate into reduced simplex coordinates. -/
def reducedSimplexToStandard  (x : reducedSimplex n) :
    stdSimplex ℝ (Fin (n + 1)) :=
  ⟨Fin.cons (1 - ∑ i, x.val i) x.val,
    (by
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using sub_nonneg.mpr x.property.2
      · simpa using x.property.1 j),
    (by simp [Fin.sum_univ_succ])⟩

/-- Omit the first barycentric coordinate. -/
def standardSimplexToReduced  (z : stdSimplex ℝ (Fin (n + 1))) :
    reducedSimplex n :=
  ⟨fun i => z.val i.succ, (fun i => z.property.1 i.succ), by
    have hs := z.property.2
    rw [Fin.sum_univ_succ] at hs
    have h0 := z.property.1 0
    
    linarith⟩

/-- The actual standard simplex is homeomorphic to the reduced-coordinate simplex. -/
def reducedSimplexHomeomorph  :
    reducedSimplex n ≃ₜ stdSimplex ℝ (Fin (n + 1)) where
  toFun := reducedSimplexToStandard n
  invFun := standardSimplexToReduced n
  left_inv x := rfl
  right_inv z := by
    apply Subtype.ext
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · have hs := z.property.2
      rw [Fin.sum_univ_succ] at hs
      change 1 - ∑ j : Fin n, z.val j.succ = z.val 0
      linarith
    · rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · fun_prop
    · fun_prop
  continuous_invFun := Continuous.subtype_mk (continuous_pi (fun i =>
      (continuous_apply i.succ).comp continuous_subtype_val)) _

/-- The reduced simplex is closed in its ambient finite-dimensional space. -/
theorem reducedSimplex_isClosed  : IsClosed (reducedSimplex n) := by
  change IsClosed ({x : Fin n → ℝ | ∀ i, 0 ≤ x i} ∩ {x | ∑ i, x i ≤ 1})
  apply IsClosed.inter
  · simp_all [Set.setOf_forall, isClosed_iInter, isClosed_le, continuous_const, continuous_apply]
  · simp_all [isClosed_le, continuous_finset_sum, continuous_apply, continuous_const]

/-- The reduced simplex is convex. -/
theorem reducedSimplex_convex  : Convex ℝ (reducedSimplex n) := by
  intro x hx y hy a b ha hb hab
  constructor
  · intro i
    exact add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i))
  · change (∑ i : Fin n, (a * x i + b * y i)) ≤ 1
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have hax := mul_le_mul_of_nonneg_left hx.2 ha
    have hby := mul_le_mul_of_nonneg_left hy.2 hb
    nlinarith

/-- The reduced simplex is compact. -/
theorem reducedSimplex_isCompact  : IsCompact (reducedSimplex n) := by
  letI  := (reducedSimplexHomeomorph n).symm.compactSpace
  exact isCompact_iff_compactSpace.mpr inferInstance

/-- The reduced simplex is bounded. -/
abbrev reducedSimplex_isBounded   :=
  IsCompact.isBounded (FiniteChains.reducedSimplex_isCompact n)

/-- Strict reduced-coordinate inequalities define the simplex interior candidate. -/
def reducedSimplexPositive  : Set (Fin n → ℝ) :=
  {x | (∀ i, 0 < x i) ∧ ∑ i, x i < 1}

 theorem reducedSimplexPositive_isOpen  : IsOpen (reducedSimplexPositive n) := by
  change IsOpen ({x : Fin n → ℝ | ∀ i, 0 < x i} ∩ {x | ∑ i, x i < 1})
  apply IsOpen.inter
  · simp_all [Set.setOf_forall, isOpen_iInter_of_finite, isOpen_lt, continuous_const, continuous_apply]
  · simp_all [isOpen_lt, continuous_finset_sum, continuous_apply, continuous_const]

 theorem reducedSimplexPositive_subset  : reducedSimplexPositive n ⊆ reducedSimplex n :=
  fun _ hx => ⟨fun i => le_of_lt (hx.1 i), le_of_lt hx.2⟩

/-- The reduced simplex has nonempty interior, including dimension zero. -/
theorem reducedSimplex_interior_nonempty  : (interior (reducedSimplex n)).Nonempty := by
  let c  := 1 / ((n : ℝ) + 1)
  have hc : 0 < c := by dsimp [c]; positivity
  have hsum : (∑ _ : Fin n, c) < 1 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    dsimp [c]
    rw [mul_one_div]
    exact (div_lt_one (by positivity)).mpr (by linarith)
  have hx : (fun _ : Fin n => c) ∈ reducedSimplexPositive n := ⟨fun _ => hc, hsum⟩
  exact ⟨_, (interior_maximal (reducedSimplexPositive_subset n)
    (reducedSimplexPositive_isOpen n)) hx⟩

/-- A genuine ambient homeomorphism takes the reduced simplex to the closed unit ball,
its interior to the open unit ball and its frontier to the unit sphere. -/
theorem reducedSimplex_exists_ball_homeomorph  :
    ∃ h : (Fin n → ℝ) ≃ₜ (Fin n → ℝ),
      h '' interior (reducedSimplex n) = Metric.ball 0 1 ∧
      h '' reducedSimplex n = Metric.closedBall 0 1 ∧
      h '' frontier (reducedSimplex n) = Metric.sphere 0 1 := by
  obtain ⟨h, hi, hc, hf⟩ := exists_homeomorph_image_interior_closure_frontier_eq_unitBall
    (reducedSimplex_convex n) (reducedSimplex_interior_nonempty n) (reducedSimplex_isBounded n)
  rw [(reducedSimplex_isClosed n).closure_eq] at hc
  exact ⟨h, hi, hc, hf⟩

end FiniteChains
