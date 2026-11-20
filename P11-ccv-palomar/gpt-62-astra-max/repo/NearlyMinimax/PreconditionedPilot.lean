module

public import NearlyMinimax.DyadicPilotPopulation
public import NearlyMinimax.PopulationInverseDerivatives


@[expose] public section

/-! Actual known-Gram preconditioning of the dyadic raw features and its
uniform original-law L² budget. -/

noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators Matrix.Norms.L2Operator
namespace NearlyMinimax

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

section
variable {d ℓ : ℕ} (θ : RegressionParameter d) (j : ℕ) (x : Covariate d) (a : LocalPilotIndex d ℓ)

def localPilotRow : AnchoredIndex d ℓ :=
  match a with
  | Sum.inl (γ, _) => γ
  | Sum.inr (Sum.inl γ) => γ
  | Sum.inr (Sum.inr γ) => γ

def localPilotReplaceRow
    (β : AnchoredIndex d ℓ) : LocalPilotIndex d ℓ :=
  match a with
  | Sum.inl (_, δ) => Sum.inl (β, δ)
  | Sum.inr (Sum.inl _) => Sum.inr (Sum.inl β)
  | Sum.inr (Sum.inr _) => Sum.inr (Sum.inr β)

/-- Precisely `K 1_I (B⁻¹ψψᵀ, B⁻¹ψY, B⁻¹ψ)` from the manuscript. -/
def preconditionedPilotFeature (z : Observation d) : ℝ :=
  ∑ β, (dyadicKnownGram j x)⁻¹ (localPilotRow a) β *
    dyadicPilotFeature j x (localPilotReplaceRow a β) z

def preconditionedPilotPopulation : ℝ :=
  ∫ z, preconditionedPilotFeature j x a z ∂observationLaw θ

theorem preconditionedPilotFeature_measurable : Measurable (preconditionedPilotFeature j x a) :=
  Finset.measurable_sum Finset.univ (fun β _ =>
    measurable_const.mul (dyadicPilotFeature_measurable j x _))

end

section
variable {d ℓ : ℕ} {C : ModelConstants d} {θ : RegressionParameter d} (hθ : Admissible C θ) (j : ℕ)
    {x : Covariate d} (hx : x ∈ unitCube d) (γ : AnchoredIndex d ℓ) (a : LocalPilotIndex d ℓ)
include hx hθ

theorem preconditionedPilotFeature_memLp_two :
    MemLp (preconditionedPilotFeature j x a) 2 (observationLaw θ) :=
  memLp_finsetSum Finset.univ (fun β _ =>
    (dyadicPilotFeature_memLp_two hθ j hx (localPilotReplaceRow a β)).const_mul _)

/-- The exact preconditioned means are the known linear transform of the
original-law raw means; no population equivalence is assumed. -/
theorem preconditionedPilotPopulation_eq_sum :
    preconditionedPilotPopulation θ j x a =
      ∑ β, (dyadicKnownGram j x)⁻¹ (localPilotRow a) β *
        dyadicPilotPopulation θ j x (localPilotReplaceRow a β) := by
  let := observationLaw_isProbability C θ hθ
  unfold preconditionedPilotPopulation preconditionedPilotFeature
  rw [integral_finsetSum _ (fun β _ =>
    ((dyadicPilotFeature_memLp_two hθ j hx _).integrable (by norm_num)).const_mul _)]
  simp only [integral_const_mul, dyadicPilotPopulation]

theorem preconditionedPilotPopulation_gram (δ : AnchoredIndex d ℓ) :
    preconditionedPilotPopulation θ j x (Sum.inl (γ, δ)) =
      dyadicPreconditionedGram θ j x γ δ := by
  rw [preconditionedPilotPopulation_eq_sum hθ j hx]
  simp only [localPilotRow, localPilotReplaceRow, dyadicPilotPopulation_gram hθ,
    dyadicPreconditionedGram, Matrix.mul_apply]

end

theorem dyadicKnownGram_inverse_uniform_bound {d ℓ : ℕ} :
    ∃ L : ℝ, 0 < L ∧ ∀ j, ∀ x ∈ unitCube d, ‖(dyadicKnownGram (ℓ := ℓ) j x)⁻¹‖ ≤ L := by
  obtain ⟨L, hL, hbound⟩ := anchoredGram_inverse_uniform_bound
  refine ⟨L, hL, ?_⟩
  intro j x hx
  rw [dyadicKnownGram_eq_normalized]
  exact hbound _ (gridNormalizedAnchor_mem_cube _ _ hx)

variable {d ℓ : ℕ} {C : ModelConstants d} {θ : RegressionParameter d} (hθ : Admissible C θ) (j : ℕ)
    {x : Covariate d} (hx : x ∈ unitCube d)

include hθ in
/-- Known preconditioning increases the raw budget by a fixed feature-count
and inverse-Gram factor; responses still require only a second moment. -/
theorem preconditionedPilotFeature_second_le {j : ℕ} {x : Covariate d}
    (hx : x ∈ unitCube d) (a : LocalPilotIndex d ℓ)
    {L : ℝ} (hL : 0 ≤ L) (hB : ‖(dyadicKnownGram (ℓ := ℓ) j x)⁻¹‖ ≤ L) :
    (∫ z, preconditionedPilotFeature j x a z ^ 2 ∂observationLaw θ) ≤
      (Fintype.card (AnchoredIndex d ℓ)) ^ 2 * L ^ 2 *
        dyadicPilotMomentConstant C * dyadicPilotScale d j := by
  let := observationLaw_isProbability C θ hθ
  letI : Nonempty (AnchoredIndex d ℓ) := ⟨localPilotRow a⟩
  let B := (dyadicKnownGram (ℓ := ℓ) j x)⁻¹
  let f (β : AnchoredIndex d ℓ) (z : Observation d) := B (localPilotRow a) β *
    dyadicPilotFeature j x (localPilotReplaceRow a β) z
  have hlp (β : AnchoredIndex d ℓ) : MemLp (f β) 2 (observationLaw θ) :=
    (dyadicPilotFeature_memLp_two hθ j hx _).const_mul _
  have hs : Integrable (fun z => (Fintype.card (AnchoredIndex d ℓ)) *
      ∑ β, f β z ^ 2) (observationLaw θ) :=
    (integrable_finsetSum Finset.univ (fun β _ => (hlp β).integrable_sq)).const_mul _
  have hfirst : (∫ z, preconditionedPilotFeature j x a z ^ 2 ∂observationLaw θ) ≤
      (Fintype.card (AnchoredIndex d ℓ)) * ∑ β, ∫ z, f β z ^ 2 ∂observationLaw θ := by
    have h := integral_mono (preconditionedPilotFeature_memLp_two hθ j hx a).integrable_sq hs
      (fun z => by exact sq_sum_le_card_mul_sum_sq)
    rwa [integral_const_mul, integral_finsetSum _ (fun β _ => (hlp β).integrable_sq)] at h
  have hb (β : AnchoredIndex d ℓ) : |B (localPilotRow a) β| ≤ L := by
    calc
      _ = _ := (Real.norm_eq_abs _).symm
      _ ≤ _ := matrix_real_entry_norm_le B (localPilotRow a) β
      _ ≤ L := hB
  have hcoord (β : AnchoredIndex d ℓ) : (∫ z, f β z ^ 2 ∂observationLaw θ) ≤
      L ^ 2 * dyadicPilotMomentConstant C * dyadicPilotScale d j := by
    simp [f, mul_pow, integral_const_mul]
    have hb2 : B (localPilotRow a) β ^ 2 ≤ L ^ 2 := by
      simpa using pow_le_pow_left₀ (abs_nonneg _) (hb β) 2
    exact (mul_le_mul_of_nonneg_left (dyadicPilotFeature_second_le hθ j hx _)
      (sq_nonneg _)).trans
      (by have hc := dyadicPilotMomentConstant_pos C
          have hk := dyadicPilotScale_pos d j
          nlinarith [mul_le_mul_of_nonneg_right hb2 (mul_nonneg hc.le hk.le)])
  apply hfirst.trans
  apply (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun β _ => hcoord β))
    (Nat.cast_nonneg _)).trans_eq
  simp [pow_two, mul_assoc]

/-- One fixed inverse-Gram bound is selected once for the feature geometry. -/
def pilotInverseBound (d ℓ : ℕ) : ℝ :=
  Classical.choose (dyadicKnownGram_inverse_uniform_bound (d := d) (ℓ := ℓ))

theorem pilotInverseBound_pos (d ℓ : ℕ) : 0 < pilotInverseBound d ℓ :=
  (Classical.choose_spec (dyadicKnownGram_inverse_uniform_bound)).1

def preconditionedPilotMomentConstant (C : ModelConstants d) (ℓ : ℕ) : ℝ :=
  max 1 ((Fintype.card (AnchoredIndex d ℓ)) ^ 2 * pilotInverseBound d ℓ ^ 2 *
    dyadicPilotMomentConstant C)

theorem preconditionedPilotMomentConstant_pos (C : ModelConstants d) (ℓ : ℕ) :
    0 < preconditionedPilotMomentConstant C ℓ := zero_lt_one.trans_le (le_max_left _ _)

include hθ hx in
/-- A single fixed-model constant bounds every actual preconditioned raw
coordinate, uniformly in dyadic level and anchor. -/
theorem preconditionedPilotFeature_uniform_second_le (a : LocalPilotIndex d ℓ) :
    (∫ z, preconditionedPilotFeature j x a z ^ 2 ∂observationLaw θ) ≤
      preconditionedPilotMomentConstant C ℓ * dyadicPilotScale d j := by
  apply (preconditionedPilotFeature_second_le hθ hx a
    (pilotInverseBound_pos d ℓ).le ((Classical.choose_spec (dyadicKnownGram_inverse_uniform_bound (d := d) (ℓ := ℓ))).2 j x hx)).trans
  exact mul_le_mul_of_nonneg_right (le_max_right _ _) (dyadicPilotScale_pos d j).le

/-- Total coordinate second-moment bound at a dyadic pilot level. -/
abbrev dyadicFeatureEnergy {d : ℕ} (C : ModelConstants d) (j : ℕ) : ℝ :=
  Fintype.card (incrementVariables (anchoredDimension d C.order)) *
    preconditionedPilotMomentConstant C C.order * dyadicPilotScale d j

theorem dyadicFeatureEnergy_nonneg {d : ℕ} (C : ModelConstants d) (j : ℕ) :
    0 ≤ dyadicFeatureEnergy C j :=
  mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (preconditionedPilotMomentConstant_pos C _).le)
    (dyadicPilotScale_pos _ _).le

/-- Factorial variance series, with degree fixed by the pilot and the anchor basis. -/
def dyadicPilotSeries {d : ℕ} (C : ModelConstants d) (A Λ : ℝ) (j m : ℕ) : ℝ :=
  ∑ k : Fin (m + anchoredDimension d C.order + 1),
    (k.val + 1).factorial *
      (A ^ 2 * dyadicFeatureEnergy C j / Λ) ^ (k.val + 1)

end NearlyMinimax
