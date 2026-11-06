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
variable {d ℓ : ℕ}

section
variable (a : LocalPilotIndex d ℓ)
include a

def localPilotRow    :=
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
end


/-- Precisely `K 1_I (B⁻¹ψψᵀ, B⁻¹ψY, B⁻¹ψ)` from the manuscript. -/
def preconditionedPilotFeature  j x
    a z  :=
  ∑ β : AnchoredIndex d ℓ, (dyadicKnownGram j x)⁻¹ (localPilotRow a) β *
    dyadicPilotFeature j x (localPilotReplaceRow a β) z

def preconditionedPilotPopulation  θ
    j x (a : LocalPilotIndex d ℓ)  :=
  ∫ z, preconditionedPilotFeature j x a z ∂observationLaw θ

theorem preconditionedPilotFeature_measurable  j
    x (a : LocalPilotIndex d ℓ) : Measurable (preconditionedPilotFeature j x a) :=
  Finset.measurable_sum Finset.univ (fun β _ =>
    measurable_const.mul (dyadicPilotFeature_measurable j x _))

section
variable (C : ModelConstants d) (θ : RegressionParameter d) (hθ : Admissible C θ) (j : ℕ) (x : Covariate d) (hx : x ∈ unitCube d)
include hθ hx

theorem preconditionedPilotFeature_memLp_two   (a : LocalPilotIndex d ℓ) :
    MemLp (preconditionedPilotFeature j x a) 2 (observationLaw θ) :=
  memLp_finsetSum Finset.univ (fun β _ =>
    (dyadicPilotFeature_memLp_two C θ hθ j x hx (localPilotReplaceRow a β)).const_mul _)

/-- The exact preconditioned means are the known linear transform of the
original-law raw means; no population equivalence is assumed. -/
theorem preconditionedPilotPopulation_eq_sum   a :
    preconditionedPilotPopulation θ j x a =
      ∑ β : AnchoredIndex d ℓ, (dyadicKnownGram j x)⁻¹ (localPilotRow a) β *
        dyadicPilotPopulation θ j x (localPilotReplaceRow a β) := by
  let := observationLaw_isProbability C θ hθ
  unfold preconditionedPilotPopulation preconditionedPilotFeature
  rw [integral_finsetSum _ (fun β _ =>
    ((dyadicPilotFeature_memLp_two C θ hθ j x hx _).integrable (by norm_num)).const_mul _)]
  simp only [integral_const_mul, dyadicPilotPopulation]

theorem preconditionedPilotPopulation_gram   (γ δ : AnchoredIndex d ℓ) :
    preconditionedPilotPopulation θ j x (Sum.inl (γ, δ)) =
      dyadicPreconditionedGram θ j x γ δ := by
  rw [preconditionedPilotPopulation_eq_sum C θ hθ j x hx]
  simp only [localPilotRow, localPilotReplaceRow, dyadicPilotPopulation_gram C θ hθ,
    dyadicPreconditionedGram, Matrix.mul_apply]

section
variable (γ : AnchoredIndex d ℓ)

theorem preconditionedPilotPopulation_response    :
    preconditionedPilotPopulation θ j x (Sum.inr (Sum.inl γ)) =
      anchoredPreconditionedMoment (dyadicNormalizedAnchor j x) (dyadicNormalizedDensity θ j x)
        (θ.regression ∘ dyadicCellAffine j x) γ := by
  rw [preconditionedPilotPopulation_eq_sum C θ hθ j x hx]
  simp only [localPilotRow, localPilotReplaceRow, dyadicPilotPopulation_response C θ hθ j x hx,
    dyadicKnownGram_eq_normalized, anchoredPreconditionedMoment, Matrix.mulVec, dotProduct,
    dyadicResponseMoment_eq_normalized C θ hθ]

theorem preconditionedPilotPopulation_constant    :
    preconditionedPilotPopulation θ j x (Sum.inr (Sum.inr γ)) =
      anchoredPreconditionedMoment (dyadicNormalizedAnchor j x) (dyadicNormalizedDensity θ j x)
        (fun _ => 1) γ := by
  rw [preconditionedPilotPopulation_eq_sum C θ hθ j x hx]
  simp only [localPilotRow, localPilotReplaceRow, dyadicPilotPopulation_constant C θ hθ,
    dyadicKnownGram_eq_normalized, anchoredPreconditionedMoment, Matrix.mulVec, dotProduct,
    dyadicConstantMoment_eq_normalized C θ hθ]
end

end


theorem dyadicKnownGram_inverse_uniform_bound  :
    ∃ L : ℝ, 0 < L ∧ ∀ j , ∀ x ∈ unitCube d, ‖(dyadicKnownGram (ℓ := ℓ) j x)⁻¹‖ ≤ L := by
  obtain ⟨L, hL, hbound⟩ := anchoredGram_inverse_uniform_bound (d := d) (ℓ := ℓ)
  refine ⟨L, hL, ?_⟩
  intro j x hx
  rw [dyadicKnownGram_eq_normalized]
  exact hbound _ (gridNormalizedAnchor_mem_cube _ _ x hx)

/-- Known preconditioning increases the raw budget by a fixed feature-count
and inverse-Gram factor; responses still require only a second moment. -/
theorem preconditionedPilotFeature_second_le  C
    θ (hθ : Admissible C θ) j x
    (hx : x ∈ unitCube d) (a : LocalPilotIndex d ℓ)
    L (hL : 0 ≤ L) (hB : ‖(dyadicKnownGram (ℓ := ℓ) j x)⁻¹‖ ≤ L) :
    (∫ z, preconditionedPilotFeature j x a z ^ 2 ∂observationLaw θ) ≤
      (Fintype.card (AnchoredIndex d ℓ)) ^ 2 * L ^ 2 *
        dyadicPilotMomentConstant C * dyadicPilotScale d j := by
  let := observationLaw_isProbability C θ hθ
  letI : Nonempty (AnchoredIndex d ℓ) := ⟨localPilotRow a⟩
  let B := (dyadicKnownGram (ℓ := ℓ) j x)⁻¹
  let f (β : AnchoredIndex d ℓ) (z : Observation d) := B (localPilotRow a) β *
    dyadicPilotFeature j x (localPilotReplaceRow a β) z
  have hlp (β : AnchoredIndex d ℓ) : MemLp (f β) 2 (observationLaw θ) :=
    (dyadicPilotFeature_memLp_two C θ hθ j x hx _).const_mul _
  have hs : Integrable (fun z => (Fintype.card (AnchoredIndex d ℓ) : ℝ) *
      ∑ β, f β z ^ 2) (observationLaw θ) :=
    (integrable_finsetSum Finset.univ (fun β _ => (hlp β).integrable_sq)).const_mul _
  have hfirst : (∫ z, preconditionedPilotFeature j x a z ^ 2 ∂observationLaw θ) ≤
      (Fintype.card (AnchoredIndex d ℓ) : ℝ) * ∑ β, ∫ z, f β z ^ 2 ∂observationLaw θ := by
    have h := integral_mono (preconditionedPilotFeature_memLp_two C θ hθ j x hx a).integrable_sq hs
      (fun z => by solve_by_elim [sq_sum_le_card_mul_sum_sq])
    rwa [integral_const_mul, integral_finsetSum _ (fun β _ => (hlp β).integrable_sq)] at h
  have hb (β : AnchoredIndex d ℓ) : |B (localPilotRow a) β| ≤ L := by
    calc
      _ = ‖B (localPilotRow a) β‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖B‖ := matrix_real_entry_norm_le B (localPilotRow a) β
      _ ≤ L := hB
  have hcoord (β : AnchoredIndex d ℓ) : (∫ z, f β z ^ 2 ∂observationLaw θ) ≤
      L ^ 2 * dyadicPilotMomentConstant C * dyadicPilotScale d j := by
    simp only [f, mul_pow, integral_const_mul]
    have hb2 : B (localPilotRow a) β ^ 2 ≤ L ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hb β) 2
    exact (mul_le_mul_of_nonneg_left (dyadicPilotFeature_second_le C θ hθ j x hx _)
      (sq_nonneg _)).trans
      (by have hc := dyadicPilotMomentConstant_pos C
          have hk := dyadicPilotScale_pos d j
          nlinarith [mul_le_mul_of_nonneg_right hb2 (mul_nonneg hc.le hk.le)])
  apply hfirst.trans
  apply (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun β _ => hcoord β))
    (Nat.cast_nonneg _)).trans_eq
  simp [pow_two, mul_assoc]
end


/-- One fixed inverse-Gram bound is selected once for the feature geometry. -/
def pilotInverseBound d ℓ  :=
  Classical.choose (dyadicKnownGram_inverse_uniform_bound (d := d) (ℓ := ℓ))

theorem pilotInverseBound_pos d ℓ : 0 < pilotInverseBound d ℓ :=
  (Classical.choose_spec (dyadicKnownGram_inverse_uniform_bound (d := d) (ℓ := ℓ))).1

theorem pilotInverseBound_le {d ℓ } j x (hx : x ∈ unitCube d) :
    ‖(dyadicKnownGram (ℓ := ℓ) j x)⁻¹‖ ≤ pilotInverseBound d ℓ :=
  (Classical.choose_spec (dyadicKnownGram_inverse_uniform_bound (d := d) (ℓ := ℓ))).2 j x hx

section
variable {d : ℕ} (C : ModelConstants d)
include C

def preconditionedPilotMomentConstant  ℓ  :=
  max 1 ((Fintype.card (AnchoredIndex d ℓ) : ℝ) ^ 2 * pilotInverseBound d ℓ ^ 2 *
    dyadicPilotMomentConstant C)

theorem preconditionedPilotMomentConstant_pos  ℓ :
    0 < preconditionedPilotMomentConstant C ℓ := zero_lt_one.trans_le (le_max_left _ _)
end


/-- A single fixed-model constant bounds every actual preconditioned raw
coordinate, uniformly in dyadic level and anchor. -/
theorem preconditionedPilotFeature_uniform_second_le {d ℓ } C
    θ (hθ : Admissible C θ) j x
    (hx : x ∈ unitCube d) (a : LocalPilotIndex d ℓ) :
    (∫ z, preconditionedPilotFeature j x a z ^ 2 ∂observationLaw θ) ≤
      preconditionedPilotMomentConstant C ℓ * dyadicPilotScale d j := by
  apply (preconditionedPilotFeature_second_le C θ hθ j x hx a (pilotInverseBound d ℓ)
    (pilotInverseBound_pos d ℓ).le (pilotInverseBound_le j x hx)).trans
  exact mul_le_mul_of_nonneg_right (le_max_right _ _) (dyadicPilotScale_pos d j).le

end NearlyMinimax
