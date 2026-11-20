module

public import NearlyMinimax.IncrementPilotCoordinates
public import NearlyMinimax.AnchoredCoefficientBounds
public import NearlyMinimax.DyadicMeasurability


@[expose] public section

/-! Actual measurable finite coordinate fields and fixed-level bounds.
These bounds establish Bochner integrability; sharp level dependence is obtained
from the separate original-law pilot energy estimates. -/

noncomputable section
open MeasureTheory Set Matrix
open scoped BigOperators Matrix.Norms.L2Operator
namespace NearlyMinimax

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

variable {ι : Type*} {q d ℓ : ℕ} (j : ℕ)

theorem dyadicPilotCoordinate_measurable (a : LocalPilotIndex d ℓ) :
    Measurable (fun x => dyadicPilotCoordinate j x a) := by
  have hlin : Measurable (fun x => pilotPolynomialLinear (ℓ := 2 * ℓ)
      (dyadicPilotLabel j x) (dyadicPilotPolynomial j x a) (dyadicPilotResponse a)) := by
    apply Finset.measurable_sum
    intro β _
    exact (dyadicPilotPolynomial_coeff_continuous j a _).measurable.smul
      ((measurable_of_countable (fun c =>
        (ContinuousLinearMap.proj ((Fintype.equivFin
          (PilotBasisIndex (Fintype.card (DyadicPilotLabelIndex d j)) d (2 * ℓ)))
            ((c, β), dyadicPilotResponse a)) :
          (Fin (DyadicGlobalDimension d ℓ j) → ℝ) →L[ℝ] ℝ))).comp (dyadicPilotLabel_measurable j))
  exact (measurable_const : Measurable (fun _ => dyadicPilotScale d j)).smul hlin

theorem preconditionedPilotCoordinate_measurable (a : LocalPilotIndex d ℓ) :
    Measurable (fun x => preconditionedPilotCoordinate j x a) := Finset.measurable_sum Finset.univ (fun β _ =>
    ((dyadicKnownGram_inverse_measurable j).eval_matrix (i := localPilotRow a) (j := β)).smul
      (dyadicPilotCoordinate_measurable ..))

theorem incrementPilotFreeCoordinate_measurable
    (a : incrementVariables (anchoredDimension d ℓ)) :
    Measurable (fun x => incrementPilotFreeCoordinate j x a) := by
  let pc : ((Fin (DyadicGlobalDimension d ℓ j) → ℝ) →L[ℝ] ℝ) →L[ℝ]
      ((Fin (Fintype.card (IncrementGlobalIndex d ℓ j)) → ℝ) →L[ℝ] ℝ) :=
    ContinuousLinearMap.precomp ℝ (incrementGlobalCurrent j)
  let pp : ((Fin (DyadicGlobalDimension d ℓ (j - 1)) → ℝ) →L[ℝ] ℝ) →L[ℝ]
      ((Fin (Fintype.card (IncrementGlobalIndex d ℓ j)) → ℝ) →L[ℝ] ℝ) :=
    ContinuousLinearMap.precomp ℝ (incrementGlobalParent j)
  have hc a  :=
    pc.measurable.comp
      (preconditionedPilotCoordinate_measurable j a)
  have hp a  :=
    pp.measurable.comp
      (preconditionedPilotCoordinate_measurable (j - 1) a)
  cases a with
  | inl a =>
    cases a with
    | inl a => exact hc _
    | inr a =>
      change Measurable (fun x => if j = 0 then
        (if a.2.1 = a.2.2 then incrementGlobalOne j else 0) else _)
      split_ifs
      · exact measurable_const
      · exact measurable_const
      · exact hp _
  | inr a =>
    rcases a with ⟨parent, response, i⟩
    simp [incrementPilotFreeCoordinate]
    split_ifs
    · exact measurable_const
    · exact hp _
    · exact hp _
    · apply hc
    · apply hc

theorem incrementPilotCoordinate_measurable :
    Measurable (incrementPilotCoordinate (d := d) (ℓ := ℓ) j) := (ContinuousLinearMap.piEquivL ℝ
    (Fin (Fintype.card (IncrementGlobalIndex d ℓ j)) → ℝ)
    (fun _ => ℝ)).continuous.measurable.comp
      (measurable_pi_iff.mpr (fun _ => incrementPilotFreeCoordinate_measurable j _))

theorem real_pi_projection_norm_le [Fintype ι] (i : ι) :
    ‖(ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  simpa using norm_le_pi_norm v i

theorem pilotPolynomialLinear_norm_le (c : Fin q)
    {P : MvPolynomial (Fin d) ℝ} (response : Bool) {M : ℝ} (hM : 0 ≤ M)
    (hP : ∀ β : PolynomialBox d ℓ, |P.coeff (polynomialBoxExponent β)| ≤ M) :
    ‖pilotPolynomialLinear (ℓ := ℓ) c P response‖ ≤
      (Fintype.card (PolynomialBox d ℓ)) * M := by
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _β, M := by
      apply Finset.sum_le_sum
      intro β _
      rw [norm_smul]
      exact (mul_le_mul (hP β) (real_pi_projection_norm_le _) (norm_nonneg _) hM).trans_eq (mul_one M)
    _ = _ := by simp

theorem dyadicPilotCoordinate_uniform_bound :
    ∃ M : ℝ, 0 < M ∧ ∀ x ∈ unitCube d, ∀ a : LocalPilotIndex d ℓ,
      ‖dyadicPilotCoordinate j x a‖ ≤ M := by
  obtain ⟨P, hP, hcap⟩ := dyadicPilotPolynomial_coeff_uniform_bound j
  let B := dyadicPilotScale d j * ((Fintype.card (PolynomialBox d (2 * ℓ))) * P)
  refine ⟨max 1 B, zero_lt_one.trans_le (le_max_left _ _), ?_⟩
  intro x hx a
  have hscale : 0 ≤ dyadicPilotScale d j := by dsimp [dyadicPilotScale]; positivity
  rw [dyadicPilotCoordinate, norm_smul, Real.norm_eq_abs, abs_of_nonneg hscale]
  exact (mul_le_mul_of_nonneg_left (pilotPolynomialLinear_norm_le _ _ hP.le
    (hcap x hx a)) hscale).trans (le_max_right _ _)

theorem preconditionedPilotCoordinate_uniform_bound :
    ∃ M : ℝ, 0 < M ∧ ∀ x ∈ unitCube d, ∀ a : LocalPilotIndex d ℓ,
      ‖preconditionedPilotCoordinate j x a‖ ≤ M := by
  obtain ⟨L, hL, hLb⟩ := dyadicKnownGram_inverse_uniform_bound
  obtain ⟨P, hP, hPb⟩ := dyadicPilotCoordinate_uniform_bound j
  let B := (Fintype.card (AnchoredIndex d ℓ)) * (L * P)
  refine ⟨max 1 B, zero_lt_one.trans_le (le_max_left _ _), ?_⟩
  intro x hx a
  letI : Nonempty (AnchoredIndex d ℓ) := ⟨localPilotRow a⟩
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _β, L * P := by
      apply Finset.sum_le_sum
      intro β _
      rw [norm_smul]
      exact mul_le_mul ((matrix_real_entry_norm_le ..).trans (hLb j x hx))
        (hPb x hx _) (norm_nonneg _) hL.le
    _ = B := by simp [B]
    _ ≤ _ := le_max_right _ _

theorem incrementPilotCoordinate_uniform_bound :
    ∃ M : ℝ, 0 < M ∧ ∀ x ∈ unitCube d, ‖incrementPilotCoordinate (ℓ := ℓ) j x‖ ≤ M := by
  obtain ⟨C, hC, hCb⟩ := preconditionedPilotCoordinate_uniform_bound j
  obtain ⟨P, hP, hPb⟩ := preconditionedPilotCoordinate_uniform_bound (j - 1)
  let M := max 1 (max C P)
  have hM : 0 < M := by positivity
  refine ⟨M, hM, ?_⟩
  intro x hx
  have hCM  := (le_max_left C P).trans (le_max_right 1 (max C P))
  have hPM  := (le_max_right C P).trans (le_max_right 1 (max C P))
  have hc (a : LocalPilotIndex d ℓ)  :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul (hCb x hx a) ((ContinuousLinearMap.norm_pi_le_of_le
          (fun _ => real_pi_projection_norm_le _) zero_le_one : ‖incrementGlobalCurrent j‖ ≤ 1)) (norm_nonneg _) hC.le).trans
        (by simpa))
  have hp (a : LocalPilotIndex d ℓ)  :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul (hPb x hx a) ((ContinuousLinearMap.norm_pi_le_of_le
          (fun _ => real_pi_projection_norm_le _) zero_le_one : ‖incrementGlobalParent j‖ ≤ 1)) (norm_nonneg _) hP.le).trans
        (by simpa))
  apply ContinuousLinearMap.norm_pi_le_of_le _ hM.le
  intro i
  let a := (Fintype.equivFin (incrementVariables (anchoredDimension d ℓ))).symm i
  change ‖incrementPilotFreeCoordinate j x a‖ ≤ M
  cases a with
  | inl a =>
    cases a with
    | inl a => exact hc _
    | inr a =>
      simp [incrementPilotFreeCoordinate]
      split_ifs
      · exact (real_pi_projection_norm_le _).trans (le_max_left _ _)
      · simpa using hM.le
      · apply hp
  | inr a =>
    rcases a with ⟨parent, response, i⟩
    simp [incrementPilotFreeCoordinate]
    split_ifs
    · simpa using hM.le
    · apply hp
    · apply hp
    · apply hc
    · apply hc

end NearlyMinimax
