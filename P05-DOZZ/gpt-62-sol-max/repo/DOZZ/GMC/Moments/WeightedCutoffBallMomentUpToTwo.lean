/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Annulus.ClippedDyadic
public import DOZZ.GMC.Annulus.CutoffScale
public import DOZZ.GMC.Annulus.BallCover
public import DOZZ.GMC.Moments.WeightedCutoffPositiveSubunit
public import DOZZ.GMC.Moments.WeightedLpFiniteSum
public import DOZZ.MeasureTheory.PowerSums
public import DOZZ.GMC.Moments.PositiveExponent

/-! Local finite-cutoff ball moments through the first positive-moment induction step. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs

theorem ennreal_lintegral_rpow_const_mul_root_eq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (p : ℝ) (hp : 0 < p) (c : ℝ≥0∞) (hc : c < ⊤)
    (f : Ω → ℝ≥0∞) (hf : AEMeasurable f P)
    (hfmom : (∫⁻ ω, ENNReal.rpow (f ω) p ∂P) < ⊤) :
    (∫⁻ ω, ENNReal.rpow (c * f ω) p ∂P) ^ (1 / p) =
      c * (∫⁻ ω, ENNReal.rpow (f ω) p ∂P) ^ (1 / p) := by
  have hp0  := hp.le
  have hpowMeas : AEMeasurable (fun ω => ENNReal.rpow (f ω) p) P :=
    ENNReal.continuous_rpow_const.measurable.comp_aemeasurable hf
  have hcPow  :=
    lt_top_iff_ne_top.mpr (ENNReal.rpow_ne_top_of_nonneg hp0 hc.ne)
  have hfactor :
      (∫⁻ ω, ENNReal.rpow (c * f ω) p ∂P) =
        c ^ p * ∫⁻ ω, ENNReal.rpow (f ω) p ∂P := by
    calc
      _ = ∫⁻ ω, c ^ p * ENNReal.rpow (f ω) p ∂P := by
        apply lintegral_congr
        intro ω
        apply ENNReal.mul_rpow_of_nonneg <;> assumption
      _ = _ := lintegral_const_mul'' _ hpowMeas
  have hroot : (c ^ p) ^ (1 / p) = c := by
    rw [← ENNReal.rpow_mul, show p * (1 / p) = 1 by field_simp [ne_of_gt hp]]
    exact ENNReal.rpow_one c
  rw [hfactor, ENNReal.mul_rpow_of_ne_top hcPow.ne hfmom.ne, hroot]

/-- Extracting a positive real scale from an `ENNReal` moment root. -/
theorem ennreal_root_mul_ofReal_rpow_eq
    (C : ℝ≥0∞) (hC : C < ⊤) (a xi p : ℝ) (ha : 0 < a) (hp : 0 < p) :
    (C * ENNReal.ofReal (a ^ xi)) ^ (1 / p) =
      C ^ (1 / p) * ENNReal.ofReal (a ^ (xi / p)) := by
  have hreal  := Real.rpow_pos_of_pos ha xi
  calc
    _ = C ^ (1 / p) * ENNReal.rpow (ENNReal.ofReal (a ^ xi)) (1 / p) :=
      ENNReal.mul_rpow_of_ne_top hC.ne ENNReal.ofReal_ne_top _
    _ = C ^ (1 / p) * ENNReal.ofReal ((a ^ xi) ^ (1 / p)) := by
      rw [ennreal_ofReal_rpow_of_pos hreal]
    _ = C ^ (1 / p) * ENNReal.ofReal (a ^ (xi / p)) := by
      congr 2
      rw [← Real.rpow_mul ha.le]
      congr 1
      field_simp [ne_of_gt hp]

private theorem weighted_cutoff_scaled_rpow (γ α p δ A : ℝ)
    (hγ : 0 < γ) (hp : 0 < p) (hδ : 0 < δ) (hA : 0 ≤ A) :
    δ ^ (-γ * α) * (A * δ) ^ (gmcScaleExponent γ p / p) =
      A ^ (gmcScaleExponent γ p / p) * δ ^ (weightedCutoffMomentScaleExponent γ α p / p) := by
  rw [Real.mul_rpow hA hδ.le, mul_left_comm, ← Real.rpow_add hδ]
  congr 2
  rw [gmcScaleExponent_eq_Q γ p hγ.ne']
  unfold weightedCutoffMomentScaleExponent
  field_simp
  ring

theorem weighted_cutoff_core_rpow_identity
    (γ α p δ : ℝ) (hγ : 0 < γ) (hp : 0 < p) (hδ : 0 < δ) :
    δ ^ (-γ * α) * (δ / (1 / 8 : ℝ)) ^ (gmcScaleExponent γ p / p) =
      ((1 / 8 : ℝ)⁻¹) ^ (gmcScaleExponent γ p / p) *
        δ ^ (weightedCutoffMomentScaleExponent γ α p / p) := by
  rw [div_eq_inv_mul δ]
  exact weighted_cutoff_scaled_rpow γ α p δ _ hγ hp hδ (by positivity)

theorem weighted_cutoff_shell_rpow_identity
    (γ α p R : ℝ) (hγ : 0 < γ) (hp : 0 < p) (hR : 0 < R) (n : ℕ) :
    (cutoffDyadicBallRadius R (n + 1)) ^ (-γ * α) *
      (cutoffDyadicBallRadius R n / (1 / 8 : ℝ)) ^ (gmcScaleExponent γ p / p) =
      (2 / (1 / 8 : ℝ)) ^ (gmcScaleExponent γ p / p) *
        R ^ (weightedCutoffMomentScaleExponent γ α p / p) *
          ((1 / 2 : ℝ) ^ (weightedCutoffMomentScaleExponent γ α p / p)) ^ (n + 1) := by
  let ρ := cutoffDyadicBallRadius R (n + 1)
  have hρ : 0 < ρ := by dsimp [ρ, cutoffDyadicBallRadius]; positivity
  have hratio : cutoffDyadicBallRadius R n / (1 / 8 : ℝ) = (2 / (1 / 8 : ℝ)) * ρ := by
    dsimp [ρ, cutoffDyadicBallRadius]
    rw [pow_succ]
    field_simp
  have hrad : ρ = R * (1 / 2 : ℝ) ^ (n + 1) := by
    simp [ρ, cutoffDyadicBallRadius, div_eq_mul_inv, inv_pow]
  rw [hratio, weighted_cutoff_scaled_rpow γ α p ρ _ hγ hp hρ (by positivity), hrad,
    Real.mul_rpow hR.le (by positivity), ← Real.rpow_natCast_mul (by positivity), mul_comm (↑(n + 1) : ℝ),
    Real.rpow_mul_natCast (by positivity), mul_assoc]

/-- For `p ≥ 1`, the positive-charge cutoff moment is bounded by the finite sum of the `Lᵖ`
sizes of its core and dyadic shell masses. This is the form used with the first induction-step
ball bound to sum the shells uniformly in the cutoff. -/
theorem cutoffWeightedGmcBallMoment_positive_lp_shell_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (γ α : ℝ) (hγ : 0 < γ) (hα : 0 < α) (z : ℂ) (R δ p : ℝ)
    (N : ℕ) (hR : 0 < R) (hδ : 0 < δ)
    (hNlo : cutoffDyadicBallRadius R (N + 1) ≤ δ)
    (hp : 1 ≤ p) :
    (∫⁻ ω, ENNReal.rpow (cutoffWeightedGmcBallMass P Xc γ α z R δ ω) p ∂P) ^
        (1 / p) ≤
      (∫⁻ ω, (ENNReal.ofReal (δ ^ (-γ * α)) *
        regularizedGMC P Xc γ (Real.log (1 / δ)) ω (Metric.ball z δ)) ^ p ∂P) ^
          (1 / p) +
      ∑ n ∈ Finset.range (N + 1),
        (∫⁻ ω, (cutoffDyadicBallWeight γ α R N n *
          regularizedGMC P Xc γ (Real.log (1 / δ)) ω
            (Metric.ball z (cutoffDyadicBallRadius R n))) ^ p ∂P) ^ (1 / p) := by
  classical
  let core  := fun ω => ENNReal.ofReal (δ ^ (-γ * α)) *
    regularizedGMC P Xc γ (Real.log (1 / δ)) ω (Metric.ball z δ)
  let shell  := fun n ω => cutoffDyadicBallWeight γ α R N n *
    regularizedGMC P Xc γ (Real.log (1 / δ)) ω
      (Metric.ball z (cutoffDyadicBallRadius R n))
  let term  := fun i ω =>
    match i with
    | none => core ω
    | some n => shell n ω
  let indices  :=
    insert none ((Finset.range (N + 1)).image some)
  have hcoreMeas : AEMeasurable core P := by
    dsimp [core]
    exact aemeasurable_const.mul (regularizedGMC_mass_aemeasurable P X hX Xc hXc γ
      (Real.log (1 / δ)) (Metric.ball z δ) Metric.isOpen_ball.measurableSet)
  have hshellMeas (n : ℕ) : AEMeasurable (shell n) P := by
    dsimp [shell]
    exact aemeasurable_const.mul (regularizedGMC_mass_aemeasurable P X hX Xc hXc γ
      (Real.log (1 / δ)) (Metric.ball z (cutoffDyadicBallRadius R n))
      Metric.isOpen_ball.measurableSet)
  have htermMeas : ∀ i ∈ indices, AEMeasurable (term i) P := by
    intro i hi
    cases i with
    | none => exact hcoreMeas
    | some n => exact hshellMeas n
  have htsum (ω : Ω) :
      (∑' n : ℕ, if n ≤ N then
        ENNReal.ofReal ((cutoffDyadicBallRadius R (n + 1)) ^ (-γ * α)) *
          regularizedGMC P Xc γ (Real.log (1 / δ)) ω
            (Metric.ball z (cutoffDyadicBallRadius R n)) else 0) =
        ∑ n ∈ Finset.range (N + 1), shell n ω := by
    rw [tsum_eq_sum (s := Finset.range (N + 1))]
    · apply Finset.sum_congr rfl
      intro n hn
      have hnle : n ≤ N := by
        have  := Finset.mem_range.mp hn
        omega
      simp [shell, cutoffDyadicBallWeight, hnle]
    · intro n hn
      have hnrange : ¬ n < N + 1 := by
        intro hnlt
        exact hn (Finset.mem_range.mpr hnlt)
      have hnle : ¬ n ≤ N := by omega
      simp [hnle]
  have hdecomp (ω : Ω) :
      cutoffWeightedGmcBallMass P Xc γ α z R δ ω ≤
        core ω + ∑ n ∈ Finset.range (N + 1), shell n ω := by
    change (∫⁻ x in Metric.ball z R,
      ENNReal.ofReal ((‖x - z‖ + δ) ^ (-γ * α)) ∂
        regularizedGMC P Xc γ (Real.log (1 / δ)) ω) ≤ _
    have h := cutoffWeightedGmcBallMass_le_positive_dyadic_cover
      (regularizedGMC P Xc γ (Real.log (1 / δ)) ω) γ α z R δ N
      hγ hα hR hδ hNlo
    rw [htsum ω] at h
    assumption
  have hsum : ∀ ω, ∑ i ∈ indices, term i ω =
      core ω + ∑ n ∈ Finset.range (N + 1), shell n ω := by
    intro ω
    simp [indices, term, core, shell, Finset.sum_image]
  have hpoint (ω : Ω) :
      ENNReal.rpow (cutoffWeightedGmcBallMass P Xc γ α z R δ ω) p ≤
        ENNReal.rpow (∑ i ∈ indices, term i ω) p := by
    rw [hsum]
    exact ENNReal.rpow_le_rpow (hdecomp ω) (le_trans zero_le_one hp)
  calc
    _ ≤ (∫⁻ ω, ENNReal.rpow (∑ i ∈ indices, term i ω) p ∂P) ^ (1 / p) := by
      apply ENNReal.rpow_le_rpow
      · exact lintegral_mono hpoint
      positivity
    _ ≤ ∑ i ∈ indices, (∫⁻ ω, ENNReal.rpow (term i ω) p ∂P) ^ (1 / p) :=
      ennreal_lintegral_rpow_finset_sum_root_le indices term p hp htermMeas
    _ = _ := by
      simp [indices, term, Finset.sum_image, core, shell]

/-- The scale-free dyadic shell coefficient for a positive insertion, with a chosen uniform
annular exponent margin. -/
noncomputable def cutoffWeightedPositiveScaleRootBoundConstant
    (A : ℝ≥0∞) (γ p ε : ℝ) : ℝ≥0∞ :=
  A * (ENNReal.ofReal (((1 / 8 : ℝ)⁻¹) ^
      ((gmcScaleExponent γ p) / p)) +
    ENNReal.ofReal ((2 / (1 / 8 : ℝ)) ^
      ((gmcScaleExponent γ p) / p)) *
      ENNReal.ofReal ((1 / 2 : ℝ) ^ ε) *
      (1 - ENNReal.ofReal ((1 / 2 : ℝ) ^ ε))⁻¹)

end DOZZ.Proofs
