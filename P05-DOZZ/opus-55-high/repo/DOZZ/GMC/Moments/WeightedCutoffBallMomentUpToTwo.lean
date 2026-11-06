/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Annulus.PositiveBase
public import DOZZ.GMC.Annulus.CutoffScale
public import DOZZ.GMC.Annulus.BallCover
public import DOZZ.GMC.Moments.WeightedCutoffPositiveSubunit
public import DOZZ.GMC.Moments.WeightedLpFiniteSum

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
  have hp0 : 0 ≤ p := hp.le
  have hpowMeas : AEMeasurable (fun ω => ENNReal.rpow (f ω) p) P :=
    ENNReal.continuous_rpow_const.measurable.comp_aemeasurable hf
  have hcPow :=
    lt_top_iff_ne_top.mpr (ENNReal.rpow_ne_top_of_nonneg hp0 hc.ne)
  have hfactor :
      (∫⁻ ω, ENNReal.rpow (c * f ω) p ∂P) =
        c ^ p * ∫⁻ ω, ENNReal.rpow (f ω) p ∂P := by
    calc
      _ = ∫⁻ ω, c ^ p * ENNReal.rpow (f ω) p ∂P := by
        apply lintegral_congr
        intro ω
        exact ENNReal.mul_rpow_of_nonneg c (f ω) hp0
      _ = _ := lintegral_const_mul'' _ hpowMeas
  have hroot : (c ^ p) ^ (1 / p) = c := by
    aesop
  rw [hfactor, ENNReal.mul_rpow_of_ne_top hcPow.ne hfmom.ne, hroot]

theorem ennreal_root_mul_ofReal_rpow_eq
    (C : ℝ≥0∞) (hC : C < ⊤) (a xi p : ℝ) (ha : 0 < a) (hp : 0 < p) :
    (C * ENNReal.ofReal (a ^ xi)) ^ (1 / p) =
      C ^ (1 / p) * ENNReal.ofReal (a ^ (xi / p)) := by
  calc
    _ = C ^ (1 / p) * ENNReal.rpow (ENNReal.ofReal (a ^ xi)) (1 / p) :=
      ENNReal.mul_rpow_of_ne_top hC.ne ENNReal.ofReal_ne_top _
    _ = C ^ (1 / p) * ENNReal.ofReal ((a ^ xi) ^ (1 / p)) := by
      rw [DOZZ.Proofs.ennreal_ofReal_rpow_of_pos_cutoff (Real.rpow_pos_of_pos ha xi)]
    _ = C ^ (1 / p) * ENNReal.ofReal (a ^ (xi / p)) := by
      congr 2
      rw [← Real.rpow_mul ha.le]
      ring

private theorem weighted_cutoff_rpow_exponent_relation (γ α p : ℝ)
    (hγ : 0 < γ) (hp : 0 < p) :
    -γ * α + (2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2) / p =
      weightedCutoffMomentScaleExponent γ α p / p := by
  dsimp [weightedCutoffMomentScaleExponent, Q]
  grind

theorem weighted_cutoff_core_rpow_identity
    (γ α p δ : ℝ) (hγ : 0 < γ) (hp : 0 < p) (hδ : 0 < δ) :
    δ ^ (-γ * α) * (δ / (1 / 8 : ℝ)) ^
      ((2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2) / p) =
      ((1 / 8 : ℝ)⁻¹) ^
        ((2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2) / p) *
        δ ^ (weightedCutoffMomentScaleExponent γ α p / p) := by
  have hδbase : 0 ≤ δ := hδ.le
  have hrecip : 0 ≤ (1 / 8 : ℝ)⁻¹ := by positivity
  rw [show δ / (1 / 8 : ℝ) = δ * (1 / 8 : ℝ)⁻¹ by field_simp]
  rw [Real.mul_rpow hδbase hrecip]
  calc
    _ = (δ ^ (-γ * α) * δ ^
          ((2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2) / p)) *
          ((1 / 8)⁻¹) ^
            ((2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2) / p) := by ac_rfl
    _ = δ ^ (-γ * α +
          (2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2) / p) *
          ((1 / 8)⁻¹) ^
            ((2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2) / p) := by
      rw [← Real.rpow_add hδ]
    _ = _ := by
      rw [weighted_cutoff_rpow_exponent_relation γ α p hγ hp]
      ring

theorem weighted_cutoff_shell_rpow_identity
    (γ α p R : ℝ) (hγ : 0 < γ) (hp : 0 < p) (hR : 0 < R) (n : ℕ) :
    (cutoffDyadicBallRadius R (n + 1)) ^ (-γ * α) *
      (cutoffDyadicBallRadius R n / (1 / 8 : ℝ)) ^
        ((2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2) / p) =
      (2 / (1 / 8 : ℝ)) ^
          ((2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2) / p) *
        R ^ (weightedCutoffMomentScaleExponent γ α p / p) *
          ((1 / 2 : ℝ) ^ (weightedCutoffMomentScaleExponent γ α p / p)) ^ (n + 1) := by
  let ρ := cutoffDyadicBallRadius R (n + 1)
  have hρ : 0 < ρ := by dsimp [ρ, cutoffDyadicBallRadius]; positivity
  have hstep : cutoffDyadicBallRadius R n = 2 * ρ := by
    dsimp [ρ, cutoffDyadicBallRadius]
    ring
  have hratio : cutoffDyadicBallRadius R n / (1 / 8 : ℝ) =
      (2 / (1 / 8 : ℝ)) * ρ := by
    linarith
  have hrad : ρ = R * (1 / 2 : ℝ) ^ (n + 1) := by
    aesop
  calc
    _ = ρ ^ (-γ * α) *
        ((2 / (1 / 8 : ℝ)) ^
          ((2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2) / p) *
          ρ ^ ((2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2) / p)) := by
      rw [show cutoffDyadicBallRadius R (n + 1) = ρ by rfl, hratio,
        Real.mul_rpow (by positivity) hρ.le]
    _ = (2 / (1 / 8 : ℝ)) ^
          ((2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2) / p) *
        ρ ^ (weightedCutoffMomentScaleExponent γ α p / p) := by
      calc
        _ = (2 / (1 / 8 : ℝ)) ^
            ((2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2) / p) *
            (ρ ^ (-γ * α) * ρ ^
              ((2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2) / p)) := by ac_rfl
        _ = (2 / (1 / 8 : ℝ)) ^
            ((2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2) / p) *
            ρ ^ (-γ * α +
              (2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2) / p) := by
          rw [← Real.rpow_add hρ]
        _ = _ := by rw [(weighted_cutoff_rpow_exponent_relation γ α p hγ hp)]
    _ = (2 / (1 / 8 : ℝ)) ^
          ((2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2) / p) *
        (R ^ (weightedCutoffMomentScaleExponent γ α p / p) *
          ((1 / 2 : ℝ) ^ (weightedCutoffMomentScaleExponent γ α p / p)) ^ (n + 1)) := by
      rw [hrad, Real.mul_rpow hR.le (by positivity)]
      have hhalf : 0 ≤ (1 / 2 : ℝ) := by norm_num
      rw [← Real.rpow_natCast_mul hhalf _
          (weightedCutoffMomentScaleExponent γ α p / p)]
      rw [show ((n + 1 : ℕ) : ℝ) *
          (weightedCutoffMomentScaleExponent γ α p / p) =
          (weightedCutoffMomentScaleExponent γ α p / p) * (n + 1 : ℕ) by ring,
        Real.rpow_mul_natCast hhalf]
    _ = _ := by ring

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
  let core : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (δ ^ (-γ * α)) *
    regularizedGMC P Xc γ (Real.log (1 / δ)) ω (Metric.ball z δ)
  let shell : ℕ → Ω → ℝ≥0∞ := fun n ω => cutoffDyadicBallWeight γ α R N n *
    regularizedGMC P Xc γ (Real.log (1 / δ)) ω
      (Metric.ball z (cutoffDyadicBallRadius R n))
  let term : Option ℕ → Ω → ℝ≥0∞ := fun i ω =>
    match i with
    | none => core ω
    | some n => shell n ω
  let indices :=
    insert none ((Finset.range (N + 1)).image some)
  have hcoreMeas : AEMeasurable core P := by
    dsimp [core]
    exact aemeasurable_const.mul (regularizedGMC_mass_aemeasurable P X hX Xc hXc γ
      (Real.log _) _ Metric.isOpen_ball.measurableSet)
  have hshellMeas (n : ℕ) : AEMeasurable (shell n) P := by
    dsimp [shell]
    exact aemeasurable_const.mul (regularizedGMC_mass_aemeasurable P X hX Xc hXc γ
      (Real.log _) _
      Metric.isOpen_ball.measurableSet)
  have htermMeas : ∀ i ∈ indices, AEMeasurable (term i) P := by
    aesop
  have htsum (ω : Ω) :
      (∑' n : ℕ, if n ≤ N then
        ENNReal.ofReal ((cutoffDyadicBallRadius R (n + 1)) ^ (-γ * α)) *
          regularizedGMC P Xc γ (Real.log (1 / δ)) ω
            (Metric.ball z (cutoffDyadicBallRadius R n)) else 0) =
        ∑ n ∈ Finset.range (N + 1), shell n ω := by
    rw [tsum_eq_sum (s := Finset.range _)]
    · apply Finset.sum_congr rfl
      intro n hn
      have hnle : n ≤ N := by
        have : n < N + 1 := Finset.mem_range.mp hn
        omega
      simp [shell, cutoffDyadicBallWeight, hnle]
    · simp_all
  have hdecomp (ω : Ω) :
      cutoffWeightedGmcBallMass P Xc γ α z R δ ω ≤
        core ω + ∑ n ∈ Finset.range (N + 1), shell n ω := by
    change (∫⁻ x in Metric.ball z R,
      ENNReal.ofReal _ ∂
        regularizedGMC P Xc γ (Real.log (1 / δ)) ω) ≤ _
    have h := cutoffWeightedGmcBallMass_le_positive_dyadic_cover
      (regularizedGMC P Xc γ (Real.log (1 / δ)) ω) γ α z R δ N
      hγ hα hR hδ hNlo
    rw [htsum ω] at h
    simpa [core, shell, cutoffDyadicBallWeight] using h
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
    _ ≤ (∫⁻ ω, ENNReal.rpow _ p ∂P) ^ (1 / p) := by
      apply ENNReal.rpow_le_rpow
      · exact lintegral_mono hpoint
      · positivity
    _ ≤ ∑ i ∈ indices, (∫⁻ ω, ENNReal.rpow _ p ∂P) ^ (1 / p) :=
      ennreal_lintegral_rpow_finset_sum_root_le indices term p hp htermMeas
    _ = _ := by
      simp [indices, term, Finset.sum_image, core, shell]

/-- The scale-free dyadic shell coefficient for a positive insertion, with a chosen uniform
annular exponent margin. -/
noncomputable def cutoffWeightedPositiveScaleRootBoundConstant
    (A : ℝ≥0∞) (γ p ε : ℝ) : ℝ≥0∞ :=
  A * (ENNReal.ofReal (((1 / 8 : ℝ)⁻¹) ^
      ((2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2) / p)) +
    ENNReal.ofReal ((2 / (1 / 8 : ℝ)) ^
      ((2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2) / p)) *
      ENNReal.ofReal ((1 / 2 : ℝ) ^ ε) *
      (1 - ENNReal.ofReal ((1 / 2 : ℝ) ^ ε))⁻¹)

end DOZZ.Proofs
