/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.FieldChaosCore
public import DOZZ.GMC.FiniteChaosMultiNegativePower
public import DOZZ.GMC.FiniteMultiMellin
public import DOZZ.Statements.GMC.FieldChaosMass
import Mathlib.Tactic

/-! Multiblock negative powers for continuum field chaos. -/

public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- A finite weighted sum of continuum chaos masses is one chaos mass with the weights summed
pointwise. -/
theorem fieldChaosMass_weighted_sum
    {Ω S κ : Type*} [MeasurableSpace Ω] [MeasurableSpace S] [Fintype κ]
    (P : Measure Ω) (Φ : Ω → S → ℝ)
    (hΦ : DOZZ.IsCenteredGaussianField P Φ)
    (ν : Measure S) (h : κ → S → ℝ≥0) (hh : ∀ k, Measurable (h k))
    (t : κ → ℝ) (γ : ℝ) (ω : Ω) :
    DOZZ.fieldChaosMass P Φ ν
        (fun x => ∑ k, Real.toNNReal (t k) * h k x) γ ω =
      ∑ k, ENNReal.ofReal (t k) * DOZZ.fieldChaosMass P Φ ν (h k) γ ω := by
  classical
  have hvar : Measurable (fun x => ∫ ω', Φ ω' x ^ 2 ∂P) := by
    simpa [DOZZ.gaussianVariance, DOZZ.gaussianCovariance, pow_two] using
      centeredGaussianField_variance_measurable P Φ hΦ
  have hsection : Measurable (Φ ω) := hΦ.1.comp (measurable_const.prodMk measurable_id)
  unfold DOZZ.fieldChaosMass
  simp_rw [ENNReal.ofNNReal_finsetSum, ENNReal.coe_mul, ENNReal.ofNNReal_toNNReal,
    Finset.sum_mul, mul_assoc]
  rw [lintegral_finsetSum]
  · congr 1
    ext k
    exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  · intro k hk
    have hw := hh k
    fun_prop

/-- The sum of several block masses has the single-field Laplace comparison whenever the
individual blocks do. -/
theorem kahane_field_multi_block_laplace
    {ΩX ΩY S κ : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY]
    [MeasurableSpace S] [Fintype κ] [Nonempty S]
    (PX : Measure ΩX) (PY : Measure ΩY)
    (Φ : ΩX → S → ℝ) (Ψ : ΩY → S → ℝ)
    (hΦ : DOZZ.IsCenteredGaussianField PX Φ)
    (hΨ : DOZZ.IsCenteredGaussianField PY Ψ)
    (ν : FiniteMeasure S) (hν : ν ≠ 0)
    (h : κ → S → ℝ≥0) (hh : ∀ k, Measurable (h k))
    (hhb : ∀ k, ∃ c : ℝ≥0, ∀ x, h k x ≤ c)
    (γ : ℝ) (t : κ → ℝ) (ht : ∀ k, 0 ≤ t k)
    (hcov : ∀ᵐ xy ∂(ν : Measure S).prod ν,
      DOZZ.gaussianCovariance PX (fun ω => Φ ω xy.1) (fun ω => Φ ω xy.2) ≤
        DOZZ.gaussianCovariance PY (fun ω => Ψ ω xy.1) (fun ω => Ψ ω xy.2))
    (hdiag : ∀ᵐ x ∂(ν : Measure S),
      DOZZ.gaussianVariance PX (fun ω => Φ ω x) ≤
        DOZZ.gaussianVariance PY (fun ω => Ψ ω x)) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (-∑ k, t k *
      (DOZZ.fieldChaosMass PX Φ (ν : Measure S) (h k) γ ω).toReal)) ∂PX ≤
      ∫⁻ ω, ENNReal.ofReal (Real.exp (-∑ k, t k *
        (DOZZ.fieldChaosMass PY Ψ (ν : Measure S) (h k) γ ω).toReal)) ∂PY := by
  classical
  let hsum  := fun x => ∑ k, Real.toNNReal (t k) * h k x
  have hsumMeas : Measurable hsum := by
    fun_prop
  have hsumBound : ∃ c : ℝ≥0, ∀ x, hsum x ≤ c := by
    classical
    choose c hc using hhb
    refine ⟨∑ k, Real.toNNReal (t k) * c k, ?_⟩
    intro x
    bound
  have hmassX ω : DOZZ.fieldChaosMass PX Φ (ν : Measure S) hsum γ ω =
      ∑ k, ENNReal.ofReal (t k) *
        DOZZ.fieldChaosMass PX Φ (ν : Measure S) (h k) γ ω :=
    fieldChaosMass_weighted_sum PX Φ hΦ (ν : Measure S) h hh t γ ω
  have hmassY ω : DOZZ.fieldChaosMass PY Ψ (ν : Measure S) hsum γ ω =
      ∑ k, ENNReal.ofReal (t k) *
        DOZZ.fieldChaosMass PY Ψ (ν : Measure S) (h k) γ ω :=
    fieldChaosMass_weighted_sum PY Ψ hΨ (ν : Measure S) h hh t γ ω
  have hmassFiniteX (k : κ) :=
    centeredGaussianField_fieldChaosMass_ne_top_ae PX Φ hΦ ν (h k) (hh k) (hhb k) γ
  have hmassFiniteY (k : κ) :=
    centeredGaussianField_fieldChaosMass_ne_top_ae PY Ψ hΨ ν (h k) (hh k) (hhb k) γ
  have hmassXtoReal : ∀ᵐ ω ∂PX,
      (DOZZ.fieldChaosMass PX Φ (ν : Measure S) hsum γ ω).toReal =
        ∑ k, t k * (DOZZ.fieldChaosMass PX Φ (ν : Measure S) (h k) γ ω).toReal := by
    filter_upwards [ae_all_iff.2 hmassFiniteX] with ω hω
    rw [hmassX ω, ENNReal.toReal_sum]
    · simp_all
    · intro k hk
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hω k)
  have hmassYtoReal : ∀ᵐ ω ∂PY,
      (DOZZ.fieldChaosMass PY Ψ (ν : Measure S) hsum γ ω).toReal =
        ∑ k, t k * (DOZZ.fieldChaosMass PY Ψ (ν : Measure S) (h k) γ ω).toReal := by
    filter_upwards [ae_all_iff.2 hmassFiniteY] with ω hω
    rw [hmassY ω, ENNReal.toReal_sum]
    · simp_all
    · intro k hk
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hω k)
  have hLap := kahane_field_laplace_of_nonzero_finite_measure_eq
    PX PY Φ Ψ hΦ hΨ ν hν hsum hsumMeas hsumBound γ 1 (by norm_num)
    hcov hdiag
  calc
    _ = ∫⁻ ω, ENNReal.ofReal (Real.exp
          (-(DOZZ.fieldChaosMass PX Φ (ν : Measure S) hsum γ ω).toReal)) ∂PX := by
            apply lintegral_congr_ae
            filter_upwards [hmassXtoReal] with ω hω
            rw [hω]
    _ ≤ ∫⁻ ω, ENNReal.ofReal (Real.exp
          (-(DOZZ.fieldChaosMass PY Ψ (ν : Measure S) hsum γ ω).toReal)) ∂PY := by
            simpa using hLap
    _ = _ := by
          apply lintegral_congr_ae
          filter_upwards [hmassYtoReal] with ω hω
          rw [hω]

/-- The continuum multiblock negative-power comparison follows by taking the Mellin transform of
the joint Laplace comparison for positive linear combinations of block masses. -/
theorem kahane_field_multi_negative_power
    {ΩX ΩY S κ : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY]
    [MeasurableSpace S] [Fintype κ]
    (PX : Measure ΩX) (PY : Measure ΩY) (Φ : ΩX → S → ℝ) (Ψ : ΩY → S → ℝ)
    (hΦ : DOZZ.IsCenteredGaussianField PX Φ) (hΨ : DOZZ.IsCenteredGaussianField PY Ψ)
    (ν : Measure S) [IsFiniteMeasure ν] (h : κ → S → ℝ≥0)
    (hh : ∀ k, Measurable (h k))
    (hhb : ∀ k, ∃ c : ℝ≥0, ∀ x, h k x ≤ c)
    (γ : ℝ) (q : κ → ℝ) (hq : ∀ k, 0 ≤ q k)
    (hcov : ∀ᵐ xy ∂ν.prod ν,
      ∫ ω, Φ ω xy.1 * Φ ω xy.2 ∂PX ≤ ∫ ω, Ψ ω xy.1 * Ψ ω xy.2 ∂PY)
    (hdiag : ∀ᵐ x ∂ν,
      ∫ ω, Φ ω x ^ 2 ∂PX ≤ ∫ ω, Ψ ω x ^ 2 ∂PY) :
    ∫⁻ ω, ∏ k, ENNReal.rpow (DOZZ.fieldChaosMass PX Φ ν (h k) γ ω) (-q k) ∂PX ≤
      ∫⁻ ω, ∏ k, ENNReal.rpow (DOZZ.fieldChaosMass PY Ψ ν (h k) γ ω) (-q k) ∂PY := by
  classical
  let := (hΦ.2 0 (fun i : Fin 0 => Fin.elim0 i)).1
  let := (hΨ.2 0 (fun i : Fin 0 => Fin.elim0 i)).1
  by_cases hνzero : ν = 0
  · simp [DOZZ.fieldChaosMass, hνzero]
  let νf : FiniteMeasure S := ⟨ν, inferInstance⟩
  have hνf : νf ≠ 0 := by
    intro hzero
    exact hνzero (congrArg (fun μ : FiniteMeasure S => (μ : Measure S)) hzero)
  have : Nonempty S := by
    obtain ⟨x, _⟩ := nonempty_of_measure_ne_zero (Measure.measure_univ_ne_zero.mpr hνzero)
    exact ⟨x⟩
  let K := {k : κ // 0 < q k}
  have hprod (M : κ → ℝ≥0∞) : (∏ k, (M k) ^ (-q k)) =
      ∏ k : K, (M k.val) ^ (-q k.val) := by
    rw [← Fintype.prod_subtype_mul_prod_subtype (fun k => 0 < q k)]
    have hinactive (k : {k : κ // ¬0 < q k}) : (M k.val) ^ (-q k.val) = 1 := by
      have hz := le_antisymm (le_of_not_gt k.property) (hq k.val)
      simp [hz]
    simp [hinactive, K]
  let MX : ΩX → K → ℝ≥0∞ := fun ω k => DOZZ.fieldChaosMass PX Φ ν (h k.val) γ ω
  let MY : ΩY → K → ℝ≥0∞ := fun ω k => DOZZ.fieldChaosMass PY Ψ ν (h k.val) γ ω
  let mX := fun ω k => (MX ω k).toReal
  let mY := fun ω k => (MY ω k).toReal
  have hmX (k : K) : Measurable (fun ω => mX ω k) :=
    (centeredGaussianField_fieldChaosMass_measurable PX Φ hΦ νf (h k.val) (hh k.val) γ).ennreal_toReal
  have hmY (k : K) : Measurable (fun ω => mY ω k) :=
    (centeredGaussianField_fieldChaosMass_measurable PY Ψ hΨ νf (h k.val) (hh k.val) γ).ennreal_toReal
  have hrepX : ∀ᵐ ω ∂PX, ∀ k : K, ENNReal.ofReal (mX ω k) = MX ω k := by
    apply ae_all_iff.2
    intro k
    filter_upwards [centeredGaussianField_fieldChaosMass_ne_top_ae
      PX Φ hΦ νf (h k.val) (hh k.val) (hhb k.val) γ] with ω hω
    exact ENNReal.ofReal_toReal hω
  have hrepY : ∀ᵐ ω ∂PY, ∀ k : K, ENNReal.ofReal (mY ω k) = MY ω k := by
    apply ae_all_iff.2
    intro k
    filter_upwards [centeredGaussianField_fieldChaosMass_ne_top_ae
      PY Ψ hΨ νf (h k.val) (hh k.val) (hhb k.val) γ] with ω hω
    exact ENNReal.ofReal_toReal hω
  have hIX : ∫⁻ ω, ∏ k, (DOZZ.fieldChaosMass PX Φ ν (h k) γ ω) ^ (-q k) ∂PX =
      ∫⁻ ω, ∏ k : K, (ENNReal.ofReal (mX ω k)) ^ (-q k.val) ∂PX := by
    apply lintegral_congr_ae
    filter_upwards [hrepX] with ω hω
    simp only [hprod, hω]
    rfl
  have hIY : ∫⁻ ω, ∏ k, (DOZZ.fieldChaosMass PY Ψ ν (h k) γ ω) ^ (-q k) ∂PY =
      ∫⁻ ω, ∏ k : K, (ENNReal.ofReal (mY ω k)) ^ (-q k.val) ∂PY := by
    apply lintegral_congr_ae
    filter_upwards [hrepY] with ω hω
    simp only [hprod, hω]
    rfl
  change (∫⁻ ω, ∏ k, (DOZZ.fieldChaosMass PX Φ ν (h k) γ ω) ^ (-q k) ∂PX) ≤
    ∫⁻ ω, ∏ k, (DOZZ.fieldChaosMass PY Ψ ν (h k) γ ω) ^ (-q k) ∂PY
  rw [hIX, hIY,
    multi_rpow_neg_lintegral_eq_weighted_laplace PX mX (fun _ _ => ENNReal.toReal_nonneg)
      hmX (fun k => q k.val) (fun k => k.property),
    multi_rpow_neg_lintegral_eq_weighted_laplace PY mY (fun _ _ => ENNReal.toReal_nonneg)
      hmY (fun k => q k.val) (fun k => k.property)]
  apply mul_le_mul_right
  apply lintegral_mono_ae
  filter_upwards [ae_pi_Ioi_pos (κ := K)] with t ht
  apply mul_le_mul_right
  apply kahane_field_multi_block_laplace PX PY Φ Ψ hΦ hΨ νf hνf
    (fun k x => h k.val x) (fun k => hh k.val) (fun k => hhb k.val)
    γ t (fun k => (ht k).le) hcov
  filter_upwards [hdiag] with x hx
  simpa [DOZZ.gaussianVariance, DOZZ.gaussianCovariance, pow_two] using hx


end DOZZ.Proofs
