/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.GMC.FieldChaosConvexOrder

public import DOZZ.GMC.FieldChaosFiniteness
public import DOZZ.GMC.FiniteMultiMellin
public import DOZZ.Statements.GMC.FieldChaosMass

/-! Multiblock negative powers for continuum field chaos. -/

@[expose] public section

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
  let wick  := fun x => ENNReal.ofReal (Real.exp
    (γ * Φ ω x - γ ^ 2 / 2 * ∫ ω', Φ ω' x ^ 2 ∂P))
  let hsum  := fun x => ∑ k, Real.toNNReal (t k) * h k x
  have hvar : Measurable (fun x => ∫ ω', Φ ω' x ^ 2 ∂P) := by
    simpa [DOZZ.gaussianVariance, DOZZ.gaussianCovariance, pow_two] using
      centeredGaussianField_variance_measurable P Φ hΦ
  have hsection : Measurable (fun x => Φ ω x) := hΦ.1.comp (measurable_const.prodMk measurable_id)
  have hwick : Measurable wick := by
    dsimp [wick]
    fun_prop
  have hkernel (x : S) :
      ENNReal.ofNNReal (hsum x) * wick x =
        ∑ k, ENNReal.ofReal (t k) *
          (ENNReal.ofNNReal (h k x) * wick x) := by
    dsimp [hsum, wick]
    rw [ENNReal.ofNNReal_finsetSum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    rw [ENNReal.coe_mul, ENNReal.ofNNReal_toNNReal]
    ring
  have hweightWickMeas (k : κ) : Measurable
      (fun x => ENNReal.ofNNReal (h k x) * wick x) := by
    fun_prop
  have htermMeas (k : κ) := (measurable_const : Measurable (fun _ : S => ENNReal.ofReal (t k))).mul
      (hweightWickMeas k)
  calc
    _ = ∫⁻ x, ∑ k, ENNReal.ofReal (t k) *
          (ENNReal.ofNNReal (h k x) * wick x) ∂ν := by
            unfold DOZZ.fieldChaosMass
            apply lintegral_congr_ae
            exact ae_of_all ν hkernel
    _ = ∑ k, ∫⁻ x, ENNReal.ofReal (t k) *
          (ENNReal.ofNNReal (h k x) * wick x) ∂ν := by
            apply lintegral_finsetSum' Finset.univ
            intro k hk
            exact (htermMeas k).aemeasurable
    _ = ∑ k, ENNReal.ofReal (t k) *
          DOZZ.fieldChaosMass P Φ ν (h k) γ ω := by
            apply Finset.sum_congr rfl
            intro k hk
            change ∫⁻ x, ENNReal.ofReal (t k) *
              (ENNReal.ofNNReal (h k x) * wick x) ∂ν =
              ENNReal.ofReal (t k) * ∫⁻ x,
                ENNReal.ofNNReal (h k x) * wick x ∂ν
            rw [lintegral_const_mul'' _ (hweightWickMeas k).aemeasurable]

section
variable {ΩX ΩY S κ : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY] [MeasurableSpace S] [Fintype κ]

private theorem fieldChaosMass_ne_top_ae
    {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (P : Measure Ω) (Φ : Ω → S → ℝ) (hΦ : DOZZ.IsCenteredGaussianField P Φ)
    (ν : Measure S) [IsFiniteMeasure ν] (h : S → ℝ≥0) (hh : Measurable h)
    (hhb : ∃ c, ∀ x, h x ≤ c) (γ : ℝ) :
    ∀ᵐ ω ∂P, DOZZ.fieldChaosMass P Φ ν h γ ω ≠ ∞ := by
  by_cases hν : ν = 0
  · simp [hν, DOZZ.fieldChaosMass]
  have : Nonempty S := by
    obtain ⟨x, _⟩ := nonempty_of_measure_ne_zero (Measure.measure_univ_ne_zero.mpr hν)
    exact ⟨x⟩
  exact centeredGaussianField_fieldChaosMass_ne_top_ae P Φ hΦ ⟨ν, inferInstance⟩ h hh hhb γ

private theorem fieldChaosMass_weighted_laplace
    {Ω S κ : Type*} [MeasurableSpace Ω] [MeasurableSpace S] [Nonempty S] [Fintype κ]
    (P : Measure Ω) (Φ : Ω → S → ℝ) (hΦ : DOZZ.IsCenteredGaussianField P Φ)
    (ν : FiniteMeasure S) (h : κ → S → ℝ≥0) (hh : ∀ k, Measurable (h k))
    (hhb : ∀ k, ∃ c : ℝ≥0, ∀ x, h k x ≤ c)
    (t : κ → ℝ) (ht : ∀ k, 0 ≤ t k) (γ : ℝ) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp (-(DOZZ.fieldChaosMass P Φ ν
      (fun x => ∑ k, Real.toNNReal (t k) * h k x) γ ω).toReal)) ∂P) =
      ∫⁻ ω, ENNReal.ofReal (Real.exp (-∑ k, t k * (DOZZ.fieldChaosMass P Φ ν (h k) γ ω).toReal)) ∂P := by
  apply lintegral_congr_ae
  filter_upwards [ae_all_iff.mpr (fun k => centeredGaussianField_fieldChaosMass_ne_top_ae
    P Φ hΦ ν (h k) (hh k) (hhb k) γ)] with ω hω
  rw [fieldChaosMass_weighted_sum P Φ hΦ ν h hh t γ ω, ENNReal.toReal_sum]
  · simp_rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (ht _)]
  · exact fun k _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hω k)

section
variable (PX : Measure ΩX) (PY : Measure ΩY) (Φ : ΩX → S → ℝ) (Ψ : ΩY → S → ℝ)
  (hΦ : DOZZ.IsCenteredGaussianField PX Φ) (hΨ : DOZZ.IsCenteredGaussianField PY Ψ) (ν : Measure S)
  [IsFiniteMeasure ν] (h : κ → S → ℝ≥0) (hh : ∀ k, Measurable (h k))
  (hhb : ∀ k, ∃ c : ℝ≥0, ∀ x, h k x ≤ c) (γ : ℝ)
include hΦ hΨ hh hhb

/-- Comparison of the joint Laplace transforms is scalar comparison with the weights summed. -/
private theorem kahane_field_multi_block_laplace (t : κ → ℝ) (ht : ∀ k, 0 ≤ t k)
    (hcov : ∀ᵐ xy ∂ν.prod ν,
      ∫ ω, Φ ω xy.1 * Φ ω xy.2 ∂PX ≤ ∫ ω, Ψ ω xy.1 * Ψ ω xy.2 ∂PY)
    (hdiag : ∀ᵐ x ∂ν, ∫ ω, Φ ω x ^ 2 ∂PX ≤ ∫ ω, Ψ ω x ^ 2 ∂PY) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (-∑ k, t k * (DOZZ.fieldChaosMass PX Φ ν (h k) γ ω).toReal)) ∂PX ≤
      ∫⁻ ω, ENNReal.ofReal (Real.exp (-∑ k, t k * (DOZZ.fieldChaosMass PY Ψ ν (h k) γ ω).toReal)) ∂PY := by
  let := (hΦ.2 0 Fin.elim0).1
  let := (hΨ.2 0 Fin.elim0).1
  by_cases hν : ν = 0
  · simp [hν, DOZZ.fieldChaosMass]
  let νf : FiniteMeasure S := ⟨ν, inferInstance⟩
  have hνf : νf ≠ 0 := fun h => hν (congrArg FiniteMeasure.toMeasure h)
  have : Nonempty S := by
    obtain ⟨x, _⟩ := nonempty_of_measure_ne_zero (Measure.measure_univ_ne_zero.mpr hν)
    exact ⟨x⟩
  let w (x : S) := ∑ k, Real.toNNReal (t k) * h k x
  have hwb : ∃ b : ℝ≥0, ∀ x, w x ≤ b := by
    choose c hc using hhb
    exact ⟨∑ k, Real.toNNReal (t k) * c k, fun x => Finset.sum_le_sum fun k _ =>
      mul_le_mul_of_nonneg_left (hc k x) (by positivity)⟩
  have hνeq : (νf : Measure S) = ν := rfl
  rw [← hνeq, ← fieldChaosMass_weighted_laplace PX Φ hΦ νf h hh hhb t ht γ,
    ← fieldChaosMass_weighted_laplace PY Ψ hΨ νf h hh hhb t ht γ]
  simpa using kahane_field_laplace_of_nonzero_finite_measure_eq PX PY Φ Ψ hΦ hΨ
    νf hνf w (by unfold w; fun_prop) hwb γ 1 zero_le_one hcov
      (by rw [hνeq]; simpa [DOZZ.gaussianVariance, DOZZ.gaussianCovariance, pow_two] using hdiag)

/-- The continuum multiblock negative-power comparison follows by taking the Mellin transform of
 the joint Laplace comparison for positive linear combinations of block masses. -/
theorem kahane_field_multi_negative_power (q : κ → ℝ) (hq : ∀ k, 0 ≤ q k)
    (hcov : ∀ᵐ xy ∂ν.prod ν,
      ∫ ω, Φ ω xy.1 * Φ ω xy.2 ∂PX ≤ ∫ ω, Ψ ω xy.1 * Ψ ω xy.2 ∂PY)
    (hdiag : ∀ᵐ x ∂ν,
      ∫ ω, Φ ω x ^ 2 ∂PX ≤ ∫ ω, Ψ ω x ^ 2 ∂PY) :
    ∫⁻ ω, ∏ k, ENNReal.rpow (DOZZ.fieldChaosMass PX Φ ν (h k) γ ω) (-q k) ∂PX ≤
      ∫⁻ ω, ∏ k, ENNReal.rpow (DOZZ.fieldChaosMass PY Ψ ν (h k) γ ω) (-q k) ∂PY := by
  classical
  let := (hΦ.2 0 Fin.elim0).1
  let := (hΨ.2 0 Fin.elim0).1
  let p (k : κ) := 0 < q k
  let K := {k // p k}
  let _ : Fintype K := Subtype.fintype p
  have hprod (u : κ → ℝ≥0∞) : ∏ k, ENNReal.rpow (u k) (-q k) = ∏ k : K, u k.val ^ (-q k.val) := by
    have hz (k : {k // ¬ p k}) : q k.val = 0 := le_antisymm (le_of_not_gt k.property) (hq k.val)
    rw [← Fintype.prod_subtype_mul_prod_subtype p (fun k => ENNReal.rpow (u k) (-q k))]
    simp [hz, K]
  simp_rw [hprod]
  rw [lintegral_prod_rpow_neg_eq_jointLaplace PX _
    (fun k : K => centeredGaussianField_fieldChaosMass_measurable PX Φ hΦ ν (h k.val) (hh k.val) γ)
    (fun k : K => fieldChaosMass_ne_top_ae PX Φ hΦ ν (h k.val) (hh k.val) (hhb k.val) γ) _ Subtype.property,
    lintegral_prod_rpow_neg_eq_jointLaplace PY _
    (fun k : K => centeredGaussianField_fieldChaosMass_measurable PY Ψ hΨ ν (h k.val) (hh k.val) γ)
    (fun k : K => fieldChaosMass_ne_top_ae PY Ψ hΨ ν (h k.val) (hh k.val) (hhb k.val) γ) _ Subtype.property]
  apply lintegral_mono_ae
  have hpos : ∀ᵐ t ∂Measure.pi (fun _ : K => volume.restrict (Ioi (0 : ℝ))), ∀ k, 0 < t k := by
    exact ae_all_iff.mpr fun k => Measure.tendsto_eval_ae_ae.eventually (ae_restrict_mem measurableSet_Ioi)
  filter_upwards [hpos] with t ht
  exact mul_le_mul_right (kahane_field_multi_block_laplace PX PY Φ Ψ hΦ hΨ ν
    (fun k : K => h k.val) (fun k => hh k.val) (fun k => hhb k.val) γ t (fun k => (ht k).le) hcov hdiag) _

end

end

/-- Kahane's comparison for all nonpositive powers of continuum field chaos. -/
theorem kahane_field_power_nonpos
    {ΩX ΩY S : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY] [MeasurableSpace S]
    (PX : Measure ΩX) (PY : Measure ΩY) (Φ : ΩX → S → ℝ) (Ψ : ΩY → S → ℝ)
    (hΦ : DOZZ.IsCenteredGaussianField PX Φ) (hΨ : DOZZ.IsCenteredGaussianField PY Ψ)
    (ν : Measure S) [IsFiniteMeasure ν] (h : S → ℝ≥0) (hh : Measurable h)
    (hhb : ∃ c : ℝ≥0, ∀ x, h x ≤ c) (γ p : ℝ) (hp : p ≤ 0)
    (hcov : ∀ᵐ xy ∂ν.prod ν,
      ∫ ω, Φ ω xy.1 * Φ ω xy.2 ∂PX ≤ ∫ ω, Ψ ω xy.1 * Ψ ω xy.2 ∂PY)
    (hdiag : ∀ᵐ x ∂ν,
      ∫ ω, Φ ω x ^ 2 ∂PX ≤ ∫ ω, Ψ ω x ^ 2 ∂PY) :
    ∫⁻ ω, DOZZ.fieldChaosMass PX Φ ν h γ ω ^ p ∂PX ≤
      ∫⁻ ω, DOZZ.fieldChaosMass PY Ψ ν h γ ω ^ p ∂PY := by
  simpa using kahane_field_multi_negative_power PX PY Φ Ψ hΦ hΨ ν (fun _ : Fin 1 => h)
    (fun _ => hh) (fun _ => hhb) γ (fun _ => -p) (fun _ => neg_nonneg.mpr hp) hcov hdiag


end DOZZ.Proofs
