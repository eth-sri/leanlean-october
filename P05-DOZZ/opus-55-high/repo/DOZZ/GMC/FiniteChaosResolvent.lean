/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Integral.Gamma
public import Mathlib.MeasureTheory.Integral.Prod

/-! Resolvent comparisons obtained by integrating the finite-chaos Laplace comparison. -/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace DOZZ.Proofs

/-- The reciprocal of a positive scalar is the Laplace integral of its negative exponential. -/
theorem ofReal_inv_eq_lintegral_exp_neg_mul {u : ℝ} (hu : 0 < u) :
    ENNReal.ofReal (u⁻¹) =
      ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(u * s))) ∂volume := by
  have hbase : IntegrableOn (fun s : ℝ => Real.exp (-s)) (Ioi 0) volume := by
    simpa [Real.rpow_zero] using
      (Real.GammaIntegral_convergent (show 0 < 1 by norm_num))
  have hscaled : IntegrableOn (fun s : ℝ => Real.exp (-(u * s)))
      (Ioi 0) volume := by
    have hbase' : IntegrableOn (fun s : ℝ => Real.exp (-s)) (Ioi (u * 0)) volume := by
      simp_all
    simpa using
      (integrableOn_Ioi_comp_mul_left_iff (fun s : ℝ => Real.exp (-s)) 0 hu).2 hbase'
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi 0)]
      (fun s : ℝ => Real.exp (-(u * s))) := by
    filter_upwards [] with s
    positivity
  have hlin := ofReal_integral_eq_lintegral_ofReal hscaled hnonneg
  have hint : (∫ s in Ioi 0, Real.exp (-(u * s)) ∂volume) = u⁻¹ := by
    convert (integral_exp_neg_mul_rpow (p := 1) (b := u) zero_lt_one hu) using 1 <;>
      simp [Real.Gamma_add_one, Real.Gamma_one, Real.rpow_one, Real.rpow_neg_one]
  simp_all

/-- Laplace-transform order implies the same order for the positive resolvent kernel. -/
theorem laplace_order_resolvent
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω') [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (m : Ω → ℝ) (m' : Ω' → ℝ)
    (hm : AEMeasurable m P) (hm' : AEMeasurable m' P')
    (hm0 : ∀ ω, 0 ≤ m ω) (hm'0 : ∀ ω, 0 ≤ m' ω)
    (hLap : ∀ s : ℝ, 0 ≤ s →
      ∫⁻ ω, ENNReal.ofReal (Real.exp (-(s * m ω))) ∂P ≤
        ∫⁻ ω', ENNReal.ofReal (Real.exp (-(s * m' ω'))) ∂P')
    (t : ℝ) (ht : 0 < t) :
    ∫⁻ ω, ENNReal.ofReal ((t + m ω)⁻¹) ∂P ≤
      ∫⁻ ω', ENNReal.ofReal ((t + m' ω')⁻¹) ∂P' := by
  let ν : Measure ℝ := volume.restrict (Ioi 0)
  let f : Ω → ℝ → ℝ≥0∞ := fun ω s =>
    ENNReal.ofReal (Real.exp (-(s * (t + m ω))))
  let f' : Ω' → ℝ → ℝ≥0∞ := fun ω s =>
    ENNReal.ofReal (Real.exp (-(s * (t + m' ω))))
  have hf : AEMeasurable (Function.uncurry f) (P.prod ν) := by
    fun_prop
  have hf' : AEMeasurable (Function.uncurry f') (P'.prod ν) := by
    fun_prop
  have hpoint (ω : Ω) :
      ENNReal.ofReal ((t + m ω)⁻¹) = ∫⁻ s, f ω s ∂ν := by
    simpa [f, ν, mul_comm] using ofReal_inv_eq_lintegral_exp_neg_mul
      (add_pos_of_pos_of_nonneg ht (hm0 ω))
  have hpoint' (ω : Ω') :
      ENNReal.ofReal ((t + m' ω)⁻¹) = ∫⁻ s, f' ω s ∂ν := by
    simpa [f', ν, mul_comm] using ofReal_inv_eq_lintegral_exp_neg_mul
      (add_pos_of_pos_of_nonneg ht (hm'0 ω))
  rw [show (∫⁻ ω, ENNReal.ofReal ((t + m ω)⁻¹) ∂P) =
      ∫⁻ ω, ∫⁻ s, f ω s ∂ν ∂P by
        simp_all]
  rw [show (∫⁻ ω', ENNReal.ofReal ((t + m' ω')⁻¹) ∂P') =
      ∫⁻ ω', ∫⁻ s, f' ω' s ∂ν ∂P' by
        simp_all]
  rw [lintegral_lintegral_swap hf, lintegral_lintegral_swap hf']
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  have hfactor : (∫⁻ ω, f ω s ∂P) =
      ENNReal.ofReal (Real.exp (-(s * t))) *
        (∫⁻ ω, ENNReal.ofReal (Real.exp (-(s * m ω))) ∂P) := by
    rw [show (fun ω => f ω s) = fun ω =>
        ENNReal.ofReal _ *
          ENNReal.ofReal _ by
          funext ω
          dsimp [f]
          rw [show -(s * (t + m ω)) = -(s * t) + -(s * m ω) by ring,
            Real.exp_add, ← ENNReal.ofReal_mul (Real.exp_nonneg _)] ]
    exact lintegral_const_mul' _ _ (ENNReal.ofReal_ne_top)
  have hfactor' : (∫⁻ ω', f' ω' s ∂P') =
      ENNReal.ofReal (Real.exp (-(s * t))) *
        (∫⁻ ω', ENNReal.ofReal (Real.exp (-(s * m' ω'))) ∂P') := by
    rw [show (fun ω' => f' ω' s) = fun ω' =>
        ENNReal.ofReal _ *
          ENNReal.ofReal _ by
          funext ω'
          dsimp [f']
          rw [show -(s * (t + m' ω')) = -(s * t) + -(s * m' ω') by ring,
            Real.exp_add, ← ENNReal.ofReal_mul (Real.exp_nonneg _)] ]
    exact lintegral_const_mul' _ _ (ENNReal.ofReal_ne_top)
  rw [hfactor, hfactor']
  gcongr
  exact hLap s (le_of_lt hs)

/-- A resolvent fraction is integrable on a probability space because its reciprocal part is
bounded by the positive scalar parameter. -/
theorem resolvent_fraction_integrable
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Ω → ℝ) (hm : AEMeasurable m P) (hm0 : ∀ ω, 0 ≤ m ω)
    (t : ℝ) (ht : 0 < t) :
    Integrable (fun ω => m ω / (t + m ω)) P := by
  have hinvMeas : AEMeasurable (fun ω => (t + m ω)⁻¹) P := by
    fun_prop
  have hinvBound (ω : Ω) : ‖(t + m ω)⁻¹‖ ≤ t⁻¹ := by
    rw [Real.norm_of_nonneg (inv_nonneg.mpr (by grind))]
    bound
  have hinvInt :=
    (integrable_const _).mono' hinvMeas.aestronglyMeasurable
      (Filter.Eventually.of_forall hinvBound)
  have heq : (fun ω => m ω / (t + m ω)) =
      fun ω => 1 - t * (t + m ω)⁻¹ := by
    grind
  rw [heq]
  fun_prop

/-- The associated bounded fraction has the reverse expectation order. Its expectation is
`1 - t E[(t + m)⁻¹]`, and the probability-space means of the constant terms agree. -/
theorem laplace_order_fraction_expectation
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω') [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (m : Ω → ℝ) (m' : Ω' → ℝ)
    (hm : AEMeasurable m P) (hm' : AEMeasurable m' P')
    (hm0 : ∀ ω, 0 ≤ m ω) (hm'0 : ∀ ω, 0 ≤ m' ω)
    (hLap : ∀ s : ℝ, 0 ≤ s →
      ∫⁻ ω, ENNReal.ofReal (Real.exp (-(s * m ω))) ∂P ≤
        ∫⁻ ω', ENNReal.ofReal (Real.exp (-(s * m' ω'))) ∂P')
    (t : ℝ) (ht : 0 < t) :
    ∫ ω, m ω / (t + m ω) ∂P ≥ ∫ ω', m' ω' / (t + m' ω') ∂P' := by
  have hinvMeas : AEMeasurable (fun ω => (t + m ω)⁻¹) P := by
    fun_prop
  have hinvMeas' : AEMeasurable (fun ω' => (t + m' ω')⁻¹) P' := by
    fun_prop
  have hinvBound (ω : Ω) : ‖(t + m ω)⁻¹‖ ≤ t⁻¹ := by
    rw [Real.norm_of_nonneg (inv_nonneg.mpr (by grind))]
    bound
  have hinvBound' (ω' : Ω') : ‖(t + m' ω')⁻¹‖ ≤ t⁻¹ := by
    rw [Real.norm_of_nonneg (inv_nonneg.mpr (by grind))]
    bound
  have hinvInt :=
    (integrable_const _).mono' hinvMeas.aestronglyMeasurable
      (Filter.Eventually.of_forall hinvBound)
  have hinvInt' :=
    (integrable_const _).mono' hinvMeas'.aestronglyMeasurable
      (Filter.Eventually.of_forall hinvBound')
  have hInvNonneg : ∀ ω, 0 ≤ (t + m ω)⁻¹ := fun ω =>
    inv_nonneg.mpr (by grind)
  have hInvNonneg' : ∀ ω', 0 ≤ (t + m' ω')⁻¹ := fun ω' =>
    inv_nonneg.mpr (by grind)
  have hlin :=
    ofReal_integral_eq_lintegral_ofReal hinvInt
      (Filter.Eventually.of_forall hInvNonneg)
  have hlin' :=
    ofReal_integral_eq_lintegral_ofReal hinvInt'
      (Filter.Eventually.of_forall hInvNonneg')
  have hInvOrdENN : ENNReal.ofReal (∫ ω, (t + m ω)⁻¹ ∂P) ≤
      ENNReal.ofReal (∫ ω', (t + m' ω')⁻¹ ∂P') := by
    rw [hlin, hlin']
    exact (laplace_order_resolvent P P' m m' hm hm' hm0 hm'0 hLap t ht)
  have hInvMeanNonneg : 0 ≤ ∫ ω', (t + m' ω')⁻¹ ∂P' :=
    integral_nonneg_of_ae (Filter.Eventually.of_forall hInvNonneg')
  have hInvOrd :=
    (ENNReal.ofReal_le_ofReal_iff hInvMeanNonneg).mp hInvOrdENN
  have hfracInt : Integrable (fun ω => m ω / (t + m ω)) P := by
    have heq : (fun ω => m ω / (t + m ω)) =
        fun ω => 1 - t * (t + m ω)⁻¹ := by
      funext ω
      have hden : t + m ω ≠ 0 := by grind
      field_simp [hden]
      ring
    rw [heq]
    exact (integrable_const 1).sub (hinvInt.const_mul t)
  have hfracInt' : Integrable (fun ω' => m' ω' / (t + m' ω')) P' := by
    have heq : (fun ω' => m' ω' / (t + m' ω')) =
        fun ω' => 1 - t * (t + m' ω')⁻¹ := by
      funext ω'
      have hden : t + m' ω' ≠ 0 := by grind
      field_simp [hden]
      ring
    rw [heq]
    exact (integrable_const (1 : ℝ)).sub (hinvInt'.const_mul t)
  have hfracMean : (∫ ω, m ω / (t + m ω) ∂P) =
      1 - t * ∫ ω, (t + m ω)⁻¹ ∂P := by
    calc
      _ = ∫ ω, (1 - t * (t + m ω)⁻¹) ∂P := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun ω => by
          have hden : t + m ω ≠ 0 := by grind
          field_simp [hden]
          ring
      _ = _ := by
        have hconst : Integrable (fun _ : Ω => (1 : ℝ)) P := integrable_const 1
        rw [integral_sub hconst (hinvInt.const_mul t), integral_const, integral_const_mul]
        simp
  have hfracMean' : (∫ ω', m' ω' / (t + m' ω') ∂P') =
      1 - t * ∫ ω', (t + m' ω')⁻¹ ∂P' := by
    calc
      _ = ∫ ω', (1 - t * (t + m' ω')⁻¹) ∂P' := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun ω' => by
          have hden : t + m' ω' ≠ 0 := by grind
          field_simp [hden]
          ring
      _ = _ := by
        have hconst : Integrable (fun _ : Ω' => (1 : ℝ)) P' := integrable_const 1
        rw [integral_sub hconst (hinvInt'.const_mul t), integral_const, integral_const_mul]
        simp
  rw [hfracMean, hfracMean']
  nlinarith

end DOZZ.Proofs
