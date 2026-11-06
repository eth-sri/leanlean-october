/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-/
module

public import DOZZ.GMC.Construction.RootedCircleTilt
public import DOZZ.GMC.Construction.RegularizedGMCExpectedMeasure

/-! Spatial integration of a circle root tilt with a fixed limiting chaos mark. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs
section
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
section
variable (hX : IsEquatorGFF P X)
include hX

/-- Spatial integration of the Wick root density is integration against the cutoff chaos. -/
theorem regularizedGMC_root_sample_lintegral
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (γ r : ℝ) (Ψ : ℂ × Ω → ℝ≥0∞) (hΨ : Measurable Ψ) :
    (∫⁻ ω, ∫⁻ u, Ψ (u, ω) ∂regularizedGMC P Xc γ r ω ∂P) =
      ∫⁻ u, ∫⁻ ω, ENNReal.ofReal (Real.exp (γ * Xc ω u r - γ ^ 2 / 2 *
        ∫ ω', Xc ω' u r ^ 2 ∂P)) * Ψ (u, ω) ∂P ∂gmcReferenceMeasure := by
  let _ := hX.1
  let V : ℂ → ℝ := fun u => ∫ ω, Xc ω u r ^ 2 ∂P
  let b : ℂ → ℝ≥0∞ := fun u => ENNReal.ofReal (normPlus u ^ (-4 : ℝ))
  let w : ℂ × Ω → ℝ≥0∞ := fun q => ENNReal.ofReal
    (Real.exp (γ * Xc q.2 q.1 r - γ ^ 2 / 2 * V q.1))
  have hV : Measurable V := by
    have hg : Measurable (fun q : ℂ × Ω => Xc q.2 q.1 r ^ 2) :=
      ((hXc.1 r).comp measurable_swap).pow_const 2
    exact hg.stronglyMeasurable.integral_prod_right.measurable
  have hn : Measurable normPlus :=
    measurable_const.max measurable_norm
  have hb : Measurable b := by
    fun_prop
  have hw : Measurable w := by
    have hx : Measurable (fun q : ℂ × Ω => Xc q.2 q.1 r) :=
      (hXc.1 r).comp measurable_swap
    have hv : Measurable (fun q : ℂ × Ω => V q.1) := hV.comp measurable_fst
    exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      ((measurable_const.mul hx).sub (measurable_const.mul hv)))
  have hprod : Measurable (fun q : Ω × ℂ => b q.2 * w (q.2, q.1) * Ψ (q.2, q.1)) :=
    by fun_prop
  have hinner : Measurable (fun u => ∫⁻ ω, w (u, ω) * Ψ (u, ω) ∂P) :=
    by fun_prop
  calc
    _ = ∫⁻ ω, ∫⁻ u, b u * w (u, ω) * Ψ (u, ω) ∂volume ∂P := by
      apply lintegral_congr
      intro ω
      have hd : Measurable (fun u => ENNReal.ofReal
          (Real.exp (γ * Xc ω u r - γ ^ 2 / 2 * V u) * normPlus u ^ (-4 : ℝ))) := by
        have hx : Measurable (fun u => Xc ω u r) :=
          (hXc.1 r).comp (measurable_const.prodMk measurable_id)
        fun_prop
      have hs : Measurable (fun u => Ψ (u, ω)) :=
        by fun_prop
      change (∫⁻ u, Ψ (u, ω) ∂volume.withDensity (fun u => ENNReal.ofReal
        (Real.exp (γ * Xc ω u r - γ ^ 2 / 2 * V u) * normPlus u ^ (-4 : ℝ)))) = _
      rw [lintegral_withDensity_eq_lintegral_mul volume hd hs]
      apply lintegral_congr
      intro u
      dsimp [b, w, V]
      rw [ENNReal.ofReal_mul (Real.exp_nonneg _)]
      ac_rfl
    _ = ∫⁻ u, ∫⁻ ω, b u * w (u, ω) * Ψ (u, ω) ∂P ∂volume := by
      rw [← lintegral_prod _ hprod.aemeasurable, lintegral_prod_symm _ hprod.aemeasurable]
    _ = ∫⁻ u, b u * ∫⁻ ω, w (u, ω) * Ψ (u, ω) ∂P ∂volume := by
      apply lintegral_congr
      intro u
      simp only [mul_assoc]
      exact lintegral_const_mul (b u)
        ((hw.mul hΨ).comp (measurable_const.prodMk measurable_id))
    _ = ∫⁻ u, ∫⁻ ω, w (u, ω) * Ψ (u, ω) ∂P ∂gmcReferenceMeasure := by
      exact (lintegral_withDensity_eq_lintegral_mul volume hb hinner).symm
    _ = _ := rfl

/-- The integrated finite-circle root identity with the limiting chaos as its mark. -/
theorem regularizedGMC_integrated_rooted_limiting_mark_identity
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) (hMmeas : Measurable M)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (r : ℝ)
    (H : ℂ → (TestFn → ℝ) → Measure ℂ → ℝ≥0∞)
    (hH : Measurable (fun q : ℂ × ((TestFn → ℝ) × Measure ℂ) =>
      H q.1 q.2.1 q.2.2)) :
    (∫⁻ ω, ∫⁻ u, H u (fun f => X ω f) (M ω) ∂regularizedGMC P Xc γ r ω ∂P) =
      ∫⁻ u, ∫⁻ ω, H u (fun f => X ω f + γ * circleCross u r f)
        ((M ω).withDensity (fun x => ENNReal.ofReal
          (Real.exp (γ ^ 2 * ∫ v, gffKernel x v ∂circleMeasure u r)))) ∂P
        ∂gmcReferenceMeasure := by
  have hfield : Measurable (fun ω f => X ω f) := by
    rw [measurable_pi_iff]
    exact fun f => (hX.2 f).1
  have hobs : Measurable (fun q : ℂ × Ω => H q.1 (fun f => X q.2 f) (M q.2)) :=
    hH.comp (measurable_fst.prodMk
      ((hfield.comp measurable_snd).prodMk (hMmeas.comp measurable_snd)))
  rw [regularizedGMC_root_sample_lintegral P X hX Xc hXc γ r _ hobs]
  apply lintegral_congr
  intro u
  exact gmc_joint_single_circle_tilt P X hX γ hγ hγ2 M hM Xc hXc u r (H u)
    (hH.comp (measurable_const.prodMk measurable_id))

end

end

end DOZZ.Proofs
