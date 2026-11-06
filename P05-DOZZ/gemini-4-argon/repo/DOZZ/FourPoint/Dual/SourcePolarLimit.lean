/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Dual.WilliamsCutLimit
public import DOZZ.FourPoint.Dual.SourceRestartWilliams
public import DOZZ.FourPoint.Dual.JointLawExpectation
public import DOZZ.FourPoint.Dual.FullMaximumLimit
public import DOZZ.FourPoint.Dual.FixedCutMaximumLimit
public import DOZZ.FourPoint.Dual.SourceWilliamsSandwich
public import DOZZ.FourPoint.Dual.CutSqueezeLimit
public import DOZZ.FourPoint.Dual.SourceParetoLimit
public import DOZZ.FourPoint.Dual.SourceParetoIncrement
public import DOZZ.FourPoint.Dual.SourceMaximumPareto
public import DOZZ.Statements.Brownian.EquatorGFFLateralGMCDecomposition
public import DOZZ.FourPoint.Reflected.RestartedWilliams
public import DOZZ.FourPoint.Dual.RadialFirstOrder
import Mathlib.Tactic
/-! The actual translated restarted polar mass has the same-witness dual leading coefficient. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal
namespace DOZZ.Proofs

/-- The actual independent Pareto maximum, full reflection mass, retained source mass and
radial restart scale give the required leading coefficient for each fixed radial buffer. -/
theorem dual_source_restarted_polar_increment_tendsto
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) X
    (hX : IsEquatorGFF P X) γ (hγ : 0 < γ) (hγ₂ : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    Xc (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (hcont : ∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Xc ω p.1 p.2))
    α₁ α₂ α₃ ξ h (hα₁ : α₁ < Q γ) (hreflect : Q γ-α₁ < γ/2)
    (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) (hh : 0 ≤ h)
    (hs : 2*Q γ+2/γ < α₁+α₂+α₃)
    (hshifted : 2*Q γ-α₁-2/γ < Q γ)
    (hslack : (4/γ)*(Q γ-α₁) < 2+γ*(Q γ-α₁)-γ^2/2) (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (hData : IsReflectionData P γ α₁ B Z)
    (hiZ : IndepFun (originRadialPath Xc) Z P) :
    let ν := Q γ-α₁
    let a := 2*ν/γ
    let p := (α₁+α₂+α₃-2/γ-2*Q γ)/γ
    let T := fun z : ℂ => Real.toNNReal (-Real.log ‖z‖+h)
    Tendsto (fun z => (fun z : ℂ => ∫ v : Ω × Ω, (((dualOuterMass γ α₁ α₂ α₃ (M v.1) z ξ).toReal+ dual_radial_scale γ ν h Xc z v.1*(∫⁻ t, (if 0 < t then ENNReal.ofReal (Real.exp (γ* (brownianShiftPath (T z) (radialPositiveHalf (originRadialPath Xc v.1)) (Real.toNNReal t)-ν*t))) else 0) ∂(Z v.2).map (fun s => s-(T z : ℝ))).toReal)^(-p)- (dualOuterMass γ α₁ α₂ α₃ (M v.1) z ξ).toReal^(-p)) ∂P.prod P) z/‖z‖^((4/γ)*ν)) (𝓝[≠] (0 : ℂ))
      (𝓝 ((a*Real.Gamma (-a)*Real.Gamma (p+a)/Real.Gamma p)*
        (∫⁻ ω, rho γ (M ω) (2*Q γ-α₁-2/γ) α₂ α₃ ^(-(p+a)) ∂P).toReal*
        (∫⁻ ω, twoSidedReflectionMass γ B Z ω ^a ∂P).toReal)) := by
  let _ : IsProbabilityMeasure P := hX.1
  let ν := Q γ-α₁
  let p := (α₁+α₂+α₃-2/γ-2*Q γ)/γ
  have hA := originRadialPath_aemeasurable P X Xc hc hcont
  have hZ := hData.2.1
  let _ := isProbabilityMeasure_brownianMaximumReferenceLaw (sub_pos.mpr hα₁)
  apply (dual_source_williams_cut_increment_tendsto P X hX γ hγ hγ₂ M hM Xc hc α₁ α₂ α₃ ξ h hα₁ hreflect hα₂ hα₃ hh hs hshifted hslack hξ hξ1 B Z hData).congr'
  filter_upwards [self_mem_nhdsWithin, ((continuous_norm.tendsto (0 : ℂ)).mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds (by norm_num : ‖(0 : ℂ)‖ < 1))]
    with z hz0 hz
  have hn0 := norm_pos_iff.mpr hz0
  let T := Real.toNNReal (-Real.log ‖z‖+h)
  have hT : (T : ℝ) = -Real.log ‖z‖+h := Real.coe_toNNReal _ (by linarith only [(Real.log_nonpos hn0.le hz.le), hh])
  have hstrict : ‖z‖ < ‖z‖^(1-ξ) := by
    simpa only [Real.rpow_one] using Real.rpow_lt_rpow_of_exponent_gt hn0 hz
      (by linarith only [hξ] : 1-ξ < 1)
  let D := fun ω => brownianShiftPath T (radialPositiveHalf ((originRadialPath Xc) ω))
  let Y := fun ω => (dual_radial_scale γ ν h Xc z ω,
    (dualOuterMass γ α₁ α₂ α₃ (M ω) z ξ).toReal)
  let J := fun q : ℝ × Ω => ENNReal.ofReal (Real.exp (γ*q.1))*twoSidedReflectionCutMass γ q.1 B Z q.2
  let G : (ℝ × ℝ) × ℝ≥0∞ → ℝ := fun v => (v.1.2+v.1.1*v.2.toReal)^(-p)-v.1.2^(-p)
  have he := dual_copied_joint_law_integral P ((brownianMaximumReferenceLaw ν).prod P) Y ((((((hc.2.1 0 (-Real.log ‖z‖+h)).aemeasurable).const_mul γ).sub aemeasurable_const).sub aemeasurable_const |>.exp).prodMk (((dual_outerMass_measure_measurable γ α₁ α₂ α₃ ξ z).comp_aemeasurable (equatorGFF_GMC_aemeasurable P X hX γ hγ hγ₂ M hM)).ennreal_toReal)) (fun ω : Ω × Ω => ∫⁻ t, (if 0 < t then ENNReal.ofReal (Real.exp (γ*(D ω.1 (Real.toNNReal t)-ν*t))) else 0) ∂(Z ω.2).map (fun s => s-(T : ℝ))) (dual_translated_polar_mass_aemeasurable P D ((continuous_brownianShiftPath.measurable.comp (measurable_const.prodMk continuous_radialPositiveHalf.measurable)).comp_aemeasurable hA) γ ν Z hZ (hiZ.comp₀ hA hZ.2.2.2.1 (continuous_brownianShiftPath.measurable.comp (measurable_const.prodMk continuous_radialPositiveHalf.measurable)).aemeasurable measurable_id.aemeasurable) T) J ((measurable_fst.aemeasurable.const_mul γ).exp.ennreal_ofReal.mul (actual_cut_mass_joint_aemeasurable P _ γ B Z (aemeasurable_of_twoSidedConditioned hData.1) hZ.2.2.2.1 hZ.2.2.2.2.1)) (dual_source_restart_outer_williams_law P X Xc hX hc hm hcont γ hγ hγ₂ M hM h α₁ α₂ α₃ ξ hα₁ z hz0 hstrict T hT (by apply le_trans ?_ hstrict.le; rw [hT]; simpa only [Real.exp_log hn0] using Real.exp_le_exp.mpr (show -(-Real.log ‖z‖+h) ≤ Real.log ‖z‖ by linarith only [hh])) Z hZ hiZ B Z hData) G (by unfold G; fun_prop)
  simp only [G, Y, J, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le] at he
  exact congrArg (fun t : ℝ => t/‖z‖^((4/γ)*ν)) he.symm

end DOZZ.Proofs
