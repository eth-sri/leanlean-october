/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Dual.SourcePolarFinite
public import DOZZ.FourPoint.Dual.PathPolarTransport
import Mathlib.Tactic
/-! Exact source-to-copied polar expectation transport on the common full-path carrier. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- The copied exterior/path model has a finite actual polar mass by the source joint law. -/
theorem dual_source_copied_polar_finite_ae
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) X
    Xc (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun v : Ω × (ℂ × ℝ) => Xc v.1 v.2.1 v.2.2))
    (hcont : ∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Xc ω p.1 p.2))
    γ (hγ : 0 < γ) (hγ₂ : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (N : Ω → Measure ℂ) (hNm : Measurable N)
    (hfin : ∀ ω K, IsCompact K → K ⊆ ({0} : Set ℂ)ᶜ → N ω K < ⊤)
    (Z : Ω → Measure ℝ) (hZ : IsLateralGMCOf P γ Z)
    α₁ α₂ α₃ ξ h (hα₁ : α₁ < Q γ) z (hz0 : z ≠ 0)
    (hz : ‖z‖ < ‖z‖^(1-ξ)) (T : ℝ≥0) (hT : (T : ℝ) = -Real.log ‖z‖+h)
    (hr : Real.exp (-(T : ℝ)) ≤ ‖z‖^(1-ξ))
    (hiZ : IndepFun (originRadialPath Xc) Z P)
    (B : Ω → BrownianPath × BrownianPath) (Z₀ : Ω → Measure ℝ)
    (hData : IsReflectionData P γ α₁ B Z₀)
    (hlaw : P.map (fun ω => (originRadialPath Xc ω,dualOuterMass γ α₁ α₂ α₃ (M ω) z ξ)) =
      (P.prod P).map (fun ω : Ω × Ω => (originRadialPath Xc ω.1,
        ∫⁻ x in reflected_outerRegion (‖z‖^(1-ξ)),
          ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ z x)*
            ENNReal.ofReal (reflected_global_reinsertionWeight γ (originRadialPath Xc ω.1) x) ∂N ω.2))) :
    ∀ᵐ ω : (Ω × Ω) × Ω ∂(P.prod P).prod P, (∫⁻ t,
      (if 0 < t then ENNReal.ofReal (Real.exp (γ*
        (brownianShiftPath T (radialPositiveHalf (originRadialPath Xc ω.1.1))
          (Real.toNNReal t)-(Q γ-α₁)*t))) else 0)
        ∂(Z ω.2).map (fun s => s-(T : ℝ))) ≠ ⊤ := by
  let _ : IsProbabilityMeasure P := hX.1
  let A := originRadialPath Xc
  let U := reflected_outerRegion (‖z‖^(1-ξ))
  have hA := originRadialPath_aemeasurable P X Xc hc hcont
  exact (dual_path_outer_polar_finite_transport P (P.prod P) P A (fun ω => A ω.1)
    (fun ω => dualOuterMass γ α₁ α₂ α₃ (M ω) z ξ) (fun ω : Ω × Ω => ∫⁻ x in U, ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ z x)* ENNReal.ofReal (reflected_global_reinsertionWeight γ (A ω.1) x) ∂N ω.2) (fun ω => (Z ω).map (fun s => s-(T : ℝ))) hA hA.comp_fst ((dual_outerMass_measure_measurable γ α₁ α₂ α₃ ξ z).comp_aemeasurable (equatorGFF_GMC_aemeasurable P X hX γ hγ hγ₂ M hM)) ((reflected_chart_parameter_mass_measurable U ((isOpen_lt continuous_const continuous_norm).inter (Set.toFinite ({0,1} : Set ℂ)).isClosed.isOpen_compl) N hNm (by intro ω K hK hKU; apply hfin ω K hK; intro x hx hx0; exact (hKU hx).2 (by simp [(mem_singleton_iff.mp hx0)])) (fun v : TwoSidedPath × ℂ => ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ z v.2)* ENNReal.ofReal (reflected_global_reinsertionWeight γ v.1 v.2)) (((dual_kernel_measurable γ α₁ α₂ α₃ z).comp measurable_snd).ennreal_ofReal.mul (reflected_global_reinsertionWeight_measurable γ).ennreal_ofReal)).comp_aemeasurable (hA.comp_fst.prodMk measurable_snd.aemeasurable)) ((Measure.measurable_map _ (measurable_id.sub_const _)).comp_aemeasurable hZ.2.2.2.1) (by filter_upwards [hZ.2.2.2.2.1] with ω hω a b; change (Z ω).map (fun s => s-(T : ℝ)) (Icc a b) < ⊤; rw [Measure.map_apply (show Measurable (fun s : ℝ => s-(T : ℝ)) from measurable_id.sub_const _) measurableSet_Icc, (show (fun s : ℝ => s-(T : ℝ)) ⁻¹' Icc a b = Icc (a+T) (b+T) by ext s; simp only [mem_preimage, mem_Icc, le_sub_iff_add_le, sub_le_iff_le_add])]; exact hω _ _) hlaw γ (Q γ-α₁) T).mp (dual_source_restarted_polar_finite_ae P X Xc hX hc hm hcont γ hγ hγ₂ M hM h α₁ α₂ α₃ ξ hα₁ z hz0 hz T hT hr Z hZ hiZ B Z₀ hData)

end DOZZ.Proofs
