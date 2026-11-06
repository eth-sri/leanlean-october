/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.CopiedRegionRegroup
public import DOZZ.Probability.RealMeasureTranslate
public import DOZZ.FourPoint.Dual.SourcePolarFinite
public import DOZZ.FourPoint.Dual.PathPolarTransport
import Mathlib.Tactic
/-! Exact source-to-copied polar expectation transport on the common full-path carrier. -/
public section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- The copied exterior/path model has a finite actual polar mass by the source joint law. -/
theorem dual_source_copied_polar_finite_ae
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (Xc : Ω → ℂ → ℝ → ℝ) (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun v : Ω × (ℂ × ℝ) => Xc v.1 v.2.1 v.2.2))
    (hcont : ∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Xc ω p.1 p.2))
    (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (N : Ω → Measure ℂ) (hNm : Measurable N)
    (hfin : ∀ ω K, IsCompact K → K ⊆ ({0} : Set ℂ)ᶜ → N ω K < ⊤)
    (Z : Ω → Measure ℝ) (hZ : IsLateralGMCOf P γ Z)
    (α₁ α₂ α₃ ξ h : ℝ) (hα₁ : α₁ < Q γ) (z : ℂ) (hz0 : z ≠ 0)
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
  let _  := hX.1
  let A := originRadialPath Xc
  let O := fun ω => dualOuterMass γ α₁ α₂ α₃ (M ω) z ξ
  let U := reflected_outerRegion (‖z‖^(1-ξ))
  let O' := fun ω : Ω × Ω => ∫⁻ x in U,
    ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ z x)*
      ENNReal.ofReal (reflected_global_reinsertionWeight γ (A ω.1) x) ∂N ω.2
  have hA := originRadialPath_aemeasurable P X Xc hc hcont
  have hO : AEMeasurable O P := (dual_outerMass_measure_measurable γ α₁ α₂ α₃ ξ z).comp_aemeasurable
    (equatorGFF_GMC_aemeasurable P X hX γ hγ hγ₂ M hM)
  have hU : IsOpen U := (isOpen_lt continuous_const continuous_norm).inter (Set.toFinite ({0,1} : Set ℂ)).isClosed.isOpen_compl
  have hU0 : U ⊆ ({0} : Set ℂ)ᶜ := by
    intro x hx hx0
    have hxzero := mem_singleton_iff.mp hx0
    exact hx.2 (by simp [hxzero])
  have hO' : AEMeasurable O' (P.prod P) :=
    reflected_copied_region_mass_aemeasurable P A N hA hNm hfin γ U hU.measurableSet hU0 _
      (dual_kernel_measurable γ α₁ α₂ α₃ z).ennreal_ofReal
  let ZT := fun ω => (Z ω).map (fun s : ℝ => s-(T : ℝ))
  have hZT : AEMeasurable ZT P := (Measure.measurable_map _ (measurable_id.sub_const _)).comp_aemeasurable hZ.2.2.2.1
  have hZTfin : ∀ᵐ ω ∂P, ∀ a b : ℝ, ZT ω (Icc a b) < ⊤ :=
    hZ.2.2.2.2.1.mono (fun ω hω => realMeasure_map_sub_Icc_lt_top hω T)
  have hf := dual_source_restarted_polar_finite_ae P X Xc hX hc hm hcont γ hγ hγ₂ M hM
    h α₁ α₂ α₃ ξ hα₁ z hz0 hz T hT hr Z hZ hiZ B Z₀ hData
  exact (dual_path_outer_polar_finite_transport P (P.prod P) P A (fun ω => A ω.1)
    O O' ZT hA hA.comp_fst hO hO' hZT hZTfin hlaw γ (Q γ-α₁) T).mp hf

end DOZZ.Proofs
