/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.GlobalReinsertion
import Mathlib.Tactic
public import DOZZ.FourPoint.Reflected.ReinsertedRegionCode
public import DOZZ.Probability.IndependentProduct
public import DOZZ.GFFStructure.ContinuousCircleAverage
public import DOZZ.MeasureTheory.FiniteOnChart
/-! # The actual limiting punctured-plane chaos with an independent radial copy -/
public section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
namespace DOZZ.Proofs

/-- Independent radial reinsertion preserves every measurable radial-path and weighted-mass observable on the full
punctured plane, including extended-real masses. -/
theorem reflected_copied_radial_plane_observable
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (Xc : Ω → ℂ → ℝ → ℝ) (hX : IsEquatorGFF P X) (hcircle : IsContinuousCircleAverage P X Xc)
    (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) :
    ∃ N : Ω → Measure ℂ,
      Measurable N ∧ IndepFun (originRadialPath Xc) N P ∧
      (∀ ω, FiniteOnChart ({0} : Set ℂ)ᶜ (N ω)) ∧
      N =ᵐ[P] (fun ω => (M ω).withDensity
        (lateralRadialWeight γ (originRadialPath Xc ω))) ∧
      (∀ ρ : ℝ, 0 < ρ → IsAdmissibleGMCVersion P (originLateralChart ρ)
        originLateralPlaneDensity (originLateralCircleRegularization Xc ρ) γ
        (fun ω => (N ω).restrict (originLateralChart ρ))) ∧
      RadialReinsertionLaw P (originRadialPath Xc) γ M N := by
  let _ : IsProbabilityMeasure P := hX.1
  obtain ⟨N, hNm, hi, hfin, heq, hNa⟩ := reflected_global_lateral_admissible
    P X Xc hX hcircle γ hγ hγ₂ M hM
  refine ⟨N, hNm, hi, hfin, heq, hNa, ?_⟩
  intro f hf G hG
  let U : Set ℂ := ({0} : Set ℂ)ᶜ
  have hU : MeasurableSet U := (measurableSet_singleton _).compl
  let A := originRadialPath Xc
  have hA := originRadialPath_aemeasurable P X Xc hcircle.isCircleAverage hcircle.continuous_ae
  let F : TwoSidedPath × ℂ → ℝ≥0∞ := fun p =>
    f p.2 * ENNReal.ofReal (reflected_global_reinsertionWeight γ p.1 p.2)
  have hF : Measurable F := (hf.comp measurable_snd).mul
    (reflected_global_reinsertionWeight_measurable γ).ennreal_ofReal
  let H : TwoSidedPath × Measure ℂ → ℝ≥0∞ := fun p => G (p.1,reflectedPuncturedMassCode F p)
  have hH : Measurable H := hG.comp (measurable_fst.prodMk (reflected_puncturedMassCode_measurable F hF))
  have hmass (a : TwoSidedPath) (ω : Ω) : H (a,N ω) = G (a, ∫⁻ x in U, F (a,x) ∂N ω) :=
    congrArg (fun t => G (a,t)) (reflected_puncturedMassCode_eq F a (N ω) (hfin ω))
  calc
    _ = ∫⁻ ω, H (A ω,N ω) ∂P := lintegral_congr_ae (heq.mono fun ω hw => by
      change G (A ω, ∫⁻ x in U, f x ∂M ω) = H (A ω,N ω)
      rw [hmass, hw]
      simp only [F]
      rw [reflected_reinserted_region_eq γ (A ω) (M ω) U hU Subset.rfl f hf])
    _ = ∫⁻ p : Ω × Ω, H (A p.1,N p.2) ∂P.prod P := lintegral_indepFun_prod hi hA hNm.aemeasurable hH
    _ = _ := lintegral_congr fun p => hmass (A p.1) p.2

end DOZZ.Proofs
