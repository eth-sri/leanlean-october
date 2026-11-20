/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.SeparatedRegions
public import DOZZ.GFFStructure.ContinuousCircleAverage
public import DOZZ.MeasureTheory.FiniteOnChart
/-! Conditional lateral comparison on a fixed, globally admissible source carrier. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal
namespace DOZZ.Proofs

/-- Transfer the spatial comparison from an admissible carrier to the source chaos. -/
theorem source_full_lateral_comparison_on_carrier
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (Xc : Ω → ℂ → ℝ → ℝ) (hX : IsEquatorGFF P X) (hcircle : IsContinuousCircleAverage P X Xc)
    (γ : ℝ) (M : Ω → Measure ℂ) (k : ℂ → ℝ) (hk : Measurable k) (hkn : ∀ x, 0 ≤ k x)
    (hkc : ContinuousOn k ({0, 1} : Set ℂ)ᶜ)
    (N : Ω → Measure ℂ) (hN : Measurable N)
    (hfin : ∀ ω, FiniteOnChart ({0} : Set ℂ)ᶜ (N ω))
    (hwhole : RadialReinsertionLaw P (originRadialPath Xc) γ M N)
    (hNa : ∀ ρ : ℝ, 0 < ρ → IsAdmissibleGMCVersion P (originLateralChart ρ)
      originLateralPlaneDensity (originLateralCircleRegularization Xc ρ) γ
      (fun ω => (N ω).restrict (originLateralChart ρ)))
    (U₀ U₁ : Set ℂ) (hU₀ : IsOpen U₀) (hU₁ : IsOpen U₁)
    (hroot₀ : U₀ ⊆ ({0, 1} : Set ℂ)ᶜ) (hroot₁ : U₁ ⊆ ({0, 1} : Set ℂ)ᶜ)
    (A : Set ℂ) (hA : MeasurableSet A) (hU₀A : U₀ ⊆ A) (hU₁A : U₁ ⊆ Aᶜ)
    (R r η : ℝ) (hR0 : 0 ≤ R) (hR : R ≤ 1/2) (hr : 0 < r) (hη : 0 < η)
    (hn₀ : ∀ x ∈ U₀, ‖x‖ ≤ R*r) (hn₁ : ∀ x ∈ U₁, r ≤ ‖x‖)
    (hD : Metric.closedBall (3 : ℂ) (1/8) ⊆ U₁) (q : ℝ) (hq : 0 < q)
    (hsource : (∫⁻ ω, (∫⁻ x in Metric.closedBall (3 : ℂ) (1/8),
      ENNReal.ofReal (k x) ∂M ω)^(-q) ∂P) < ⊤) :
    let J := fun (U : Set ℂ) (p : TwoSidedPath × Ω) => ∫⁻ x in U,
        ENNReal.ofReal (k x)*
          ENNReal.ofReal (reflected_global_reinsertionWeight γ p.1 x) ∂N p.2
    let original := ∫⁻ ω,
        ((∫⁻ x in U₀, ENNReal.ofReal (k x) ∂M ω)+
         (∫⁻ x in U₁, ENNReal.ofReal (k x) ∂M ω))^(-q) ∂P
    let copied := ∫⁻ p : TwoSidedPath × (Ω × Ω),
        (J U₀ (p.1, p.2.1)+J U₁ (p.1, p.2.2))^(-q) ∂(P.map (originRadialPath Xc)).prod (P.prod P)
    let m := ENNReal.ofReal (Real.exp (γ^2*(2*R+η)/2*(q^2+q)))
    original ≤ m*copied ∧ copied ≤ m*original := by
  let _ : IsProbabilityMeasure P := hX.1
  let Ar := originRadialPath Xc
  have hAr := originRadialPath_aemeasurable P X Xc hcircle.isCircleAverage hcircle.continuous_ae
  let _ : IsProbabilityMeasure (P.map Ar) := inferInstance
  have htransport {S : Set ℂ} := radial_reinsertion_moments P Ar hAr γ M N hN hfin hwhole (S := S)
  have hD0 : Metric.closedBall (3 : ℂ) (1/8) ⊆ ({0} : Set ℂ)ᶜ := by
    norm_num
  have hguard := (htransport measurableSet_closedBall hD0 (fun x => ENNReal.ofReal (k x))
    hk.ennreal_ofReal (-q)).2.symm.trans_lt hsource
  have hb := full_spatial_comparison P X Xc hX hcircle.isCircleAverage hcircle.measurable γ k hk hkn hkc N hN hfin hNa
    (P.map Ar) U₀ U₁ hU₀ hU₁ hroot₀ hroot₁ A hA hU₀A hU₁A R r η hR0 hR hr hη
      hn₀ hn₁ hD q hq hguard.ne
  have hU : U₀ ∪ U₁ ⊆ ({0} : Set ℂ)ᶜ := (union_subset hroot₀ hroot₁).trans
    (compl_subset_compl.mpr (by simp))
  have hdis : Disjoint U₀ U₁ := disjoint_left.mpr fun _ hx₀ hx₁ => hU₁A hx₁ (hU₀A hx₀)
  have he := (htransport (hU₀.measurableSet.union hU₁.measurableSet) hU
    (fun x => ENNReal.ofReal (k x)) hk.ennreal_ofReal (-q)).1
  simp only [lintegral_union hU₁.measurableSet hdis] at he
  dsimp only at hb ⊢
  rw [← he] at hb
  exact hb

end DOZZ.Proofs
