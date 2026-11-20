/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.GlobalCompactMassComparison
public import DOZZ.MeasureTheory.FiniteOnChart
public import DOZZ.FourPoint.Reflected.ReinsertedRegionCode
/-! The compact conditional comparison extends to full separated spatial regions. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal
namespace DOZZ.Proofs

theorem full_spatial_comparison
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (Xc : Ω → ℂ → ℝ → ℝ) (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (γ : ℝ) (k : ℂ → ℝ) (hk : Measurable k) (hkn : ∀ x, 0 ≤ k x)
    (hkc : ContinuousOn k ({0, 1} : Set ℂ)ᶜ)
    (N : Ω → Measure ℂ) (hNm : Measurable N)
    (hfin : ∀ ω, FiniteOnChart ({0} : Set ℂ)ᶜ (N ω))
    (hNa : ∀ ρ : ℝ, 0 < ρ → IsAdmissibleGMCVersion P (originLateralChart ρ)
      originLateralPlaneDensity (originLateralCircleRegularization Xc ρ) γ
      (fun ω => (N ω).restrict (originLateralChart ρ)))
    (Q : Measure TwoSidedPath) [IsProbabilityMeasure Q]
    (U₀ U₁ : Set ℂ) (hU₀ : IsOpen U₀) (hU₁ : IsOpen U₁)
    (hroot₀ : U₀ ⊆ ({0, 1} : Set ℂ)ᶜ) (hroot₁ : U₁ ⊆ ({0, 1} : Set ℂ)ᶜ)
    (A : Set ℂ) (hA : MeasurableSet A) (hU₀A : U₀ ⊆ A) (hU₁A : U₁ ⊆ Aᶜ)
    (R r η : ℝ) (hR0 : 0 ≤ R) (hR : R ≤ 1/2) (hr : 0 < r) (hη : 0 < η)
    (hn₀ : ∀ x ∈ U₀, ‖x‖ ≤ R*r) (hn₁ : ∀ x ∈ U₁, r ≤ ‖x‖)
    (hD : Metric.closedBall (3 : ℂ) (1/8) ⊆ U₁) (q : ℝ) (hq : 0 < q)
    (hguard : (∫⁻ a, ∫⁻ ω, (∫⁻ x in Metric.closedBall (3 : ℂ) (1/8),
      ENNReal.ofReal (k x)*
        ENNReal.ofReal (reflected_global_reinsertionWeight γ a x) ∂N ω)^(-q) ∂P ∂Q) ≠ ⊤) :
    let J := fun (U : Set ℂ) (p : TwoSidedPath × Ω) => ∫⁻ x in U,
      ENNReal.ofReal (k x)*
        ENNReal.ofReal (reflected_global_reinsertionWeight γ p.1 x) ∂N p.2
    let m := ENNReal.ofReal (Real.exp (γ^2*(2*R+η)/2*(q^2+q)))
    (∫⁻ p, (J U₀ p+J U₁ p)^(-q) ∂Q.prod P) ≤
      m*(∫⁻ p : TwoSidedPath × (Ω × Ω),
        (J U₀ (p.1, p.2.1)+J U₁ (p.1, p.2.2))^(-q) ∂Q.prod (P.prod P)) ∧
    (∫⁻ p : TwoSidedPath × (Ω × Ω),
        (J U₀ (p.1, p.2.1)+J U₁ (p.1, p.2.2))^(-q) ∂Q.prod (P.prod P)) ≤
      m*(∫⁻ p, (J U₀ p+J U₁ p)^(-q) ∂Q.prod P) := by
  let _ : IsProbabilityMeasure P := hX.1
  let D := Metric.closedBall (3 : ℂ) (1/8)
  obtain ⟨g₀, _, hgc₀, hgU₀, hgn₀, hlim₀⟩ := reflected_open_weighted_mass_approximation
    U₀ hU₀ ∅ isCompact_empty (empty_subset _) k
    (hkc.mono hroot₀) hk hkn
  obtain ⟨g₁, hgD, hgc₁, hgU₁, hgn₁, hlim₁⟩ := reflected_open_weighted_mass_approximation
    U₁ hU₁ D (isCompact_closedBall _ _) hD k
    (hkc.mono hroot₁) hk hkn
  let W : TwoSidedPath × ℂ → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (reflected_global_reinsertionWeight γ p.1 p.2)
  have hroot {U : Set ℂ} (h : U ⊆ ({0, 1} : Set ℂ)ᶜ) : U ⊆ ({0} : Set ℂ)ᶜ :=
    h.trans (compl_subset_compl.mpr (by simp))
  let mass (U : Set ℂ) (f : ℂ → ℝ) (p : TwoSidedPath × Ω) :=
    ∫⁻ x in U, ENNReal.ofReal (f x) * W (p.1, x) ∂N p.2
  let I₀ n := mass U₀ (g₀ n)
  let I₁ n := mass U₁ (g₁ n)
  have hmassMeas {U : Set ℂ} (hU : MeasurableSet U) (hU0 : U ⊆ ({0, 1} : Set ℂ)ᶜ)
      {f : ℂ → ℝ} (hf : Measurable f) : Measurable (mass U f) :=
    reflected_reinserted_region_measurable hNm hfin γ hU (hroot hU0) hf.ennreal_ofReal
  have hi₀ n := hmassMeas hU₀.measurableSet hroot₀ (g₀ n).continuous.measurable
  have hi₁ n := hmassMeas hU₁.measurableSet hroot₁ (g₁ n).continuous.measurable
  have hG : Measurable (mass D k) := hmassMeas measurableSet_closedBall (hD.trans hroot₁) hk
  have hl₀ (p : TwoSidedPath × Ω) : Tendsto (fun n => I₀ n p) atTop (𝓝 (mass U₀ k p)) :=
    reflected_global_spatial_mass_limit γ p.1 (N p.2) U₀ hU₀.measurableSet k hk g₀ hgU₀ hlim₀
  have hl₁ (p : TwoSidedPath × Ω) : Tendsto (fun n => I₁ n p) atTop (𝓝 (mass U₁ k p)) :=
    reflected_global_spatial_mass_limit γ p.1 (N p.2) U₁ hU₁.measurableSet k hk g₁ hgU₁ hlim₁
  have hgl n p : mass D k p ≤ I₁ n p := by
    have he : mass D k p = mass D (g₁ n) p := setLIntegral_congr_fun measurableSet_closedBall
      fun x hx => by rw [hgD n hx]
    rw [he]
    exact lintegral_mono_set hD
  let m := ENNReal.ofReal (Real.exp (γ^2*(2*R+η)/2*(q^2+q)))
  have hcmp (n : ℕ) :
      (∫⁻ p, (I₀ n p+I₁ n p)^(-q) ∂Q.prod P) ≤
        m*(∫⁻ p : TwoSidedPath × (Ω × Ω),
          (I₀ n (p.1, p.2.1)+I₁ n (p.1, p.2.2))^(-q) ∂Q.prod (P.prod P)) ∧
      (∫⁻ p : TwoSidedPath × (Ω × Ω),
          (I₀ n (p.1, p.2.1)+I₁ n (p.1, p.2.2))^(-q) ∂Q.prod (P.prod P)) ≤
        m*(∫⁻ p, (I₀ n p+I₁ n p)^(-q) ∂Q.prod P) := by
    let K := tsupport (g₀ n : ℂ → ℝ) ∪ tsupport (g₁ n : ℂ → ℝ)
    have hK : IsCompact K := (hgc₀ n).union (hgc₁ n)
    have hg₀K : tsupport (g₀ n : ℂ → ℝ) ⊆ K := subset_union_left
    have hg₁K : tsupport (g₁ n : ℂ → ℝ) ⊆ K := subset_union_right
    have hK0 : K ⊆ ({0} : Set ℂ)ᶜ := union_subset
      ((hgU₀ n).trans (hroot hroot₀)) ((hgU₁ n).trans (hroot hroot₁))
    have hmono : Monotone (fun j => originLateralChart (originLateralChartRadius j)) :=
      fun _ _ h => originLateralChart_antitone (originLateralChartRadius_antitone h)
    obtain ⟨j, hKj⟩ := hK.elim_directed_cover
      (fun j => originLateralChart (originLateralChartRadius j))
      (fun j => isOpen_originLateralChart _) (by rwa [originLateralChart_exhaustion]) hmono.directed_le
    have hnK₀ : ∀ x ∈ K, x ∈ A → ‖x‖ ≤ R*r := by
      intro x hx hxA
      rcases hx with hx | hx
      · exact hn₀ x (hgU₀ n hx)
      · exact False.elim (hU₁A (hgU₁ n hx) hxA)
    have hnK₁ : ∀ x ∈ K, x ∉ A → r ≤ ‖x‖ := by
      intro x hx hxA
      rcases hx with hx | hx
      · exact False.elim (hxA (hU₀A (hgU₀ n hx)))
      · exact hn₁ x (hgU₁ n hx)
    have hb (a : TwoSidedPath) := reflected_global_compact_mass_comparison
      P X Xc hX hc hm (originLateralChartRadius j) γ (originLateralChartRadius_pos j)
      N (hNa _ (originLateralChartRadius_pos j)) K hK hKj (fun ω => hfin ω K hK hK0)
      A hA R r η hR0 hR hr hη hnK₀ hnK₁ (g₀ n) (g₁ n) (hgn₀ n) (hgn₁ n)
      hg₀K hg₁K ((hgU₀ n).trans hU₀A) ((hgU₁ n).trans hU₁A) q hq a
    have he {U : Set ℂ} (hU : MeasurableSet U) (f : BoundedContinuousFunction ℂ ℝ)
        (hfK : tsupport (f : ℂ → ℝ) ⊆ K) (hfU : tsupport (f : ℂ → ℝ) ⊆ U)
        (a : TwoSidedPath) (ω : Ω) : mass K f (a, ω) = mass U f (a, ω) :=
      (reflected_supported_test_lintegral (N ω) K hK.measurableSet f hfK _).trans
        (reflected_supported_test_lintegral (N ω) U hU f hfU _).symm
    have he₀ := he hU₀.measurableSet (g₀ n) hg₀K (hgU₀ n)
    have he₁ := he hU₁.measurableSet (g₁ n) hg₁K (hgU₁ n)
    dsimp [mass, W] at he₀ he₁
    dsimp only at hb
    simp_rw [he₀, he₁] at hb
    have hO : Measurable (fun p => (I₀ n p+I₁ n p)^(-q)) := ((hi₀ n).add (hi₁ n)).pow_const (-q)
    have hC : Measurable (fun p : TwoSidedPath × (Ω × Ω) =>
        (I₀ n (p.1, p.2.1)+I₁ n (p.1, p.2.2))^(-q)) :=
      (((hi₀ n).comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).add
        ((hi₁ n).comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))).pow_const (-q)
    rw [lintegral_prod _ hO.aemeasurable, lintegral_prod _ hC.aemeasurable]
    constructor
    · calc
        _ ≤ ∫⁻ a, m*(∫⁻ ω : Ω × Ω, (I₀ n (a, ω.1)+I₁ n (a, ω.2))^(-q) ∂P.prod P) ∂Q :=
          lintegral_mono fun a => (hb a).1
        _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    · calc
        _ ≤ ∫⁻ a, m*(∫⁻ ω, (I₀ n (a, ω)+I₁ n (a, ω))^(-q) ∂P) ∂Q :=
          lintegral_mono fun a => (hb a).2
        _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  exact reflected_two_region_inverse_limit Q P I₀ I₁ (mass U₀ k) (mass U₁ k) (mass D k)
    hi₀ hi₁ hG hl₀ hl₁ hgl
    q hq.le hguard m ENNReal.ofReal_ne_top hcmp

end DOZZ.Proofs
