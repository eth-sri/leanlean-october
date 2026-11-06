/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Construction.GMCFiniteCoordinateTilt
public import DOZZ.GMC.Construction.GMCBoxMassLimit
public import DOZZ.GMC.Construction.GMCWeightedBoxMass
public import DOZZ.GMC.Construction.GMCWeightedBoxMassVarying
public import DOZZ.GMC.Construction.GMCVaryingWeightedTotalMassLimit
public import DOZZ.GMC.Construction.GMCExpCovarianceWeight
public import DOZZ.GMC.Construction.GMCGeneralTiltBasisProxy
public import DOZZ.GMC.Construction.RootedSizeBiasedLimit
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Topology.EMetricSpace.Pi

/-! Finite-coordinate convergence for the two sides of the general GMC tilt. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped Distributions ENNReal NNReal BoundedContinuousFunction

namespace DOZZ.Proofs

private theorem tendstoInMeasure_pi_of_coord
    {α ι : Type*} [MeasurableSpace α] (μ : Measure α)
    (s : Finset ι) (f : ℝ → α → (∀ _i : {i // i ∈ s}, ℝ))
    (g : α → (∀ _i : {i // i ∈ s}, ℝ))
    (hcoord : ∀ i : {i // i ∈ s},
      TendstoInMeasure μ (fun r ω => f r ω i) atTop (fun ω => g ω i)) :
    TendstoInMeasure μ f atTop g := by
  intro ε hε
  let A : ℝ → {i // i ∈ s} → Set α := fun r i =>
    {ω | ε ≤ edist (f r ω i) (g ω i)}
  have hsub r : {ω | ε ≤ edist (f r ω) (g ω)} ⊆ ⋃ i, A r i := by
    intro ω hω
    by_contra hnot
    have hlt (i : {i // i ∈ s}) : edist (f r ω i) (g ω i) < ε := lt_of_not_ge (fun hi => hnot (Set.mem_iUnion.2 ⟨i, hi⟩))
    change ε ≤ edist (f r ω) (g ω) at hω
    rw [edist_pi_def] at hω
    exact (not_lt_of_ge hω) ((Finset.sup_lt_iff hε).2 (fun i _ => hlt i))
  have hbound r : μ {ω | ε ≤ edist (f r ω) (g ω)} ≤
      ∑ i : {i // i ∈ s}, μ (A r i) := by
    calc
      μ {ω | ε ≤ edist (f r ω) (g ω)} ≤ μ (⋃ i, A r i) := measure_mono (hsub r)
      _ ≤ ∑ i : {i // i ∈ s}, μ (A r i) := by
        simpa [A] using measure_biUnion_finset_le (μ := μ)
          (Finset.univ : Finset {i // i ∈ s}) (fun i : {i // i ∈ s} => A r i)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (by simpa [A] using (tendsto_finsetSum (s := Finset.univ) (fun i hi => hcoord i ε hε)))
    (fun _ => zero_le) hbound

private theorem tendstoInMeasure_add_of_sub
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (f g : ℝ → Ω → ℝ) y
    (hfg : TendstoInMeasure P (fun r ω => f r ω - g r ω) atTop (fun _ => 0))
    (hgy : TendstoInMeasure P g atTop y) : TendstoInMeasure P f atTop y := by
  rw [tendstoInMeasure_iff_norm] at hfg hgy ⊢
  intro ε hε
  let δ : ℝ := ε / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ => (0 : ℝ≥0∞)) atTop (𝓝 0)) (by simpa using (show Tendsto (fun r => P {ω | δ ≤ ‖f r ω - g r ω‖}) atTop (𝓝 0) by simpa [δ, sub_zero] using hfg δ hδ).add (hgy δ hδ))
  · exact Filter.Eventually.of_forall (fun _ => bot_le)
  · filter_upwards [] with r
    calc
      P {ω | ε ≤ ‖f r ω - y ω‖} ≤
          P ({ω | δ ≤ ‖f r ω - g r ω‖} ∪ {ω | δ ≤ ‖g r ω - y ω‖}) := by
            apply measure_mono
            intro ω hω
            by_contra hnot
            rcases not_or.mp (by simpa only [Set.mem_union] using hnot) with ⟨h1, h2⟩
            have hsum : ‖f r ω - y ω‖ < ε := by
              calc
                ‖f r ω - y ω‖ = ‖(f r ω - g r ω) + (g r ω - y ω)‖ := by congr 1; ring
                _ ≤ ‖f r ω - g r ω‖ + ‖g r ω - y ω‖ := norm_add_le _ _
                _ < δ + δ := add_lt_add (lt_of_not_ge h1) (lt_of_not_ge h2)
                _ = ε := by dsimp [δ]; ring
            exact (not_le_of_gt hsum) hω
      _ ≤ P {ω | δ ≤ ‖f r ω - g r ω‖} + P {ω | δ ≤ ‖g r ω - y ω‖} :=
        MeasureTheory.measure_union_le _ _

private def gmcCoordinateB (i : Option (ℚ × ℚ)) : Set ℂ :=
  match i with
  | none => Set.univ
  | some j => gmcLowerBox j





/-- A fixed Cameron--Martin density has total mass one. -/
theorem equatorGFF_gaussianL2_tilt_density_integral_eq_one
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    X (hX : IsEquatorGFF P X)
    Xc (hXc : IsCircleAverage P X Xc)
    L (hL : IsGaussianL2Limit P X L) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (L ω - gaussianVariance P L / 2)) ∂P = 1 := by
  calc
    _ = P Set.univ := by simpa [div_eq_mul_inv, mul_comm] using (equatorGFF_finite_test_circle_tilt (P := P) (X := X) (hX := hX) (Xc := Xc) (hXc := hXc) (r := 0) (L := L) (hL := hL) (coord := fun i : Empty => i.elim) (t := 1) (F := fun _ => (1 : ℝ≥0∞)) (hF := measurable_const))
    _ = 1 := measure_univ


/-- The radius-dependent exact covariance weights have the same finite-coordinate limit as
their uniformly convergent bounded-continuous representatives. -/
theorem equatorGFF_expCovariance_finiteCoordinate_tendstoInMeasure
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (γ : ℝ) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (L : Ω → ℝ) (hL : IsGaussianL2Limit P X L)
    (c : BoundedContinuousFunction ℂ ℝ)
    (hc : TendstoUniformly
      (fun r z => gaussianCovariance P (fun ω => Xc ω z r) L) c atTop)
    (s : Finset gmcTiltCoordinateIndex) :
    ∃ u : ℝ → BoundedContinuousFunction ℂ ℝ,
    ∃ w : BoundedContinuousFunction ℂ ℝ,
      (∀ r z, 0 ≤ u r z) ∧ (∀ z, 0 ≤ w z) ∧
      TendstoUniformly (fun r z => u r z) w atTop ∧
      (∀ᶠ r : ℝ in atTop, ∀ z : ℂ,
        u r z = Real.exp (γ * gaussianCovariance P (fun ω => Xc ω z r) L)) ∧
      TendstoInMeasure P
        (fun r ω => gmcTiltFiniteCoordinatePath s
          (fun f => X ω f + gaussianCovariance P (fun ω' => X ω' f) L)
          ((regularizedGMC P Xc γ r ω).withDensity
            (fun z => ENNReal.ofReal (Real.exp
              (γ * gaussianCovariance P (fun ω' => Xc ω' z r) L))))) atTop
        (fun ω => gmcTiltFiniteCoordinatePath s
          (fun f => X ω f + gaussianCovariance P (fun ω' => X ω' f) L)
          ((M ω).withDensity (fun z => ENNReal.ofReal (w z)))) := by
  have regularizedGMC_varyingWeighted_finiteCoordinatePath_tendstoInMeasure (P : Measure Ω) X (hX : IsEquatorGFF P X) Xc (hXc : IsCircleAverage P X Xc) (γ : ℝ) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) (shift : TestFn → ℝ) (u : ℝ → BoundedContinuousFunction ℂ ℝ) (hu : ∀ r z, 0 ≤ u r z) (v : BoundedContinuousFunction ℂ ℝ) (hv : ∀ z, 0 ≤ v z) (hconv : TendstoUniformly (fun r z => u r z) v atTop) (s : Finset gmcTiltCoordinateIndex) : TendstoInMeasure P (fun r ω => gmcTiltFiniteCoordinatePath s (fun f => X ω f + shift f) ((regularizedGMC P Xc γ r ω).withDensity (fun z => ENNReal.ofReal (u r z)))) atTop (fun ω => gmcTiltFiniteCoordinatePath s (fun f => X ω f + shift f) ((M ω).withDensity (fun z => ENNReal.ofReal (v z)))) := by
    apply tendstoInMeasure_pi_of_coord P s
    intro i
    change TendstoInMeasure P
      (fun r ω => gmcTiltCoordinatePath (fun f => X ω f + shift f)
        ((regularizedGMC P Xc γ r ω).withDensity
          (fun z => ENNReal.ofReal (u r z))) i.1) atTop
      (fun ω => gmcTiltCoordinatePath (fun f => X ω f + shift f)
        ((M ω).withDensity (fun z => ENNReal.ofReal (v z))) i.1)
    rcases i.1 with f | j
    · intro ε hε
      simp [gmcTiltCoordinatePath, hε.ne']
    · cases j with
      | none =>
        simpa [gmcTiltCoordinatePath, gmcTiltCoordinateSet, gmcCoordinateB] using
          regularizedGMC_varyingWithDensity_univ_mass_tendstoInMeasure
            P X hX Xc hXc γ M hM u hu v hv hconv
      | some j =>
        let leftVarying : ℝ → Ω → ℝ := fun r ω =>
          (((regularizedGMC P Xc γ r ω).withDensity
            (fun z => ENNReal.ofReal (u r z))) (gmcLowerBox j)).toReal
        let rightVarying : ℝ → Ω → ℝ := fun r ω =>
          (((regularizedGMC P Xc γ r ω).withDensity
            (fun z => ENNReal.ofReal (v z))) (gmcLowerBox j)).toReal
        let limitMass : Ω → ℝ := fun ω =>
          (((M ω).withDensity (fun z => ENNReal.ofReal (v z)))
            (gmcLowerBox j)).toReal
        simpa [gmcTiltCoordinatePath, gmcTiltCoordinateSet, gmcCoordinateB,
          leftVarying, limitMass] using
          tendstoInMeasure_add_of_sub P leftVarying rightVarying limitMass (by simpa [leftVarying, rightVarying] using regularizedGMC_varyingWithDensity_box_mass_diff_tendstoInMeasure P X hX Xc hXc γ u hu v hv hconv j) (by simpa [rightVarying, limitMass] using regularizedGMC_withDensity_box_mass_tendstoInMeasure P X hX Xc hXc γ M hM v hv j)
  obtain ⟨u, w, hu, hw, hconv, heventual⟩ :=
    equatorGFF_circleCovariance_exp_weight_family P X hX Xc hXc L hL γ c hc
  let cutoffBCF : ℝ → Ω → (∀ _i : {i // i ∈ s}, ℝ) := fun r ω =>
    gmcTiltFiniteCoordinatePath s
      (fun f => X ω f + gaussianCovariance P (fun ω' => X ω' f) L)
      ((regularizedGMC P Xc γ r ω).withDensity
        (fun z => ENNReal.ofReal (u r z)))
  let cutoffExact : ℝ → Ω → (∀ _i : {i // i ∈ s}, ℝ) := fun r ω =>
    gmcTiltFiniteCoordinatePath s
      (fun f => X ω f + gaussianCovariance P (fun ω' => X ω' f) L)
      ((regularizedGMC P Xc γ r ω).withDensity
        (fun z => ENNReal.ofReal (Real.exp
          (γ * gaussianCovariance P (fun ω' => Xc ω' z r) L))))
  let limit : Ω → (∀ _i : {i // i ∈ s}, ℝ) := fun ω =>
    gmcTiltFiniteCoordinatePath s
      (fun f => X ω f + gaussianCovariance P (fun ω' => X ω' f) L)
      ((M ω).withDensity (fun z => ENNReal.ofReal (w z)))
  have hBCF : TendstoInMeasure P cutoffBCF atTop limit := by
    simpa [cutoffBCF, limit] using
      regularizedGMC_varyingWeighted_finiteCoordinatePath_tendstoInMeasure
        P X hX Xc hXc γ M hM
        (fun f => gaussianCovariance P (fun ω => X ω f) L)
        u hu w hw hconv s
  have hcutoffEq : ∀ᶠ r : ℝ in atTop, cutoffBCF r =ᵐ[P] cutoffExact r := by
    filter_upwards [heventual] with r hr
    have hmeasure (ω : Ω) :
        (regularizedGMC P Xc γ r ω).withDensity (fun z => ENNReal.ofReal (u r z)) =
        (regularizedGMC P Xc γ r ω).withDensity (fun z => ENNReal.ofReal (Real.exp
          (γ * gaussianCovariance P (fun ω' => Xc ω' z r) L))) := by
      rw [(show (fun z => ENNReal.ofReal (u r z)) = fun z => ENNReal.ofReal (Real.exp (γ * gaussianCovariance P (fun ω' => Xc ω' z r) L)) by funext z; rw [hr z])]
    filter_upwards [] with ω
    simp [cutoffBCF, cutoffExact, hmeasure ω]
  refine ⟨u, w, hu, hw, hconv, heventual, ?_⟩
  exact hBCF.congr' hcutoffEq EventuallyEq.rfl

/-- The uniform limit of the bounded-continuous covariance exponential weights is the stated
exponential of the limiting covariance profile. -/
theorem equatorGFF_expCovariance_weight_limit_value
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Xc : Ω → ℂ → ℝ → ℝ) L γ
    c
    (hc : TendstoUniformly
      (fun r z => gaussianCovariance P (fun ω => Xc ω z r) L) c atTop)
    (u : ℝ → BoundedContinuousFunction ℂ ℝ)
    w
    (hconv : TendstoUniformly (fun r z => u r z) w atTop)
    (heventual : ∀ᶠ r : ℝ in atTop, ∀ z : ℂ,
      u r z = Real.exp (γ * gaussianCovariance P (fun ω => Xc ω z r) L))
    z : w z = Real.exp (γ * c z) := by
  exact tendsto_nhds_unique (hconv.tendsto_at z) (((Real.continuous_exp.tendsto (γ * c z)).comp (tendsto_const_nhds.mul (hc.tendsto_at z))).congr' (show (fun r => u r z) =ᶠ[atTop] fun r => Real.exp (γ * gaussianCovariance P (fun ω => Xc ω z r) L) by filter_upwards [heventual] with r hr; exact hr z).symm)

/-- Equality of the finite-dimensional weak limits passes the exact finite-radius
Cameron--Martin identity to the limiting chaos coordinates. -/
theorem equatorGFF_finiteGmcCoordinate_limit_law
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (γ : ℝ) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (L : Ω → ℝ) (hL : IsGaussianL2Limit P X L)
    (c : BoundedContinuousFunction ℂ ℝ)
    (hc : TendstoUniformly
      (fun r z => gaussianCovariance P (fun ω => Xc ω z r) L) c atTop)
    (s : Finset gmcTiltCoordinateIndex) :
    Measure.map
      (fun ω => gmcTiltFiniteCoordinatePath s (fun f => X ω f) (M ω))
      (P.withDensity (fun ω => ENNReal.ofReal
        (Real.exp (L ω - gaussianVariance P L / 2)))) =
    Measure.map
      (fun ω => gmcTiltFiniteCoordinatePath s
        (fun f => X ω f + gaussianCovariance P (fun ω' => X ω' f) L)
        ((M ω).withDensity (fun z => ENNReal.ofReal (Real.exp (γ * c z))))) P := by
  classical
  have equatorGFF_unweightedFiniteCoordinate_tendstoInMeasure_under_tilt (P : Measure Ω) X (hX : IsEquatorGFF P X) Xc (hXc : IsCircleAverage P X Xc) (γ : ℝ) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) L (hL : IsGaussianL2Limit P X L) s : TendstoInMeasure (P.withDensity (fun ω => ENNReal.ofReal (Real.exp (L ω - gaussianVariance P L / 2)))) (fun r ω => gmcTiltFiniteCoordinatePath s (fun f => X ω f) (regularizedGMC P Xc γ r ω)) atTop (fun ω => gmcTiltFiniteCoordinatePath s (fun f => X ω f) (M ω)) := by
    have regularizedGMC_finiteCoordinatePath_tendstoInMeasure : TendstoInMeasure P (fun r ω => gmcTiltFiniteCoordinatePath s (fun f => X ω f) (regularizedGMC P Xc γ r ω)) atTop (fun ω => gmcTiltFiniteCoordinatePath s (fun f => X ω f) (M ω)) := by
      apply tendstoInMeasure_pi_of_coord P s
      intro i
      change TendstoInMeasure P
        (fun r ω => gmcTiltCoordinatePath (fun f => X ω f)
          (regularizedGMC P Xc γ r ω) i.1) atTop
        (fun ω => gmcTiltCoordinatePath (fun f => X ω f) (M ω) i.1)
      rcases i.1 with f | j
      · intro ε hε
        simp [gmcTiltCoordinatePath, hε.ne']
      · cases j with
        | none =>
          simpa [gmcTiltFiniteCoordinatePath, gmcTiltCoordinatePath,
            gmcTiltCoordinateSet, gmcCoordinateB] using (regularizedGMC_withDensity_univ_mass_tendstoInMeasure P X hX Xc hXc γ M hM (1 : BoundedContinuousFunction ℂ ℝ) (by intro z; norm_num))
        | some j =>
          simpa [gmcTiltFiniteCoordinatePath, gmcTiltCoordinatePath,
            gmcTiltCoordinateSet, gmcCoordinateB] using
            regularizedGMC_box_mass_tendstoInMeasure P X hX Xc hXc γ M hM j
    have exists_measurable_unweighted_finitePath_proxy : ∃ G : Ω → (∀ _i : {i // i ∈ s}, ℝ), Measurable G ∧ (fun ω => gmcTiltFiniteCoordinatePath s (fun f => X ω f) (M ω)) =ᵐ[P] G := by
      obtain ⟨E, hE, hEae⟩ := equatorGFF_GMC_finiteEval_field_proxy P X hX γ M hM
      let eval : Ω → TestFn → ℝ := fun ω f => X ω f
      let G : Ω → (∀ _i : {i // i ∈ s}, ℝ) := fun ω i =>
        match i.1 with
        | .inl f => eval ω f
        | .inr j => (E (eval ω) j).toReal
      have hG : Measurable G := by
        rw [measurable_pi_iff]
        intro i
        cases hi : i.1 with
        | inl f =>
          simpa [G, hi, eval, Function.comp_def] using (hX.2 f).1
        | inr j =>
          simpa [G, hi, eval, Function.comp_def] using ENNReal.measurable_toReal.comp
            ((measurable_pi_apply j).comp (hE.comp (by rw [measurable_pi_iff]; exact fun f => (hX.2 f).1)))
      have hEq : (fun ω => gmcTiltFiniteCoordinatePath s (eval ω) (M ω)) =ᵐ[P] G := by
        filter_upwards [hEae] with ω hω
        funext i
        cases hi : i.1 with
        | inl f =>
          simp [gmcTiltFiniteCoordinatePath, gmcTiltCoordinatePath, G, eval, hi]
        | inr j =>
          simp only [gmcTiltFiniteCoordinatePath, gmcTiltCoordinatePath, G, hi, eval]
          convert congrArg ENNReal.toReal (congrFun hω j) using 1
          all_goals cases j <;> rfl
      exact ⟨G, hG, hEq⟩
    let density : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal
      (Real.exp (L ω - gaussianVariance P L / 2))
    let Q := P.withDensity density
    let field : Ω → TestFn → ℝ := fun ω f => X ω f
    obtain ⟨proxy, hproxyMeas, hproxyAE⟩ :=
      exists_measurable_unweighted_finitePath_proxy
    exact (tendstoInMeasure_withDensity_of_lintegral_lt_top density (by rw [(show ∫⁻ ω, density ω ∂P = 1 by simpa [density] using @equatorGFF_gaussianL2_tilt_density_integral_eq_one Ω _ P hX.1 X hX Xc hXc L hL)]; norm_num) (show ∀ r, Measurable (fun ω => gmcTiltFiniteCoordinatePath s (field ω) (regularizedGMC P Xc γ r ω)) by intro r; exact (measurable_gmcTiltFiniteCoordinatePath s).comp (Measurable.prodMk (by rw [measurable_pi_iff]; exact fun f => (hX.2 f).1) (regularizedGMC_measurable P X hX Xc hXc γ r))) hproxyMeas ((regularizedGMC_finiteCoordinatePath_tendstoInMeasure).congr_right (by simpa [field] using hproxyAE))).congr_right ((withDensity_ae_eq (by exact ENNReal.measurable_ofReal.comp_aemeasurable (Real.measurable_exp.comp_aemeasurable (hL.1.aestronglyMeasurable.aemeasurable.sub_const _))) (by filter_upwards [] with ω; apply (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne')).2 (by simpa [field, Q, density] using hproxyAE)).symm
  have measurable_regularizedGMC_withDensity (r : ℝ) (W : ℂ → ℝ≥0∞) (hW : Measurable W) : Measurable (fun ω => (regularizedGMC P Xc γ r ω).withDensity W) := by
    apply Measure.measurable_of_measurable_coe
    intro A hA
    rw [(show (fun ω => (regularizedGMC P Xc γ r ω).withDensity W A) = fun ω => ∫⁻ z, A.indicator W z ∂regularizedGMC P Xc γ r ω by funext ω; rw [withDensity_apply _ hA, ← lintegral_indicator hA])]
    exact (Measure.measurable_lintegral (hW.indicator hA)).comp (regularizedGMC_measurable P X hX Xc hXc γ r)
  let density : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal
    (Real.exp (L ω - gaussianVariance P L / 2))
  let Q := P.withDensity density
  let field : Ω → TestFn → ℝ := fun ω f => X ω f
  let shift : TestFn → ℝ := fun f => gaussianCovariance P (fun ω => X ω f) L
  let leftCutoff : ℝ → Ω → (∀ _i : {i // i ∈ s}, ℝ) := fun r ω =>
    gmcTiltFiniteCoordinatePath s (field ω) (regularizedGMC P Xc γ r ω)
  let leftLimit : Ω → (∀ _i : {i // i ∈ s}, ℝ) := fun ω =>
    gmcTiltFiniteCoordinatePath s (field ω) (M ω)
  obtain ⟨u, w, hu, hw, hconv, heventual, hrightMeasure⟩ :=
    equatorGFF_expCovariance_finiteCoordinate_tendstoInMeasure
      P X hX Xc hXc γ M hM L hL c hc s
  let rightCutoff : ℝ → Ω → (∀ _i : {i // i ∈ s}, ℝ) := fun r ω =>
    gmcTiltFiniteCoordinatePath s (fun f => field ω f + shift f)
      ((regularizedGMC P Xc γ r ω).withDensity
        (fun z => ENNReal.ofReal (Real.exp
          (γ * gaussianCovariance P (fun ω' => Xc ω' z r) L))))
  let rightLimit : Ω → (∀ _i : {i // i ∈ s}, ℝ) := fun ω =>
    gmcTiltFiniteCoordinatePath s (fun f => field ω f + shift f)
      ((M ω).withDensity (fun z => ENNReal.ofReal (w z)))
  have hQprob : IsProbabilityMeasure Q := by
    refine ⟨?_⟩
    have hQmass : Q Set.univ = ∫⁻ ω, density ω ∂P := by
      dsimp [Q]
      rw [withDensity_apply density MeasurableSet.univ]
      simp
    rw [hQmass]
    exact (by simpa [density] using @equatorGFF_gaussianL2_tilt_density_integral_eq_one Ω _ P hX.1 X hX Xc hXc L hL)
  have hleftDistAux [IsProbabilityMeasure Q] := (show TendstoInMeasure Q leftCutoff atTop leftLimit by simpa [leftCutoff, leftLimit, Q, density, field] using equatorGFF_unweightedFiniteCoordinate_tendstoInMeasure_under_tilt P X hX Xc hXc γ M hM L hL s).tendstoInDistribution (fun r => ((show ∀ r, Measurable (leftCutoff r) by intro r; exact (measurable_gmcTiltFiniteCoordinatePath s).comp (Measurable.prodMk (by rw [measurable_pi_iff]; exact fun f => (hX.2 f).1) (regularizedGMC_measurable P X hX Xc hXc γ r))) r).aemeasurable)
  have hrightDistAux [IsProbabilityMeasure P] := (show TendstoInMeasure P rightCutoff atTop rightLimit by simpa [rightCutoff, rightLimit, field, shift] using hrightMeasure).tendstoInDistribution (fun r => ((show ∀ r, Measurable (rightCutoff r) by intro r; exact (measurable_gmcTiltFiniteCoordinatePath s).comp (Measurable.prodMk (by rw [measurable_pi_iff]; intro f; exact (hX.2 f).1.add measurable_const) (measurable_regularizedGMC_withDensity r _ (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul (continuous_gaussianCovariance_circle_of_IsGaussianL2Limit P X hX Xc hXc L hL r).measurable)))))) r).aemeasurable)
  have hcutlaw (r : ℝ) : Measure.map (leftCutoff r) Q = Measure.map (rightCutoff r) P := by
    dsimp [leftCutoff, rightCutoff, Q, density, field, shift]
    exact equatorGFF_tilted_finiteGmcCoordinate_law_at_cutoff
      P X hX Xc hXc γ L hL s r
  have hseqAux [IsProbabilityMeasure Q] [IsProbabilityMeasure P] :
      (fun r : ℝ => (⟨Q.map (leftCutoff r), inferInstance⟩ :
        ProbabilityMeasure (∀ _i : {i // i ∈ s}, ℝ))) = fun r =>
      (⟨P.map (rightCutoff r), inferInstance⟩ :
        ProbabilityMeasure (∀ _i : {i // i ∈ s}, ℝ)) := by
    funext r
    apply Subtype.ext
    exact hcutlaw r
  have hrightTendsto := @TendstoInDistribution.tendsto
    (ι := ℝ) (E := ∀ _i : {i // i ∈ s}, ℝ) (Ω' := Ω)
    (Ω := fun _ => Ω) (m := fun _ => inferInstance)
    (m' := inferInstance) (mE := inferInstance) inferInstance inferInstance
    (X := rightCutoff) (l := atTop) (Z := rightLimit)
    (μ := fun _ => P) (fun _ => hX.1)
    (μ' := P) hX.1 (@hrightDistAux hX.1)
  rw [← (@hseqAux hQprob hX.1)] at hrightTendsto
  have hlimit := tendsto_nhds_unique (@TendstoInDistribution.tendsto (ι := ℝ) (E := ∀ _i : {i // i ∈ s}, ℝ) (Ω' := Ω) (Ω := fun _ => Ω) (m := fun _ => inferInstance) (m' := inferInstance) (mE := inferInstance) inferInstance inferInstance (X := leftCutoff) (l := atTop) (Z := leftLimit) (μ := fun _ => Q) (fun _ => hQprob) (μ' := Q) hQprob (@hleftDistAux hQprob)) hrightTendsto
  have hrightPath : (fun ω => gmcTiltFiniteCoordinatePath s
      (fun f => X ω f + gaussianCovariance P (fun ω' => X ω' f) L)
      ((M ω).withDensity (fun z => ENNReal.ofReal (Real.exp (γ * c z))))) = rightLimit := by
    funext ω
    simp only [rightLimit, field, shift]
    simp_rw [(show (fun z : ℂ => ENNReal.ofReal (Real.exp (γ * c z))) = fun z => ENNReal.ofReal (w z) by funext z; rw [← (show ∀ z : ℂ, w z = Real.exp (γ * c z) by intro z; exact equatorGFF_expCovariance_weight_limit_value P Xc L γ c hc u w hconv heventual z) z])]
  change Measure.map (fun ω => gmcTiltFiniteCoordinatePath s
      (fun f => X ω f) (M ω)) (P.withDensity density) =
    Measure.map (fun ω => gmcTiltFiniteCoordinatePath s
      (fun f => X ω f + gaussianCovariance P (fun ω' => X ω' f) L)
      ((M ω).withDensity (fun z => ENNReal.ofReal (Real.exp (γ * c z))))) P
  rw [(show (fun ω => gmcTiltFiniteCoordinatePath s (fun f => X ω f) (M ω)) = leftLimit by funext ω; rfl), hrightPath]
  change Measure.map leftLimit Q = Measure.map rightLimit P
  exact (congrArg Subtype.val hlimit)

end DOZZ.Proofs
