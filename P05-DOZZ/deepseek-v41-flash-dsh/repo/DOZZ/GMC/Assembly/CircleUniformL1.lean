/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Assembly.CircleIntensity
public import DOZZ.GMC.Construction.GMCUniformL1FromCauchy
public import DOZZ.GMC.Assembly.CutoffIntegral
public import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
public import DOZZ.GMC.Construction.ReferenceMeasureTight

/-! Uniform `L¹` convergence of the circle cutoff chaos (proof of `DOZZ.equatorGFF_GMC_uniform_L1`)
and `L¹` continuity of circle GMC masses in the charge (proof of
`DOZZ.equatorGFF_GMC_L1_continuous_gamma`). -/

@[expose] public section

/-! ### Uniform `L¹` convergence

Uniform `L¹` convergence of the circle cutoff chaos to the GMC, uniformly over compact
charge intervals and bounded Borel tests supported in a compact set.

Continuous tests converge uniformly by the cutoff `L¹` Cauchy estimate and Fatou along convergence
in measure. A Borel test is within any prescribed reference `L¹` distance of a continuous test
with the same bound; both the cutoff chaos and the limit have intensity at most the reference
measure, so this distance controls both approximation errors. -/

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs

open DOZZ.Assembly

/-- Uniform `L¹` convergence of regularized GMC masses on compact charge intervals, uniformly
over bounded Borel tests supported in a compact set. -/
theorem equatorGFF_GMC_uniform_L1
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X) (Xc : Ω → ℂ → ℝ → ℝ)
    (hXc : IsCircleAverage P X Xc) (Mfam : ℝ → Ω → Measure ℂ)
    (hMfam : ∀ γ ∈ Set.Ioo (0 : ℝ) 2, IsGMCOf P X γ (Mfam γ))
    (I : Set ℝ) (hI : IsCompact I) (hI2 : I ⊆ Set.Ioo 0 2)
    (K : Set ℂ) (hK : IsCompact K) (Lb : ℝ) :
    Tendsto (fun r : ℝ => ⨆ γ ∈ I, ⨆ (f : ℂ → ℝ) (_ : Measurable f)
        (_ : ∀ x, |f x| ≤ Lb) (_ : ∀ x ∉ K, f x = 0),
        ∫⁻ ω, ENNReal.ofReal
          |∫ x, f x ∂regularizedGMC P Xc γ r ω - ∫ x, f x ∂Mfam γ ω| ∂P)
      atTop (𝓝 0) := by
  classical
  have : IsProbabilityMeasure P := hX.1
  have : IsFiniteMeasure gmcReferenceMeasure :=
    ⟨lt_top_iff_ne_top.mpr gmcReferenceMeasure_univ_ne_top⟩
  obtain ⟨ρ, hρ⟩ : ∃ ρ, K ⊆ Metric.closedBall (0 : ℂ) ρ := hK.isBounded.subset_closedBall 0
  set Lb' : ℝ := max Lb 0 with hLb'def
  set K' : Set ℂ := Metric.closedBall (0 : ℂ) (ρ + 1) with hK'def
  let ι := {p : ℝ × (ℂ → ℝ) // p.1 ∈ I ∧ Continuous p.2 ∧ (∀ x, |p.2 x| ≤ Lb') ∧
    ∀ x, ρ + 1 < ‖x‖ → p.2 x = 0}
  let bcf : ι → BoundedContinuousFunction ℂ ℝ := fun i => BoundedContinuousFunction.ofNormedAddCommGroup i.1.2
    i.2.2.1 Lb' (fun x => by rw [Real.norm_eq_abs]; exact i.2.2.2.1 x)
  let F : ℝ → ι → Ω → ℝ := fun r i ω => ∫ x, i.1.2 x ∂regularizedGMC P Xc i.1.1 r ω
  let G : ι → Ω → ℝ := fun i ω => ∫ x, i.1.2 x ∂Mfam i.1.1 ω
  have hFmeas : ∀ r i, Measurable (F r i) := fun r i =>
    regularizedGMC_integral_measurable P X hX Xc hXc _ r _ i.2.2.1.measurable
  have hFG : ∀ i, TendstoInMeasure P (fun r => F r i) atTop (G i) := fun i =>
    isGMCOf_tendstoInMeasure P X hX Xc hXc i.1.1 (Mfam i.1.1) (hMfam _ (hI2 i.2.1)) (bcf i)
  have hCauchy : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ r ≥ R, ∀ s ≥ R, ∀ i,
      ∫⁻ ω, ENNReal.ofReal |F r i ω - F s i ω| ∂P < ENNReal.ofReal ε := by
    intro ε hε
    obtain ⟨R, hR⟩ := regularizedGMC_integral_L1_uniform_cauchy P X hX Xc hXc I hI hI2 K' (isCompact_closedBall _ _)
      Lb' ε hε
    refine ⟨R, fun r hr s hs i => hR r s hr hs i.1.1 i.2.1 i.1.2 i.2.2.1.measurable i.2.2.2.1
      (fun x hx => i.2.2.2.2 x ?_)⟩
    simpa [K', Metric.mem_closedBall, dist_zero_right] using hx
  have hS := tendsto_iSup_lintegral_abs_sub_of_uniform_l1_cauchy P F G hFmeas hFG hCauchy
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hS (fun r => zero_le)
    (fun r => ?_)
  refine iSup₂_le fun γ hγ => iSup_le fun f => iSup_le fun hf => iSup_le fun hfL =>
    iSup_le fun hfK => ?_
  have hγ2 := hI2 hγ
  have hM := hMfam γ hγ2
  obtain ⟨N, hNmeas, -, hMN⟩ :=
    DOZZ.Proofs.equatorGFF_GMC_measurable_version P X hX γ hγ2.1 hγ2.2 (Mfam γ) hM
  apply ENNReal.le_of_forall_pos_le_add
  intro δ hδ _
  have hδ2 : ((δ / 2 : ℝ≥0) : ℝ≥0∞) ≠ 0 := by
    simpa using (half_pos hδ).ne'
  have hfρ : ∀ x, ρ < ‖x‖ → f x = 0 := fun x hx => hfK x (fun hxK => by
    have := hρ hxK
    rw [Metric.mem_closedBall, dist_zero_right] at this
    linarith)
  obtain ⟨h, hcont, hhL, hhsupp, happrox⟩ := exists_continuous_L1_approx gmcReferenceMeasure ρ
    Lb' f hf (fun x => (hfL x).trans (le_max_left _ _)) hfρ _ hδ2
  let i : ι := ⟨(γ, h), hγ, hcont, hhL, hhsupp⟩
  have hfh : Measurable (fun x => ENNReal.ofReal |f x - h x|) :=
    ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp (hf.sub hcont.measurable))
  have hhf : Measurable (fun x => ENNReal.ofReal |h x - f x|) :=
    ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp (hcont.measurable.sub hf))
  have hpt : ∀ᵐ ω ∂P, ENNReal.ofReal |∫ x, f x ∂regularizedGMC P Xc γ r ω -
      ∫ x, f x ∂Mfam γ ω| ≤
      ∫⁻ x, ENNReal.ofReal |f x - h x| ∂regularizedGMC P Xc γ r ω +
        (ENNReal.ofReal |F r i ω - G i ω| + ∫⁻ x, ENNReal.ofReal |h x - f x| ∂N ω) := by
    filter_upwards [hMN] with ω hω
    set A := ∫ x, f x ∂regularizedGMC P Xc γ r ω
    set A' := ∫ x, h x ∂regularizedGMC P Xc γ r ω
    set B' := ∫ x, h x ∂Mfam γ ω
    set B := ∫ x, f x ∂Mfam γ ω
    have hFi : F r i ω = A' := rfl
    have hGi : G i ω = B' := rfl
    rw [hFi, hGi]
    calc ENNReal.ofReal |A - B| ≤ ENNReal.ofReal (|A - A'| + |A' - B'| + |B' - B|) := by
          apply ENNReal.ofReal_le_ofReal
          calc |A - B| = |(A - A') + (A' - B') + (B' - B)| := by ring_nf
            _ ≤ |A - A'| + |A' - B'| + |B' - B| := abs_add_three _ _ _
      _ = ENNReal.ofReal |A - A'| + (ENNReal.ofReal |A' - B'| + ENNReal.ofReal |B' - B|) := by
          rw [ENNReal.ofReal_add (by positivity) (abs_nonneg _),
            ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _), add_assoc]
      _ ≤ _ := by
          gcongr
          · exact ofReal_abs_integral_sub_le_lintegral _ f h hf hcont.measurable
          · calc ENNReal.ofReal |B' - B| ≤ ∫⁻ x, ENNReal.ofReal |h x - f x| ∂Mfam γ ω :=
                ofReal_abs_integral_sub_le_lintegral (Mfam γ ω) h f hcont.measurable hf
              _ = ∫⁻ x, ENNReal.ofReal |h x - f x| ∂N ω := by rw [hω]
  have ha : Measurable (fun ω => ∫⁻ x, ENNReal.ofReal |f x - h x| ∂regularizedGMC P Xc γ r ω) :=
    (Measure.measurable_lintegral hfh).comp (regularizedGMC_measurable P X hX Xc hXc γ r)
  have hc : Measurable (fun ω => ∫⁻ x, ENNReal.ofReal |h x - f x| ∂N ω) :=
    (Measure.measurable_lintegral hhf).comp hNmeas
  have hA : ∫⁻ ω, ∫⁻ x, ENNReal.ofReal |f x - h x| ∂regularizedGMC P Xc γ r ω ∂P ≤
      ((δ / 2 : ℝ≥0) : ℝ≥0∞) := by
    rw [regularizedGMC_lintegral_test_eq_reference P X hX Xc hXc γ r _ hfh]
    exact happrox
  have hC : ∫⁻ ω, ∫⁻ x, ENNReal.ofReal |h x - f x| ∂N ω ∂P ≤ ((δ / 2 : ℝ≥0) : ℝ≥0∞) := by
    calc ∫⁻ ω, ∫⁻ x, ENNReal.ofReal |h x - f x| ∂N ω ∂P =
          ∫⁻ ω, ∫⁻ x, ENNReal.ofReal |h x - f x| ∂Mfam γ ω ∂P := by
          apply lintegral_congr_ae
          filter_upwards [hMN] with ω hω
          rw [hω]
      _ ≤ ∫⁻ x, ENNReal.ofReal |h x - f x| ∂gmcReferenceMeasure :=
          isGMCOf_lintegral_le P X hX γ hγ2.1 hγ2.2 (Mfam γ) hM _ hhf
      _ = ∫⁻ x, ENNReal.ofReal |f x - h x| ∂gmcReferenceMeasure := by
          apply lintegral_congr
          intro x
          rw [abs_sub_comm]
      _ ≤ _ := happrox
  have hB : ∫⁻ ω, ENNReal.ofReal |F r i ω - G i ω| ∂P ≤
      ⨆ j, ∫⁻ ω, ENNReal.ofReal |F r j ω - G j ω| ∂P :=
    le_iSup (fun j => ∫⁻ ω, ENNReal.ofReal |F r j ω - G j ω| ∂P) i
  calc ∫⁻ ω, ENNReal.ofReal |∫ x, f x ∂regularizedGMC P Xc γ r ω - ∫ x, f x ∂Mfam γ ω| ∂P
      ≤ ∫⁻ ω, ∫⁻ x, ENNReal.ofReal |f x - h x| ∂regularizedGMC P Xc γ r ω +
        (ENNReal.ofReal |F r i ω - G i ω| + ∫⁻ x, ENNReal.ofReal |h x - f x| ∂N ω) ∂P :=
        lintegral_mono_ae hpt
    _ = ∫⁻ ω, ∫⁻ x, ENNReal.ofReal |f x - h x| ∂regularizedGMC P Xc γ r ω ∂P +
        (∫⁻ ω, ENNReal.ofReal |F r i ω - G i ω| ∂P +
          ∫⁻ ω, ∫⁻ x, ENNReal.ofReal |h x - f x| ∂N ω ∂P) := by
        rw [lintegral_add_left ha, lintegral_add_right _ hc]
    _ ≤ ((δ / 2 : ℝ≥0) : ℝ≥0∞) + ((⨆ j, ∫⁻ ω, ENNReal.ofReal |F r j ω - G j ω| ∂P) +
        ((δ / 2 : ℝ≥0) : ℝ≥0∞)) := add_le_add hA (add_le_add hB hC)
    _ = (⨆ j, ∫⁻ ω, ENNReal.ofReal |F r j ω - G j ω| ∂P) + δ := by
        rw [add_comm, add_assoc, ← ENNReal.coe_add, add_halves]

end DOZZ.Proofs

/-! ### Fixed-cutoff continuity in the charge

At a fixed cutoff, admissible cutoff integrals are continuous in the charge in `L¹(P)`.

The Wick weights `exp (γ Z - γ² v / 2)` of a centered Gaussian `Z` with variance `v` are dominated,
for charges near `γ₀`, by `2 (exp (c Z) + exp (-c Z))`, whose expectation is finite by Wick
normalization; dominated convergence in the sample and then in the point gives continuity. -/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace DOZZ.Assembly

open DOZZ.Proofs

/-- The Gaussian exponential moments of one admissible coordinate are finite. -/
theorem admissible_lintegral_exp_mul_ne_top
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ : ℝ)
    (Y : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y) (ε : ℝ) (hε : 0 < ε) (hεcut : ε ≤ ε₀)
    (x : ℂ) (t : ℝ) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (t * Y ω ε x)) ∂P ≠ ⊤ := by
  have hone := lintegral_admissibleLogWickWeight P U dens ε₀ Y hY t ε hε hεcut x
  have heq : (fun ω => ENNReal.ofReal (Real.exp (t * Y ω ε x))) = fun ω =>
      ENNReal.ofReal (Real.exp (t ^ 2 / 2 * gaussianVariance P (fun ω => Y ω ε x))) *
        admissibleLogWickWeight P Y t ε x ω := by
    funext ω
    unfold admissibleLogWickWeight
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2
    ring
  rw [heq, lintegral_const_mul _ (admissibleLogWickWeight_measurable_sample P U dens ε₀ Y hY t ε x),
    hone, mul_one]
  exact ENNReal.ofReal_ne_top

/-- The Wick weight at one point is continuous in the charge in `L¹(P)`. -/
theorem admissible_wick_weight_L1_continuous
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ : ℝ)
    (Y : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y) (ε : ℝ) (hε : 0 < ε) (hεcut : ε ≤ ε₀)
    (x : ℂ) (γ₀ : ℝ) :
    Tendsto (fun γ => ∫⁻ ω, ENNReal.ofReal
        |Real.exp (γ * Y ω ε x - γ ^ 2 / 2 * ∫ ω', Y ω' ε x ^ 2 ∂P) -
          Real.exp (γ₀ * Y ω ε x - γ₀ ^ 2 / 2 * ∫ ω', Y ω' ε x ^ 2 ∂P)| ∂P)
      (𝓝 γ₀) (𝓝 0) := by
  set v : ℝ := ∫ ω', Y ω' ε x ^ 2 ∂P with hvdef
  set c : ℝ := |γ₀| + 1 with hcdef
  have hZ : Measurable (fun ω => Y ω ε x) := admissible_field_measurable_sample P U dens ε₀ Y hY ε x
  let bound : Ω → ℝ≥0∞ := fun ω => 2 * (ENNReal.ofReal (Real.exp (c * Y ω ε x)) +
    ENNReal.ofReal (Real.exp (-c * Y ω ε x)))
  have hexp_le (t z : ℝ) (ht : |t| ≤ c) :
      Real.exp (t * z) ≤ Real.exp (c * z) + Real.exp (-c * z) := by
    have hle : t * z ≤ c * |z| := by
      calc t * z ≤ |t * z| := le_abs_self _
        _ = |t| * |z| := abs_mul _ _
        _ ≤ c * |z| := mul_le_mul_of_nonneg_right ht (abs_nonneg _)
    rcases le_total 0 z with hz | hz
    · rw [abs_of_nonneg hz] at hle
      exact (Real.exp_le_exp.mpr hle).trans (le_add_of_nonneg_right (Real.exp_pos _).le)
    · rw [abs_of_nonpos hz] at hle
      have : t * z ≤ -c * z := by linarith
      exact (Real.exp_le_exp.mpr this).trans (le_add_of_nonneg_left (Real.exp_pos _).le)
  have hweight_le (t z : ℝ) (ht : |t| ≤ c) :
      Real.exp (t * z - t ^ 2 / 2 * v) ≤ Real.exp (c * z) + Real.exp (-c * z) := by
    refine le_trans (Real.exp_le_exp.mpr ?_) (hexp_le t z ht)
    have : 0 ≤ t ^ 2 / 2 * v := by positivity
    linarith
  rw [show (𝓝 (0 : ℝ≥0∞)) = 𝓝 (∫⁻ _ : Ω, (0 : ℝ≥0∞) ∂P) by rw [lintegral_zero]]
  apply tendsto_lintegral_filter_of_dominated_convergence (f := fun _ => 0) bound
  · filter_upwards [] with γ
    exact ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp
      ((Real.measurable_exp.comp ((hZ.const_mul γ).sub_const _)).sub
        (Real.measurable_exp.comp ((hZ.const_mul γ₀).sub_const _))))
  · have hball : ∀ᶠ γ in 𝓝 γ₀, |γ| ≤ c := by
      filter_upwards [Metric.ball_mem_nhds γ₀ one_pos] with γ hγ
      rw [Metric.mem_ball, Real.dist_eq] at hγ
      have := abs_sub_abs_le_abs_sub γ γ₀
      rw [hcdef]
      linarith
    filter_upwards [hball] with γ hγ
    filter_upwards [] with ω
    have hγ₀c : |γ₀| ≤ c := by rw [hcdef]; linarith
    have h1 := hweight_le γ (Y ω ε x) hγ
    have h2 := hweight_le γ₀ (Y ω ε x) hγ₀c
    have hsum : |Real.exp (γ * Y ω ε x - γ ^ 2 / 2 * v) - Real.exp (γ₀ * Y ω ε x - γ₀ ^ 2 / 2 * v)|
        ≤ 2 * (Real.exp (c * Y ω ε x) + Real.exp (-c * Y ω ε x)) := by
      rw [abs_le]
      constructor <;> linarith [Real.exp_pos (γ * Y ω ε x - γ ^ 2 / 2 * v),
        Real.exp_pos (γ₀ * Y ω ε x - γ₀ ^ 2 / 2 * v)]
    calc ENNReal.ofReal |Real.exp (γ * Y ω ε x - γ ^ 2 / 2 * v) -
          Real.exp (γ₀ * Y ω ε x - γ₀ ^ 2 / 2 * v)|
        ≤ ENNReal.ofReal (2 * (Real.exp (c * Y ω ε x) + Real.exp (-c * Y ω ε x))) :=
          ENNReal.ofReal_le_ofReal hsum
      _ = bound ω := by
          simp only [bound]
          rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_add (Real.exp_pos _).le
            (Real.exp_pos _).le, ENNReal.ofReal_ofNat]
  · have h1 := admissible_lintegral_exp_mul_ne_top P U dens ε₀ Y hY ε hε hεcut x c
    have h2 := admissible_lintegral_exp_mul_ne_top P U dens ε₀ Y hY ε hε hεcut x (-c)
    have hm1 : Measurable (fun ω => ENNReal.ofReal (Real.exp (c * Y ω ε x))) :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hZ.const_mul c))
    have hm2 : Measurable (fun ω => ENNReal.ofReal (Real.exp (-c * Y ω ε x))) :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hZ.const_mul (-c)))
    have hm12 : Measurable (fun ω => ENNReal.ofReal (Real.exp (c * Y ω ε x)) +
        ENNReal.ofReal (Real.exp (-c * Y ω ε x))) := hm1.add hm2
    simp only [bound]
    rw [lintegral_const_mul _ hm12, lintegral_add_left hm1]
    exact ENNReal.mul_ne_top (by norm_num) (ENNReal.add_ne_top.mpr ⟨h1, h2⟩)
  · filter_upwards [] with ω
    have hcont : Continuous (fun γ : ℝ => ENNReal.ofReal
        |Real.exp (γ * Y ω ε x - γ ^ 2 / 2 * v) - Real.exp (γ₀ * Y ω ε x - γ₀ ^ 2 / 2 * v)|) :=
      ENNReal.continuous_ofReal.comp (by fun_prop)
    have h := hcont.tendsto γ₀
    simpa using h

end DOZZ.Assembly

/-! ### `L¹` continuity in the charge

`L¹` continuity of circle GMC masses in the charge, for bounded continuous tests.

A bounded continuous test splits into a compactly supported part and a tail. The tail is
uniformly small by the intensity bound and the reference tail. For the compact part, cutoff
masses converge uniformly on a compact charge neighbourhood, and at a fixed cutoff they depend
continuously on the charge in `L¹`. -/

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal

namespace DOZZ.Assembly

open DOZZ.Proofs

/-- The triangle inequality for expected absolute differences of almost everywhere measurable
real random variables. -/
theorem lintegral_ofReal_abs_sub_le_add
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (U V W : Ω → ℝ)
    (hU : AEMeasurable U P) (hV : AEMeasurable V P) :
    ∫⁻ ω, ENNReal.ofReal |U ω - W ω| ∂P ≤
      ∫⁻ ω, ENNReal.ofReal |U ω - V ω| ∂P + ∫⁻ ω, ENNReal.ofReal |V ω - W ω| ∂P := by
  have hUV : AEMeasurable (fun ω => ENNReal.ofReal |U ω - V ω|) P :=
    ENNReal.measurable_ofReal.comp_aemeasurable (continuous_abs.measurable.comp_aemeasurable
      (hU.sub hV))
  rw [← lintegral_add_left' hUV]
  apply lintegral_mono
  intro ω
  beta_reduce
  rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  calc |U ω - W ω| = |(U ω - V ω) + (V ω - W ω)| := by ring_nf
    _ ≤ |U ω - V ω| + |V ω - W ω| := abs_add_le _ _

end DOZZ.Assembly

namespace DOZZ.Proofs

open DOZZ.Assembly

end DOZZ.Proofs
