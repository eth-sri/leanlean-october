/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.IsGMCOf
public import DOZZ.Statements.Defs.IsEquatorGFF
import DOZZ.GMC.Construction.RegularizedGMCExpectedMeasure
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.MeasurableSpace.Prod
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Measurable versions for random measures defined by weak limits in probability. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set MeasurableSpace
open scoped Distributions ENNReal NNReal BoundedContinuousFunction

noncomputable section

namespace DOZZ.Proofs



private def ratLowerIntervals : Set (Set ℝ) :=
  ⋃ q : ℚ, {Set.Iic (q : ℝ)}


private def ratLowerRectangles : Set (Set (ℝ × ℝ)) :=
  Set.image2 (fun s t : Set ℝ => s ×ˢ t) ratLowerIntervals ratLowerIntervals



private abbrev realProdEquiv : ℂ ≃ᵐ ℝ × ℝ := Complex.measurableEquivRealProd

private def lowerBox (i : ℚ × ℚ) : Set ℂ :=
  realProdEquiv ⁻¹' (Set.Iic (i.1 : ℝ) ×ˢ Set.Iic (i.2 : ℝ))

private def lowerBoxFamily : Set (Set ℂ) :=
  {s | ∃ t ∈ ratLowerRectangles, realProdEquiv ⁻¹' t = s}




private def basisSet : Option (ℚ × ℚ) → Set ℂ
  | none => Set.univ
  | some i => lowerBox i

private def basisFamily : Set (Set ℂ) := Set.range basisSet




private def lowerApprox (q : ℚ) (n : ℕ) (x : ℝ) : ℝ :=
  max 0 (min 1 (1 - (n : ℝ) * (x - q)))




private def lowerBoxApproxFun (i : ℚ × ℚ) (n : ℕ) (z : ℂ) : ℝ :=
  lowerApprox i.1 n z.re * lowerApprox i.2 n z.im

private theorem lowerBoxApproxFun_continuous i n :
    Continuous (lowerBoxApproxFun i n) := by
  have lowerApprox_continuous q n : Continuous (lowerApprox q n) := by
    change Continuous (fun x : ℝ => max 0 (min 1 (1 - (n : ℝ) * (x - q))))
    fun_prop
  exact ((lowerApprox_continuous i.1 n).comp Complex.continuous_re).mul
    ((lowerApprox_continuous i.2 n).comp Complex.continuous_im)

private theorem lowerBoxApprox_bounds i n z :
    0 ≤ lowerBoxApproxFun i n z ∧ lowerBoxApproxFun i n z ≤ 1 := by
  have lowerApprox_bounds q n x : 0 ≤ lowerApprox q n x ∧ lowerApprox q n x ≤ 1 := by
    constructor
    · exact le_max_left _ _
    · exact max_le_iff.mpr ⟨by norm_num, min_le_left _ _⟩
  have h₁ := lowerApprox_bounds i.1 n z.re
  have h₂ := lowerApprox_bounds i.2 n z.im
  constructor
  · exact mul_nonneg h₁.1 h₂.1
  · calc
      lowerApprox i.1 n z.re * lowerApprox i.2 n z.im ≤
          1 * lowerApprox i.2 n z.im :=
        mul_le_mul_of_nonneg_right h₁.2 h₂.1
      _ ≤ 1 := by simpa using h₂.2

private def lowerBoxApprox (i : ℚ × ℚ) (n : ℕ) : BoundedContinuousFunction ℂ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨lowerBoxApproxFun i n, lowerBoxApproxFun_continuous i n⟩
    1 (by
      intro z w
      have hz := lowerBoxApprox_bounds i n z
      have hw := lowerBoxApprox_bounds i n w
      change dist (lowerBoxApproxFun i n z) (lowerBoxApproxFun i n w) ≤ 1
      rw [Real.dist_eq]
      rw [abs_le]
      constructor <;> linarith)





theorem equatorGFF_GMC_measurable_version
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) X (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) :
    ∃ N : Ω → Measure ℂ, Measurable N ∧ (∀ ω, IsFiniteMeasure (N ω)) ∧
      ∀ᵐ ω ∂P, M ω = N ω := by
  classical
  have lowerApprox_tendsto (q : ℚ) x : Tendsto (fun n : ℕ => lowerApprox q n x) atTop (𝓝 (if x ≤ (q : ℝ) then 1 else 0)) := by
    by_cases hx : x ≤ (q : ℝ)
    · have heq : ∀ n, lowerApprox q n x = 1 := by
        intro n
        have harg : 1 ≤ 1 - (n : ℝ) * (x - q) := by
          nlinarith [mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg n) (sub_nonpos.mpr hx)]
        simp [lowerApprox, min_eq_left harg]
      simp [hx, heq]
    · have hpos : 0 < x - (q : ℝ) := sub_pos.mpr (lt_of_not_ge hx)
      obtain ⟨N, hN⟩ := exists_nat_gt (1 / (x - (q : ℝ)))
      have heventually : (fun _ : ℕ => (0 : ℝ)) =ᶠ[atTop]
          fun n => lowerApprox q n x := by
        filter_upwards [eventually_ge_atTop N] with n hn
        have hNn : 1 / (x - (q : ℝ)) < (n : ℝ) := lt_of_lt_of_le hN (by exact_mod_cast hn)
        have : 1 ≤ (n : ℝ) * (x - (q : ℝ)) := by
          have := (div_lt_iff₀ hpos).mp hNn
          nlinarith
        have hmin : min 1 (1 - (n : ℝ) * (x - (q : ℝ))) ≤ 0 :=
          le_trans (min_le_right _ _) (by linarith)
        simp [lowerApprox, max_eq_left hmin]
      convert (Tendsto.congr' heventually tendsto_const_nhds) using 1
      simp [not_le_of_gt (lt_of_not_ge hx)]
  have lowerBoxFamily_representation {s} (hs : s ∈ lowerBoxFamily) : ∃ i : ℚ × ℚ, lowerBox i = s := by
    rcases hs with ⟨t, ht, rfl⟩
    change t ∈ Set.image2 (fun a b : Set ℝ => a ×ˢ b)
      ratLowerIntervals ratLowerIntervals at ht
    rcases Set.mem_image2.mp ht with ⟨a, ha, b, hb, rfl⟩
    rcases Set.mem_iUnion.mp ha with ⟨p, hp⟩
    rcases Set.mem_iUnion.mp hb with ⟨q, hq⟩
    simp only [Set.mem_singleton_iff] at hp hq
    subst a
    subst b
    exact ⟨(p, q), rfl⟩
  have basisFamily_eq : basisFamily = insert Set.univ lowerBoxFamily := by
    ext s
    constructor
    · rintro ⟨i, rfl⟩
      cases i with
      | none => simp [basisSet]
      | some i =>
          right
          refine ⟨Set.Iic (i.1 : ℝ) ×ˢ Set.Iic (i.2 : ℝ), ?_, rfl⟩
          change (Set.Iic (i.1 : ℝ) ×ˢ Set.Iic (i.2 : ℝ)) ∈
            Set.image2 (fun a b => a ×ˢ b) ratLowerIntervals ratLowerIntervals
          exact Set.mem_image2_of_mem
            (Set.mem_iUnion.mpr ⟨i.1, Set.mem_singleton _⟩)
            (Set.mem_iUnion.mpr ⟨i.2, Set.mem_singleton _⟩)
    · intro hs
      rcases hs with hs | hs
      · subst s
        exact ⟨none, rfl⟩
      · obtain ⟨i, hi⟩ := lowerBoxFamily_representation hs
        exact ⟨some i, hi⟩
  have lowerBoxFamily_generate : generateFrom lowerBoxFamily = borel ℂ := by
    have ratLowerIntervals_spanning : IsCountablySpanning ratLowerIntervals := by
      refine ⟨fun n => Set.Iic (n : ℝ), ?_, ?_⟩
      · intro n
        exact Set.mem_iUnion.mpr ⟨(n : ℚ), Set.mem_singleton _⟩
      · ext x
        simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
        obtain ⟨n, hn⟩ := exists_nat_gt x
        exact ⟨n, le_of_lt hn⟩
    have ratLowerRectangles_generate : generateFrom ratLowerRectangles = borel (ℝ × ℝ) := by
      have hreal : generateFrom ratLowerIntervals = borel ℝ := Real.borel_eq_generateFrom_Iic_rat.symm
      simpa only [ratLowerRectangles, BorelSpace.measurable_eq] using (generateFrom_eq_prod hreal hreal ratLowerIntervals_spanning ratLowerIntervals_spanning)
    calc
      generateFrom lowerBoxFamily =
          MeasurableSpace.comap realProdEquiv (generateFrom ratLowerRectangles) := by
            rw [MeasurableSpace.comap_generateFrom]
            rfl
      _ = MeasurableSpace.comap realProdEquiv (borel (ℝ × ℝ)) := by
            rw [ratLowerRectangles_generate]
      _ = borel ℂ := by
            simpa only [BorelSpace.measurable_eq] using
              realProdEquiv.measurableEmbedding.comap_eq
  have gmc_testIntegral_aemeasurable (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (M : Ω → Measure ℂ) (hconv : ∀ f : BoundedContinuousFunction ℂ ℝ, TendstoInMeasure P (fun r ω => ∫ x, f x ∂regularizedGMC P Xc γ r ω) atTop (fun ω => ∫ x, f x ∂M ω)) (f : BoundedContinuousFunction ℂ ℝ) : AEMeasurable (fun ω => ∫ x, f x ∂M ω) P := by
    have regularized_testIntegral_aemeasurable (r : ℝ) (f : BoundedContinuousFunction ℂ ℝ) : AEMeasurable (fun ω => ∫ x, f x ∂regularizedGMC P Xc γ r ω) P := by
      let μ : Ω → Measure ℂ := fun ω => regularizedGMC P Xc γ r ω
      have := regularizedGMC_measurable P X hX Xc hXc γ r
      let pos : Ω → ℝ≥0∞ := fun ω =>
        ∫⁻ x, (f.nnrealPart x : ℝ≥0∞) ∂μ ω
      let neg : Ω → ℝ≥0∞ := fun ω =>
        ∫⁻ x, ((-f).nnrealPart x : ℝ≥0∞) ∂μ ω
      exact (show Measurable (fun ω => (pos ω).toReal - (neg ω).toReal) by fun_prop).aemeasurable.congr (show (fun ω => ∫ x, f x ∂μ ω) =ᵐ[P] fun ω => (pos ω).toReal - (neg ω).toReal by filter_upwards [(regularizedGMC_finite_ae P X hX Xc hXc γ r)] with ω hω; rw [BoundedContinuousFunction.integral_eq_integral_nnrealPart_sub (μ := μ ω) f, ← BoundedContinuousFunction.toReal_lintegral_coe_eq_integral f.nnrealPart (μ ω), ← BoundedContinuousFunction.toReal_lintegral_coe_eq_integral (-f).nnrealPart (μ ω)]).symm
    apply (hconv f).aemeasurable
    intro r
    exact regularized_testIntegral_aemeasurable r f
  have lowerBox_realMass_aemeasurable (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (M : Ω → Measure ℂ) (hMfinite : ∀ ω, IsFiniteMeasure (M ω)) (hconv : ∀ f : BoundedContinuousFunction ℂ ℝ, TendstoInMeasure P (fun r ω => ∫ x, f x ∂regularizedGMC P Xc γ r ω) atTop (fun ω => ∫ x, f x ∂M ω)) (i : ℚ × ℚ) : AEMeasurable (fun ω => (M ω (lowerBox i)).toReal) P := by
    have lowerBoxApprox_integral_tendsto (μ : Measure ℂ) [IsFiniteMeasure μ] : Tendsto (fun n : ℕ => ∫ z, lowerBoxApprox i n z ∂μ) atTop (𝓝 (μ.real (lowerBox i))) := by
      have lowerBoxApprox_tendsto z : Tendsto (fun n : ℕ => lowerBoxApprox i n z) atTop (𝓝 ((lowerBox i).indicator (fun _ => (1 : ℝ)) z)) := by
        convert ((lowerApprox_tendsto i.1 z.re).mul (lowerApprox_tendsto i.2 z.im)) using 1
        · rfl
        · by_cases hr : z.re ≤ (i.1 : ℝ) <;>
            by_cases hi : z.im ≤ (i.2 : ℝ) <;>
            simp [lowerBox, realProdEquiv, Complex.measurableEquivRealProd_apply,
              Set.indicator, hr, hi]
      have hdom : ∀ n, ∀ᵐ z ∂μ, ‖lowerBoxApprox i n z‖ ≤ (1 : ℝ) := by
        intro n
        filter_upwards [] with z
        have hz := lowerBoxApprox_bounds i n z
        change |lowerBoxApproxFun i n z| ≤ 1
        rw [abs_le]
        exact ⟨by linarith, hz.2⟩
      rw [← integral_indicator_one (show MeasurableSet (lowerBox i) by apply (realProdEquiv.measurable (MeasurableSet.prod measurableSet_Iic measurableSet_Iic)))]
      exact (tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ)) (fun n => (lowerBoxApprox i n).continuous.measurable.aestronglyMeasurable) (integrable_const 1) hdom (ae_of_all _ (lowerBoxApprox_tendsto)))
    have hlim : ∀ᵐ ω ∂P, Tendsto
        (fun n => ∫ z, lowerBoxApprox i n z ∂M ω) atTop
        (𝓝 ((M ω (lowerBox i)).toReal)) := by
      filter_upwards [] with ω
      have : IsFiniteMeasure (M ω) := hMfinite ω
      simpa [Measure.real_def] using lowerBoxApprox_integral_tendsto (M ω)
    exact aemeasurable_of_tendsto_metrizable_ae' (by intro n; exact gmc_testIntegral_aemeasurable Xc hXc M hconv (lowerBoxApprox i n)) hlim
  have totalMass_real_aemeasurable (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (M : Ω → Measure ℂ) (hconv : ∀ f : BoundedContinuousFunction ℂ ℝ, TendstoInMeasure P (fun r ω => ∫ x, f x ∂regularizedGMC P Xc γ r ω) atTop (fun ω => ∫ x, f x ∂M ω)) : AEMeasurable (fun ω => (M ω Set.univ).toReal) P := by
    have hEq : (fun ω => ∫ x, (1 : ℝ) ∂M ω) =
        fun ω => (M ω Set.univ).toReal := by
      funext ω
      rw [integral_const]
      simp [Measure.real_def]
    exact (gmc_testIntegral_aemeasurable Xc hXc M hconv (1 : BoundedContinuousFunction ℂ ℝ)).congr (ae_of_all P (fun ω => congrFun hEq ω))
  have basisFamily_generate : generateFrom basisFamily = borel ℂ := by
    rw [basisFamily_eq]
    apply le_antisymm
    · apply generateFrom_le
      intro s hs
      rcases hs with hs | hs
      · subst s
        exact MeasurableSet.univ
      · have hgen := lowerBoxFamily_generate
        exact hgen ▸ GenerateMeasurable.basic s hs
    · rw [← lowerBoxFamily_generate]
      exact generateFrom_mono (Set.subset_insert _ _)
  have basisFamily_pi : IsPiSystem basisFamily := by
    have ratLowerRectangles_pi : IsPiSystem ratLowerRectangles := (Real.isPiSystem_Iic_rat).prod Real.isPiSystem_Iic_rat
    have lowerBoxFamily_pi : IsPiSystem lowerBoxFamily := ratLowerRectangles_pi.comap realProdEquiv
    rw [basisFamily_eq]
    exact IsPiSystem.insert_univ lowerBoxFamily_pi
  rcases hM with ⟨hMfinite, Xc, hXc, hconv⟩
  let coordinate : Option (ℚ × ℚ) → Ω → ℝ := fun i ω =>
    (M ω (basisSet i)).toReal
  have hcoordinate : ∀ i, AEMeasurable (coordinate i) P := by
    intro i
    cases i with
    | none =>
        simpa [coordinate, basisSet] using
          totalMass_real_aemeasurable Xc hXc M hconv
    | some i =>
        simpa [coordinate, basisSet] using
          lowerBox_realMass_aemeasurable Xc hXc M hMfinite hconv i
  let coordinateMeas : Option (ℚ × ℚ) → Ω → ℝ :=
    fun i => (hcoordinate i).mk (coordinate i)
  have hcoordinateMeas : ∀ i, Measurable (coordinateMeas i) :=
    fun i => (hcoordinate i).measurable_mk
  have hcoordinateAE := ae_all_iff.mpr fun i => (hcoordinate i).ae_eq_mk
  let bad := {ω | ∃ i, coordinate i ω ≠ coordinateMeas i ω}
  obtain ⟨badMeas, hbadSub, hbadMeasurable, hbadZero⟩ :=
    exists_measurable_superset_of_null (by simpa [bad] using (ae_iff.mp hcoordinateAE))
  let good := badMeasᶜ
  have hgoodMeasurable := hbadMeasurable.compl
  have hgood : ∀ᵐ ω ∂P, ω ∈ good := by
    rw [ae_iff]
    simpa [good] using hbadZero
  have hcoordinate_eq : ∀ ω, ω ∈ good → ∀ i,
      coordinate i ω = coordinateMeas i ω := by
    intro ω hω i
    by_contra hne
    change ω ∉ badMeas at hω
    exact hω (hbadSub ⟨i, hne⟩)
  let N : Ω → Measure ℂ := fun ω => if ω ∈ good then M ω else 0
  have hNfinite : ∀ ω, IsFiniteMeasure (N ω) := by
    intro ω
    by_cases hω : ω ∈ good
    · simpa [N, hω] using hMfinite ω
    · simpa [N, hω] using (inferInstance : IsFiniteMeasure (0 : Measure ℂ))
  have hEvalMeasurable i :
      Measurable (fun ω => N ω (basisSet i)) := by
    have hEval : (fun ω => N ω (basisSet i)) =
        fun ω => if ω ∈ good then ENNReal.ofReal (coordinateMeas i ω) else 0 := by
      funext ω
      by_cases hω : ω ∈ good
      · have hcoord := hcoordinate_eq ω hω i
        have : IsFiniteMeasure (M ω) := hMfinite ω
        have hfiniteSet := measure_ne_top (M ω) (basisSet i)
        simp [N, hω]
        calc
          M ω (basisSet i) = ENNReal.ofReal (M ω (basisSet i)).toReal :=
            (ENNReal.ofReal_toReal hfiniteSet).symm
          _ = ENNReal.ofReal (coordinateMeas i ω) := by rw [← hcoord]
      · simp [N, hω]
    rw [hEval]
    exact Measurable.ite hgoodMeasurable
      (ENNReal.measurable_ofReal.comp (hcoordinateMeas i)) measurable_const
  have hNmeasurable : Measurable N := by
    have hbasic : ∀ s ∈ basisFamily, Measurable (fun ω => N ω s) := by
      intro s hs
      rw [basisFamily_eq] at hs
      rcases hs with hs | hs
      · subst s
        simpa [basisSet] using hEvalMeasurable none
      · obtain ⟨i, hi⟩ := lowerBoxFamily_representation hs
        subst s
        simpa [basisSet] using hEvalMeasurable (some i)
    have huniv : Measurable (fun ω => N ω Set.univ) := by
      simpa [basisSet] using hEvalMeasurable none
    exact @Measurable.measure_of_isPiSystem Ω ℂ _ _ N hNfinite basisFamily
      (BorelSpace.measurable_eq.trans basisFamily_generate.symm) basisFamily_pi hbasic huniv
  refine ⟨N, hNmeasurable, hNfinite, ?_⟩
  filter_upwards [hgood] with ω hω
  simp [N, hω]

end DOZZ.Proofs
