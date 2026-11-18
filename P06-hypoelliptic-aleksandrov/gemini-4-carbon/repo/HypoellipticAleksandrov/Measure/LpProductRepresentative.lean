module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Function.LpSpace.Complete

@[expose] public noncomputable section

namespace HypoellipticAleksandrov
open MeasureTheory Filter Topology
open scoped ENNReal MeasureTheory



/-- The raw product representative obtained from a finite-range outer simple function. -/
noncomputable def simpleUncurry {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {ν : Measure β} (s : SimpleFunc α (MeasureTheory.Lp ℝ (2 : ℝ≥0∞) ν)) : α × β → ℝ :=
  fun z => s z.1 z.2

/-- A finite-range outer `L²` function has a jointly strongly measurable raw lift. -/
theorem stronglyMeasurable_simpleUncurry
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {ν : Measure β} (s : SimpleFunc α (MeasureTheory.Lp ℝ (2 : ℝ≥0∞) ν)) :
    StronglyMeasurable (simpleUncurry s) := by
  classical
  refine SimpleFunc.induction' (P := fun s => StronglyMeasurable (simpleUncurry s)) ?_ ?_ s
  · intro c
    exact (MeasureTheory.Lp.stronglyMeasurable c).comp_measurable measurable_snd
  · intro f g t ht hf hg
    let : DecidablePred fun z : α × β => z ∈ t ×ˢ Set.univ := Classical.decPred _
    convert StronglyMeasurable.piecewise (MeasurableSet.prod ht MeasurableSet.univ) hf hg using 1
    · ext z
      by_cases hz : z.1 ∈ t <;> simp [simpleUncurry, hz]
    · exact Classical.decPred _

private theorem integral_sq_coeFn_eq_norm_sq
    {β : Type*} [MeasurableSpace β] (ν : Measure β)
    (c : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) ν) :
    ∫ y, c y ^ 2 ∂ν = ‖c‖ ^ 2 := by
  calc
    ∫ y, c y ^ 2 ∂ν = ∫ y, inner ℝ (c y) (c y) ∂ν := by
      congr with y
      simp [pow_two]
    _ = inner ℝ c c := (MeasureTheory.L2.inner_def c c).symm
    _ = ‖c‖ ^ 2 := real_inner_self_eq_norm_sq c

/-- The raw lift of an outer simple `L²` function belongs to product `L²`. -/
theorem memLp_simpleUncurry_two
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite ν]
    (s : SimpleFunc α (MeasureTheory.Lp ℝ (2 : ℝ≥0∞) ν))
    (hs : MeasureTheory.MemLp s (2 : ℝ≥0∞) μ) :
    MeasureTheory.MemLp (simpleUncurry s) (2 : ℝ≥0∞) (μ.prod ν) := by
  rw [MeasureTheory.memLp_two_iff_integrable_sq
    (stronglyMeasurable_simpleUncurry s).aestronglyMeasurable]
  refine (MeasureTheory.integrable_prod_iff ?_).2 ?_
  · exact
      ((stronglyMeasurable_simpleUncurry s).pow 2).aestronglyMeasurable
  constructor
  · filter_upwards with x
    simpa [simpleUncurry] using (MeasureTheory.Lp.memLp (s x)).integrable_sq
  · have houter : Integrable (fun x => ‖s x‖ ^ 2) μ :=
      (MeasureTheory.memLp_two_iff_integrable_sq_norm hs.aestronglyMeasurable).mp hs
    refine houter.congr ?_
    filter_upwards with x
    symm
    calc
      (∫ y, ‖s x y ^ 2‖ ∂ν) = ∫ y, s x y ^ 2 ∂ν := by
        apply integral_congr_ae
        filter_upwards with y
        rw [Real.norm_eq_abs]
        exact abs_of_nonneg (sq_nonneg (s x y))
      _ = ‖s x‖ ^ 2 := integral_sq_coeFn_eq_norm_sq ν (s x)

/-- Subtraction of raw lifts agrees almost everywhere with the raw lift of subtraction. -/
theorem ae_simpleUncurry_sub
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite ν]
    (s t : SimpleFunc α (MeasureTheory.Lp ℝ (2 : ℝ≥0∞) ν)) :
    simpleUncurry (s - t) =ᵐ[μ.prod ν] simpleUncurry s - simpleUncurry t := by
  apply (MeasureTheory.Measure.ae_prod_iff_ae_ae
    ((stronglyMeasurable_simpleUncurry (s - t)).measurableSet_eq_fun
      ((stronglyMeasurable_simpleUncurry s).sub (stronglyMeasurable_simpleUncurry t)))).2
  filter_upwards with x
  filter_upwards [MeasureTheory.Lp.coeFn_sub (s x) (t x)] with y hy
  exact hy

/-- The `L²` norm of the product lift equals the outer `L²` norm. -/
theorem norm_simpleUncurry_toLp_eq
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite ν]
    (s : SimpleFunc α (MeasureTheory.Lp ℝ (2 : ℝ≥0∞) ν))
    (hs : MeasureTheory.MemLp s (2 : ℝ≥0∞) μ) :
    ‖(memLp_simpleUncurry_two μ ν s hs).toLp (simpleUncurry s)‖ = ‖hs.toLp s‖ := by
  rw [MeasureTheory.Lp.norm_toLp, MeasureTheory.Lp.norm_toLp]
  apply congrArg ENNReal.toReal
  apply ENNReal.rpow_left_injective (by norm_num : (2 : ℝ) ≠ 0)
  calc
    MeasureTheory.eLpNorm (simpleUncurry s) 2 (μ.prod ν) ^ (2 : ℝ) =
        ∫⁻ z, ‖simpleUncurry s z‖ₑ ^ 2 ∂μ.prod ν := by
      simpa using (MeasureTheory.eLpNorm_nnreal_pow_eq_lintegral
 (μ := μ.prod ν) (p := 2) (by norm_num)
        (stronglyMeasurable_simpleUncurry s).aestronglyMeasurable)
    _ = ∫⁻ x, ∫⁻ y, ‖simpleUncurry s (x, y)‖ₑ ^ 2 ∂ν ∂μ :=
      MeasureTheory.lintegral_prod _
        (ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
          (stronglyMeasurable_simpleUncurry s).enorm.aemeasurable)
    _ = ∫⁻ x, ‖s x‖ₑ ^ 2 ∂μ := by
      apply lintegral_congr_ae
      filter_upwards with x
      symm
      simpa [simpleUncurry, MeasureTheory.Lp.enorm_def] using
        (MeasureTheory.eLpNorm_nnreal_pow_eq_lintegral
          (f := fun y => s x y) (μ := ν) (p := 2) (by norm_num)
          (MeasureTheory.Lp.aestronglyMeasurable (s x)))
    _ = MeasureTheory.eLpNorm s 2 μ ^ (2 : ℝ) := by
      simpa using (MeasureTheory.eLpNorm_nnreal_pow_eq_lintegral
        (f := s) (μ := μ) (p := 2) (by norm_num) hs.aestronglyMeasurable).symm

/-- The norm of the difference of two product lifts equals the outer difference norm. -/
theorem norm_sub_simpleUncurry_toLp_eq
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite ν]
    (s t : SimpleFunc α (MeasureTheory.Lp ℝ (2 : ℝ≥0∞) ν))
    (hs : MeasureTheory.MemLp s (2 : ℝ≥0∞) μ)
    (ht : MeasureTheory.MemLp t (2 : ℝ≥0∞) μ) :
    ‖(memLp_simpleUncurry_two μ ν s hs).toLp (simpleUncurry s) -
        (memLp_simpleUncurry_two μ ν t ht).toLp (simpleUncurry t)‖ =
      ‖hs.toLp s - ht.toLp t‖ := by
  have hproduct_sub :
      (memLp_simpleUncurry_two μ ν s hs).toLp (simpleUncurry s) -
        (memLp_simpleUncurry_two μ ν t ht).toLp (simpleUncurry t) =
      (memLp_simpleUncurry_two μ ν (s - t) (hs.sub ht)).toLp (simpleUncurry (s - t)) := by
    rw [← MeasureTheory.MemLp.toLp_sub]
    apply MeasureTheory.MemLp.toLp_congr
    exact (ae_simpleUncurry_sub μ ν s t).symm
  calc
    ‖(memLp_simpleUncurry_two μ ν s hs).toLp (simpleUncurry s) -
        (memLp_simpleUncurry_two μ ν t ht).toLp (simpleUncurry t)‖ =
        ‖(memLp_simpleUncurry_two μ ν (s - t) (hs.sub ht)).toLp
          (simpleUncurry (s - t))‖ := by rw [hproduct_sub]
    _ = ‖(hs.sub ht).toLp (s - t)‖ :=
      norm_simpleUncurry_toLp_eq μ ν (s - t) (hs.sub ht)
    _ = ‖hs.toLp s - ht.toLp t‖ := by
      rw [← MeasureTheory.MemLp.toLp_sub]
      apply congrArg norm
      apply MeasureTheory.MemLp.toLp_congr
      filter_upwards with x
      rfl





private theorem exists_outer_simple_sequence
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β)
    (q : Lp (Lp ℝ (2 : ℝ≥0∞) ν) (2 : ℝ≥0∞) μ) :
    ∃ S : ℕ → Lp.simpleFunc (Lp ℝ (2 : ℝ≥0∞) ν) (2 : ℝ≥0∞) μ,
      Tendsto (fun n => (S n : Lp (Lp ℝ (2 : ℝ≥0∞) ν) (2 : ℝ≥0∞) μ))
        atTop (𝓝 q) := by
  rcases mem_closure_iff_seq_limit.mp (Lp.simpleFunc.denseRange (E := Lp ℝ 2 ν) (μ := μ) (by norm_num) q) with ⟨u, hu, hlim⟩
  choose S hS using hu
  refine ⟨S, ?_⟩
  convert hlim using 1
  funext n
  exact hS n

private theorem exists_product_simple_limit
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite ν]
    (q : Lp (Lp ℝ (2 : ℝ≥0∞) ν) (2 : ℝ≥0∞) μ) :
    ∃ (S : ℕ → Lp.simpleFunc (Lp ℝ (2 : ℝ≥0∞) ν) (2 : ℝ≥0∞) μ)
      (pQ : Lp ℝ (2 : ℝ≥0∞) (μ.prod ν)),
      Tendsto (fun n => (S n : Lp (Lp ℝ (2 : ℝ≥0∞) ν) (2 : ℝ≥0∞) μ))
        atTop (𝓝 q) ∧
      Tendsto (fun n =>
        (memLp_simpleUncurry_two μ ν (Lp.simpleFunc.toSimpleFunc (S n))
          (Lp.simpleFunc.memLp (S n))).toLp
            (simpleUncurry (Lp.simpleFunc.toSimpleFunc (S n)))) atTop (𝓝 pQ) := by
  obtain ⟨S, hS⟩ := exists_outer_simple_sequence μ ν q
  let P : ℕ → Lp ℝ 2 (μ.prod ν) := fun n =>
    (memLp_simpleUncurry_two μ ν (Lp.simpleFunc.toSimpleFunc (S n))
      (Lp.simpleFunc.memLp (S n))).toLp
        (simpleUncurry (Lp.simpleFunc.toSimpleFunc (S n)))
  have hdist (m n : ℕ) :
      dist (P m) (P n) =
        dist ((S m : Lp (Lp ℝ 2 ν) 2 μ))
          ((S n : Lp (Lp ℝ 2 ν) 2 μ)) := by
    simp only [P, dist_eq_norm]
    rw [norm_sub_simpleUncurry_toLp_eq]
    change ‖(Lp.simpleFunc.memLp (S m)).toLp (Lp.simpleFunc.toSimpleFunc (S m)) -
        (Lp.simpleFunc.memLp (S n)).toLp (Lp.simpleFunc.toSimpleFunc (S n))‖ =
      ‖(S m : Lp (Lp ℝ 2 ν) 2 μ) -
        (S n : Lp (Lp ℝ 2 ν) 2 μ)‖
    have hm : (Lp.simpleFunc.memLp (S m)).toLp
        (Lp.simpleFunc.toSimpleFunc (S m)) =
        (S m : Lp (Lp ℝ 2 ν) 2 μ) := by
      rw [← Lp.simpleFunc.toLp_eq_toLp]
      exact congrArg (fun r : Lp.simpleFunc (Lp ℝ 2 ν)
          2 μ => (r : Lp (Lp ℝ 2 ν) 2 μ))
        (Lp.simpleFunc.toLp_toSimpleFunc (S m))
    have hn : (Lp.simpleFunc.memLp (S n)).toLp
        (Lp.simpleFunc.toSimpleFunc (S n)) =
        (S n : Lp (Lp ℝ 2 ν) 2 μ) := by
      rw [← Lp.simpleFunc.toLp_eq_toLp]
      exact congrArg (fun r : Lp.simpleFunc (Lp ℝ 2 ν)
          2 μ => (r : Lp (Lp ℝ 2 ν) 2 μ))
        (Lp.simpleFunc.toLp_toSimpleFunc (S n))
    rw [hm, hn]
  have hP_cauchy : CauchySeq P := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    rcases Metric.cauchySeq_iff.mp hS.cauchySeq ε hε with ⟨N, hN⟩
    refine ⟨N, fun m hm n hn => ?_⟩
    rw [hdist]
    exact hN m hm n hn
  obtain ⟨pQ, hP⟩ := cauchySeq_tendsto_of_complete hP_cauchy
  exact ⟨S, pQ, hS, hP⟩

/-- A nested `L²` class has a product `L²` representative with the expected slices. -/
theorem exists_uncurry_memLp_two
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite ν]
    (q : Lp (Lp ℝ (2 : ℝ≥0∞) ν) (2 : ℝ≥0∞) μ) :
    ∃ Q : α × β → ℝ,
      MemLp Q (2 : ℝ≥0∞) (μ.prod ν) ∧
      ∀ᵐ x ∂μ, (fun y => Q (x, y)) =ᵐ[ν] fun y => q x y := by
  obtain ⟨S, pQ, hS, hP⟩ := exists_product_simple_limit μ ν q
  let P : ℕ → Lp ℝ 2 (μ.prod ν) := fun n =>
    (memLp_simpleUncurry_two μ ν (Lp.simpleFunc.toSimpleFunc (S n))
      (Lp.simpleFunc.memLp (S n))).toLp
        (simpleUncurry (Lp.simpleFunc.toSimpleFunc (S n)))
  change Tendsto P atTop (𝓝 pQ) at hP
  refine ⟨fun z => pQ z, Lp.memLp pQ, ?_⟩
  obtain ⟨φ, hφmono, hφ⟩ :=
    (tendstoInMeasure_of_tendsto_Lp hP).exists_seq_tendsto_ae
  have hSφ : Tendsto (fun i =>
      (S (φ i) : Lp (Lp ℝ 2 ν) 2 μ)) atTop (𝓝 q) :=
    hS.comp hφmono.tendsto_atTop
  obtain ⟨ψ, hψmono, hψ⟩ :=
    (tendstoInMeasure_of_tendsto_Lp hSφ).exists_seq_tendsto_ae
  have hφψ : ∀ᵐ z ∂μ.prod ν,
      Tendsto (fun i => P (φ (ψ i)) z) atTop (𝓝 (pQ z)) :=
    hφ.mono fun _ hz => hz.comp hψmono.tendsto_atTop
  have hproduct_raw : ∀ᵐ z ∂μ.prod ν,
      Tendsto (fun i => simpleUncurry (Lp.simpleFunc.toSimpleFunc
        (S (φ (ψ i)))) z) atTop (𝓝 (pQ z)) := by
    filter_upwards [(ae_all_iff.mpr fun n => MemLp.coeFn_toLp (memLp_simpleUncurry_two μ ν (Lp.simpleFunc.toSimpleFunc (S n)) (Lp.simpleFunc.memLp (S n)))), hφψ] with z hz hlim
    refine hlim.congr' ?_
    filter_upwards with i
    exact hz (φ (ψ i))
  filter_upwards [(ae_all_iff.mpr fun n => Lp.simpleFunc.toSimpleFunc_eq_toFun (S n)), hψ, (MeasureTheory.Measure.ae_ae_of_ae_prod hproduct_raw)] with x hxraw hxouter hxslice
  have hxinner : Tendsto (fun i => Lp.simpleFunc.toSimpleFunc
      (S (φ (ψ i))) x) atTop (𝓝 (q x)) := by
    refine hxouter.congr' ?_
    filter_upwards with i
    exact (hxraw (φ (ψ i))).symm
  obtain ⟨κ, hκmono, hκ⟩ :=
    (tendstoInMeasure_of_tendsto_Lp hxinner).exists_seq_tendsto_ae
  filter_upwards [hκ, hxslice] with y hky hsy
  exact tendsto_nhds_unique (hsy.comp hκmono.tendsto_atTop) hky


end HypoellipticAleksandrov

