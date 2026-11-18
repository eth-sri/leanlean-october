module

public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.MajorantApprox
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.MajorantAbstract
public import Mathlib.MeasureTheory.Integral.CompactlySupported
import PDEFoundation.Measure.LpTendsto
import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
public import PDEFoundation.Measure.LpPower
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.Topology.Compactness.SigmaCompact

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Occupation
section
section

open MeasureTheory Set Metric
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
/-- A smooth compact cutoff equals one on a prescribed compact subset of an open set. -/
theorem exists_test_cutoff {K U : Set E} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ χ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ U ∧ (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧ ∀ x ∈ K, χ x = 1 := by
  obtain ⟨δ, hδ, hdouble, χ, hs, h01, h1, h0⟩ := exists_smooth_cutoff hU hK hKU
  have hcompact : IsCompact (cthickening δ K) := hK.cthickening
  have hsupport : tsupport χ ⊆ cthickening δ K := by
    exact closure_minimal (fun x hx => by
      by_contra hn
      exact hx (h0 x hn)) isClosed_cthickening
  refine ⟨χ, hs, (HasCompactSupport.intro hcompact h0), hsupport.trans ?_, h01, h1⟩
  exact (cthickening_mono (by linarith) K).trans hdouble

/-- A compactly supported `Lp` function admits continuous approximants supported inside `U`. -/
theorem exists_continuous_test_approximation (η : Measure E)
    [η.Regular] {p : ℝ≥0∞} (hpt : p ≠ ∞)
    {f : E → ℝ} (hfp : MemLp f p η) {K U : Set E} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) (hfK : Function.support f ⊆ K)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ g : E → ℝ, Continuous g ∧ HasCompactSupport g ∧ tsupport g ⊆ U ∧
      eLpNorm (g - f) p η ≤ ε := by
  obtain ⟨χ, hs, hc, hχU, h01, h1⟩ := exists_test_cutoff hK hU hKU
  obtain ⟨a, _hac, han, ha, _hap⟩ :=
    hfp.exists_hasCompactSupport_eLpNorm_sub_le hpt hε
  refine ⟨fun x => χ x * a x, hs.continuous.mul ha, hc.mul_right,
    tsupport_mul_subset_left.trans hχU, ?_⟩
  have heq : (fun x => χ x * a x) - f = fun x => χ x * (a x - f x) := by
    funext x
    by_cases hx : f x = 0
    · simp [hx]
    · have hxK : x ∈ K := hfK hx
      simp [h1 x hxK]
  rw [heq]
  refine (eLpNorm_mono_ae (g := a - f)
    (hs.continuous.aestronglyMeasurable.mul (ha.aestronglyMeasurable.sub
      hfp.aestronglyMeasurable)) (Filter.Eventually.of_forall fun x => ?_)).trans ?_
  · change ‖χ x * (a x - f x)‖ ≤ ‖a x - f x‖
    rw [norm_mul, Real.norm_of_nonneg (h01 x).1]
    exact mul_le_of_le_one_left (norm_nonneg _) (h01 x).2
  · simpa only [eLpNorm_sub_comm] using han

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
/-- Finite-measure `Lp` convergence, for `p ≥ 1`, implies `L¹` convergence. -/
theorem tendsto_eLpNorm_one_of_finite (μ : Measure E) [IsFiniteMeasure μ]
    {p : ℝ≥0∞} (hp : 1 ≤ p) {F : ℕ → E → ℝ} {f : E → ℝ}
    (hmeas : ∀ n, AEStronglyMeasurable (F n - f) μ)
    (h : Filter.Tendsto (fun n => eLpNorm (F n - f) p μ)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => eLpNorm (F n - f) 1 μ) Filter.atTop (nhds 0) := by
  let a := μ univ ^ (1 - 1 / p.toReal)
  have ha : a ≠ ∞ := by
    apply ENNReal.rpow_ne_top_of_nonneg
    · have hpReal : 0 ≤ p.toReal := ENNReal.toReal_nonneg
      by_cases hpt : p = ∞
      · simp [hpt]
      · have hpr : 1 ≤ p.toReal := by
          simpa using ENNReal.toReal_mono hpt hp
        have hi : 1 / p.toReal ≤ 1 := by
          exact (div_le_one (by linarith)).2 hpr
        linarith
    · exact measure_ne_top μ univ
  have ht := ENNReal.Tendsto.mul_const h (Or.inr ha)
  rw [zero_mul] at ht
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
    (Filter.Eventually.of_forall fun _ => bot_le) ?_
  exact Filter.Eventually.of_forall fun n => by
    simpa [a] using eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp (hmeas n)

end
section

open MeasureTheory Set
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Positive smooth-test bounds extend sharply to continuous compactly supported tests. -/
theorem integral_le_of_smooth_tests (ν μ : Measure E) [ν.IsAddHaarMeasure]
    [IsFiniteMeasure μ] {U : Set E} (hU : IsOpen U) {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hpt : p ≠ ∞) {C : ℝ} (hC : 0 ≤ C)
    (htest : ∀ f : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f →
      tsupport f ⊆ U → (∀ x, 0 ≤ f x) →
      (∫ x, f x ∂μ) ≤ C * (eLpNorm f p (ν.restrict U)).toReal)
    {f : E → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hfs : tsupport f ⊆ U) (hf0 : ∀ x, 0 ≤ f x) :
    (∫ x, f x ∂μ) ≤ C * (eLpNorm f p (ν.restrict U)).toReal := by
  have hfp : MemLp f p (ν.restrict U) := hf.memLp_of_hasCompactSupport hfc
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hδ : 0 < ε / (C + 1) := div_pos hε (by positivity)
  obtain ⟨g, hgs, hgc, hgU, hg0, hfg, hgn⟩ :=
    exists_smooth_majorant_toReal_le ν hU hfc hfs hf.continuousOn
      (fun x _ => hf0 x) (Filter.Eventually.of_forall fun _ => le_rfl)
      hp hpt hfp hδ
  have hfg' : ∀ x, f x ≤ g x := by
    intro x
    by_cases hx : x ∈ tsupport f
    · exact hfg x hx
    · rw [image_eq_zero_of_notMem_tsupport hx]
      exact hg0 x
  calc
    (∫ x, f x ∂μ) ≤ ∫ x, g x ∂μ :=
      integral_mono (hf.integrable_of_hasCompactSupport hfc)
        (hgs.continuous.integrable_of_hasCompactSupport hgc) hfg'
    _ ≤ C * (eLpNorm g p (ν.restrict U)).toReal := htest g hgs hgc hgU hg0
    _ ≤ C * ((eLpNorm f p (ν.restrict U)).toReal + ε / (C + 1)) :=
      mul_le_mul_of_nonneg_left hgn hC
    _ ≤ C * (eLpNorm f p (ν.restrict U)).toReal + ε := by
      have hmul : C * (ε / (C + 1)) ≤ ε := by
        rw [← mul_div_assoc]
        exact (div_le_iff₀ (by positivity)).2 (by nlinarith)
      nlinarith

/-- Positive smooth-test bounds control the absolute integral of signed continuous tests. -/
theorem abs_integral_le_of_smooth_tests (ν μ : Measure E) [ν.IsAddHaarMeasure]
    [IsFiniteMeasure μ] {U : Set E} (hU : IsOpen U) {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hpt : p ≠ ∞) {C : ℝ} (hC : 0 ≤ C)
    (htest : ∀ f : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f →
      tsupport f ⊆ U → (∀ x, 0 ≤ f x) →
      (∫ x, f x ∂μ) ≤ C * (eLpNorm f p (ν.restrict U)).toReal)
    {f : E → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hfs : tsupport f ⊆ U) :
    |∫ x, f x ∂μ| ≤ C * (eLpNorm f p (ν.restrict U)).toReal := by
  have has : tsupport (fun x => |f x|) ⊆ U := by
    exact (closure_mono (fun x hx => by
      exact fun hz => hx (by simp [hz]))).trans hfs
  have hb := integral_le_of_smooth_tests ν μ hU hp hpt hC htest
    hf.abs hfc.norm has (fun x => abs_nonneg (f x))
  have hn : eLpNorm (fun x => |f x|) p (ν.restrict U) =
      eLpNorm f p (ν.restrict U) := by
    simpa using eLpNorm_norm f hf.aestronglyMeasurable
  rw [hn] at hb
  have hi : |∫ x, f x ∂μ| ≤ ∫ x, |f x| ∂μ := by
    simpa using norm_integral_le_integral_norm f
  exact hi.trans hb

end

open MeasureTheory Set Filter
open scoped ENNReal Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
/-- The sum of two measures finite on compacts is finite on compacts. -/
theorem finiteOnCompacts_add (ν μ : Measure E) [IsFiniteMeasureOnCompacts ν]
    [IsFiniteMeasureOnCompacts μ] : IsFiniteMeasureOnCompacts (ν + μ) := by
  constructor
  intro K hK
  rw [Measure.add_apply]
  exact ENNReal.add_lt_top.2 ⟨hK.measure_lt_top, hK.measure_lt_top⟩

/-- Compact measurable tests inherit the sharp norm bound from positive smooth tests. -/
theorem abs_integral_le_of_smooth_tests_compact (ν μ : Measure E)
    [ν.IsAddHaarMeasure] [IsFiniteMeasure μ] {U : Set E} (hU : IsOpen U)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞) {C : ℝ} (hC : 0 ≤ C)
    (htest : ∀ f : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f →
      tsupport f ⊆ U → (∀ x, 0 ≤ f x) →
      (∫ x, f x ∂μ) ≤ C * (eLpNorm f p (ν.restrict U)).toReal)
    {f : E → ℝ} (hfp : MemLp f p (ν + μ)) {K : Set E} (hK : IsCompact K)
    (hKU : K ⊆ U) (hfK : Function.support f ⊆ K) :
    |∫ x, f x ∂μ| ≤ C * (eLpNorm f p (ν.restrict U)).toReal := by
  have : IsFiniteMeasureOnCompacts (ν + μ) := finiteOnCompacts_add ν μ
  let ε : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal (1 / ((n : ℝ) + 1))
  have hεpos (n : ℕ) : ε n ≠ 0 := by
    dsimp [ε]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity))
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    simpa [ε, Function.comp_def] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hex (n : ℕ) := exists_continuous_test_approximation (ν + μ) hpt hfp
    hK hU hKU hfK (hεpos n)
  choose g hgc hgcompact hgU hgn using hex
  have hμsum : μ ≤ ν + μ := Measure.le_add_left le_rfl
  have hνsum : ν.restrict U ≤ ν + μ := Measure.restrict_le_self.trans (Measure.le_add_right le_rfl)
  have herrμ : Tendsto (fun n => eLpNorm (g n - f) p μ) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hεlim
      (Eventually.of_forall fun _ => bot_le) ?_
    exact Eventually.of_forall fun n =>
      (eLpNorm_mono_measure _ hμsum).trans (hgn n)
  have herrν : Tendsto (fun n => eLpNorm (g n - f) p (ν.restrict U))
      atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hεlim
      (Eventually.of_forall fun _ => bot_le) ?_
    exact Eventually.of_forall fun n =>
      (eLpNorm_mono_measure _ hνsum).trans (hgn n)
  have hLpμ : MemLp f p μ := hfp.mono_measure hμsum
  have hi :=
    tendsto_integral_of_L1' f
      (Eventually.of_forall fun n => (hgc n).integrable_of_hasCompactSupport
        (hgcompact n)) (tendsto_eLpNorm_one_of_finite μ hp (fun n => (hgc n).aestronglyMeasurable.sub hLpμ.aestronglyMeasurable) herrμ)
  have hLpν : MemLp f p (ν.restrict U) := hfp.mono_measure hνsum
  have hnr :=
    (ENNReal.continuousAt_toReal hLpν.eLpNorm_ne_top).tendsto.comp (PDE.tendsto_eLpNorm_of_tendsto_sub hp (fun n => (hgc n).aestronglyMeasurable) hLpν.aestronglyMeasurable hLpν.eLpNorm_ne_top herrν)
  exact le_of_tendsto_of_tendsto' hi.abs (tendsto_const_nhds.mul hnr)
    (fun n => abs_integral_le_of_smooth_tests ν μ hU hp hpt hC htest
      (hgc n) (hgcompact n) (hgU n))

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Bounded measurable functions supported on a compact set belong to every finite `Lp`. -/
theorem memLp_of_bounded_compact_support (η : Measure E) [IsFiniteMeasureOnCompacts η]
    {f : E → ℝ} (hf : Measurable f) {K : Set E} (hK : IsCompact K)
    (hfK : Function.support f ⊆ K) {M : ℝ} (hM : ∀ x, |f x| ≤ M)
    (p : ℝ≥0∞) : MemLp f p η := by
  have : IsFiniteMeasure (η.restrict K) := ⟨by
    simpa using hK.measure_lt_top⟩
  have hfp : MemLp f p (η.restrict K) :=
    MemLp.of_bound hf.aestronglyMeasurable M
      (Eventually.of_forall fun x => by simpa using hM x)
  have heq : K.indicator f = f := by
    ext x
    by_cases hx : x ∈ K
    · exact indicator_of_mem hx f
    · rw [indicator_of_notMem hx]
      exact (Function.notMem_support.mp (fun h => hx (hfK h))).symm
  rw [← heq]
  exact (memLp_indicator_iff_restrict hK.measurableSet).2 hfp

end
section

open MeasureTheory Set Filter
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Smooth-test norm bounds force absolute continuity with respect to restricted Haar measure. -/
theorem absolutelyContinuous_of_smooth_tests (ν μ : Measure E)
    [ν.IsAddHaarMeasure] [IsFiniteMeasure μ] {U : Set E} (hU : IsOpen U)
    (hμU : μ Uᶜ = 0) {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞)
    {C : ℝ} (hC : 0 ≤ C)
    (htest : ∀ f : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f →
      tsupport f ⊆ U → (∀ x, 0 ≤ f x) →
      (∫ x, f x ∂μ) ≤ C * (eLpNorm f p (ν.restrict U)).toReal) :
    μ ≪ ν.restrict U := by
  have : IsFiniteMeasureOnCompacts (ν + μ) := finiteOnCompacts_add ν μ
  have hcompact : ∀ K : Set E, IsCompact K → K ⊆ U → ν K = 0 → μ K = 0 := by
    intro K hK hKU hνK
    let f : E → ℝ := K.indicator (fun _ => 1)
    have hf : Measurable f := measurable_const.indicator hK.measurableSet
    have hsupport : Function.support f ⊆ K := Set.support_indicator_subset
    have hb : ∀ x, |f x| ≤ 1 := by
      intro x
      by_cases hx : x ∈ K <;> simp [f, hx]
    have hn : eLpNorm f p (ν.restrict U) = 0 := by
      have hnull : (ν.restrict U) K = 0 := by
        rw [Measure.restrict_apply hK.measurableSet]
        exact measure_mono_null inter_subset_left hνK
      rw [eLpNorm_congr_ae (show f =ᵐ[ν.restrict U] 0 from ?_)]
      · simp
      · have hx0 : ∀ᵐ x ∂ν.restrict U, x ∉ K := by
          rw [ae_iff]
          simpa using hnull
        filter_upwards [hx0] with x hx
        simp [f, hx]
    have hi := abs_integral_le_of_smooth_tests_compact ν μ hU hp hpt hC htest
      (memLp_of_bounded_compact_support (ν + μ) hf hK hsupport hb p) hK hKU hsupport
    rw [hn, ENNReal.toReal_zero, mul_zero] at hi
    have hreal : (μ K).toReal = 0 := by
      simpa [f, integral_indicator hK.measurableSet, measureReal_def] using
        le_antisymm hi (abs_nonneg _)
    exact ((ENNReal.toReal_eq_zero_iff (μ K)).mp hreal).resolve_right
      (measure_ne_top μ K)
  intro A hA
  let A' := toMeasurable (ν.restrict U) A
  have hA' : MeasurableSet A' := measurableSet_toMeasurable _ _
  have hνA' : ν (A' ∩ U) = 0 := by
    rw [← Measure.restrict_apply hA', measure_toMeasurable]
    exact hA
  have hμA' : μ (A' ∩ U) = 0 := by
    rw [(hA'.inter hU.measurableSet).measure_eq_iSup_isCompact μ]
    apply le_antisymm _ (bot_le)
    refine iSup_le fun K => iSup_le fun hKsub => iSup_le fun hK => ?_
    exact (hcompact K hK (hKsub.trans inter_subset_right)
      (measure_mono_null hKsub hνA')).le
  have hμA0 : μ A' = 0 := by
    rwa [measure_inter_conull hμU] at hμA'
  exact measure_mono_null (subset_toMeasurable _ _) hμA0

end
section

open MeasureTheory Set
open scoped ENNReal

noncomputable section

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- The absolute value of `g`, truncated to the set where it is at most
`n + 1`. -/
def truncatedAbs (g : α → ℝ) (n : ℕ) (x : α) : ℝ :=
  {x | |g x| ≤ n + 1}.indicator (fun x => |g x|) x

/-- The signed conjugate power of the bounded absolute-value truncation. -/
def signedTruncatedDualPower (g : α → ℝ) (r : ℝ) (n : ℕ) (x : α) : ℝ :=
  if 0 ≤ g x then (truncatedAbs g n x) ^ (r - 1)
  else -(truncatedAbs g n x) ^ (r - 1)

/-- The absolute-value truncation is measurable. -/
theorem measurable_truncatedAbs {g : α → ℝ} (hg : Measurable g) (n : ℕ) :
    Measurable (truncatedAbs g n) := by
  exact hg.norm.indicator (measurableSet_le hg.norm measurable_const)

omit [MeasurableSpace α] in
/-- The absolute-value truncation is nonnegative. -/
theorem truncatedAbs_nonneg (g : α → ℝ) (n : ℕ) (x : α) :
    0 ≤ truncatedAbs g n x := by
  by_cases hx : x ∈ {x | |g x| ≤ n + 1}
  · rw [truncatedAbs, indicator_of_mem hx]
    exact abs_nonneg _
  · rw [truncatedAbs, indicator_of_notMem hx]

omit [MeasurableSpace α] in
/-- The truncation is bounded by its cutoff. -/
theorem abs_truncatedAbs_le (g : α → ℝ) (n : ℕ) (x : α) :
    |truncatedAbs g n x| ≤ n + 1 := by
  by_cases hx : x ∈ {x | |g x| ≤ n + 1}
  · rw [truncatedAbs, indicator_of_mem hx, abs_abs]
    exact hx
  · rw [truncatedAbs, indicator_of_notMem hx, abs_zero]
    positivity

/-- Bounded truncations belong to every Lp space over a finite measure. -/
theorem memLp_truncatedAbs [IsFiniteMeasure μ] {g : α → ℝ}
    (hg : Measurable g) (n : ℕ) (p : ENNReal) :
    MemLp (truncatedAbs g n) p μ := by
  apply MemLp.of_bound (measurable_truncatedAbs hg n).aestronglyMeasurable (n + 1)
  exact ae_of_all _ fun x => by
    simpa using abs_truncatedAbs_le g n x



omit [MeasurableSpace α] in
private theorem signedTruncatedDualPower_mul
    (g : α → ℝ) {r : ℝ} (hr : 1 < r) (n : ℕ) (x : α) :
    signedTruncatedDualPower g r n x * g x =
      truncatedAbs g n x ^ r := by
  by_cases hxmem : x ∈ {x | |g x| ≤ n + 1}
  · rw [truncatedAbs, indicator_of_mem hxmem]
    by_cases hxzero : |g x| = 0
    · have hgzero : g x = 0 := abs_eq_zero.mp hxzero
      rw [signedTruncatedDualPower, truncatedAbs, indicator_of_mem hxmem, hgzero,
        abs_zero, Real.zero_rpow (sub_ne_zero.mpr (ne_of_gt hr)),
        Real.zero_rpow (ne_of_gt (zero_lt_one.trans hr))]
      simp
    · have habsPos : 0 < |g x| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hxzero)
      by_cases hx : 0 ≤ g x
      · rw [signedTruncatedDualPower, ite_eq_left hx, truncatedAbs,
          indicator_of_mem hxmem, abs_of_nonneg hx]
        calc
          g x ^ (r - 1) * g x = g x ^ (r - 1) * g x ^ 1 := by
            rw [Real.rpow_one]
          _ = g x ^ ((r - 1) + 1) := (Real.rpow_add (by simpa [abs_of_nonneg hx]
            using habsPos) _ _).symm
          _ = g x ^ r := by
            congr 1
            ring
      · have hxneg : g x < 0 := lt_of_not_ge hx
        rw [signedTruncatedDualPower, ite_eq_right hx, truncatedAbs,
          indicator_of_mem hxmem, abs_of_neg hxneg]
        calc
          -(-g x) ^ (r - 1) * g x = (-g x) ^ (r - 1) * (-g x) := by ring
          _ =
              (-g x) ^ (r - 1) * (-g x) ^ (1 : ℝ) := by rw [Real.rpow_one]
          _ = (-g x) ^ ((r - 1) + 1) :=
            (Real.rpow_add (by linarith) _ _).symm
          _ = (-g x) ^ r := by
            congr 1
            ring
  · rw [signedTruncatedDualPower, truncatedAbs, indicator_of_notMem hxmem]
    rw [Real.zero_rpow (sub_ne_zero.mpr (ne_of_gt hr)),
      Real.zero_rpow (ne_of_gt (zero_lt_one.trans hr))]
    simp


end

end
section

open Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- A sharp bound against every bounded measurable conjugate test forces the
tested function to belong to `Lʳ`, with the same norm bound. -/
theorem memLp_and_eLpNorm_le_of_bounded_conjugate_tests
    [IsFiniteMeasure μ] {r M : ℝ} (hr : 1 < r) (hM : 0 ≤ M)
    {g : α → ℝ} (hgMeas : Measurable g) (_hgInt : Integrable g μ)
    (htest : ∀ φ : α → ℝ, Measurable φ →
      (∃ C : ℝ, 0 ≤ C ∧ ∀ x, |φ x| ≤ C) →
      |∫ x, φ x * g x ∂μ| ≤
        M * (eLpNorm φ (ENNReal.ofReal (r / (r - 1))) μ).toReal) :
    MemLp g (ENNReal.ofReal r) μ ∧
      (eLpNorm g (ENNReal.ofReal r) μ).toReal ≤ M    := by
  have signedTruncatedDualPower_measurable_bounded {g : α → ℝ} (hg : Measurable g) (n : ℕ) :
      Measurable (signedTruncatedDualPower g r n) ∧
      ∀ x, |signedTruncatedDualPower g r n x| ≤
        (n + 1 : ℝ) ^ (r - 1) := by
    have hpow :=
      (Real.continuous_rpow_const (sub_nonneg.mpr hr.le)).measurable.comp
        (measurable_truncatedAbs hg n)
    refine ⟨Measurable.ite (measurableSet_le measurable_const hg) hpow hpow.neg,
      fun x => ?_⟩
    rw [signedTruncatedDualPower]
    by_cases hx : 0 ≤ g x
    · rw [ite_eq_left hx, abs_of_nonneg (Real.rpow_nonneg (truncatedAbs_nonneg g n x) _)]
      have hbound := abs_truncatedAbs_le g n x
      rw [abs_of_nonneg (truncatedAbs_nonneg g n x)] at hbound
      exact Real.rpow_le_rpow (truncatedAbs_nonneg g n x)
        hbound
        (sub_nonneg.mpr hr.le)
    · rw [ite_eq_right hx, abs_neg,
        abs_of_nonneg (Real.rpow_nonneg (truncatedAbs_nonneg g n x) _)]
      have hbound := abs_truncatedAbs_le g n x
      rw [abs_of_nonneg (truncatedAbs_nonneg g n x)] at hbound
      exact Real.rpow_le_rpow (truncatedAbs_nonneg g n x)
        hbound (sub_nonneg.mpr hr.le)
  have integral_signedTruncatedDualPower_mul [IsFiniteMeasure μ] {g : α → ℝ} (hg : Measurable g) (n : ℕ) :
      ∫ x, signedTruncatedDualPower g r n x * g x ∂μ =
      (eLpNorm (truncatedAbs g n) (ENNReal.ofReal r) μ).toReal ^ r := by
    rw [PDE.toReal_eLpNorm_ofReal_rpow_eq_integral_rpow_norm
      (zero_lt_one.trans hr) (memLp_truncatedAbs hg n _)]
    apply integral_congr_ae
    exact ae_of_all _ fun x => by
      change signedTruncatedDualPower g r n x * g x = ‖truncatedAbs g n x‖ ^ r
      rw [signedTruncatedDualPower_mul g hr n x, Real.norm_eq_abs,
        abs_of_nonneg (truncatedAbs_nonneg g n x)]
  have eLpNorm_signedTruncatedDualPower {g : α → ℝ} (hg : Measurable g) (n : ℕ) :
      eLpNorm (signedTruncatedDualPower g r n)
        (ENNReal.ofReal (r / (r - 1))) μ =
      eLpNorm (truncatedAbs g n) (ENNReal.ofReal r) μ ^ (r - 1) := by
    have hTrunc := measurable_truncatedAbs hg n
    rw [eLpNorm_congr_norm_ae
      (signedTruncatedDualPower_measurable_bounded hg n).1.aestronglyMeasurable
      ((hTrunc.pow_const (r - 1)).aestronglyMeasurable)
      (ae_of_all _ fun x => by
        show ‖signedTruncatedDualPower g r n x‖ =
          ‖(truncatedAbs g n x) ^ (r - 1)‖
        rw [signedTruncatedDualPower]
        split_ifs <;> simp)]
    have hrSub := sub_pos.mpr hr
    have hexp : ENNReal.ofReal (r / (r - 1)) * ENNReal.ofReal (r - 1) =
        ENNReal.ofReal r := by
      rw [← ENNReal.ofReal_mul (div_nonneg (zero_le_one.trans hr.le) hrSub.le)]
      congr 1
      field_simp
    have hfun : (fun x => truncatedAbs g n x ^ (r - 1)) =
        fun x => ‖truncatedAbs g n x‖ ^ (r - 1) := by
      funext x
      rw [Real.norm_of_nonneg (truncatedAbs_nonneg g n x)]
    rw [hfun, eLpNorm_norm_rpow _ hTrunc.aestronglyMeasurable hrSub, hexp]
  have hnormTrunc (n : ℕ) :
      (eLpNorm (truncatedAbs g n) (ENNReal.ofReal r) μ).toReal ≤ M := by
    let N := (eLpNorm (truncatedAbs g n) (ENNReal.ofReal r) μ).toReal
    have htestn := htest (signedTruncatedDualPower g r n)
      (signedTruncatedDualPower_measurable_bounded hgMeas n).1
      ⟨(n + 1 : ℝ) ^ (r - 1),
        Real.rpow_nonneg (by positivity) _,
        signedTruncatedDualPower_measurable_bounded hgMeas n |>.2⟩
    rw [integral_signedTruncatedDualPower_mul hgMeas n,
      eLpNorm_signedTruncatedDualPower hgMeas n] at htestn
    rw [← ENNReal.toReal_rpow] at htestn
    change |N ^ r| ≤ M * N ^ (r - 1) at htestn
    have hN0 : 0 ≤ N := ENNReal.toReal_nonneg
    rw [abs_of_nonneg (Real.rpow_nonneg hN0 _)] at htestn
    by_cases hNz : N = 0
    · simpa [N, hNz] using hM
    · have hNpos : 0 < N := lt_of_le_of_ne hN0 (Ne.symm hNz)
      have hsplit : N ^ r = N * N ^ (r - 1) := by
        calc
          N ^ r = N ^ (1 + (r - 1)) := by
            congr 1
            ring
          _ = N ^ 1 * N ^ (r - 1) := Real.rpow_add hNpos _ _
          _ = N * N ^ (r - 1) := by rw [Real.rpow_one]
      rw [hsplit] at htestn
      exact le_of_mul_le_mul_right htestn (Real.rpow_pos_of_pos hNpos _)
  have htruncNormENN (n : ℕ) :
      eLpNorm (truncatedAbs g n) (ENNReal.ofReal r) μ ≤ ENNReal.ofReal M := by
    apply (ENNReal.toReal_le_toReal
      (memLp_truncatedAbs hgMeas n _).eLpNorm_ne_top ENNReal.ofReal_ne_top).mp
    rw [ENNReal.toReal_ofReal hM]
    exact hnormTrunc n
  have hlim (x : α) :
      Tendsto (fun n => truncatedAbs g n x) atTop (𝓝 |g x|) := by
    apply tendsto_atTop_of_eventually_const
      (i₀ := Nat.ceil |g x|)
    intro n hn
    rw [truncatedAbs, Set.indicator_of_mem]
    have hceil : |g x| ≤ Nat.ceil |g x| := Nat.le_ceil _
    exact hceil.trans (by exact_mod_cast (hn.trans (Nat.le_add_right n 1)))
  have habsNorm : eLpNorm (fun x => |g x|) (ENNReal.ofReal r) μ ≤
      ENNReal.ofReal M := by
    refine (Lp.eLpNorm_lim_le_liminf_eLpNorm
      (fun n => (measurable_truncatedAbs hgMeas n).aestronglyMeasurable)
      (fun x => |g x|) (continuous_abs.measurable.comp hgMeas).aestronglyMeasurable
      (ae_of_all _ hlim)).trans ?_
    exact liminf_le_of_frequently_le (Frequently.of_forall htruncNormENN)
  have habsLp : MemLp (fun x => |g x|) (ENNReal.ofReal r) μ := by
    exact habsNorm.trans_lt ENNReal.ofReal_lt_top
  have hnormEq : eLpNorm g (ENNReal.ofReal r) μ =
      eLpNorm (fun x => |g x|) (ENNReal.ofReal r) μ := by
    apply eLpNorm_congr_norm_ae hgMeas.aestronglyMeasurable
      (continuous_abs.measurable.comp hgMeas).aestronglyMeasurable
    exact ae_of_all _ fun x => by simp [Real.norm_eq_abs]
  have hgLp : MemLp g (ENNReal.ofReal r) μ := by
    rw [memLp_iff, hnormEq]
    exact habsLp.eLpNorm_lt_top
  refine ⟨hgLp, ?_⟩
  rw [hnormEq]
  simpa [ENNReal.toReal_ofReal hM] using (ENNReal.toReal_mono ENNReal.ofReal_ne_top habsNorm)

end

end
section

open MeasureTheory Set Filter
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The density forced by smooth tests is measurable, nonnegative, and integrable. -/
theorem rnDensity_of_smooth_tests (ν μ : Measure E)
    [ν.IsAddHaarMeasure] [IsFiniteMeasure μ] {U : Set E} (hU : IsOpen U)
    (hμU : μ Uᶜ = 0) {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞)
    {C : ℝ} (hC : 0 ≤ C)
    (htest : ∀ f : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f →
      tsupport f ⊆ U → (∀ x, 0 ≤ f x) →
      (∫ x, f x ∂μ) ≤ C * (eLpNorm f p (ν.restrict U)).toReal) :
    let g := fun x => (μ.rnDeriv (ν.restrict U) x).toReal
    Measurable g ∧ (∀ x, 0 ≤ g x) ∧ Integrable g (ν.restrict U) ∧
      (∀ f : E → ℝ, (∫ x, f x * g x ∂ν.restrict U) = ∫ x, f x ∂μ) ∧
      (∫ x, g x ∂ν.restrict U) = (μ univ).toReal := by
  have hac := absolutelyContinuous_of_smooth_tests ν μ hU hμU hp hpt hC htest
  dsimp only
  refine ⟨(Measure.measurable_rnDeriv _ _).ennreal_toReal,
    fun _ => ENNReal.toReal_nonneg, ?_, ?_, ?_⟩
  · have hi := Measure.integrableOn_toReal_rnDeriv (μ := μ) (ν := ν.restrict U)
      (measure_ne_top μ univ)
    simpa using hi
  · intro f
    simpa only [mul_comm] using integral_toReal_rnDeriv_mul hac
  · simpa only [measureReal_def] using Measure.integral_toReal_rnDeriv hac

/-- The Radon–Nikodym density has the sharp `Lʳ` bound on each compact interior subset. -/
theorem rnDensity_compact_norm_le (ν μ : Measure E)
    [ν.IsAddHaarMeasure] [IsFiniteMeasure μ] {U : Set E} (hU : IsOpen U)
    (hμU : μ Uᶜ = 0) {r C : ℝ} (hr : 1 < r) (hC : 0 ≤ C)
    (htest : ∀ f : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f →
      tsupport f ⊆ U → (∀ x, 0 ≤ f x) →
      (∫ x, f x ∂μ) ≤ C *
        (eLpNorm f (ENNReal.ofReal (r / (r - 1))) (ν.restrict U)).toReal)
    {K : Set E} (hK : IsCompact K) (hKU : K ⊆ U) :
    let g := fun x => (μ.rnDeriv (ν.restrict U) x).toReal
    MemLp g (ENNReal.ofReal r) ((ν.restrict U).restrict K) ∧
      (eLpNorm g (ENNReal.ofReal r) ((ν.restrict U).restrict K)).toReal ≤ C := by
  let p := ENNReal.ofReal (r / (r - 1))
  have hp : 1 ≤ p := by
    apply ENNReal.one_le_ofReal.mpr
    exact (le_div_iff₀ (by linarith)).2 (by linarith)
  have hpt : p ≠ ∞ := ENNReal.ofReal_ne_top
  have hprops := rnDensity_of_smooth_tests ν μ hU hμU hp hpt hC htest
  let g := fun x => (μ.rnDeriv (ν.restrict U) x).toReal
  have hfin : IsFiniteMeasure ((ν.restrict U).restrict K) := ⟨by
    rw [Measure.restrict_apply_univ, Measure.restrict_eq_self ν hKU]
    exact hK.measure_lt_top⟩
  have : IsFiniteMeasureOnCompacts (ν + μ) := finiteOnCompacts_add ν μ
  apply memLp_and_eLpNorm_le_of_bounded_conjugate_tests hr hC hprops.1
    hprops.2.2.1.restrict
  intro φ hφ hφbound
  obtain ⟨M, hM, hφM⟩ := hφbound
  let f := K.indicator φ
  have hf : Measurable f := hφ.indicator hK.measurableSet
  have hfK : Function.support f ⊆ K := Set.support_indicator_subset
  have hfM : ∀ x, |f x| ≤ M := by
    intro x
    by_cases hx : x ∈ K
    · simpa [f, hx] using hφM x
    · simpa [f, hx] using hM
  have hb := abs_integral_le_of_smooth_tests_compact ν μ hU hp hpt hC htest
    (memLp_of_bounded_compact_support (ν + μ) hf hK hfK hfM p) hK hKU hfK
  have hpair : (∫ x, φ x * g x ∂(ν.restrict U).restrict K) = ∫ x, f x ∂μ := by
    rw [show (fun x => φ x * g x) = (fun x => g x * φ x) by
      funext x; exact mul_comm _ _]
    change (∫ x in K, (μ.rnDeriv (ν.restrict U) x).toReal * φ x ∂ν.restrict U) = _
    rw [setIntegral_toReal_rnDeriv_mul (absolutelyContinuous_of_smooth_tests ν μ hU hμU hp hpt hC htest) hK.measurableSet,
      ← integral_indicator hK.measurableSet]
  rw [hpair]
  simpa only [f, eLpNorm_indicator_eq_eLpNorm_restrict hK.measurableSet] using hb

end

open MeasureTheory Set Filter
open scoped ENNReal Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
/-- An open set has compact interior subsets eventually containing each of its points. -/
theorem exists_compact_interior_exhaustion {U : Set E} (hU : IsOpen U) :
    ∃ K : ℕ → Set E, (∀ n, IsCompact (K n)) ∧ (∀ n, K n ⊆ U) ∧
      ∀ x ∈ U, ∀ᶠ n in atTop, x ∈ K n := by
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  let k : CompactExhaustion U := CompactExhaustion.choice U
  let K : ℕ → Set E := fun n => Subtype.val '' k n
  refine ⟨K, fun n => (k.isCompact n).image continuous_subtype_val,
    fun n x hx => ?_, ?_⟩
  · obtain ⟨y, _, rfl⟩ := hx
    exact y.property
  · intro x hx
    have hxall : (⟨x, hx⟩ : U) ∈ ⋃ n, k n := by rw [k.iUnion_eq]; trivial
    obtain ⟨N, hN⟩ := mem_iUnion.mp hxall
    filter_upwards [eventually_ge_atTop N] with n hn
    exact ⟨⟨x, hx⟩, k.subset hn hN, rfl⟩

/-- A conjugate positive smooth-test bound gives a measurable nonnegative sharp `Lʳ` density.
The finite tested measure is concentrated on the open region `U`; all norms use `ν.restrict U`.
The same density has its exact `L¹` mass and represents every real test integral. -/
theorem exists_density_of_smooth_tests (ν μ : Measure E)
    [ν.IsAddHaarMeasure] [IsFiniteMeasure μ] {U : Set E} (hU : IsOpen U)
    (hμU : μ Uᶜ = 0) {r C : ℝ} (hr : 1 < r) (hC : 0 ≤ C)
    (htest : ∀ f : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f →
      tsupport f ⊆ U → (∀ x, 0 ≤ f x) →
      (∫ x, f x ∂μ) ≤ C *
        (eLpNorm f (ENNReal.ofReal (r / (r - 1))) (ν.restrict U)).toReal) :
    μ ≪ ν.restrict U ∧ ∃ g : E → ℝ,
      Measurable g ∧ (∀ x, 0 ≤ g x) ∧ Integrable g (ν.restrict U) ∧
      MemLp g (ENNReal.ofReal r) (ν.restrict U) ∧
      (eLpNorm g (ENNReal.ofReal r) (ν.restrict U)).toReal ≤ C ∧
      (∫ x, g x ∂ν.restrict U) = (μ univ).toReal ∧
      ∀ f : E → ℝ, (∫ x, f x * g x ∂ν.restrict U) = ∫ x, f x ∂μ := by
  have hp : 1 ≤ ENNReal.ofReal (r / (r - 1)) := by
    apply ENNReal.one_le_ofReal.mpr
    exact (le_div_iff₀ (by linarith)).2 (by linarith)
  have hprops := rnDensity_of_smooth_tests ν μ hU hμU hp ENNReal.ofReal_ne_top hC htest
  let g := fun x => (μ.rnDeriv (ν.restrict U) x).toReal
  obtain ⟨K, hK, hKU, hcover⟩ := exists_compact_interior_exhaustion hU
  have hlocal (n : ℕ) := rnDensity_compact_norm_le ν μ hU hμU hr hC htest (hK n) (hKU n)
  have hnorm (n : ℕ) :
      eLpNorm ((K n).indicator g) (ENNReal.ofReal r) (ν.restrict U) ≤
        ENNReal.ofReal C := by
    rw [eLpNorm_indicator_eq_eLpNorm_restrict (hK n).measurableSet]
    exact (ENNReal.toReal_le_toReal (hlocal n).1.eLpNorm_ne_top
      ENNReal.ofReal_ne_top).mp (by simpa only [ENNReal.toReal_ofReal hC] using (hlocal n).2)
  have hlim : ∀ᵐ x ∂ν.restrict U,
      Tendsto (fun n => (K n).indicator g x) atTop (𝓝 (g x)) := by
    filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
    apply tendsto_const_nhds.congr'
    filter_upwards [hcover x hx] with n hn
    exact (indicator_of_mem hn g).symm
  have hglobal : eLpNorm g (ENNReal.ofReal r) (ν.restrict U) ≤ ENNReal.ofReal C := by
    refine (Lp.eLpNorm_lim_le_liminf_eLpNorm
      (fun n => hprops.1.aestronglyMeasurable.indicator (hK n).measurableSet)
      g hprops.1.aestronglyMeasurable hlim).trans ?_
    exact liminf_le_of_frequently_le (Frequently.of_forall hnorm)
  refine ⟨(absolutelyContinuous_of_smooth_tests ν μ hU hμU hp ENNReal.ofReal_ne_top hC htest), g, hprops.1, hprops.2.1, hprops.2.2.1,
    hglobal.trans_lt ENNReal.ofReal_lt_top, ?_, hprops.2.2.2.2, hprops.2.2.2.1⟩
  simpa only [ENNReal.toReal_ofReal hC] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hglobal

end HypoellipticAleksandrov.KineticAleksandrov.Occupation

