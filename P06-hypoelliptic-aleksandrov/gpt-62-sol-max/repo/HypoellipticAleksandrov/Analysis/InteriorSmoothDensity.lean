module

public import HypoellipticAleksandrov.Analysis.SmoothCutoff
public import Mathlib.Analysis.Normed.Lp.SmoothApprox
public import Mathlib.MeasureTheory.Measure.Regular

/-! # Density of smooth tests compactly supported in an open set -/

@[expose] public section

open Filter Function MeasureTheory Set
open scoped ContDiff ENNReal

noncomputable section

namespace HypoellipticAleksandrov.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

private theorem smooth_cutoff_approximation {μ : Measure E} [IsFiniteMeasureOnCompacts μ]
    [μ.InnerRegularCompactLTTop] {U : Set E} (hU : IsOpen U) {g : E → ℝ}
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) {ε : ℝ} (hε : 0 < ε) :
    ∃ q : E → ℝ, ContDiff ℝ ∞ q ∧ HasCompactSupport q ∧ tsupport q ⊆ U ∧
      eLpNorm (g - q) 2 (μ.restrict U) ≤ ENNReal.ofReal ε := by
  let ν := μ.restrict U
  let A := U ∩ tsupport g
  have hA : MeasurableSet A := hU.measurableSet.inter (isClosed_tsupport _).measurableSet
  have hAfin : ν A ≠ ⊤ := (lt_of_le_of_lt (measure_mono inter_subset_right) hgc.measure_lt_top).ne
  obtain ⟨B, hB⟩ := hg.continuous.bounded_above_of_compact_support hgc
  let C := max B 1
  have hC : 0 < C := zero_lt_one.trans_le (le_max_right _ _)
  let r := ε / C
  have hr : 0 < r := div_pos hε hC
  obtain ⟨K, hKA, hK, hsmall⟩ := hA.exists_isCompact_diff_lt (μ := ν) hAfin
    (ENNReal.ofReal_pos.mpr (sq_pos_of_pos hr)).ne'
  obtain ⟨χ, hχ, _, hχU, hχr, hχ1⟩ := exists_smooth_cutoff hK hU (hKA.trans inter_subset_left)
  let q := χ * g
  refine ⟨q, hχ.mul hg, hgc.mono (support_mul_subset_right χ g),
    tsupport_mul_subset_left.trans hχU, ?_⟩
  have heq : g - q =ᵐ[ν] (A \ K).indicator (g - q) :=
    ae_restrict_of_forall_mem hU.measurableSet fun x hx => by
      by_cases hs : x ∈ A \ K
      · simp [hs]
      rw [indicator_of_notMem hs]
      by_cases hxK : x ∈ K
      · simp [q, hχ1 x hxK]
      have hz : x ∉ tsupport g := fun h => hs ⟨⟨hx, h⟩, hxK⟩
      simp [q, image_eq_zero_of_notMem_tsupport hz]
  have hs : MeasurableSet (A \ K) := hA.diff hK.measurableSet
  have hmeas := ((hg.sub (hχ.mul hg)).continuous.aestronglyMeasurable (μ := ν)).indicator hs
  rw [eLpNorm_congr_ae heq]
  refine (eLpNorm_indicator_sub_le_of_dist_bdd ν ENNReal.coe_ne_top hs.nullMeasurableSet hC.le
    hmeas (fun x _ => ?_)).trans ?_
  · rw [dist_eq_norm, show g x - χ x * g x = (1 - χ x) * g x by ring,
      norm_mul, Real.norm_of_nonneg (sub_nonneg.mpr (hχr x).2)]
    exact (mul_le_of_le_one_left (norm_nonneg _) (by linarith [(hχr x).1])).trans
      ((hB x).trans (le_max_left _ _))
  · calc
      _ ≤ ENNReal.ofReal C * (ENNReal.ofReal (r ^ 2)) ^ (1 / (2 : ℝ≥0∞).toReal) := by
        gcongr
        exact ENNReal.rpow_le_rpow hsmall.le (by positivity)
      _ = ENNReal.ofReal ε := by
        rw [show 1 / (2 : ℝ≥0∞).toReal = (1 / 2 : ℝ) by norm_num,
          ENNReal.ofReal_rpow_of_nonneg (sq_nonneg r) (by norm_num), ← Real.sqrt_eq_rpow,
          Real.sqrt_sq hr.le, ← ENNReal.ofReal_mul hC.le]
        simp [r, mul_div_cancel₀ _ hC.ne']

private theorem dist_toLp_le {μ : Measure E} {f g : E → ℝ} {δ : ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) (hδ : 0 ≤ δ)
    (h : eLpNorm (f - g) 2 μ ≤ ENNReal.ofReal δ) : dist (hf.toLp f) (hg.toLp g) ≤ δ := by
  rw [Lp.dist_def, eLpNorm_congr_ae (hf.coeFn_toLp.sub hg.coeFn_toLp), ← ENNReal.toReal_ofReal hδ]
  exact ENNReal.toReal_mono ENNReal.ofReal_ne_top h

/-- Smooth compactly supported functions with topological support inside `U` are
 dense in the restricted real `L²` space. -/
theorem dense_interior_smooth_toLp (μ : Measure E) [IsFiniteMeasureOnCompacts μ]
    [μ.InnerRegularCompactLTTop] {U : Set E} (hU : IsOpen U) :
    Dense {q : Lp ℝ 2 (μ.restrict U) | ∃ (φ : E → ℝ) (hφ : MemLp φ 2 (μ.restrict U)),
      ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ U ∧ q = hφ.toLp φ} := by
  intro u
  refine (mem_closure_iff_nhds_basis Metric.nhds_basis_closedBall).mpr fun ε hε => ?_
  have hδ : 0 < ε / 2 := by positivity
  obtain ⟨g, hgc, hg, hug⟩ := (Lp.memLp u).exist_eLpNorm_sub_le ENNReal.coe_ne_top (by norm_num) hδ
  obtain ⟨q, hq, hqc, hqU, hgq⟩ := smooth_cutoff_approximation (μ := μ) hU hg hgc hδ
  have mg : MemLp g 2 (μ.restrict U) := hg.continuous.memLp_of_hasCompactSupport hgc
  have mq : MemLp q 2 (μ.restrict U) := hq.continuous.memLp_of_hasCompactSupport hqc
  have h1 : dist u (mg.toLp g) ≤ ε / 2 := by
    simpa only [Lp.toLp_coeFn] using dist_toLp_le (Lp.memLp u) mg hδ.le hug
  have h2 := dist_toLp_le mg mq hδ.le hgq
  refine ⟨mq.toLp q, ⟨q, mq, hq, hqc, hqU, rfl⟩, ?_⟩
  rw [Metric.mem_closedBall, dist_comm]
  linarith [dist_triangle u (mg.toLp g) (mq.toLp q)]

end HypoellipticAleksandrov.Analysis
