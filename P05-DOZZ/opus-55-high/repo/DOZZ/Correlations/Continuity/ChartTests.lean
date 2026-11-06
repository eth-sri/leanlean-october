/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.Correlations.Continuity.ParameterDomain
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- Coupling, finite roots, finite charges and the charge at infinity. -/
abbrev ContinuityCoulombParameter (N : ℕ) := ℝ × ((Fin N → ℂ) × (Fin N → ℝ) × ℝ)

/-- The real finite-chart cutoff test, including its partition weight. -/
noncomputable def continuityFiniteCutoffTest {N : ℕ} (partition : GMCChartPartition)
    (r : ℝ) (c : ContinuityCoulombParameter N) (x : ℂ) : ℝ :=
  (partition.finiteWeight x : ℝ) *
    (∏ k, (normPlus x / (‖x - c.2.1 k‖ + Real.exp (-r))) ^ (c.1 * c.2.2.1 k)) *
      normPlus x ^ (c.1 * c.2.2.2)

/-- The real inverted-chart cutoff test, including its partition weight. -/
noncomputable def continuityInfinityCutoffTest {N : ℕ} (partition : GMCChartPartition)
    (r : ℝ) (c : ContinuityCoulombParameter N) (u : ℂ) : ℝ :=
  (partition.infinityWeight u : ℝ) *
    (∏ k, (normPlus u / (‖1 - c.2.1 k * u‖ + Real.exp (-r))) ^ (c.1 * c.2.2.1 k)) *
      (normPlus u / (‖u‖ + Real.exp (-r))) ^ (c.1 * c.2.2.2)
section
variable {N : ℕ} (partition : GMCChartPartition) (r : ℝ)
section
variable (c : ContinuityCoulombParameter N) (x : ℂ)

theorem continuityFiniteCutoffTest_nonneg :
    0 ≤ continuityFiniteCutoffTest partition r c x := by
  unfold continuityFiniteCutoffTest normPlus
  positivity

theorem continuityInfinityCutoffTest_nonneg :
    0 ≤ continuityInfinityCutoffTest partition r c x := by
  unfold continuityInfinityCutoffTest normPlus
  positivity

end

theorem continuityFiniteCutoffTest_continuous :
    Continuous (fun p : ContinuityCoulombParameter N × ℂ =>
      continuityFiniteCutoffTest partition r p.1 p.2) := by
  have hp : Continuous (fun p : ContinuityCoulombParameter N × ℂ =>
      (partition.finiteWeight p.2 : ℝ)) :=
    by fun_prop
  have hn : Continuous (fun p : ContinuityCoulombParameter N × ℂ => normPlus p.2) := by
    unfold normPlus
    fun_prop
  refine (hp.mul (continuous_finsetProd _ fun k _ => ?_)).mul ?_
  · have hd : Continuous (fun p : ContinuityCoulombParameter N × ℂ =>
        ‖p.2 - p.1.2.1 k‖ + Real.exp (-r)) := by fun_prop
    exact (hn.div hd (fun p => (add_pos_of_nonneg_of_pos (norm_nonneg _)
      (Real.exp_pos _)).ne')).rpow (by fun_prop) (fun p => Or.inl
        (div_pos (lt_of_lt_of_le zero_lt_one (one_le_normPlus _))
          (add_pos_of_nonneg_of_pos (norm_nonneg _) (Real.exp_pos _))).ne')
  · exact hn.rpow (by fun_prop) (fun p => Or.inl
      (lt_of_lt_of_le zero_lt_one (one_le_normPlus _)).ne')

theorem continuityInfinityCutoffTest_continuous :
    Continuous (fun p : ContinuityCoulombParameter N × ℂ =>
      continuityInfinityCutoffTest partition r p.1 p.2) := by
  have hp : Continuous (fun p : ContinuityCoulombParameter N × ℂ =>
      (partition.infinityWeight p.2 : ℝ)) :=
    by fun_prop
  have hn : Continuous (fun p : ContinuityCoulombParameter N × ℂ => normPlus p.2) := by
    unfold normPlus
    fun_prop
  refine (hp.mul (continuous_finsetProd _ fun k _ => ?_)).mul ?_
  · have hd : Continuous (fun p : ContinuityCoulombParameter N × ℂ =>
        ‖1 - p.1.2.1 k * p.2‖ + Real.exp (-r)) := by fun_prop
    exact (hn.div hd (fun p => (add_pos_of_nonneg_of_pos (norm_nonneg _)
      (Real.exp_pos _)).ne')).rpow (by fun_prop) (fun p => Or.inl
        (div_pos (lt_of_lt_of_le zero_lt_one (one_le_normPlus _))
          (add_pos_of_nonneg_of_pos (norm_nonneg _) (Real.exp_pos _))).ne')
  · have hd : Continuous (fun p : ContinuityCoulombParameter N × ℂ =>
        ‖p.2‖ + Real.exp (-r)) := by fun_prop
    exact (hn.div hd (fun p => (add_pos_of_nonneg_of_pos (norm_nonneg _)
      (Real.exp_pos _)).ne')).rpow (by fun_prop) (fun p => Or.inl
        (div_pos (lt_of_lt_of_le zero_lt_one (one_le_normPlus _))
          (add_pos_of_nonneg_of_pos (norm_nonneg _) (Real.exp_pos _))).ne')

end

/-- Compact parameters and a common compact spatial support give one test bound. -/
theorem continuity_compact_support_bound
    {T : Type*} [TopologicalSpace T] (S : Set T) (hS : IsCompact S)
    (K : Set ℂ) (hK : IsCompact K) (F : T × ℂ → ℝ) (hF : Continuous F)
    (hz : ∀ c x, x ∉ K → F (c, x) = 0) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ c ∈ S, ∀ x, |F (c, x)| ≤ L := by
  obtain ⟨L, hL⟩ := (hS.prod hK).exists_bound_of_continuousOn hF.continuousOn
  refine ⟨max L 0, le_max_right .., fun c hc x => ?_⟩
  by_cases hx : x ∈ K
  · simp_all
  simp_all
section
variable {N : ℕ} (partition : GMCChartPartition) (r : ℝ)

/-- Both softened chart tests are uniformly bounded on a compact parameter set,
including charges of either sign. -/
theorem continuityCutoffTests_uniform_bound (S : Set (ContinuityCoulombParameter N)) (hS : IsCompact S) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ c ∈ S, ∀ x,
      |continuityFiniteCutoffTest partition r c x| ≤ L ∧
      |continuityInfinityCutoffTest partition r c x| ≤ L := by
  obtain ⟨Lf, hLf, hf⟩ := continuity_compact_support_bound S hS _
    partition.finite_hasCompactSupport.isCompact _
    (continuityFiniteCutoffTest_continuous partition r) (fun c x hx => by
      simp only [continuityFiniteCutoffTest, (image_eq_zero_of_notMem_tsupport hx), NNReal.coe_zero, zero_mul])
  obtain ⟨Li, hLi, hi⟩ := continuity_compact_support_bound S hS _
    partition.infinity_hasCompactSupport.isCompact _
    (continuityInfinityCutoffTest_continuous partition r) (fun c x hx => by
      simp only [continuityInfinityCutoffTest, (image_eq_zero_of_notMem_tsupport hx), NNReal.coe_zero, zero_mul])
  grind

/-- Passing from real chart tests to the extended weight `coulombCutoffWeight` is exact. -/
theorem coulombCutoffWeight_eq_ofReal_continuityCutoffTest (c : ContinuityCoulombParameter N) (x : ℂ) :
    coulombCutoffWeight partition c.1 c.2.2.1 c.2.1 c.2.2.2 r x =
      ENNReal.ofReal (continuityFiniteCutoffTest partition r c x +
        continuityInfinityCutoffTest partition r c x⁻¹) := by
  have hnorm (x : ℂ) : 0 < normPlus x := lt_of_lt_of_le zero_lt_one (one_le_normPlus x)
  have hf : coulombCutoffFiniteWeight c.1 c.2.2.1 c.2.1 c.2.2.2 r x =
      ENNReal.ofReal ((∏ k, (normPlus x / (‖x - c.2.1 k‖ + Real.exp (-r))) ^
        (c.1 * c.2.2.1 k)) * normPlus x ^ (c.1 * c.2.2.2)) := by
    unfold coulombCutoffFiniteWeight
    simp_rw [coulombWeight_rpow_ofReal (div_pos (hnorm x)
      (add_pos_of_nonneg_of_pos (norm_nonneg _) (Real.exp_pos _))),
      coulombWeight_rpow_ofReal (hnorm x)]
    rw [← ENNReal.ofReal_prod_of_nonneg (fun k _ => Real.rpow_nonneg (by unfold normPlus; positivity) _),
      ← ENNReal.ofReal_mul (by unfold normPlus; positivity)]
  have hi : coulombCutoffInfinityWeight c.1 c.2.2.1 c.2.1 c.2.2.2 r x⁻¹ =
      ENNReal.ofReal ((∏ k, (normPlus x⁻¹ / (‖1 - c.2.1 k * x⁻¹‖ + Real.exp (-r))) ^
        (c.1 * c.2.2.1 k)) * (normPlus x⁻¹ / (‖x⁻¹‖ + Real.exp (-r))) ^ (c.1 * c.2.2.2)) := by
    unfold coulombCutoffInfinityWeight
    simp_rw [coulombWeight_rpow_ofReal (div_pos (hnorm x⁻¹)
      (add_pos_of_nonneg_of_pos (norm_nonneg _) (Real.exp_pos _)))]
    rw [← ENNReal.ofReal_prod_of_nonneg (fun k _ => Real.rpow_nonneg (by unfold normPlus; positivity) _),
      ← ENNReal.ofReal_mul (by unfold normPlus; positivity)]
  rw [coulombCutoffWeight, hf, hi, ENNReal.ofReal_add
    (continuityFiniteCutoffTest_nonneg partition r c x)
    (continuityInfinityCutoffTest_nonneg partition r c x⁻¹)]
  congr 1
  · simp only [continuityFiniteCutoffTest, mul_assoc,
      ENNReal.ofReal_mul (partition.finiteWeight x).coe_nonneg, ENNReal.ofReal_coe_nnreal]
  · simp only [continuityInfinityCutoffTest, mul_assoc,
      ENNReal.ofReal_mul (partition.infinityWeight x⁻¹).coe_nonneg, ENNReal.ofReal_coe_nnreal]

end

end DOZZ.Proofs
