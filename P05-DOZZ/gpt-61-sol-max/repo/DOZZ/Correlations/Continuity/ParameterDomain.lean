/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.Statements.Correlations.ExtendedSeibergN
public import DOZZ.GMC.SharpMoments.ExtendedSeibergCutoffUI
public import DOZZ.GMC.Assembly.AdmissibleGMC
import Mathlib.Tactic
@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- Clipping complementary real numbers to the unit interval preserves their sum. -/
theorem continuityClip_complement (a : ℝ) :
    max 0 (min 1 a) + max 0 (min 1 (1 - a)) = 1 := by
  grind

/-- A compact chart partition, symmetric under complex inversion. -/
noncomputable def continuityChartWeight (x : ℂ) : ℝ≥0 :=
  Real.toNNReal (max 0 (min 1 ((2 - ‖x‖) / (1 + ‖x‖))))

theorem continuityChartWeight_continuous : Continuous continuityChartWeight := by
  unfold continuityChartWeight
  fun_prop (disch := intro x; positivity)

theorem continuityChartWeight_le_one (x : ℂ) : continuityChartWeight x ≤ 1 := by
  rw [continuityChartWeight, Real.toNNReal_le_iff_le_coe]
  exact max_le zero_le_one (min_le_left _ _)

theorem continuityChartWeight_zero {x : ℂ} (hx : 2 ≤ ‖x‖) :
    continuityChartWeight x = 0 := by
  rw [continuityChartWeight, max_eq_left (min_le_right _ _ |>.trans
    (div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)))]
  exact Real.toNNReal_zero

theorem continuityChartWeight_hasCompactSupport : HasCompactSupport continuityChartWeight := by
  apply HasCompactSupport.intro (K := Metric.closedBall (0 : ℂ) 2)
    (isCompact_closedBall _ _)
  intro x hx
  apply continuityChartWeight_zero
  rw [Metric.mem_closedBall, dist_zero_right] at hx
  exact (not_le.mp hx).le

noncomputable def continuityChartWeightBCF : BoundedContinuousFunction ℂ ℝ≥0 :=
  BoundedContinuousFunction.mkOfBound ⟨continuityChartWeight, continuityChartWeight_continuous⟩ 1
    (fun x y => by
      change dist (continuityChartWeight x) (continuityChartWeight y) ≤ 1
      rw [NNReal.dist_eq]
      have hx : (continuityChartWeight x : ℝ) ≤ 1 := by exact_mod_cast continuityChartWeight_le_one x
      have hy : (continuityChartWeight y : ℝ) ≤ 1 := by exact_mod_cast continuityChartWeight_le_one y
      exact abs_le.mpr ⟨by bound, by bound⟩)

theorem continuityChartWeight_sum_one {x : ℂ} (hx : x ≠ 0) :
    continuityChartWeight x + continuityChartWeight x⁻¹ = 1 := by
  
  have he : (2 - ‖x⁻¹‖) / (1 + ‖x⁻¹‖) = 1 - (2 - ‖x‖) / (1 + ‖x‖) := by
    rw [norm_inv]
    field_simp
    ring
  apply NNReal.coe_injective
  simp only [NNReal.coe_add, NNReal.coe_one, continuityChartWeight,
    Real.coe_toNNReal _ (le_max_left _ _)]
  rw [he]
  exact continuityClip_complement _

/-- A concrete partition is needed only for the two-chart cutoff estimate
`DOZZ.equatorGFF_extendedSeiberg_cutoff_UI`. -/
noncomputable def continuityChartPartition : GMCChartPartition where
  finiteWeight := continuityChartWeightBCF
  infinityWeight := continuityChartWeightBCF
  finite_hasCompactSupport := continuityChartWeight_hasCompactSupport
  infinity_hasCompactSupport := continuityChartWeight_hasCompactSupport
  sum_one := fun _ hx => continuityChartWeight_sum_one hx

/-- A GMC family specified on a compact parameter set extends to all subcritical
charges without changing any given version on that set. No charge measurability is assumed. -/
theorem extendGMCFamily_on_compact
    {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (M : ℝ → Ω → Measure ℂ) (K : Set (ℝ × (Fin N → ℝ)))
    (hM : ∀ q ∈ K, IsGMCOf P X q.1 (M q.1)) :
    ∃ Mfam : ℝ → Ω → Measure ℂ,
      (∀ γ ∈ Ioo (0 : ℝ) 2, IsGMCOf P X γ (Mfam γ)) ∧
      ∀ q ∈ K, Mfam q.1 = M q.1 := by
  classical
  let Γ := Prod.fst '' K
  have hex : ∀ γ : ℝ, ∃ Mg : Ω → Measure ℂ,
      γ ∈ Ioo (0 : ℝ) 2 → IsGMCOf P X γ Mg := by
    intro γ
    by_cases hγ : γ ∈ Ioo (0 : ℝ) 2
    · obtain ⟨_, Mg, _, hg⟩ := equatorGFF_circle_average_GMC_exists P X hX γ hγ.1 hγ.2
      exact ⟨Mg, fun _ => hg⟩
    · exact ⟨fun _ => 0, fun h => (hγ h).elim⟩
  choose Mg hg using hex
  let Mfam : ℝ → Ω → Measure ℂ := fun γ => if γ ∈ Γ then M γ else Mg γ
  refine ⟨Mfam, ?_, ?_⟩
  all_goals grind

end DOZZ.Proofs
