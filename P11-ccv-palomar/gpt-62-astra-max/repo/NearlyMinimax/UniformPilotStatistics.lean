module

public import NearlyMinimax.PilotAnalyticToStatistics
public import NearlyMinimax.UniformPilotDerivatives


@[expose] public section

/-! Domain-uniform actual statistical pilot bounds. Analytic witnesses are
chosen before the extension domain, then transferred through the genuine
L² factorial kernel calculations and multilevel aggregation. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace NearlyMinimax
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

section
variable {d : ℕ} {C : ModelConstants d} [Nonempty (AnchoredIndex d C.order)] {θ : RegressionParameter d}
    (hθ : Admissible C θ) {D A : ℝ} (hD : 0 < D) (hA : 0 < A)
include hA hD hθ

theorem dyadicMultilevelErrorField_point_second_of_variance
    (hv : PilotVarianceBound C θ D A) :
    ∀ n J L, J ≤ L → ∀ x ∈ unitCube d, ∀ z ∈ unitCube d,
      dyadicGridLabel L x =
        dyadicGridLabel L z →
      ∀ y, |y| ≤ C.holderBound → ∀ m,
      (∀ j : Fin (J + 1), m j.val + anchoredDimension d C.order + 1 ≤ n) →
      ∀ Λ, 0 < Λ →
      (∀ j : Fin (J + 1), Λ ≤ (n : ℝ) - (m j.val + anchoredDimension d C.order + 1) + 1) →
      (∫ t, dyadicMultilevelErrorField C θ J y m t (x, z) ^ 2 ∂sampleLaw θ n) ≤
        4 * ((anchoredDimension d C.order) * D) ^ 2 * d *
          dyadicMultilevelBudget (dyadicSeriesEnvelope C A Λ J m) J L := by
  have hpoint := dyadicPilotErrorField_point_second_of_variance hθ hD hA hv
  intro n J L hJL x hx z hz hc y hy m hdegree Λ hΛ hΛn
  let H := dyadicSeriesEnvelope C A Λ J m
  have hH  := dyadicSeriesEnvelope_nonneg C A Λ hΛ.le J m
  let B := ((anchoredDimension d C.order) * D) ^ 2 * d *
    ((2 ^ L)⁻¹) ^ 2 * H
  have hB : 0 ≤ B := by positivity
  let X (j : Fin (J + 1)) (t : Fin n → Observation d) :=
    dyadicPilotErrorField C θ j.val y (m j.val) t (x, z)
  have hX (j : Fin (J + 1))  :=
    (dyadicPilotErrorField_point_moment_facts hθ n j.val hx z y (hdegree j)).1
  have hE (j : Fin (J + 1)) : (∫ t, X j t ^ 2 ∂sampleLaw θ n) ≤ B * (2 ^ j.val) ^ 2 := by
    have h := hpoint n j.val L ((Nat.le_of_lt_succ j.isLt).trans hJL)
      x hx z hz hc y hy (m j.val) (hdegree j) Λ hΛ (hΛn j)
    apply h.trans
    rw [dyadicPilotRowCap_square]
    calc
      _ ≤ _ :=
        mul_le_mul_of_nonneg_left (by have hnon := dyadicPilotSeries_nonneg C A Λ hΛ.le j.val (m j.val); apply le_trans _ (dyadicSeriesEnvelope_level_le C A Λ J m j); exact le_mul_of_one_le_right hnon (le_max_left _ _)) (by positivity)
      _ = _ := by ring
  have h := secondMoment_dyadic_sum_le hX hB hE
  apply h.trans_eq
  dsimp [B, dyadicMultilevelBudget]
  ring


theorem dyadicMultilevelErrorField_test_second_of_variance
    (htest : PilotTestVarianceBound C θ D A) :
    ∀ n J L, J ≤ L → ∀ y, |y| ≤ C.holderBound → ∀ m,
      (∀ j : Fin (J + 1), m j.val + anchoredDimension d C.order + 1 ≤ n) →
      ∀ Λ, 0 < Λ →
      (∀ j : Fin (J + 1), Λ ≤ (n : ℝ) - (m j.val + anchoredDimension d C.order + 1) + 1) →
      ∀ ν,
      MemLp ν 2 (dyadicPairDesignMeasure θ L) →
      (∫ t, (∫ w, ν w * dyadicMultilevelErrorField C θ J y m t w
        ∂dyadicPairDesignMeasure θ L) ^ 2 ∂sampleLaw θ n) ≤
        (4 * C.densityUpper ^ 2 * 2 ^ d *
          ((anchoredDimension d C.order) * D) ^ 2 * d *
            dyadicMultilevelBudget (dyadicSeriesEnvelope C A Λ J m) J L / Λ) *
          (∫ w, ν w ^ 2 ∂dyadicPairDesignMeasure θ L) := by
  intro n J L hJL y hy m hdegree Λ hΛ hΛn ν hν
  let := sampleLaw_isProbability C θ hθ n
  let M := dyadicPairDesignMeasure θ L
  let H := dyadicSeriesEnvelope C A Λ J m
  have hH  := dyadicSeriesEnvelope_nonneg C A Λ hΛ.le J m
  let I := ∫ w, ν w ^ 2 ∂M
  have hI : 0 ≤ I := by positivity
  let scale := ((anchoredDimension d C.order) * D) ^ 2
  let B := C.densityUpper ^ 2 * 2 ^ d *
    scale * d *
      ((2 ^ L)⁻¹) ^ 2 * (H / Λ) * I
  have hB : 0 ≤ B := by positivity
  let X (j : Fin (J + 1)) (t : Fin n → Observation d) :=
    ∫ w, ν w * dyadicPilotErrorField C θ j.val y (m j.val) t w ∂M
  have hf (j : Fin (J + 1)) := dyadicPilotErrorField_test_moment_facts hθ
    ((Nat.le_of_lt_succ j.isLt).trans hJL) hy (hdegree j) hν
  have hE (j : Fin (J + 1)) : (∫ t, X j t ^ 2 ∂sampleLaw θ n) ≤ B * (2 ^ j.val) ^ 2 := by
    have h := htest n j.val L ((Nat.le_of_lt_succ j.isLt).trans hJL) y hy
      (m j.val) (hdegree j) Λ hΛ (hΛn j) ν hν
    rw [variance_of_integral_eq_zero (hf j).1.aemeasurable (hf j).2] at h
    apply h.trans
    change _ ≤ _
    rw [dyadicPilotRowCap_square]
    have hratio : dyadicPilotScale d j.val / dyadicPilotScale d (j.val - 1) ≤ 2 ^ d :=
      (div_le_iff₀ (dyadicPilotScale_pos _ _)).mpr dyadicPilotScale_parent_ratio_le
    have hs := dyadicPilotSeries_div_scale_le_envelope C A Λ hΛ m j
    have hsnon := div_nonneg (dyadicPilotSeries_nonneg C A Λ hΛ.le j.val (m j.val))
      (dyadicPilotScale_pos d j.val).le
    calc
      _ = (C.densityUpper ^ 2 * scale *
          d * ((2 ^ L)⁻¹) ^ 2 * (2 ^ j.val) ^ 2) *
          (dyadicPilotScale d j.val / dyadicPilotScale d (j.val - 1)) *
          (dyadicPilotSeries C A Λ j.val (m j.val) / dyadicPilotScale d j.val) * I := by
        field_simp [(dyadicPilotScale_pos d j.val).ne', (dyadicPilotScale_pos d (j.val - 1)).ne']
        <;> ring
      _ ≤ (C.densityUpper ^ 2 * scale *
          d * ((2 ^ L)⁻¹) ^ 2 * (2 ^ j.val) ^ 2) *
          (2 ^ d) * (H / Λ) * I := by
        apply mul_le_mul_of_nonneg_right _ hI
        exact mul_le_mul (mul_le_mul_of_nonneg_left hratio (by positivity)) hs hsnon (by positivity)
      _ = _ := by ring
  have h := secondMoment_dyadic_sum_le (X := X) (fun j => (hf j).1) hB hE
  have heq : (fun t => ∑ j, X j t) =
      (fun t => ∫ w, ν w * dyadicMultilevelErrorField C θ J y m t w ∂M) := by
    funext t
    exact (dyadicMultilevelErrorField_test_integral_sum hθ hJL hy hdegree hν t).symm
  have heqpoint (t : Fin n → Observation d) := congrFun heq t
  simp_rw [heqpoint] at h
  apply h.trans_eq
  dsimp [B, dyadicMultilevelBudget]
  ring

end


theorem uniform_domain_common_dyadicMultilevel_bounds {d : ℕ} (C : ModelConstants d)
    [Nonempty (AnchoredIndex d C.order)] :
    ∃ D A : ℝ, 0 < D ∧ 0 < A ∧ ∀ U, ∀ θ, Admissible (C.withDomain U) θ →
      ∀ n J L, J ≤ L → ∀ y, |y| ≤ max C.holderBound 1 → ∀ m,
      (∀ j : Fin (J + 1), m j.val + anchoredDimension d C.order + 1 ≤ n) →
      ∀ Λ, 0 < Λ →
      (∀ j : Fin (J + 1), Λ ≤ (n : ℝ) - (m j.val + anchoredDimension d C.order + 1) + 1) →
      (∀ x ∈ unitCube d, ∀ z ∈ unitCube d,
        dyadicGridLabel L x =
          dyadicGridLabel L z →
        (∫ t, dyadicMultilevelErrorField C θ J y m t (x, z) ^ 2 ∂sampleLaw θ n) ≤
          4 * ((anchoredDimension d C.order) * D) ^ 2 * d *
            dyadicMultilevelBudget (dyadicSeriesEnvelope (pilotModelConstants C) A Λ J m) J L) ∧
      (∀ ν,
        MemLp ν 2 (dyadicPairDesignMeasure θ L) →
        (∫ t, (∫ w, ν w * dyadicMultilevelErrorField C θ J y m t w
          ∂dyadicPairDesignMeasure θ L) ^ 2 ∂sampleLaw θ n) ≤
          (4 * C.densityUpper ^ 2 * 2 ^ d *
            ((anchoredDimension d C.order) * D) ^ 2 * d *
              dyadicMultilevelBudget (dyadicSeriesEnvelope (pilotModelConstants C) A Λ J m) J L / Λ) *
            (∫ w, ν w ^ 2 ∂dyadicPairDesignMeasure θ L)) := by
  letI : Nonempty (AnchoredIndex d (pilotModelConstants C).order) :=
    inferInstanceAs (Nonempty (AnchoredIndex d C.order))
  obtain ⟨D, A, hD, hA, hder⟩ := uniform_domain_admissible_dyadic_increment_all_derivative_bound
    (pilotModelConstants C) (pilotModelConstants C).holderBound_pos.le
  refine ⟨D, A, hD, hA, ?_⟩
  intro U θ hθ n J L hJL y hy m hdegree Λ hΛ hΛn
  let CE := (pilotModelConstants C).withDomain U
  letI : Nonempty (AnchoredIndex d CE.order) := inferInstanceAs (Nonempty (AnchoredIndex d C.order))
  have hθe : Admissible CE θ := by
    exact admissible_pilotModelConstants hθ
  have hd := hder U θ hθe
  have hr := dyadicIncrementKernel_raw_budget_of_derivative hθe hD hA hd
  have hv := dyadicPolynomialPilot_variance_of_derivative hθe hD hA hd
  have ht := dyadicPilotErrorField_test_variance_of_raw_budget hθe hD hA hr
  constructor
  · intro x hx z hz hc
    exact dyadicMultilevelErrorField_point_second_of_variance hθe hD hA hv
      n J L hJL x hx z hz hc y hy m hdegree Λ hΛ hΛn
  · exact dyadicMultilevelErrorField_test_second_of_variance hθe hD hA ht
      n J L hJL y hy m hdegree Λ hΛ hΛn

end NearlyMinimax
