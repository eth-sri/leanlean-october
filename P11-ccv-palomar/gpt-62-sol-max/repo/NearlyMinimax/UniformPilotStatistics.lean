module

public import NearlyMinimax.PilotAnalyticToStatistics
public import NearlyMinimax.UniformPopulationPairBounds


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

/-- Sum the dyadic second moments after factoring out the common row scale. -/
private theorem dyadic_sum_second_of_rowCap {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (d ℓ J L : ℕ) (X : Fin (J + 1) → Ω → ℝ) (hX : ∀ j, MemLp (X j) 2 μ)
    (D B : ℝ) (hB : 0 ≤ B)
    (hE : ∀ j, (∫ z, X j z ^ 2 ∂μ) ≤ (dyadicPilotRowCap d ℓ j.val L * D) ^ 2 * B) :
    (∫ z, (∑ j, X j z) ^ 2 ∂μ) ≤
      4 * ((anchoredDimension d ℓ : ℝ) * D) ^ 2 * (d : ℝ) * dyadicMultilevelBudget B J L := by
  let P := ((anchoredDimension d ℓ : ℝ) * D) ^ 2 * (d : ℝ) * (((2 : ℝ) ^ L)⁻¹) ^ 2 * B
  refine (secondMoment_dyadic_sum_le μ J X hX P (by dsimp [P]; positivity) (fun j => ?_)).trans_eq ?_
  · apply (hE j).trans_eq
    rw [dyadicPilotRowCap_square]; dsimp [P]; ring
  · dsimp [P, dyadicMultilevelBudget]; ring

section
variable {d : ℕ} (C : ModelConstants d)
    [Nonempty (AnchoredIndex d C.order)]

theorem uniform_domain_common_dyadicMultilevel_bounds :
    ∃ D A : ℝ, 0 < D ∧ 0 < A ∧ ∀ U : ExtensionDomain d, ∀ θ : RegressionParameter d, Admissible (C.withDomain U) θ →
      ∀ n J L : ℕ, J ≤ L → ∀ y : ℝ, |y| ≤ max C.holderBound 1 → ∀ m : ℕ → ℕ,
      (∀ j : Fin (J + 1), m j.val + anchoredDimension d C.order + 1 ≤ n) →
      ∀ Λ : ℝ, 0 < Λ →
      (∀ j : Fin (J + 1), Λ ≤ (n : ℝ) - (m j.val + anchoredDimension d C.order + 1) + 1) →
      (∀ x ∈ unitCube d, ∀ z ∈ unitCube d,
        regularGridCell ((2 : ℕ) ^ L) (by positivity) x =
          regularGridCell ((2 : ℕ) ^ L) (by positivity) z →
        (∫ t, dyadicMultilevelErrorField C θ n J y m t (x, z) ^ 2 ∂sampleLaw θ n) ≤
          4 * ((anchoredDimension d C.order : ℝ) * D) ^ 2 * (d : ℝ) *
            dyadicMultilevelBudget (dyadicSeriesEnvelope (pilotModelConstants C) A Λ J m) J L) ∧
      (∀ ν : CovariatePair d → ℝ,
        MemLp ν 2 (regularPairDesignMeasure θ ((2 : ℕ) ^ L) (by positivity)) →
        (∫ t, (∫ w, ν w * dyadicMultilevelErrorField C θ n J y m t w
          ∂regularPairDesignMeasure θ ((2 : ℕ) ^ L) (by positivity)) ^ 2 ∂sampleLaw θ n) ≤
          (4 * C.densityUpper ^ 2 * (2 : ℝ) ^ d *
            ((anchoredDimension d C.order : ℝ) * D) ^ 2 * (d : ℝ) *
              dyadicMultilevelBudget (dyadicSeriesEnvelope (pilotModelConstants C) A Λ J m) J L / Λ) *
            (∫ w, ν w ^ 2 ∂regularPairDesignMeasure θ ((2 : ℕ) ^ L) (by positivity))) := by
  letI : Nonempty (AnchoredIndex d (pilotModelConstants C).order) :=
    inferInstanceAs (Nonempty (AnchoredIndex d C.order))
  obtain ⟨D, A, hD, hA, hder⟩ := uniform_domain_admissible_dyadic_increment_all_derivative_bound
    (pilotModelConstants C) (pilotModelConstants C).holderBound (pilotModelConstants C).holderBound_pos.le
  refine ⟨D, A, hD, hA, ?_⟩
  intro U θ hθ n J L hJL y hy m hdegree Λ hΛ hΛn
  let CE := (pilotModelConstants C).withDomain U
  letI : Nonempty (AnchoredIndex d CE.order) := inferInstanceAs (Nonempty (AnchoredIndex d C.order))
  have hθe : Admissible CE θ := by
    simpa only [pilotModelConstants_withDomain] using admissible_pilotModelConstants (C.withDomain U) θ hθ
  have hr := dyadicIncrementKernel_raw_budget_of_derivative CE θ hθe D A hD hA (hder U θ hθe)
  let H := dyadicSeriesEnvelope CE A Λ J m
  have hH : 0 ≤ H := dyadicSeriesEnvelope_nonneg CE A Λ hΛ.le J m
  have hj (j : Fin (J + 1)) : j.val ≤ L := (Nat.le_of_lt_succ j.isLt).trans hJL
  let E (j : Fin (J + 1)) (t : ObservedSample d n) := dyadicPilotErrorField CE θ n j.val y (m j.val) t
  refine ⟨fun x hx z hz hc => ?_, fun ν hν => ?_⟩
  · have hf (j) := dyadicPilotErrorField_point_energy CE θ hθe D A hD hA n j.val L
      (hj j) y hy (m j.val) (hdegree j) Λ hΛ (hΛn j) hr x hx z hz hc
    refine dyadic_sum_second_of_rowCap _ d C.order J L (fun j t => E j t (x,z))
      (fun j => (hf j).1) D H hH fun j => (hf j).2.trans ?_
    exact mul_le_mul_of_nonneg_left (dyadicPilotSeries_le_envelope CE A Λ hΛ.le J m j) (sq_nonneg _)
  · let M := regularPairDesignMeasure θ ((2 : ℕ) ^ L) (by positivity)
    let I := ∫ w, ν w ^ 2 ∂M
    have hI : 0 ≤ I := integral_nonneg (fun _ => sq_nonneg _)
    let B := CE.densityUpper ^ 2 * (2 : ℝ) ^ d * (H / Λ) * I
    have hB : 0 ≤ B := by dsimp [B]; positivity
    let X (j : Fin (J + 1)) (t : ObservedSample d n) := ∫ w, ν w * E j t w ∂M
    have hf (j) := dyadicPilotErrorField_test_energy CE θ hθe D A hD hA n j.val L
      (hj j) y hy (m j.val) (hdegree j) Λ hΛ (hΛn j) hr ν hν
    have hE (j : Fin (J + 1)) : (∫ t, X j t ^ 2 ∂sampleLaw θ n) ≤
        (dyadicPilotRowCap d CE.order j.val L * D) ^ 2 * B := by
      apply (hf j).2.trans
      have hratio : dyadicPilotScale d j.val / dyadicPilotScale d (j.val - 1) ≤ (2 : ℝ) ^ d :=
        (div_le_iff₀ (dyadicPilotScale_pos _ _)).mpr dyadicPilotScale_parent_ratio_le
      have hs := dyadicPilotSeries_div_scale_le_envelope CE A Λ hΛ J m j
      have hS := div_nonneg (dyadicPilotSeries_nonneg CE A Λ hΛ.le j.val (m j.val))
        (dyadicPilotScale_pos d j.val).le
      have hprod := mul_le_mul hratio hs hS (by positivity)
      have hb := mul_le_mul_of_nonneg_left hprod
        (show 0 ≤ (dyadicPilotRowCap d CE.order j.val L * D)^2 * CE.densityUpper^2 * I by positivity)
      dsimp only [B, I] at hb ⊢
      convert hb using 1 <;> field_simp [(dyadicPilotScale_pos d j.val).ne'] <;> ring
    have h := dyadic_sum_second_of_rowCap _ d CE.order J L X (fun j => (hf j).1) D B hB hE
    have hs (t : ObservedSample d n) :=
      dyadicMultilevelErrorField_test_integral_sum CE θ hθe n J L hJL y hy m hdegree ν hν t
    refine (le_of_eq (integral_congr_ae (.of_forall fun t => congrArg (· ^ 2) (hs t)))).trans (h.trans_eq ?_)
    change _ = (4 * CE.densityUpper ^ 2 * (2 : ℝ) ^ d *
      ((anchoredDimension d CE.order : ℝ) * D)^2 * (d : ℝ) * dyadicMultilevelBudget H J L / Λ) * I
    dsimp only [B, dyadicMultilevelBudget]
    ring


end

end NearlyMinimax
