module
public import GuthMaynard.Improvement.MiddleLowLargeValues
public import GuthMaynard.Improvement.SourceTranslation
import WeylPort.Analytic.RealLaplace

public section
namespace GuthMaynard.Improvement

/-- Full bounded-coefficient middle-range large-values theorem, including all
positive thresholds, arbitrary translates and a uniform constant. Every
analytic estimate is discharged by the actual moment/extraction chain. -/
theorem middle_range_large_values : CandidateMiddleRangeEstimate := by
  intro ε hε
  pm_313 C₁ hC₁ hlow middle_large_values_low hε C₂ hC₂ hhigh middle_large_values_high
  let C := C₁+C₂+2
  pm_4312
  refine ⟨C,hC,?_⟩
  intro N T V t₀ a W hN hlo hhi hV ha hloc hsep hlarge
  have hn : 0 < N := by linarith
  obtain ⟨hNT,hTN⟩ := middle_time_bounds hN hlo hhi
  have ht : 0 < T := by linarith
  pm_8295 hP
  pm_4532 hpow ε hε.le
  pm_6316 hp0 N ε hn.le
  have hB : 0 ≤ N^2/V^2+middleMoment N T/V^4 := by positivity
  have horigin : ∀ (b : ℕ → ℂ) (Z : Finset ℝ),
      (∀ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2*N⌋₊, ‖b n‖ ≤ 1) →
      (∀ t ∈ Z, 0 ≤ t ∧ t ≤ T) →
      (∀ t ∈ Z, ∀ u ∈ Z, t ≠ u → 1 ≤ |t-u|) →
      (∀ t ∈ Z, V ≤ ‖boundedPolynomial N b t‖) →
      (Z.card:ℝ) ≤ C*N^ε*(N^2/V^2+middleMoment N T/V^4) := by
    intro b Z hb hZ hZsep hZv
    by_cases hsmall : V < 1
    · have hh := middle_large_values_small (t₀ := 0) hN ht.le hTN hV hsmall Z
        (by intro t ht; simpa using hZ t ht) hZsep
      have h2 : 2 ≤ C*N^ε := by
        have hc2 : 2 ≤ C := by dsimp [C]; linarith
        exact hc2.trans (le_mul_of_one_le_right hC.le hpow)
      calc
        _ ≤ 2*N^2/V^2 := hh
        _ = 2*(N^2/V^2) := by ring
        _ ≤ C*N^ε*(N^2/V^2) := mul_le_mul_of_nonneg_right h2 (by positivity)
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_right (by positivity)) (by positivity)
    · have hV1 : 1 ≤ V := le_of_not_gt hsmall
      by_cases hVU : V ≤ middleThreshold N T
      · have hh := hlow N T V hN hlo hhi hV1 hVU b Z hb hZ hZsep hZv
        pm_182 hc C₁ C
        calc
          _ ≤ C₁*N^ε*middleMoment N T/V^4 := hh
          _ = (C₁*N^ε)*(middleMoment N T/V^4) := by ring
          _ ≤ (C*N^ε)*(middleMoment N T/V^4) := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hc hp0) (by positivity)
          _ ≤ _ := mul_le_mul_of_nonneg_left
            (le_add_of_nonneg_left (by positivity)) (by positivity)
      · have hh := hhigh N T V 0 hN hlo hhi (le_of_not_ge hVU) b Z hb
          (by intro t ht; simpa using hZ t ht) hZsep hZv
        pm_182 hc C₂ C
        exact hh.trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hc hp0) hB)
  exact source_large_values_translation horigin t₀ a W ha hloc hsep hlarge

end GuthMaynard.Improvement
