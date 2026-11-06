module

public import Registry.P046.SupportingObligations
public import proofs.RAFCriticalWindowQuantitative.SourceCalibration
public import proofs.RAFCriticalWindowQuantitative.UniformApproximation
public import proofs.RAFCriticalWindowQuantitative.LowIntensity
public import proofs.RAFCriticalWindowQuantitative.ProductiveHistory
public import proofs.RAFCriticalWindowQuantitative.WorkedBound

@[expose] public section

namespace RAFCriticalWindowQuantitative
open HordijkSteelThreshold RAFReactionQuotient MeasureTheory unitInterval RAF.Polymer RAF.Concrete OverlapCorrectedRAF.Source

/-- Quantitative properties of the specified actual profile and executable programs. -/
structure ProfileGuarantees (S : I → ENNReal) (escape : I → ℕ → ENNReal)
    (evaluate : (q : ℚ) → 0 ≤ q → q ≤ 1 → (ε : ℚ) → 0 < ε → ℚ × ℚ)
    (cap : (q : ℚ) → 0 < q → q ≤ 1 → (ε : ℚ) → 0 < ε → ℕ)
    (coefficient : ℕ → ℕ) : Prop where
  enclosure : ∀ q hq hq1 ε hε,
    let v := evaluate q hq hq1 ε hε
    (v.1 : ℝ) ≤ (S (rationalParameter q hq hq1)).toReal ∧
      (S (rationalParameter q hq hq1)).toReal ≤ (v.2 : ℝ) ∧ v.2-v.1 < ε
  uniform_error : ∀ q hq hq1 ε hε a, rationalParameter q (le_of_lt hq) hq1 ≤ a →
    (escape a (cap q hq hq1 ε hε)).toReal ≤ (S a).toReal+(ε : ℝ)/2
  power_bound : ∀ a r, (S a).toReal ≤ (coefficient r : ℝ)*(a : ℝ)^r
  intensity_flatness : ∀ d ε, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ lam : ℝ, ∀ hlam : 0 < lam, lam < δ → (S (criticalOpenness lam hlam)).toReal < ε*lam^d

/-- The source contract uses actual catalytic inputs, not an assumed convergence rate. -/
def SourceGuarantees : Prop :=
  (∀ n m K, ∀ _hn : 4 ≤ n, ∀ _hm : 0 < m,
    ∀ p hp hp1 q hq hq1, ∀ _hk : 6 < nearFullPoolSize n m,
    ∀ _hpool : q ≤ rationalPool p (nearFullPoolSize n m),
    ∀ s hs hs1 ε hε,
    |(splitCatalyticProbability n (rationalParameter p hp hp1)).toReal -
      (staticSurvival (rationalParameter s hs hs1)).toReal| ≤
      (rationalIntervalError (splitSourceInterval n m K p q hq hq1)
        (splitTotalInterval s hs hs1 ε hε) : ℝ)) ∧
  (∀ n m K, ∀ _hn : 0 < n, ∀ _hm : 0 < m,
    ∀ p hp hp1 q hq hq1, ∀ _hk : 6 < nearFullPoolSize n m,
    ∀ _hpool : q ≤ rationalPool p (nearFullPoolSize n m),
    ∀ s hs hs1 ε hε,
    |(quotientRAFProbability n (rationalParameter p hp hp1)).toReal -
      (quotientSurvival (rationalParameter s hs hs1)).toReal| ≤
      (rationalIntervalError (quotientSourceInterval n m K p q hq hq1)
        (quotientTotalInterval s hs hs1 ε hε) : ℝ))

/-- Compiled minimum quantitative/computability successor for both literal RAF models.
The programs are explicit definitions; no desired bound or validity oracle is assumed. -/
theorem quantitative_critical_window_resolution :
    ProfileGuarantees staticSurvival splitEscapeProbability
      splitTotalInterval splitEvaluationCap splitSparseCoefficient ∧
    ProfileGuarantees quotientSurvival quotientEscapeProbability
      quotientTotalInterval quotientEvaluationCap quotientSparseCoefficient ∧
    SourceGuarantees ∧
    (∀ N k S x, x ∈ temporaryReactionClosure (N := N) 2 S → 2^(k+1) < molLength x →
      ∃ T, ProductiveHistory (binaryPolymerCRS N 2) S k T ∧ T.card = k ∧ T ⊆ S) ∧
    (∀ N k S x, x ∈ quotientClosure N 2 S → 2^(k+1) < molLength x →
      ∃ T, ProductiveHistory (repositoryCRS N 2) S k T ∧ T.card = k ∧ T ⊆ S) ∧
    (∀ a : I, (a : ℝ) ≤ 1/10^20 → (staticSurvival a).toReal < 8/10^26) :=
  ⟨⟨splitTotalInterval_correct,
    fun q hq hq1 ε hε a ha => real_truncation_error q hq hq1 ε hε _ a ha _ _ (measure_ne_top _ _)
      (explicit_split_truncation q hq hq1 _ (precisionIndex_ge_two ε) a ha _),
    split_sparse_real,
    power_bound_intensity_flatness _ splitSparseCoefficient split_sparse_real⟩,
   ⟨quotientTotalInterval_correct,
    fun q hq hq1 ε hε a ha => real_truncation_error q hq hq1 ε hε _ a ha _ _ (measure_ne_top _ _)
      (explicit_quotient_truncation q hq hq1 _ (precisionIndex_ge_two ε) a ha _),
    quotient_sparse_real,
    power_bound_intensity_flatness _ quotientSparseCoefficient quotient_sparse_real⟩,
   ⟨fun n m K hn hm p hp hp1 q hq hq1 hk hpool s hs hs1 ε hε =>
      interval_comparison_error (splitSourceInterval_correct n m K hn hm p hp hp1 q hq hq1 hk hpool)
        (splitTotalInterval_correct s hs hs1 ε hε),
    fun n m K hn hm p hp hp1 q hq hq1 hk hpool s hs hs1 ε hε =>
      interval_comparison_error (quotientSourceInterval_correct n m K hn hm p hp hp1 q hq hq1 hk hpool)
        (quotientTotalInterval_correct s hs hs1 ε hε)⟩,
   split_long_target_history, quotient_long_target_history, worked_low_openness_bound⟩

end RAFCriticalWindowQuantitative
