module

public import proofs.RAFCriticalWindowQuantitative.QuotientRecordIteration
public import proofs.RAFCriticalWindowQuantitative.QuotientEffectiveSeedSurvival
public import proofs.RAFCriticalWindowQuantitative.ExplicitTruncation

@[expose] public section

namespace RAFCriticalWindowQuantitative
open Classical RAFReactionQuotient HordijkSteelThreshold MeasureTheory unitInterval RAF.Polymer
open scoped ENNReal

noncomputable def quotientEscapeProbability (a : I) (K : ℕ) : ENNReal :=
  infiniteSplitPi a {ω | ∃ w, K < w.length ∧ InfiniteReversibleGenerated 2 (quotientField ω) w}

theorem explicit_quotient_truncation (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1)
    (m : ℕ) (hm : 2 ≤ m) (a : I) (ha : rationalParameter q hq.le hq1 ≤ a) (r : ℕ) :
    let hhalf : 0 < q/2 := by positivity
    let hhalf1 : q/2 ≤ 1 := by linarith
    let L := 10*seedIndex (q/2) hhalf hhalf1 m
    quotientEscapeProbability a (recordCap L r) ≤ quotientSurvival a + (m : ENNReal)⁻¹ +
      ((actualBinaryWords L).card : ENNReal) * (1-(toNNReal a : ENNReal)^(L+1))^r :=
  explicit_truncation_idx canonicalIndex canonicalIndex_product canonicalIndex_prefix
    quotientField_measurable a (quotientSurvival a) m _ r
    (effective_quotient_seed_survival q hq hq1 m hm a ha)

end RAFCriticalWindowQuantitative
