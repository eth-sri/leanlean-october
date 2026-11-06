module

public import proofs.RAFCriticalWindowQuantitative.EscapeEvaluation
public import proofs.RAFCriticalWindowQuantitative.RealErrorBudget

@[expose] public section

namespace RAFCriticalWindowQuantitative
open HordijkSteelThreshold RAFReactionQuotient MeasureTheory unitInterval

def splitEvaluationCap (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1) (ε : ℚ) (hε : 0 < ε) : ℕ :=
  let L := 10*seedIndex q hq hq1 (precisionIndex ε)
  recordCap L (recordIndex q hq hq1 L ε hε)

def splitCertifiedInterval (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1) (ε : ℚ) (hε : 0 < ε) : ℚ × ℚ :=
  let e := splitEscapeEval q (splitEvaluationCap q hq hq1 ε hε-2)
  (e-ε/2,e)

theorem certifiedInterval_of_bounds (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1)
    (ε : ℚ) (hε : 0 < ε) (L : ℕ) (e : ℚ) (E S : ENNReal) (hS : S ≠ ⊤) (hE : E ≠ ⊤)
    (htrunc : E ≤ S + (precisionIndex ε : ENNReal)⁻¹ +
      ((actualBinaryWords L).card : ENNReal) *
        (1 - (toNNReal (rationalParameter q hq.le hq1) : ENNReal) ^ (L + 1)) ^ (recordIndex q hq hq1 L ε hε))
    (he : (e : ℝ) = E.toReal) (hl : S ≤ E) :
    ((e - ε / 2 : ℚ) : ℝ) ≤ S.toReal ∧ S.toReal ≤ (e : ℝ) ∧ e - (e - ε / 2) < ε := by
  have ht := real_truncation_error q hq hq1 ε hε L (rationalParameter q hq.le hq1) le_rfl E S hS htrunc
  exact ⟨by push_cast; linarith, he ▸ ENNReal.toReal_mono hE hl, by linarith⟩

end RAFCriticalWindowQuantitative
