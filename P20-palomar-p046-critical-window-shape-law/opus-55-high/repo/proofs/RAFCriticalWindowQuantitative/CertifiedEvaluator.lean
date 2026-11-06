module

public import proofs.RAFCriticalWindowQuantitative.EscapeEvaluation
public import proofs.RAFCriticalWindowQuantitative.RealErrorBudget

@[expose] public section

namespace RAFCriticalWindowQuantitative
open HordijkSteelThreshold RAFReactionQuotient MeasureTheory unitInterval

variable (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1) (ε : ℚ) (hε : 0 < ε)

def splitEvaluationCap  : ℕ :=
  let L := 10*seedIndex q hq hq1 (precisionIndex ε)
  recordCap L (recordIndex q hq hq1 L ε hε)

def splitCertifiedInterval  : ℚ × ℚ :=
  let e := splitEscapeEval q $ splitEvaluationCap q hq hq1 ε hε-2
  (e-ε/2,e)

def quotientEvaluationCap  : ℕ :=
  let hhalf : 0 < q/2 := rationalHalf_pos q hq
  let hhalf1 : q/2 ≤ 1 := rationalHalf_le_one q hq hq1
  let L := 10*seedIndex (q/2) hhalf hhalf1 (precisionIndex ε)
  recordCap L (recordIndex q hq hq1 L ε hε)

def quotientCertifiedInterval  : ℚ × ℚ :=
  let e := quotientEscapeEval q $ quotientEvaluationCap q hq hq1 ε hε-2
  (e-ε/2,e)

end RAFCriticalWindowQuantitative
