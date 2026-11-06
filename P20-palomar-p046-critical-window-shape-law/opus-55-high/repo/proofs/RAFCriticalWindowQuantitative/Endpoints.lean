module

public import proofs.RAFCriticalWindowQuantitative.SmallOpenness
public import proofs.RAFCriticalWindowQuantitative.CertifiedEvaluator

@[expose] public section

namespace RAFCriticalWindowQuantitative
open HordijkSteelThreshold RAFReactionQuotient unitInterval

variable (q : ℚ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (ε : ℚ) (hε : 0 < ε)

def splitTotalInterval  : ℚ × ℚ :=
  if h : q = 0 then (0,0) else splitCertifiedInterval q (lt_of_le_of_ne hq $ Ne.symm h) hq1 ε hε

def quotientTotalInterval  : ℚ × ℚ :=
  if h : q = 0 then (0,0) else quotientCertifiedInterval q (lt_of_le_of_ne hq $ Ne.symm h) hq1 ε hε

end RAFCriticalWindowQuantitative
