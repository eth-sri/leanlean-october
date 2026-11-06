module

public import proofs.RAFCriticalWindowQuantitative.FiniteSourceLower
public import proofs.RAFCriticalWindowQuantitative.FiniteSourceUpper
public import proofs.RAFEmergenceApprox.ParameterAdapter

@[expose] public section

namespace RAFCriticalWindowQuantitative
open HordijkSteelThreshold RAFReactionQuotient unitInterval

variable (p : ℚ)

def rationalPool  (k : ℕ) : ℚ := 1-(1-p)^k

theorem rationalPool_nonneg  (hp : 0 ≤ p) (hp1 : p ≤ 1) (k : ℕ) :
    0 ≤ rationalPool p k := by
  exact sub_nonneg.mpr $ pow_le_one₀ (sub_nonneg.mpr hp1) $ by linarith

theorem rationalPool_le_one  (hp1 : p ≤ 1) (k : ℕ) : rationalPool p k ≤ 1 := by
  dsimp [rationalPool]
  simp_all

theorem rationalPool_correct  (hp : 0 ≤ p) (hp1 : p ≤ 1) (k : ℕ) :
    rationalParameter (rationalPool p k) (rationalPool_nonneg p hp hp1 k) (rationalPool_le_one p hp1 k) =
      fixedPoolParameter (rationalParameter p hp hp1) k := by
  apply Subtype.ext
  simp [rationalParameter,rationalPool]

end RAFCriticalWindowQuantitative
