module

public import proofs.RAFCriticalWindowQuantitative.EffectiveSeed

@[expose] public section

namespace RAFCriticalWindowQuantitative

def geometricIndex (t c ε : ℚ) (ht0 : 0 ≤ t) (ht1 : t < 1) (hε : 0 < ε) : ℕ :=
  Nat.find (geometricTest_exists t c ε ht0 ht1 hε)

theorem geometricIndex_spec (t c ε : ℚ) (ht0 : 0 ≤ t) (ht1 : t < 1) (hε : 0 < ε) :
    geometricTest t c ε (geometricIndex t c ε ht0 ht1 hε) :=
  Nat.find_spec (geometricTest_exists t c ε ht0 ht1 hε)

/-- The repair-failure ratio is a genuine geometric ratio at every positive openness. -/
theorem repair_ratio (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1) (L : ℕ) :
    0 ≤ 1-q^(L+1) ∧ 1-q^(L+1) < 1 :=
  ⟨by linarith [pow_le_one₀ hq.le hq1 (n := L+1)], by linarith [pow_pos hq (L+1)]⟩

end RAFCriticalWindowQuantitative
