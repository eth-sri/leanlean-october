module

public import proofs.RAFCriticalWindowQuantitative.SmallOpenness
public import proofs.RAFReactionQuotient.Resolution

@[expose] public section

namespace RAFCriticalWindowQuantitative
open HordijkSteelThreshold RAFReactionQuotient unitInterval

theorem power_bound_intensity_flatness (S : I → ℝ) (C : ℕ → ℕ)
    (hbound : ∀ a r, S a ≤ (C r : ℝ)*(a : ℝ)^r) (d : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ lam : ℝ, ∀ hlam : 0 < lam, lam < δ →
      S (criticalOpenness lam hlam) < ε*lam^d := by
  let c : ℝ := C (d+1)
  have hc : 0 ≤ c := Nat.cast_nonneg _
  refine ⟨ε/(c+1), by positivity, fun lam hlam hlamδ => ?_⟩
  let a := criticalOpenness lam hlam
  have ha1 : 0 < (a : ℝ) := by
    change 0 < 1 - Real.exp (-lam)
    linarith [Real.exp_lt_one_iff.mpr (neg_neg_of_pos hlam)]
  have ha2 : (a : ℝ) ≤ lam := by
    change 1 - Real.exp (-lam) ≤ lam
    linarith [Real.add_one_le_exp (-lam)]
  have hx := (lt_div_iff₀ (show 0 < c+1 by positivity)).mp (ha2.trans_lt hlamδ)
  have hp := mul_lt_mul_of_pos_right (show c*(a : ℝ) < ε by nlinarith) (pow_pos ha1 d)
  have hb := hbound a (d+1)
  rw [pow_succ] at hb; dsimp [c] at hp
  exact (show S a < ε*(a : ℝ)^d by nlinarith).trans_le
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha1.le ha2 d) hε.le)

end RAFCriticalWindowQuantitative
