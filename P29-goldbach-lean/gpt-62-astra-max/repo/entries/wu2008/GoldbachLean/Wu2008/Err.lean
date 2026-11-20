module

public import GoldbachLean.Wu2008.Sum

/-!
# Specialization to Wu’s sequence

Every `N − p` in `wuA` is eligible. Convert `lemma22_sum` to a real inequality and use
`WuSieve.squareful_le` to bound its error term.
-/

@[expose] public section
namespace GoldbachLean.Wu2008.WuSum
open Finset WuReal WuSieve

variable (N : ℕ) (k1 k2 : ℝ)

/-- Wu's set `A = {N − p : p < N prime, p ∤ N}`. -/
def wuA := {p ∈ range N | p.Prime ∧ ¬ p ∣ N}.image (N - ·)

/-- Wu's conclusion for his sequence, including the two size hypotheses on `N`. -/
scoped notation "WuBound " N:arg k:arg l:arg =>
  1 < N → 1 < (N : ℝ) ^ k → weight[ℝ] (wuA N) N k l ≤ 4 * D12 (wuA N) + 4 * (N / ((N : ℝ) ^ k - 1))

/-- **(2.2) for Wu's own `A = {N − p}`, explicit error.** -/
theorem lemma22_wuA (hA : Admissible k1 k2) : WuBound N k1 k2 := by
  intro hN hNk
  have hAN : ∀ a ∈ wuA N, a eligibleFor N := by
    simp [wuA]
    grind [→ Nat.Prime.pos, Nat.coprime_self_sub_left, Nat.Prime.coprime_iff_not_dvd]
  have h := lemma22_sum _ _ _ _ hA hN hAN
  rify [Esq] at h
  linarith [squareful_le hNk hAN]

end GoldbachLean.Wu2008.WuSum
