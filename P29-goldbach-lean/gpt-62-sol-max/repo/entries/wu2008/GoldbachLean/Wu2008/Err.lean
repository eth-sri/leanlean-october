module

public import GoldbachLean.Wu2008.Sum

namespace GoldbachLean.Wu2008.WuSum
open Finset WuSieve WuReal

@[expose] public noncomputable section
open scoped Classical

/-- Wu's set `A = {N − p : p < N prime, p ∤ N}`. -/
def wuA (N : ℕ) := ((range N).filter (fun p => p.Prime ∧ ¬ p ∣ N)).image (fun p => N - p)

/-- The repaired inequality for `A = {N − p}`, with its explicit error term. -/
scoped notation "WuBound(" N "," k "," l ")" =>
  WuLHS(ℝ, wuA N, N, k, l) ≤ 4 * D12 (wuA N) + 4 * (N / ((N : ℝ) ^ k - 1))

theorem lemma22_wuA (N : ℕ) (k1 k2 : ℝ) (hA : Admissible k1 k2) (hN : 1 < N)
    (hNk : 1 < (N : ℝ) ^ k1) : WuBound(N, k1, k2) := by
  let A := wuA N
  have hAN : ∀ a ∈ A, 0 < a ∧ a < N ∧ a.Coprime N := by
    grind [wuA, → Nat.Prime.pos, Nat.Prime.coprime_iff_not_dvd, Nat.coprime_self_sub_left]
  have h := (Int.cast_le (R := ℝ)).mpr (lemma22_sum A N k1 k2 hA hN hAN)
  push_cast at h
  let z := (N : ℝ) ^ k1
  suffices (Esq A N k1 : ℝ) ≤ N / (z - 1) by linarith
  let M := ⌈z - 1⌉₊
  -- The upper endpoint covers q ≤ N and is at least M even if the error set is empty.
  let Q := Ioc M (M + N)
  let multiples (q : ℕ) := {a ∈ Ioc 0 N | q * q ∣ a}
  -- Cover each nonsquarefree sifted member by a multiple of some q².
  calc
    _ ≤ ↑(∑ q ∈ Q, #(multiples q)) := by
      norm_cast
      refine (card_le_card ?_).trans card_biUnion_le
      intro a
      simp [Q, multiples, M, Nat.squarefree_iff_prime_squarefree, not_forall]
      intro ha hs q hq hqq
      obtain ⟨ha0, haN, hcop⟩ := hAN a ha
      have hd := dvd_of_mul_left_dvd hqq
      have := Nat.le_of_dvd ha0 hd
      have : ⌈z⌉₊ ≤ q := Nat.ceil_le.mpr ((sifted_coprime ha0.ne' hcop).mp hs (hq.mem_primeFactors hd ha0.ne'))
      have := hq.pos
      exact ⟨q, by omega, ⟨⟨ha0, haN.le⟩, hqq⟩⟩
    _ ≤ N * ∑ q ∈ Q, ((q : ℝ) ^ 2)⁻¹ := by
      simp_rw [multiples, Nat.Ioc_filter_dvd_card_eq_div, Nat.cast_sum,
        mul_sum, ← div_eq_mul_inv, pow_two, ← Nat.cast_mul]
      exact sum_le_sum fun _ _ => Nat.cast_div_le
    _ ≤ _ := by
      have hp : 0 < z - 1 := sub_pos.mpr hNk
      grw [div_eq_mul_inv, sum_Ioc_inv_sq_le_sub (Nat.ceil_pos.mpr hp).ne' le_self_add,
        sub_le_self _ (by positivity), ← Nat.le_ceil (z - 1)]

end
end GoldbachLean.Wu2008.WuSum
