import GradedNear.Tactics
import GradedNear.Defs

/-! # Complete character sums and extension of interval bounds -/

namespace GradedNear


/-- Burgess's bound for intervals of any length: split off complete periods, on which the
character sums to zero, and apply the bound for `H ≤ q` to the remainder. -/
lemma burgess_any_length {q : ℕ} (hq : 0 < q) (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ N H : ℕ, 1 ≤ H → H ≤ q →
      ‖charSum χ N H‖ ≤ K * ↑H ^ ⅔) :
    ∀ N H : ℕ, ‖charSum χ N H‖ ≤ K * ↑H ^ ⅔ := by
  have period_zero (N : ℕ) : charSum χ N q = 0 := by
    cases q with
    | zero => omega
    | succ q =>
      rw [← Finset.Ico_add_one_add_one_eq_Ioc, Finset.sum_Ico_eq_sum_range]
      rw [show N + (q + 1) + 1 - (N + 1) = q + 1 by omega, ← Fin.sum_univ_eq_sum_range]
      simp
      change ∑ x : ZMod (q + 1), χ ((N : ZMod (q + 1)) + 1 + x.val) = 0
      simp
      exact (Equiv.sum_comp (Equiv.addLeft ((N : ZMod (q + 1)) + 1)) χ).trans
        (MulChar.sum_eq_zero_of_ne_one hχ)
  intro N H
  induction H using Nat.strong_induction_on generalizing N with
  | _ H ih =>
    rcases Nat.eq_zero_or_pos H with rfl | hH
    · simp
    by_cases hHq : H ≤ q
    · bound
    ·
      have hsplit : charSum χ N H =
          charSum χ N q +
            charSum χ (N + q) (H - q) := by
        grind [Finset.sum_Ioc_consecutive]
      rw [hsplit, period_zero, zero_add]
      calc _ ≤ K * ((H - q : ℕ) : ℝ) ^ ⅔ := ih (H - q) (by omega) (N + q)
        _ ≤ K * ↑H ^ ⅔ := by
          bound

/-- A sum over the multiples of `l` in `(a, b]`, after the substitution `k = l m`. -/
lemma sum_Ioc_ite_dvd {M : Type*} [AddCommMonoid M] (f : ℕ → M) {l : ℕ} (hl : 0 < l)
    (a b : ℕ) :
    ∑ k ∈ Finset.Ioc a b, (if l ∣ k then f k else 0) =
      ∑ m ∈ Finset.Ioc (a / l) (b / l), f (l * m) := by
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_nbij (l * ·)
  · simp_all [Finset.mem_Ioc, Finset.mem_filter, Nat.div_lt_iff_lt_mul, Nat.le_div_iff_mul_le, Nat.mul_comm]
  · intro m _ m' _ h
    nlinarith
  · intro k hk
    obtain ⟨hk, ⟨m, rfl⟩⟩ := Finset.mem_filter.1 hk

    grind [Nat.div_lt_iff_lt_mul, Nat.le_div_iff_mul_le]
  simp_all

end GradedNear
