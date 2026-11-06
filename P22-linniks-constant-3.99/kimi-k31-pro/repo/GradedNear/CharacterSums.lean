module

public import GradedNear.Defs

@[expose] public section

open Complex

namespace GradedNear

/-- A non-principal character sums to zero over `q` consecutive integers. -/
lemma sum_range_char_eq_zero {q : ℕ} (hq : 0 < q) (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (c : ℕ) : ∑ k ∈ Finset.range q, χ ((c + k : ℕ) : ZMod q) = 0 := by
  have : NeZero q := ⟨hq.ne'⟩
  rw [← MulChar.sum_eq_zero_of_ne_one hχ]
  apply Finset.sum_nbij (fun k : ℕ => ((c + k : ℕ) : ZMod q))
  · intro k _; exact Finset.mem_univ _
  · intro k hk k' hk' h
    simp only [Finset.coe_range, Set.mem_Iio] at hk hk'
    simp only [Nat.cast_add, add_right_inj] at h
    rw [ZMod.natCast_eq_natCast_iff'] at h
    rwa [Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt hk'] at h
  · intro x _
    refine ⟨(x - (c : ZMod q)).val, ?_, ?_⟩
    · simp only [Finset.coe_range, Set.mem_Iio]; exact ZMod.val_lt _
    · simp only [Nat.cast_add, ZMod.natCast_zmod_val]; ring
  · intro k _; rfl

/-- A non-principal character sums to zero over a complete period `(N, N + q]`. -/
lemma sum_Ioc_period_eq_zero {q : ℕ} (hq : 0 < q) (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (N : ℕ) : ∑ n ∈ Finset.Ioc N (N + q), χ n = 0 := by
  rw [← Finset.Ico_add_one_add_one_eq_Ioc, Finset.sum_Ico_eq_sum_range]
  rw [show N + q + 1 - (N + 1) = q by omega]
  exact sum_range_char_eq_zero hq χ hχ (N + 1)

/-- A sum over the multiples of `l` in `(a, b]`, after the substitution `k = l m`. -/
lemma sum_Ioc_ite_dvd {M : Type*} [AddCommMonoid M] (f : ℕ → M) {l : ℕ} (hl : 0 < l)
    (a b : ℕ) :
    ∑ k ∈ Finset.Ioc a b, (if l ∣ k then f k else 0) =
      ∑ m ∈ Finset.Ioc (a / l) (b / l), f (l * m) := by
  classical
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_nbij (fun m => l * m) <;>
    simp_all [Finset.mem_Ioc, Nat.div_lt_iff_lt_mul hl, Nat.le_div_iff_mul_le hl,
      Nat.mul_comm]
  · intro m _ m' _ h
    exact Nat.eq_of_mul_eq_mul_left hl h
  · rintro k ⟨⟨h1, h2⟩, m, rfl⟩
    refine ⟨m, ?_, rfl⟩
    simp_all [Nat.div_lt_iff_lt_mul hl, Nat.le_div_iff_mul_le hl, Nat.mul_comm]

end GradedNear
