module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.NFDecompPass

/-!
# Tree decomposition (WP-C), part 3: the shrinking of components and the number of rounds

A round cuts every component of `m ≥ 1` edges into components of at most
`hstep D m = (D - 1) m / D` edges (`exists_good`).  `rounds D K` is the least `i` with
`hstep D ^[i] K = 0`; it bounds the depth of the decomposition, and
`rounds_le : rounds D K ≤ D ⌈log₂ (K + 1)⌉` for `D ≥ 1` (`D` halvings after every `D` rounds).
-/

namespace Chazelle.Core.Dec

@[expose] public section

/-- The edge bound after one round: `(D - 1) m / D`. -/
def hstep (D m : ℕ) : ℕ := (D - 1) * m / D

theorem hstep_le (D m : ℕ) : hstep D m ≤ m := by
  unfold hstep
  rcases Nat.eq_zero_or_pos D with rfl | hD
  · simp
  · exact Nat.div_le_of_le_mul (Nat.mul_le_mul_right _ (Nat.sub_le _ _))

theorem hstep_lt (D m : ℕ) (hm : 1 ≤ m) : hstep D m < m := by
  unfold hstep
  rcases Nat.eq_zero_or_pos D with rfl | hD
  · simp; omega
  · apply Nat.div_lt_of_lt_mul
    simp_all +arith

theorem hstep_mono (D : ℕ) {a b : ℕ} (hab : a ≤ b) : hstep D a ≤ hstep D b :=
  Nat.div_le_div_right (Nat.mul_le_mul_left _ hab)


theorem hstep_iter_anti (D m : ℕ) {i j : ℕ} (hij : i ≤ j) : (hstep D)^[j] m ≤ (hstep D)^[i] m := by
  induction hij with
  | refl => exact le_rfl
  | step _ ih =>
    rw [Function.iterate_succ_apply']
    exact (hstep_le D _).trans ih

/-- `m' ≤ hstep D m` as soon as `D m' ≤ (D - 1) m`. -/
theorem le_hstep {D m m' : ℕ} (hD : 1 ≤ D) (h : D * m' ≤ (D - 1) * m) : m' ≤ hstep D m := by
  unfold hstep
  rw [Nat.le_div_iff_mul_le (by omega)]
  grind

section
variable (D K : ℕ)
include D K
theorem hstep_exists : ∃ i, (hstep D)^[i] K = 0 := by
  refine ⟨K, ?_⟩
  have : ∀ i, (hstep D)^[i] K + i ≤ K ∨ (hstep D)^[i] K = 0 := by
    intro i
    induction i with
    | zero => left; simp
    | succ i ih =>
      rw [Function.iterate_succ_apply']
      rcases ih with h1 | h1
      · by_cases h0 : (hstep D)^[i] K = 0
        · right; rw [h0]; exact Nat.le_zero.1 (hstep_le D 0)
        · left; have := hstep_lt D ((hstep D)^[i] K) (by omega); omega
      · right; rw [h1]; exact Nat.le_zero.1 (hstep_le D 0)
  grind

/-- The number of rounds: the least `i` with `hstep D ^[i] K = 0`. -/
noncomputable def rounds : ℕ := Nat.find (hstep_exists D K)



end

/-- A round index with a nonzero edge bound is below `rounds`. -/
theorem lt_rounds {D K i : ℕ} (h : 1 ≤ (hstep D)^[i] K) : i < rounds D K := by
  by_contra hle
  rw [not_lt] at hle
  have := hstep_iter_anti D K hle
  core_grind

section
variable {D : ℕ} (hD : 1 ≤ D)
include hD
/-- `D` rounds halve the edge bound. -/
theorem iter_D_half (m : ℕ) : 2 * (hstep D)^[D] m ≤ m := by
  have key : ∀ i, i ≤ D → 2 * (hstep D)^[i] m ≤ m ∨ 2 * D * (hstep D)^[i] m + i * m ≤ 2 * D * m := by
    intro i hi
    induction i with
    | zero => right; simp
    | succ i ih =>
      rw [Function.iterate_succ_apply']
      set x := (hstep D)^[i] m
      have hx : hstep D x ≤ x := hstep_le D x
      have hDx : D * hstep D x ≤ (D - 1) * x := by
        unfold hstep
        have := Nat.div_mul_le_self ((D - 1) * x) D
        grind
      rcases ih (by omega) with h1 | h1
      · left; omega
      · by_cases h2 : 2 * x ≤ m
        · left; omega
        · right
          have e1 : (D - 1) * x + x = D * x := by
            rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hD]
          nlinarith
  rcases key D le_rfl with h1 | h1
  · exact h1
  · nlinarith

/-- **The number of rounds**: at most `D ⌈log₂ (K + 1)⌉`. -/
theorem rounds_le (K : ℕ) : rounds D K ≤ D * Nat.clog 2 (K + 1) := by
  have key : ∀ c m, m + 1 ≤ 2 ^ c → (hstep D)^[D * c] m = 0 := by
    intro c
    induction c with
    | zero => simp_all
    | succ c ih =>
      intro m hm
      rw [Nat.mul_succ, Function.iterate_add_apply]
      have h1 := iter_D_half hD m
      grind
  exact Nat.find_min' _ (key _ K (Nat.le_pow_clog (by norm_num) _))


end

theorem rounds_zero (D : ℕ) : rounds D 0 = 0 :=
  Nat.le_zero.1 (Nat.find_min' _ (by simp))

end

end Chazelle.Core.Dec
