module

public import PottsDiscontinuity.Bethe.AsymptoticOffset

/-! # Bulk and boundary sums for the offset expansion -/

@[expose] public section

open scoped BigOperators

namespace PottsDiscontinuity.Bethe

theorem sum_fin_three_blocks (a n b : ℕ) (f : Fin (a + n + b) → ℝ) :
    (∑ j, f j) = (∑ j : Fin a, f ⟨j.val, by omega⟩) +
      (∑ j : Fin n, f ⟨a + j.val, by omega⟩) +
      ∑ j : Fin b, f ⟨a + n + j.val, by omega⟩ := by
  rw [Fin.sum_univ_add, Fin.sum_univ_add]
  rfl

theorem sum_fin_split_block {m a n b : ℕ} (hcount : a + n + b = m)
    (f : Fin m → ℝ) :
    (∑ j, f j) = (∑ j : Fin n, f ⟨j.val + a, by omega⟩) +
      (∑ j : Fin a, f ⟨j.val, by omega⟩) +
      ∑ j : Fin b, f ⟨a + n + j.val, by omega⟩ := by
  subst m
  have h := sum_fin_three_blocks a n b f
  grind

/-- Both parity clauses are means of the floor and ceiling shifts. For even
`r` the two roots coincide; for odd `r` they are consecutive. -/
theorem alignedRoot_average {N r : ℕ} (hr : r ≤ N / 2)
    (p : Fin (N / 2) → ℝ) (j : Fin (N / 2 - r)) :
    alignedRoot hr p j =
      (p ⟨j.val + r / 2, by omega⟩ + p ⟨j.val + (r - r / 2), by omega⟩) / 2 := by
  unfold alignedRoot
  grind

theorem offsetDisplacement_bethe_average {Δ : ℝ} {N r : ℕ} (h4 : 4 ∣ N)
    (hr : r ≤ N / 2) {p : Fin (N / 2) → ℝ} {q : Fin (N / 2 - r) → ℝ}
    (hp : DiscreteBetheEquation Δ N (N / 2) p)
    (hq : DiscreteBetheEquation Δ N (N / 2 - r) q) (j : Fin (N / 2 - r)) :
    offsetDisplacement (N := N) (r := r) h4 hr p q j =
      ((∑ k, theta Δ (p ⟨j.val + r / 2, by omega⟩) (p k)) +
        ∑ k, theta Δ (p ⟨j.val + (r - r / 2), by omega⟩) (p k)) / 2 -
        ∑ k, theta Δ (q j) (q k) := by
  have hp₀ := hp ⟨j.val + r / 2, by omega⟩
  have hp₁ := hp ⟨j.val + (r - r / 2), by omega⟩
  have hqj := hq j
  have hi : (discreteBetheIndex (n := (N / 2)) ⟨j.val + r / 2, by omega⟩ +
      discreteBetheIndex (n := (N / 2)) ⟨j.val + (r - r / 2), by omega⟩) / 2 =
      discreteBetheIndex (n := (N / 2 - r)) j := by
    have hr' : (r : ℝ) = ((r / 2 : ℕ) : ℝ) + ((r - r / 2 : ℕ) : ℝ) := by
      exact_mod_cast (show r = r / 2 + (r - r / 2) by omega)
    simp only [discreteBetheIndex, Nat.cast_add, Nat.cast_sub hr]
    linarith
  grind [offsetDisplacement_eq_alignedRoot, alignedRoot_average hr]

end PottsDiscontinuity.Bethe
