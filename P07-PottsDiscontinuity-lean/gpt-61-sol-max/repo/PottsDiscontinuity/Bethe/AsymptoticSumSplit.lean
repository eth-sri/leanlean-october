module
public import Mathlib

public import PottsDiscontinuity.Bethe.AsymptoticOffset

/-! # Bulk and boundary sums for the offset expansion -/

@[expose] public section



namespace PottsDiscontinuity.Bethe

theorem sum_fin_three_blocks (a n b : ℕ) (f : Fin (a + n + b) → ℝ) :
     ∑ j, f j  =  ∑ j : Fin a, f ⟨j.val, by omega⟩  +
       ∑ j : Fin n, f ⟨a + j.val, by omega⟩  +
      ∑ j : Fin b, f ⟨a + n + j.val, by omega⟩ := by
  rw [Fin.sum_univ_add, Fin.sum_univ_add]
  rfl

theorem sum_fin_split_block {m a n b : ℕ} (hcount : a + n + b = m)
    (f : Fin m → ℝ) :
     ∑ j, f j  =  ∑ j : Fin n, f ⟨j.val + a, by omega⟩  +
       ∑ j : Fin a, f ⟨j.val, by omega⟩  +
      ∑ j : Fin b, f ⟨a + n + j.val, by omega⟩ := by
  subst m
  have h := sum_fin_three_blocks a n b f
  grind

/-- Both parity clauses are means of the floor and ceiling shifts. For even
`r` the two roots coincide; for odd `r` they are consecutive. -/
theorem alignedRoot_average {N r : ℕ} (hr : r ≤ N / 2)
    (p : Fin (N / 2) → ℝ) (j : Fin (N / 2 - r)) :
    alignedRoot N r hr p j =
      (p ⟨j.val + r / 2, by omega⟩ + p ⟨j.val + (r - r / 2), by omega⟩) / 2 := by
  grind [alignedRoot]

theorem offsetDisplacement_bethe_average {Δ : ℝ} {N r : ℕ} (h4 : 4 ∣ N)
    (hr : r ≤ N / 2) {p : Fin (N / 2) → ℝ} {q : Fin (N / 2 - r) → ℝ}
    (hp : DiscreteBetheEquation Δ N (N / 2) p)
    (hq : DiscreteBetheEquation Δ N (N / 2 - r) q) (j : Fin (N / 2 - r)) :
    offsetDisplacement N r h4 hr p q j =
      ( ∑ k, theta Δ (p ⟨j.val + r / 2, by omega⟩) (p k)  +
        ∑ k, theta Δ (p ⟨j.val + (r - r / 2), by omega⟩) (p k)) / 2 -
        ∑ k, theta Δ (q j) (q k) := by
  
  
  
  have hi : (discreteBetheIndex (N / 2) ⟨j.val + r / 2, by omega⟩ +
      discreteBetheIndex (N / 2) ⟨j.val + (r - r / 2), by omega⟩) / 2 =
      discreteBetheIndex (N / 2 - r) j := by
    have hr' :  r  =  (r / 2 : ℕ)  + ((r - r / 2 : ℕ) : ℝ) := by
      exact_mod_cast  show r = r / 2 + (r - r / 2) by omega 
    simp only [discreteBetheIndex, Nat.cast_add, Nat.cast_sub hr]
    linarith
  have hi' := congrArg (fun z  => 2 * Real.pi * z) hi
  rw [offsetDisplacement_eq_alignedRoot, alignedRoot_average hr]
  nlinarith only [ hp ⟨j.val + r / 2, by omega⟩ ,  hp ⟨j.val + (r - r / 2), by omega⟩ ,  hq j , hi']

end PottsDiscontinuity.Bethe
