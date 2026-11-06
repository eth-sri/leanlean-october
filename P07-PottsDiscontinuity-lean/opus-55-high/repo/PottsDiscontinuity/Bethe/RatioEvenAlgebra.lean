module

public import PottsDiscontinuity.Bethe.RatioProducts

/-! # The exact finite even-ratio factorization (3.7) -/

public section

open Finset
open scoped BigOperators

namespace PottsDiscontinuity.Bethe

open BetheAnsatz

theorem ratio_modulus_reflection {m : ℕ} {p : Fin m → ℝ}
    (hp : p ∈ S_n m) (c : ℝ) (j : Fin m) :
    ‖M c (z (p (Fin.rev j)))‖ = ‖M c (z (p j))‖ := by
  rw [show p (Fin.rev j) = -p j from hp.2.2 j, ratio_M_neg, Complex.norm_conj]

/-- Split an even symmetric deletion into a central block and equal tails. -/
theorem ratio_product_symmetric_split {m n s : ℕ} (hcount : s + n + s = m)
    (f : Fin m → ℝ) (hsym : ∀ j, f (Fin.rev j) = f j) :
    (∏ j, f j) = (∏ j : Fin n, f ⟨j.val + s, by omega⟩) *
      (∏ j : Fin s, f ⟨j.val, by omega⟩) ^ 2 := by
  subst m
  have hR : (∏ j : Fin s, f ⟨s + n + j.val, by omega⟩) =
      ∏ j : Fin s, f ⟨j.val, by omega⟩ := by
    calc
      _ = ∏ j : Fin s, f ⟨(Fin.rev j).val, by omega⟩ := by
        grind
      _ = _ := Equiv.prod_comp (Fin.revPerm : Equiv.Perm (Fin s))
        (fun j => f ⟨j.val, by omega⟩)
  have hprod : (∏ j, f j) = (∏ j : Fin s, f ⟨j.val, by omega⟩) *
      (∏ j : Fin n, f ⟨s + j.val, by omega⟩) *
      ∏ j : Fin s, f ⟨s + n + j.val, by omega⟩ := by
    rw [Fin.prod_univ_add, Fin.prod_univ_add]
    rfl
  grind

/-- A regular-branch quotient before the symmetric block decomposition. -/
theorem ratio_regular_quotient {m n : ℕ} {p : Fin m → ℝ} {q : Fin n → ℝ}
    {c : ℝ} (hc : 2 < c) (hp : p ∈ S_n m) (hq : q ∈ S_n n) :
    eigenvalueRegular c q / eigenvalueRegular c p =
      (((∏ j, ‖M c (z (q j))‖) / ∏ j, ‖M c (z (p j))‖ : ℝ) : ℂ) := by
  rw [ratio_eigenvalueRegular hc hq, ratio_eigenvalueRegular hc hp]
  push_cast
  ring

/-- Exact source equation (3.7), expressed with the half-deficit s. -/
theorem ratio_even_quotient_split {m n s : ℕ} (hcount : s + n + s = m)
    {p : Fin m → ℝ} {q : Fin n → ℝ} {c : ℝ} (hc : 2 < c)
    (hp : p ∈ S_n m) (hq : q ∈ S_n n) :
    eigenvalueRegular c q / eigenvalueRegular c p =
      (((∏ j : Fin n, ‖M c (z (q j))‖ / ‖M c (z (p ⟨j.val + s, by omega⟩))‖) *
        ((∏ j : Fin s, ‖M c (z (p ⟨j.val, by omega⟩))‖) ^ 2)⁻¹ : ℝ) : ℂ) := by
  rw [ratio_regular_quotient hc hp hq]
  congr 1
  rw [ratio_product_symmetric_split hcount (fun j => ‖M c (z (p j))‖)
    (ratio_modulus_reflection hp c), prod_div_distrib]
  ring

end PottsDiscontinuity.Bethe
