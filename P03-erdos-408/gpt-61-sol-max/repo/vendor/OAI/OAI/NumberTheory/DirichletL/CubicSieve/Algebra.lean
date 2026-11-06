module

public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum

@[expose] public section

namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical


theorem square_eq_star_of_fourth_eq (z : ℂ) (hz : z ^ 4 = z) : z ^ 2 = star z := by
  by_cases h0 : z = 0
  · simp [h0]
  have h3 : z ^ 3 = 1 := by
    grind
  have hn := Complex.norm_eq_one_of_pow_eq_one h3 (by decide : (3 : ℕ) ≠ 0)
  change z ^ 2 = (starRingEnd ℂ) z
  rw [← Complex.inv_eq_conj hn]
  grind

variable {R : Type*} [CommRing R] [Finite Rˣ]

omit [Finite Rˣ] in
theorem cubic_fourth_eq (χ : MulChar R ℂ) (hχ : χ ^ 3 = 1)  x  :
    χ x ^ 4 = χ x := by
  have h : χ ^ 4 = χ := by
    rw [show (4 : ℕ) = 3 + 1 by decide, pow_add, hχ, one_mul, pow_one]
  rw [← MulChar.pow_apply' χ (by decide : (4 : ℕ) ≠ 0), h]

omit [Finite Rˣ] in
theorem cubic_cube_eq_mask (χ : MulChar R ℂ) (hχ : χ ^ 3 = 1)  x  :
    χ (x ^ 3) = if IsUnit x then 1 else 0 := by
  classical
  rw [map_pow, ← MulChar.pow_apply' χ (by decide : (3 : ℕ) ≠ 0), hχ]
  rfl


end SevenEighths.CubicSieve

end OAI
