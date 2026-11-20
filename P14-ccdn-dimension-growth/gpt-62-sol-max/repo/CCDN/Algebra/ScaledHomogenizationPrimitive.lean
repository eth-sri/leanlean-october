/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.HomogeneousChart
import Mathlib.Data.Nat.Prime.Int

/-! A prime scaling preserves primitive integer equations when it does not
divide the constant coefficient. This is the arithmetic input for affine scaling. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

section

variable {n : ℕ} {f : MvPolynomial (Fin n) ℤ}
  (hf : PrimitiveIntegerPolynomial f) (d : ℕ)
include n f hf d

/-- If `f` is a primitive integer polynomial and the prime `p` does not divide its constant
coefficient, then the scaled homogenization `scaledHomogenize d p f` is primitive. -/
theorem PrimitiveIntegerPolynomial.scaledHomogenize {p : ℕ} (hp : p.Prime)
    (hp0 : ¬ (p : ℤ) ∣ f.coeff 0) :
    PrimitiveIntegerPolynomial (CCDN.scaledHomogenize d (p : ℤ) f) := by
  intro c hc
  apply Int.isUnit_iff_natAbs_eq.mpr
  by_contra hunit
  obtain ⟨l, hl, hlc⟩ := Nat.exists_prime_and_dvd hunit
  have hlZ := Nat.prime_iff_prime_int.mp hl
  have hld :=
    fun m => (Int.natCast_dvd.mpr hlc).trans (hc m)
  have hlp : l ≠ p := by
    intro he
    subst l
    have h := hld (homogenizedExponent d 0)
    rw [scaledHomogenize_coefficient] at h
    simp_all
  have hn : ¬ (l : ℤ) ∣ (p : ℤ) := by
    intro h
    exact hlp ((Nat.prime_dvd_prime_iff_eq hl hp).mp (by exact_mod_cast h))
  have hcoeff : ∀ m, (l : ℤ) ∣ f.coeff m := by
    intro m
    have h := hld (homogenizedExponent d m)
    rw [scaledHomogenize_coefficient] at h
    rcases hlZ.dvd_or_dvd h with h | h
    · exact False.elim (hn (hlZ.dvd_of_dvd_pow h))
    · exact h
  exact hlZ.not_isUnit (hf l hcoeff)

/-- The homogenization (with scaling factor `1`) of a primitive integer polynomial is
primitive. -/
lemma PrimitiveIntegerPolynomial.scaledHomogenize_one :
    PrimitiveIntegerPolynomial (CCDN.scaledHomogenize d 1 f) := by
  intro c hc
  apply hf c
  intro m
  have h := hc (homogenizedExponent d m)
  simpa only [scaledHomogenize_coefficient, one_pow, one_mul] using h

end

end
end CCDN
