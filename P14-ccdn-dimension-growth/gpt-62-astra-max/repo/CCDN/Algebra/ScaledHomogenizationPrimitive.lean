/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.Equations
public import CCDN.Algebra.ScaledHomogenization
import Mathlib.Data.Nat.Prime.Int

/-! A prime scaling preserves primitive integer equations when it does not
divide the constant coefficient. This is the arithmetic input for affine scaling. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

variable {n : ℕ} {f : IntegerPolynomial n} (hf : PrimitiveIntegerPolynomial f) (d : ℕ)

include hf in
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
    simp_all [scaledHomogenize_coefficient]
  have hn : ¬ (l : ℤ) ∣ (p : ℤ) := by
    intro h
    have h'  := by exact_mod_cast h
    grind [Nat.prime_dvd_prime_iff_eq]
  have hcoeff : ∀ m, (l : ℤ) ∣ f.coeff m := by
    intro m
    have h := hld (homogenizedExponent d m)
    rw [scaledHomogenize_coefficient] at h
    rcases hlZ.dvd_or_dvd h with h | h
    grind [False.elim, hlZ.dvd_of_dvd_pow]
    · exact h
  exact hlZ.not_isUnit (hf l hcoeff)

include hf in
/-- The homogenization (with scaling factor `1`) of a primitive integer polynomial is
primitive. -/
lemma PrimitiveIntegerPolynomial.scaledHomogenize_one :
    PrimitiveIntegerPolynomial (CCDN.scaledHomogenize d 1 f) := by
  intro c hc
  apply hf c
  intro m
  simpa [scaledHomogenize_coefficient] using (hc (homogenizedExponent d m))

end
end CCDN
