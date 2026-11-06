module

/-
Upstream source and modification notice
Modified from OpenAI's matrix-multiplication sources to support arbitrary fields.
See UPSTREAM.md for provenance and changes; Apache-2.0 license retained in LICENSE.
-/

public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Algebra.Order.Group.Unbundled.Int
public import Lean.Elab.Tactic.Omega
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

public section

@[expose] section

namespace OAI

/-!
# Finite root-of-unity filters

Averaging the integer powers of a primitive root over one period detects
exactly the exponents divisible by that period. This is the finite Fourier
filter used for auxiliary separation.
-/

open scoped BigOperators Classical

namespace MatrixMultiplication.AuxiliarySeparation

variable {K : Type*} [Field K]

/-- Divisibility by a positive period is exact equality to zero inside one period. -/
lemma int_dvd_iff_eq_zero_of_abs_lt {L : ℕ} {e : ℤ} (he : |e| < (L : ℤ)) :
    (L : ℤ) ∣ e ↔ e = 0 := by
  constructor
  · intro hd
    apply abs_eq_zero.mp
    exact Int.eq_zero_of_dvd_of_nonneg_of_lt (abs_nonneg e) he
      ((dvd_abs (L : ℤ) e).mpr hd)
  · rintro rfl
    exact dvd_zero _

end MatrixMultiplication.AuxiliarySeparation

end OAI
