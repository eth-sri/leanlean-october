module

public import Mathlib.RingTheory.Ideal.Norm.AbsNorm

@[expose] public section

namespace Ideal

variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Module.Free ℤ R] [Module.Finite ℤ R]
  {I : Ideal R}
local instance : Infinite R := Module.Free.infinite ℤ R

/-- A nonzero ideal has positive absolute norm. -/
theorem absNorm_pos_of_ne_bot (hI : I ≠ ⊥) : 0 < absNorm I :=
  Nat.pos_of_ne_zero (absNorm_eq_zero_iff.not.mpr hI)

theorem one_le_absNorm_of_ne_bot (hI : I ≠ ⊥) : 1 ≤ absNorm I := absNorm_pos_of_ne_bot hI

theorem cast_absNorm_ne_zero_of_ne_bot {S : Type*} [AddMonoidWithOne S] [CharZero S]
    (hI : I ≠ ⊥) : (absNorm I : S) ≠ 0 :=
  Nat.cast_ne_zero.mpr (absNorm_pos_of_ne_bot hI).ne'

end Ideal
