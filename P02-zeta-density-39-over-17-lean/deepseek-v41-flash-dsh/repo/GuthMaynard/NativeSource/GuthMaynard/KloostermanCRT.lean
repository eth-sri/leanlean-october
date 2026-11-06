module
public import GuthMaynard.NativeSource.GuthMaynard.QuadraticDivisor
public import Mathlib.Data.Int.GCD

@[expose] public section

/-!
# Chinese-remainder factorization of Kloosterman sums

This is the first recursive dependency of DFI equation (25).  It proves the
exact Bézout-scaled factorization of the standard additive character, moves
units and their inverses through the Chinese remainder equivalence, and then
factors the complete Kloosterman sum at coprime moduli.
-/

open Complex Classical
open scoped BigOperators

namespace GuthMaynard.NativeMoment

/-- CRT on the unit groups, including componentwise inversion. -/
noncomputable def kloostermanCRTUnits (m n : ℕ) (h : m.Coprime n) :
    (ZMod (m * n))ˣ ≃ (ZMod m)ˣ × (ZMod n)ˣ :=
  ((Units.mapEquiv (ZMod.chineseRemainder h).toMulEquiv).trans
    MulEquiv.prodUnits).toEquiv

@[simp]
theorem kloostermanCRTUnits_inv (m n : ℕ) (h : m.Coprime n)
    (d : (ZMod (m * n))ˣ) :
    kloostermanCRTUnits m n h d⁻¹ =
      ((kloostermanCRTUnits m n h d).1⁻¹,
        (kloostermanCRTUnits m n h d).2⁻¹) := rfl

end GuthMaynard.NativeMoment
