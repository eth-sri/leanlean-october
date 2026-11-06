module

public import Mathlib

public import ClassFieldTheory.LubinTate.EqualCharacteristic.FormalModule.AmbientBracketAction

@[expose] public section


/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/



set_option autoImplicit false

/-!
# Ambient Lubin--Tate division groups

The kernel of the `n`-fold distinguished endomorphism in any ambient field is
stable under all truncated brackets.  Units of `κ⟦T⟧` therefore act on it by
actual additive automorphisms.  This is the version needed in the separable
closure, where the nonzero division points live.
-/

noncomputable section

open scoped PowerSeries LaurentSeries

universe u v w

namespace LubinTate
namespace EqualCharacteristic

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

section
variable (F : LocalField.{u, v} K)
    {A : Type w} [Field A] [CharP A F.residueCharacteristic]
include F A
/-- The level-`n` division group inside an ambient field. -/
noncomputable def equalCharacteristicLubinTateAmbientTorsionAddSubgroup
     
    (t : A) (n : ℕ)  :=
  (equalCharacteristicLubinTateAmbientPiIterate F t n).ker











/-- Every iterate of `e` commutes with every ambient bracket. -/
theorem equalCharacteristicLubinTateAmbientPiIterate_bracket
     
    (ι : F.residueField →+* A) (t : A)
    (i n : ℕ) (a : F.residueField⟦X⟧) (x : A) :
    equalCharacteristicLubinTateAmbientPiIterate F t i
        (equalCharacteristicLubinTateAmbientBracket F ι t n a x) =
      equalCharacteristicLubinTateAmbientBracket F ι t n a
        (equalCharacteristicLubinTateAmbientPiIterate F t i x) := by
  induction i generalizing x with
  | zero =>
      simp [equalCharacteristicLubinTateAmbientPiIterate_zero]
  | succ i ih =>
      rw [equalCharacteristicLubinTateAmbientPiIterate_succ,
        equalCharacteristicLubinTateAmbientPiEnd_bracket, ih,
        equalCharacteristicLubinTateAmbientPiIterate_succ]
end


section
variable (F : LocalField.{u, v} K)
    {A : Type w} [Field A] [CharP A F.residueCharacteristic]
    (ι : F.residueField →+* A) (t : A)
    (n : ℕ)
include F A ι t n
/-- Every bracket preserves the ambient division group. -/
theorem equalCharacteristicLubinTateAmbientBracket_torsion
      (a : F.residueField⟦X⟧) (x : A)
    (hx : IsEqualCharacteristicLubinTateAmbientTorsion F t n x) :
    IsEqualCharacteristicLubinTateAmbientTorsion F t n
      (equalCharacteristicLubinTateAmbientBracket F ι t n a x) := by
  rw [IsEqualCharacteristicLubinTateAmbientTorsion,
    equalCharacteristicLubinTateAmbientPiIterate_bracket,
    hx, map_zero]

/-- The endomorphism of the ambient level-`n` division group induced by a
bracket. -/
noncomputable def equalCharacteristicLubinTateAmbientTorsionEnd
      (a : F.residueField⟦X⟧) :
    AddMonoid.End
      (equalCharacteristicLubinTateAmbientTorsionAddSubgroup F t n) where
  toFun x :=
    ⟨equalCharacteristicLubinTateAmbientBracket F ι t n a x.1,
      equalCharacteristicLubinTateAmbientBracket_torsion
        F ι t n a x.1 x.2⟩
  map_zero' := by
    apply Subtype.ext
    exact (equalCharacteristicLubinTateAmbientBracket F ι t n a).map_zero
  map_add' x y := by
    apply Subtype.ext
    exact (equalCharacteristicLubinTateAmbientBracket F ι t n a).map_add
      x.1 y.1

/-- States the theorem `equalCharacteristicLubinTateAmbientTorsionEnd_apply`. -/
@[simp]
theorem equalCharacteristicLubinTateAmbientTorsionEnd_apply
      (a : F.residueField⟦X⟧)
    (x : equalCharacteristicLubinTateAmbientTorsionAddSubgroup F t n) :
    (equalCharacteristicLubinTateAmbientTorsionEnd F ι t n a x).1 =
      equalCharacteristicLubinTateAmbientBracket F ι t n a x.1 :=
  rfl

/-- The bracket of `1` fixes all ambient division points, also at level
zero. -/
theorem equalCharacteristicLubinTateAmbientBracket_one_apply_of_torsion
      (x : A)
    (hx : IsEqualCharacteristicLubinTateAmbientTorsion F t n x) :
    equalCharacteristicLubinTateAmbientBracket F ι t n 1 x = x := by
  cases n with
  | zero =>
      simp_all [LubinTate.EqualCharacteristic.IsEqualCharacteristicLubinTateAmbientTorsion, LubinTate.EqualCharacteristic.equalCharacteristicLubinTateAmbientPiIterate_zero] <;> aesop
  | succ n =>
      have h := congrArg (fun f : AddMonoid.End A ↦ f x)
        (equalCharacteristicLubinTateAmbientBracket_C F ι t n 1)
      simpa [equalCharacteristicLubinTateAmbientCoefficientEnd_apply] using h

/-- A unit power series acts by an automorphism of every ambient division
group. -/
noncomputable def equalCharacteristicLubinTateAmbientTorsionUnitAut
      (a : F.residueField⟦X⟧ˣ) :
    AddEquiv
      (equalCharacteristicLubinTateAmbientTorsionAddSubgroup F t n)
      (equalCharacteristicLubinTateAmbientTorsionAddSubgroup F t n) where
  toFun := equalCharacteristicLubinTateAmbientTorsionEnd F ι t n
    a
  invFun := equalCharacteristicLubinTateAmbientTorsionEnd F ι t n
    (↑(a⁻¹))
  left_inv x := by
    apply Subtype.ext
    change equalCharacteristicLubinTateAmbientBracket F ι t n
      (↑(a⁻¹))
        (equalCharacteristicLubinTateAmbientBracket F ι t n
          a x.1) = x.1
    rw [← equalCharacteristicLubinTateAmbientBracket_mul_apply_of_torsion
      F ι t n (↑(a⁻¹))
        a x.1 x.2]
    simpa using
      equalCharacteristicLubinTateAmbientBracket_one_apply_of_torsion
        F ι t n x.1 x.2
  right_inv x := by
    apply Subtype.ext
    change equalCharacteristicLubinTateAmbientBracket F ι t n
      a
        (equalCharacteristicLubinTateAmbientBracket F ι t n
          (↑(a⁻¹)) x.1) = x.1
    rw [← equalCharacteristicLubinTateAmbientBracket_mul_apply_of_torsion
      F ι t n a
        (↑(a⁻¹)) x.1 x.2]
    simpa using
      equalCharacteristicLubinTateAmbientBracket_one_apply_of_torsion
        F ι t n x.1 x.2
  map_add' x y :=
    (equalCharacteristicLubinTateAmbientTorsionEnd F ι t n
      (a : F.residueField⟦X⟧)).map_add x y

/-- States the theorem `equalCharacteristicLubinTateAmbientTorsionUnitAut_apply`. -/
@[simp]
theorem equalCharacteristicLubinTateAmbientTorsionUnitAut_apply
      (a : F.residueField⟦X⟧ˣ)
    (x : equalCharacteristicLubinTateAmbientTorsionAddSubgroup F t n) :
    (equalCharacteristicLubinTateAmbientTorsionUnitAut F ι t n a x).1 =
      equalCharacteristicLubinTateAmbientBracket F ι t n
        a x.1 :=
  rfl

/-- Equality of the first `n` coefficients makes two ambient brackets
equal. -/
theorem equalCharacteristicLubinTateAmbientBracket_eq_of_coeff_eq
      (a b : F.residueField⟦X⟧)
    (hab : ∀ i < n, PowerSeries.coeff i a = PowerSeries.coeff i b) :
    equalCharacteristicLubinTateAmbientBracket F ι t n a =
      equalCharacteristicLubinTateAmbientBracket F ι t n b := by
  apply AddMonoidHom.ext
  intro x
  change
    equalCharacteristicLubinTateAmbientBracket F ι t n a x =
      equalCharacteristicLubinTateAmbientBracket F ι t n b x
  rw [equalCharacteristicLubinTateAmbientBracket_apply,
    equalCharacteristicLubinTateAmbientBracket_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hab i (Finset.mem_range.mp hi)]
end


end EqualCharacteristic
end LubinTate

end
