module

public import ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.ResidueRoots
public import Mathlib.Algebra.CharP.Lemmas

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

namespace LocalFieldTheory

open ValuationTheory
open ValuationTheory.DiscreteValuationField.ResidueField

/-!
# Teichmuller lifts

Constructs multiplicative Teichmuller representatives, and in equal characteristic the
coefficient-field section of the residue map.
-/

noncomputable section

open scoped BigOperators

universe u v

namespace DiscreteValuationField
namespace CompleteDVF

variable {K : Type u} [Field K]

namespace higherPrincipalUnitGroup

variable (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K)

section

variable [Finite F.residueField]

/-- The Teichmuller representative lift from the finite residue field to the
valuation ring: `0` lifts to `0`, and nonzero residue classes lift through the
root-of-unity splitting of `κˣ`. -/
noncomputable def residueTeichmullerLift :
    F.residueField → F.valuationSubring :=
  fun y =>
    letI := Classical.decEq F.residueField
    if hy : y = 0 then
      0
    else
      (((higherPrincipalUnitGroup.residueRootsOfUnityEquivResidueFieldUnits F).symm
          (Units.mk0 y hy) :
        higherPrincipalUnitGroup.residueRootsOfUnityGroup F) :
        F.valuationSubringˣ)

/-- Establishes the identity `higherPrincipalUnitGroup.residueTeichmullerLift F 0 = 0`. -/
@[simp] theorem residueTeichmullerLift_zero :
    higherPrincipalUnitGroup.residueTeichmullerLift F 0 = 0 := by
  simp [higherPrincipalUnitGroup.residueTeichmullerLift]

/-- Establishes the identity `higherPrincipalUnitGroup.residueTeichmullerLift F 1 = 1`. -/
@[simp] theorem residueTeichmullerLift_one :
    higherPrincipalUnitGroup.residueTeichmullerLift F 1 = 1 := by
  simp [higherPrincipalUnitGroup.residueTeichmullerLift]

/-- The Teichmuller lift reduces to the residue class it lifts. -/
theorem residueMap_residueTeichmullerLift
    (y : F.residueField) :
    F.residueMap (higherPrincipalUnitGroup.residueTeichmullerLift F y) = y := by
  classical
  by_cases hy : y = 0
  · simp [higherPrincipalUnitGroup.residueTeichmullerLift, hy]
  · let e :=
      higherPrincipalUnitGroup.residueRootsOfUnityEquivResidueFieldUnits F
    have hroot :
        higherPrincipalUnitGroup.residueUnitHom F
            (((e.symm (Units.mk0 y hy) :
              higherPrincipalUnitGroup.residueRootsOfUnityGroup F) :
              F.valuationSubringˣ)) =
          Units.mk0 y hy := by
      change e (e.symm (Units.mk0 y hy)) = Units.mk0 y hy
      simp
    simpa [higherPrincipalUnitGroup.residueTeichmullerLift, hy, e, higherPrincipalUnitGroup.residueUnitHom] using congrArg (fun u : F.residueFieldˣ => (u : F.residueField)) hroot

/-- The Teichmuller lift is multiplicative. -/
theorem residueTeichmullerLift_mul
    (x y : F.residueField) :
    higherPrincipalUnitGroup.residueTeichmullerLift F (x * y) =
      higherPrincipalUnitGroup.residueTeichmullerLift F x *
        higherPrincipalUnitGroup.residueTeichmullerLift F y := by
  classical
  by_cases hx : x = 0
  · simp [higherPrincipalUnitGroup.residueTeichmullerLift, hx]
  by_cases hy : y = 0
  · simp [higherPrincipalUnitGroup.residueTeichmullerLift, hy]
  simp_all [higherPrincipalUnitGroup.residueTeichmullerLift]

/-- Every Teichmuller representative is a root of `T^q - T`, where
`q = #κ`. -/
theorem residueTeichmullerLift_pow_card
    (y : F.residueField) :
    higherPrincipalUnitGroup.residueTeichmullerLift F y ^
        Nat.card F.residueField =
      higherPrincipalUnitGroup.residueTeichmullerLift F y := by
  classical
  let := Fintype.ofFinite F.residueField
  have hcard_pos : 0 < Nat.card F.residueField := by
    simpa [Nat.card_eq_fintype_card] using
      Fintype.card_pos
  by_cases hy : y = 0
  · simp [higherPrincipalUnitGroup.residueTeichmullerLift, hy]
  · let u :=
      (higherPrincipalUnitGroup.residueRootsOfUnityEquivResidueFieldUnits F).symm
        (Units.mk0 y hy)
    have hpowRing :
        ((u : F.valuationSubringˣ) : F.valuationSubring) ^
            (Nat.card F.residueField - 1) = 1 := by
      simpa using
        congrArg (fun z : F.valuationSubringˣ => (z : F.valuationSubring))
          u.property
    have hpow :
        ((u : F.valuationSubringˣ) : F.valuationSubring) ^
            Nat.card F.residueField =
          ((u : F.valuationSubringˣ) : F.valuationSubring) := by
      calc
        _ =
            ((u : F.valuationSubringˣ) : F.valuationSubring) ^
              ((Nat.card F.residueField - 1) + 1) := by
              rw [Nat.sub_one_add_one_eq_of_pos hcard_pos]
        _ =
            ((u : F.valuationSubringˣ) : F.valuationSubring) ^
              (Nat.card F.residueField - 1) *
            ((u : F.valuationSubringˣ) : F.valuationSubring) := by
              rw [pow_succ]
        _ = ((u : F.valuationSubringˣ) : F.valuationSubring) := by
              rw [hpowRing, one_mul]
    simpa [higherPrincipalUnitGroup.residueTeichmullerLift, hy, u] using hpow

/--
Every residue Teichmüller lift is a root of the polynomial `X^q - X`, where `q` is the
residue-field cardinality.
-/
theorem residueTeichmullerLift_isRoot_X_pow_card_sub_X (y : F.residueField) :
    (Polynomial.X ^ Nat.card F.residueField - Polynomial.X :
        Polynomial F.valuationSubring).IsRoot
      (higherPrincipalUnitGroup.residueTeichmullerLift F y) := by
  simp [Polynomial.eval_sub,
    higherPrincipalUnitGroup.residueTeichmullerLift_pow_card]

end

variable [Finite F.residueField] (p : ℕ) [Fact p.Prime] [CharP F.valuationSubring p] {n : ℕ+}
    (hcard : Nat.card F.residueField = p ^ (n : ℕ))

include hcard in
/-- In equal characteristic, `T^q - T` has unit derivative at every
Teichmuller representative. -/
theorem residueTeichmullerRootPolynomial_derivative_eval_isUnit_of_charP
    (y : F.residueField) :
    IsUnit
      (((Polynomial.X ^ Nat.card F.residueField - Polynomial.X :
          Polynomial F.valuationSubring).derivative).eval
        (higherPrincipalUnitGroup.residueTeichmullerLift F y)) := by
  have hderiv :
      ((Polynomial.X ^ Nat.card F.residueField - Polynomial.X :
          Polynomial F.valuationSubring).derivative).eval
        (higherPrincipalUnitGroup.residueTeichmullerLift F y) = -1 := by
    simp [Polynomial.derivative_sub, Polynomial.derivative_X_pow,
      Polynomial.derivative_X, ((CharP.cast_eq_zero_iff F.valuationSubring p
        (Nat.card F.residueField)).2 (by
          simp [hcard]))]
  rw [hderiv]
  exact isUnit_neg_one

include hcard in
/-- In equal characteristic, the Teichmuller lift from the finite residue field
to the valuation ring is additive. -/
theorem residueTeichmullerLift_add_of_charP
    (x y : F.residueField) :
    higherPrincipalUnitGroup.residueTeichmullerLift F (x + y) =
      higherPrincipalUnitGroup.residueTeichmullerLift F x +
        higherPrincipalUnitGroup.residueTeichmullerLift F y := by
  let f : Polynomial F.valuationSubring :=
    Polynomial.X ^ Nat.card F.residueField - Polynomial.X
  let a : F.valuationSubring :=
    higherPrincipalUnitGroup.residueTeichmullerLift F (x + y)
  let b : F.valuationSubring :=
    higherPrincipalUnitGroup.residueTeichmullerLift F x +
      higherPrincipalUnitGroup.residueTeichmullerLift F y
  have ha : f.IsRoot a := by
    simpa [f, a] using
      higherPrincipalUnitGroup.residueTeichmullerLift_isRoot_X_pow_card_sub_X
        (F := F) (x + y)
  have hb : f.IsRoot b := by
    rw [Polynomial.IsRoot.def]
    have hxpow :=
      higherPrincipalUnitGroup.residueTeichmullerLift_pow_card (F := F) x
    have hypow :=
      higherPrincipalUnitGroup.residueTeichmullerLift_pow_card (F := F) y
    have hfresh :
        b ^ (p ^ (n : ℕ)) =
          higherPrincipalUnitGroup.residueTeichmullerLift F x ^
              (p ^ (n : ℕ)) +
            higherPrincipalUnitGroup.residueTeichmullerLift F y ^
              (p ^ (n : ℕ)) := by
      simpa [b] using
        add_pow_char_pow
          (higherPrincipalUnitGroup.residueTeichmullerLift F x)
          (higherPrincipalUnitGroup.residueTeichmullerLift F y)
          p (n : ℕ)
    have hxpow' :
        higherPrincipalUnitGroup.residueTeichmullerLift F x ^
            (p ^ (n : ℕ)) =
          higherPrincipalUnitGroup.residueTeichmullerLift F x := by
      simpa [hcard] using hxpow
    have hypow' :
        higherPrincipalUnitGroup.residueTeichmullerLift F y ^
            (p ^ (n : ℕ)) =
          higherPrincipalUnitGroup.residueTeichmullerLift F y := by
      simpa [hcard] using hypow
    have hbpow : b ^ Nat.card F.residueField = b := by
      rw [hcard, hfresh]
      rw [hxpow', hypow']
    simp [f, b, Polynomial.eval_sub, hbpow]
  have hres : F.residueMap b = F.residueMap a := by
    simp [a, b, map_add,
      higherPrincipalUnitGroup.residueMap_residueTeichmullerLift]
  have hderiv : IsUnit (f.derivative.eval a) := by
    simpa [f, a] using
      higherPrincipalUnitGroup.residueTeichmullerRootPolynomial_derivative_eval_isUnit_of_charP
        (F := F) p hcard (x + y)
  exact (F.toHenselianDVF.eq_of_isRoot_of_isRoot_of_residue_eq_of_derivative_isUnit
    ha hb hres hderiv).symm

/-- In equal characteristic, the Teichmuller lift is a ring homomorphic
coefficient-field section of the residue map. -/
noncomputable def residueTeichmullerRingHomOfCharP :
    F.residueField →+* F.valuationSubring where
  toFun := higherPrincipalUnitGroup.residueTeichmullerLift F
  map_zero' := higherPrincipalUnitGroup.residueTeichmullerLift_zero (F := F)
  map_one' := higherPrincipalUnitGroup.residueTeichmullerLift_one (F := F)
  map_mul' := fun x y =>
    higherPrincipalUnitGroup.residueTeichmullerLift_mul (F := F) x y
  map_add' := fun x y =>
    higherPrincipalUnitGroup.residueTeichmullerLift_add_of_charP
      (F := F) p hcard x y

/--
The defining evaluation formula for `residueTeichmullerRingHomOfCharP` is
`higherPrincipalUnitGroup.residueTeichmullerRingHomOfCharP (F := F) p hcard x =
higherPrincipalUnitGroup.residueTeichmullerLift F x`.
-/
@[simp] theorem residueTeichmullerRingHomOfCharP_apply
    (x : F.residueField) :
    higherPrincipalUnitGroup.residueTeichmullerRingHomOfCharP
        (F := F) p hcard x =
      higherPrincipalUnitGroup.residueTeichmullerLift F x :=
  rfl

/--
Establishes the identity `F.residueMap.comp
(higherPrincipalUnitGroup.residueTeichmullerRingHomOfCharP (F := F) p hcard) = RingHom.id
F.residueField`.
-/
theorem residueMap_comp_residueTeichmullerRingHomOfCharP :
    F.residueMap.comp
        (higherPrincipalUnitGroup.residueTeichmullerRingHomOfCharP
          (F := F) p hcard) =
      RingHom.id F.residueField := by
  exact RingHom.ext fun x ↦ residueMap_residueTeichmullerLift F x

/-- The corresponding coefficient-field embedding into the fraction field. -/
noncomputable def residueTeichmullerFieldHomOfCharP :
    F.residueField →+* K :=
  F.valuation.valuationSubring.subtype.comp
    (higherPrincipalUnitGroup.residueTeichmullerRingHomOfCharP
      (F := F) p hcard)

/--
The defining evaluation formula for `residueTeichmullerFieldHomOfCharP` is
`higherPrincipalUnitGroup.residueTeichmullerFieldHomOfCharP (F := F) p hcard x =
(higherPrincipalUnitGroup.residueTeichmullerLift F x : K)`.
-/
@[simp] theorem residueTeichmullerFieldHomOfCharP_apply
    (x : F.residueField) :
    higherPrincipalUnitGroup.residueTeichmullerFieldHomOfCharP
        (F := F) p hcard x =
      (higherPrincipalUnitGroup.residueTeichmullerLift F x : K) :=
  rfl
end higherPrincipalUnitGroup

end CompleteDVF
end DiscreteValuationField

end

end LocalFieldTheory
