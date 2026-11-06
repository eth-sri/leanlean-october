module

public import Mathlib

public import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitQuotients

@[expose] public section


/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-!
# Actions on principal-unit quotients

Transports valuation-ring automorphisms to maximal-ideal powers, principal
units, and their successive quotients, together with the resulting actions.
-/

set_option autoImplicit false

namespace LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel

section
variable (K : Type u) [Field K] [ValuativeRel K]
    (e : 𝒪[K] ≃+* 𝒪[K])
include K e
/-- A ring equivalence of a valuation integer ring preserves the maximal ideal. -/
theorem integerRingEquiv_mem_maximalIdeal
      (x : 𝒪[K]) :
    e x ∈ (𝓂[K] : Ideal 𝒪[K]) ↔ x ∈ (𝓂[K] : Ideal 𝒪[K]) := by
  rw [IsLocalRing.mem_maximalIdeal, map_mem_nonunits_iff e,
    ← IsLocalRing.mem_maximalIdeal]

/-- A ring equivalence of a valuation integer ring maps the maximal ideal to itself. -/
theorem integerRingEquiv_map_maximalIdeal
      :
    Ideal.map e.toRingHom (𝓂[K] : Ideal 𝒪[K]) = (𝓂[K] : Ideal 𝒪[K]) := by
  ext y
  constructor
  · intro hy
    rcases (Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective).1 hy with
      ⟨x, hx, rfl⟩
    exact (integerRingEquiv_mem_maximalIdeal K e x).2 hx
  · intro hy
    refine (Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective).2 ?_
    refine ⟨e.symm y, ?_, by simp⟩
    have hy' : e (e.symm y) ∈ (𝓂[K] : Ideal 𝒪[K]) := by
      simpa using hy
    exact (integerRingEquiv_mem_maximalIdeal K e (e.symm y)).1 hy'

/-- A ring equivalence of a valuation integer ring maps every maximal-ideal power to itself. -/
theorem integerRingEquiv_map_maximalIdeal_pow
      (n : Nat) :
    Ideal.map e.toRingHom (𝓂[K] ^ n : Ideal 𝒪[K]) =
      (𝓂[K] ^ n : Ideal 𝒪[K]) := by
  rw [Ideal.map_pow, integerRingEquiv_map_maximalIdeal]

/-- Membership in every maximal-ideal power is invariant under an integer-ring equivalence. -/
theorem integerRingEquiv_mem_maximalIdeal_pow
      (n : Nat) (x : 𝒪[K]) :
    e x ∈ (𝓂[K] ^ n : Ideal 𝒪[K]) ↔ x ∈ (𝓂[K] ^ n : Ideal 𝒪[K]) := by
  constructor
  · intro hx
    have hxmap :
        e.symm (e x) ∈ Ideal.map e.symm.toRingHom (𝓂[K] ^ n : Ideal 𝒪[K]) :=
      Ideal.mem_map_of_mem e.symm.toRingHom hx
    rw [integerRingEquiv_map_maximalIdeal_pow K e.symm n] at hxmap
    simpa using hxmap
  · intro hx
    have hxmap : e x ∈ Ideal.map e.toRingHom (𝓂[K] ^ n : Ideal 𝒪[K]) :=
      Ideal.mem_map_of_mem e.toRingHom hx
    rw [integerRingEquiv_map_maximalIdeal_pow K e n] at hxmap
    exact hxmap
end


section
variable (K : Type u) [Field K] [ValuativeRel K]
    (n : Nat) (e : 𝒪[K] ≃+* 𝒪[K])
include K n e
/-- The induced additive equivalence on the ideal power `𝓂^n`. -/
def maximalIdealPowMapEquivOfIntegerRingEquiv
      :
    ((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u) ≃+
      ((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u) where
  toFun a := ⟨e (a : 𝒪[K]), (integerRingEquiv_mem_maximalIdeal_pow K e n a).2 a.2⟩
  invFun a :=
    ⟨e.symm (a : 𝒪[K]), (integerRingEquiv_mem_maximalIdeal_pow K e.symm n a).2 a.2⟩
  left_inv := by
    intro a
    ext
    simp
  right_inv := by
    intro a
    ext
    simp
  map_add' := by
    intro a b
    ext
    simp










 theorem maximalIdealPowSuccQuotMapOfIntegerRingEquiv_respects
     
    (a b : ((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u))
    (hab : a - b ∈ maximalIdealPowSuccSubmodule K n) :
    maximalIdealPowSuccQuotMk K n
        (maximalIdealPowMapEquivOfIntegerRingEquiv K n e a) =
      maximalIdealPowSuccQuotMk K n
        (maximalIdealPowMapEquivOfIntegerRingEquiv K n e b) := by
  apply (maximalIdealPowSuccQuotMk_eq_iff K n _ _).2
  rw [mem_maximalIdealPowSuccSubmodule_iff]
  change e (a : 𝒪[K]) - e (b : 𝒪[K]) ∈
    (𝓂[K] ^ (n + 1) : Ideal 𝒪[K])
  rw [← map_sub]
  exact (integerRingEquiv_mem_maximalIdeal_pow K e (n + 1)
    ((a - b : (𝓂[K] ^ n : Ideal 𝒪[K])) : 𝒪[K])).2
      ((mem_maximalIdealPowSuccSubmodule_iff K n (a - b)).1 hab)

/-- The induced additive homomorphism on `𝓂^n/𝓂^(n+1)`. -/
def maximalIdealPowSuccQuotMapOfIntegerRingEquiv
      :
    MaximalIdealPowSuccQuot K n →+ MaximalIdealPowSuccQuot K n := by
  let f  :=
    maximalIdealPowSuccQuotLift n
      (fun a => maximalIdealPowSuccQuotMk K n
        (maximalIdealPowMapEquivOfIntegerRingEquiv K n e a))
      (maximalIdealPowSuccQuotMapOfIntegerRingEquiv_respects K n e)
  refine
    { toFun := f
      map_zero' := ?_
      map_add' := ?_ }
  · change f 0 = 0
    rw [← map_zero (maximalIdealPowSuccQuotMk K n)]
    dsimp only [f]
    rw [maximalIdealPowSuccQuotLift_mk, map_zero, map_zero]
  · intro x y
    change f (x + y) = f x + f y
    refine MaximalIdealPowSuccQuot.inductionOn₂ n
      (motive := fun x' y' => f (x' + y') = f x' + f y') x y ?_
    intro a b
    rw [← map_add (maximalIdealPowSuccQuotMk K n)]
    dsimp only [f]
    rw [maximalIdealPowSuccQuotLift_mk,
      maximalIdealPowSuccQuotLift_mk,
      maximalIdealPowSuccQuotLift_mk, map_add, map_add]

/-- The map on successive maximal-ideal quotients sends a representative to the class of its image
under the ring equivalence. -/
theorem maximalIdealPowSuccQuotMapOfIntegerRingEquiv_mk
     
    (a : ((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u)) :
    maximalIdealPowSuccQuotMapOfIntegerRingEquiv K n e
        (maximalIdealPowSuccQuotMk K n a) =
      maximalIdealPowSuccQuotMk K n
        (maximalIdealPowMapEquivOfIntegerRingEquiv K n e a) := by
  rfl

/-- The induced additive equivalence on `𝓂^n/𝓂^(n+1)`. -/
def maximalIdealPowSuccQuotMapEquivOfIntegerRingEquiv
      :
    MaximalIdealPowSuccQuot K n ≃+ MaximalIdealPowSuccQuot K n where
  toFun := maximalIdealPowSuccQuotMapOfIntegerRingEquiv K n e
  invFun := maximalIdealPowSuccQuotMapOfIntegerRingEquiv K n e.symm
  left_inv := by
    intro x
    refine MaximalIdealPowSuccQuot.inductionOn n
      (motive := fun x' =>
        maximalIdealPowSuccQuotMapOfIntegerRingEquiv K n e.symm
            (maximalIdealPowSuccQuotMapOfIntegerRingEquiv K n e x') = x')
      x ?_
    intro a
    rw [maximalIdealPowSuccQuotMapOfIntegerRingEquiv_mk,
      maximalIdealPowSuccQuotMapOfIntegerRingEquiv_mk]
    have h := (maximalIdealPowMapEquivOfIntegerRingEquiv K n e).left_inv a
    apply congrArg <;> assumption
  right_inv := by
    intro x
    refine MaximalIdealPowSuccQuot.inductionOn n
      (motive := fun x' =>
        maximalIdealPowSuccQuotMapOfIntegerRingEquiv K n e
            (maximalIdealPowSuccQuotMapOfIntegerRingEquiv K n e.symm x') = x')
      x ?_
    intro a
    rw [maximalIdealPowSuccQuotMapOfIntegerRingEquiv_mk,
      maximalIdealPowSuccQuotMapOfIntegerRingEquiv_mk]
    have h := (maximalIdealPowMapEquivOfIntegerRingEquiv K n e).right_inv a
    apply congrArg <;> assumption
  map_add' := by
    intro x y
    apply map_add













/-- Principal units are preserved by every valuation-integer-ring equivalence. -/
def principalUnits_integerRingEquiv_mem_self
      (u : 𝒪[K]ˣ)
    (hu : u ∈ principalUnits K n)  :=
  principalUnits_integerRingEquiv_mem K n e
    (fun x hx => (integerRingEquiv_mem_maximalIdeal_pow K e n x).2 hx) u hu

/-- The induced multiplicative equivalence on the `n`-th principal-unit group. -/
def principalUnitsMapEquivOfIntegerRingEquiv
      :
    principalUnits K n ≃* principalUnits K n where
  toFun u :=
    ⟨Units.mapEquiv e.toMulEquiv u.1,
      principalUnits_integerRingEquiv_mem_self K n e u.1 u.2⟩
  invFun u :=
    ⟨Units.mapEquiv e.symm.toMulEquiv u.1,
      principalUnits_integerRingEquiv_mem_self K n e.symm u.1 u.2⟩
  left_inv := by
    intro u
    ext
    simp
  right_inv := by
    intro u
    ext
    simp
  map_mul' := by
    intro a b
    ext
    simp

























/-- The induced homomorphism on the successive principal-unit quotient. -/
def principalUnitsSuccQuotMapOfIntegerRingEquiv
      :
    PrincipalUnitsSuccQuot K n →* PrincipalUnitsSuccQuot K n :=
  principalUnitsSuccQuotLift n
    ((principalUnitsSuccQuotMk K n).comp
      (principalUnitsMapEquivOfIntegerRingEquiv K n e).toMonoidHom)
    (by
      intro u hu
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply,
        principalUnitsSuccQuotMk_eq_one_iff]
      exact principalUnits_integerRingEquiv_mem_self K (n + 1) e u.1 hu)

/-- The map on successive principal-unit quotients sends each class to the class of its transported
representative. -/
theorem principalUnitsSuccQuotMapOfIntegerRingEquiv_apply
      (u : principalUnits K n) :
    principalUnitsSuccQuotMapOfIntegerRingEquiv K n e
        (principalUnitsSuccQuotMk K n u) =
      principalUnitsSuccQuotMk K n
        (principalUnitsMapEquivOfIntegerRingEquiv K n e u) :=
  rfl

/-- The induced multiplicative equivalence on `U^n/U^(n+1)`. -/
def principalUnitsSuccQuotMapEquivOfIntegerRingEquiv
      :
    PrincipalUnitsSuccQuot K n ≃* PrincipalUnitsSuccQuot K n where
  toFun := principalUnitsSuccQuotMapOfIntegerRingEquiv K n e
  invFun := principalUnitsSuccQuotMapOfIntegerRingEquiv K n e.symm
  left_inv := by
    intro x
    refine PrincipalUnitsSuccQuot.inductionOn n
      (motive := fun x' =>
        principalUnitsSuccQuotMapOfIntegerRingEquiv K n e.symm
            (principalUnitsSuccQuotMapOfIntegerRingEquiv K n e x') = x')
      x ?_
    intro u
    rw [principalUnitsSuccQuotMapOfIntegerRingEquiv_apply,
      principalUnitsSuccQuotMapOfIntegerRingEquiv_apply]
    have h := (principalUnitsMapEquivOfIntegerRingEquiv K n e).left_inv u
    apply congrArg <;> assumption
  right_inv := by
    intro x
    refine PrincipalUnitsSuccQuot.inductionOn n
      (motive := fun x' =>
        principalUnitsSuccQuotMapOfIntegerRingEquiv K n e
            (principalUnitsSuccQuotMapOfIntegerRingEquiv K n e.symm x') = x')
      x ?_
    intro u
    rw [principalUnitsSuccQuotMapOfIntegerRingEquiv_apply,
      principalUnitsSuccQuotMapOfIntegerRingEquiv_apply]
    have h := (principalUnitsMapEquivOfIntegerRingEquiv K n e).right_inv u
    apply congrArg <;> assumption
  map_mul' := by
    intro x y
    apply map_mul












/-- The induced additive equivalence on the additive form of
`U^n/U^(n+1)`. -/
def principalUnitsSuccQuotAddEquivOfIntegerRingEquiv
      :
    Additive (PrincipalUnitsSuccQuot K n) ≃+
      Additive (PrincipalUnitsSuccQuot K n) where
  toFun x :=
    Additive.ofMul
      (principalUnitsSuccQuotMapEquivOfIntegerRingEquiv K n e (Additive.toMul x))
  invFun x :=
    Additive.ofMul
      (principalUnitsSuccQuotMapEquivOfIntegerRingEquiv K n e.symm (Additive.toMul x))
  left_inv := by
    intro x
    change Additive.ofMul
        (principalUnitsSuccQuotMapEquivOfIntegerRingEquiv K n e.symm
          (principalUnitsSuccQuotMapEquivOfIntegerRingEquiv K n e (Additive.toMul x))) =
      Additive.ofMul (Additive.toMul x)
    exact congrArg Additive.ofMul
      ((principalUnitsSuccQuotMapEquivOfIntegerRingEquiv K n e).left_inv
        (Additive.toMul x))
  right_inv := by
    intro x
    change Additive.ofMul
        (principalUnitsSuccQuotMapEquivOfIntegerRingEquiv K n e
          (principalUnitsSuccQuotMapEquivOfIntegerRingEquiv K n e.symm
            (Additive.toMul x))) =
      Additive.ofMul (Additive.toMul x)
    exact congrArg Additive.ofMul
      ((principalUnitsSuccQuotMapEquivOfIntegerRingEquiv K n e).right_inv
        (Additive.toMul x))
  map_add' := by
    simp_all

/-- The additive equivalence on successive principal-unit quotients agrees with transport of
quotient representatives. -/
@[simp]
theorem principalUnitsSuccQuotAddEquivOfIntegerRingEquiv_apply
      (x : PrincipalUnitsSuccQuot K n) :
    principalUnitsSuccQuotAddEquivOfIntegerRingEquiv K n e (Additive.ofMul x) =
      Additive.ofMul (principalUnitsSuccQuotMapEquivOfIntegerRingEquiv K n e x) :=
  rfl

/-- Multiplicative form of the induced equivalence on
`𝓂^n/𝓂^(n+1)`. -/
def maximalIdealPowSuccQuotMultiplicativeMapEquivOfIntegerRingEquiv
      :
    Multiplicative (MaximalIdealPowSuccQuot K n) ≃*
      Multiplicative (MaximalIdealPowSuccQuot K n) where
  toFun x :=
    Multiplicative.ofAdd
      (maximalIdealPowSuccQuotMapEquivOfIntegerRingEquiv K n e
        (Multiplicative.toAdd x))
  invFun x :=
    Multiplicative.ofAdd
      (maximalIdealPowSuccQuotMapEquivOfIntegerRingEquiv K n e.symm
        (Multiplicative.toAdd x))
  left_inv := by
    intro x
    change Multiplicative.ofAdd
        (maximalIdealPowSuccQuotMapEquivOfIntegerRingEquiv K n e.symm
          (maximalIdealPowSuccQuotMapEquivOfIntegerRingEquiv K n e
            (Multiplicative.toAdd x))) =
      Multiplicative.ofAdd (Multiplicative.toAdd x)
    exact congrArg Multiplicative.ofAdd
      ((maximalIdealPowSuccQuotMapEquivOfIntegerRingEquiv K n e).left_inv
        (Multiplicative.toAdd x))
  right_inv := by
    intro x
    change Multiplicative.ofAdd
        (maximalIdealPowSuccQuotMapEquivOfIntegerRingEquiv K n e
          (maximalIdealPowSuccQuotMapEquivOfIntegerRingEquiv K n e.symm
            (Multiplicative.toAdd x))) =
      Multiplicative.ofAdd (Multiplicative.toAdd x)
    exact congrArg Multiplicative.ofAdd
      ((maximalIdealPowSuccQuotMapEquivOfIntegerRingEquiv K n e).right_inv
        (Multiplicative.toAdd x))
  map_mul' := by
    intro x y
    change Multiplicative.ofAdd
        (maximalIdealPowSuccQuotMapEquivOfIntegerRingEquiv K n e
          (Multiplicative.toAdd (x * y))) =
      Multiplicative.ofAdd
        (maximalIdealPowSuccQuotMapEquivOfIntegerRingEquiv K n e
          (Multiplicative.toAdd x) +
        maximalIdealPowSuccQuotMapEquivOfIntegerRingEquiv K n e
          (Multiplicative.toAdd y))
    rw [show Multiplicative.toAdd (x * y) =
        Multiplicative.toAdd x + Multiplicative.toAdd y from rfl]
    rw [map_add]

/-- The multiplicative encoding of a successive ideal-quotient equivalence applies the original
additive transport map. -/
@[simp]
theorem maximalIdealPowSuccQuotMultiplicativeMapEquivOfIntegerRingEquiv_apply
      (x : MaximalIdealPowSuccQuot K n) :
    maximalIdealPowSuccQuotMultiplicativeMapEquivOfIntegerRingEquiv K n e
        (Multiplicative.ofAdd x) =
      Multiplicative.ofAdd (maximalIdealPowSuccQuotMapEquivOfIntegerRingEquiv K n e x) :=
  rfl
end


















































































end
end LocalFieldTheory
