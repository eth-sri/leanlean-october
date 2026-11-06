module

public import Mathlib

public import GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Core
public import GaloisCohomology.Cyclic.Herbrand.PrincipalUnits.QuotientReps
public import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.GaloisIntegerRing
public import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.IdealQuotients

@[expose] public section


/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/






set_option autoImplicit false
/-! Provides the public declarations in the `CyclicCohomology.Herbrand.PrincipalUnits.QuotientTower` Lean module. -/

namespace CyclicCohomology

open LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel

section
variable (K : Type u) [Field K] [ValuativeRel K]
include K
/-- The natural projection `𝒪_Kˣ/U_K^m → 𝒪_Kˣ/U_K^n` for `n ≤ m`. -/
def integerUnitsModPrincipalUnitsMapOfLe
      {n m : Nat} (hnm : n ≤ m) :
    IntegerUnitsModPrincipalUnitsAtLevel K m →*
      IntegerUnitsModPrincipalUnitsAtLevel K n :=
  integerUnitsModPrincipalUnitsAtLevelLift m
    (integerUnitsModPrincipalUnitsAtLevelMk K n)
    (by
      intro x hx
      rw [MonoidHom.mem_ker,
        integerUnitsModPrincipalUnitsAtLevelMk_eq_one_iff]
      apply principalUnits_antitone <;> assumption)

/-- The level-change map sends a unit class to the class of the same unit. -/
@[simp]
theorem integerUnitsModPrincipalUnitsMapOfLe_mk
      {n m : Nat} (hnm : n ≤ m)
    (x : 𝒪[K]ˣ) :
    integerUnitsModPrincipalUnitsMapOfLe K hnm
        (integerUnitsModPrincipalUnitsAtLevelMk K m x) =
      integerUnitsModPrincipalUnitsAtLevelMk K n x :=
  integerUnitsModPrincipalUnitsAtLevelLift_mk m
    (integerUnitsModPrincipalUnitsAtLevelMk K n) _ x

/-- The successive projection `𝒪_Kˣ/U_K^(n+1) → 𝒪_Kˣ/U_K^n`. -/
def integerUnitsModPrincipalUnitsSuccMap
      (n : Nat)  :=
  integerUnitsModPrincipalUnitsMapOfLe K (Nat.le_succ n)

/-- The successor-level map sends a unit representative to its successor quotient class. -/
@[simp]
theorem integerUnitsModPrincipalUnitsSuccMap_mk
      (n : Nat)
    (x : 𝒪[K]ˣ) :
    integerUnitsModPrincipalUnitsSuccMap K n
        (integerUnitsModPrincipalUnitsAtLevelMk K (n + 1) x) =
      integerUnitsModPrincipalUnitsAtLevelMk K n x :=
  integerUnitsModPrincipalUnitsMapOfLe_mk K (Nat.le_succ n) x
end













section
variable (K : Type u) [Field K] [ValuativeRel K]
    (n : Nat) (e : 𝒪[K] ≃+* 𝒪[K])
include K n e
/-- The induced homomorphism on the finite quotient `𝒪_Kˣ/U_K^n`. -/
def integerUnitsModPrincipalUnitsMapOfIntegerRingEquiv
      :
    IntegerUnitsModPrincipalUnitsAtLevel K n →*
      IntegerUnitsModPrincipalUnitsAtLevel K n :=
  integerUnitsModPrincipalUnitsAtLevelLift n
    ((integerUnitsModPrincipalUnitsAtLevelMk K n).comp
      (Units.mapEquiv e.toMulEquiv).toMonoidHom)
    (by
      intro u hu
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply,
        integerUnitsModPrincipalUnitsAtLevelMk_eq_one_iff]
      apply principalUnits_integerRingEquiv_mem_self <;> assumption)

/-- An integer-ring equivalence maps a unit quotient class via its representative. -/
@[simp]
theorem integerUnitsModPrincipalUnitsMapOfIntegerRingEquiv_mk
      (u : 𝒪[K]ˣ) :
    integerUnitsModPrincipalUnitsMapOfIntegerRingEquiv K n e
        (integerUnitsModPrincipalUnitsAtLevelMk K n u) =
      integerUnitsModPrincipalUnitsAtLevelMk K n
        (Units.mapEquiv e.toMulEquiv u) :=
  integerUnitsModPrincipalUnitsAtLevelLift_mk n
    ((integerUnitsModPrincipalUnitsAtLevelMk K n).comp
      (Units.mapEquiv e.toMulEquiv).toMonoidHom) _ u

/-- A valuation-integer-ring equivalence descends to the finite quotient
`𝒪_Kˣ/U_K^n`. -/
def integerUnitsModPrincipalUnitsMapEquivOfIntegerRingEquiv
      :
    IntegerUnitsModPrincipalUnitsAtLevel K n ≃*
      IntegerUnitsModPrincipalUnitsAtLevel K n where
  toFun := integerUnitsModPrincipalUnitsMapOfIntegerRingEquiv K n e
  invFun := integerUnitsModPrincipalUnitsMapOfIntegerRingEquiv K n e.symm
  left_inv := by
    intro x
    refine IntegerUnitsModPrincipalUnitsAtLevel.inductionOn n
      (motive := fun x =>
        integerUnitsModPrincipalUnitsMapOfIntegerRingEquiv K n e.symm
            (integerUnitsModPrincipalUnitsMapOfIntegerRingEquiv K n e x) = x)
      x ?_
    intro u
    rw [integerUnitsModPrincipalUnitsMapOfIntegerRingEquiv_mk,
      integerUnitsModPrincipalUnitsMapOfIntegerRingEquiv_mk]
    have h :
        Units.mapEquiv e.symm.toMulEquiv (Units.mapEquiv e.toMulEquiv u) = u := by
      ext
      simp
    apply congrArg <;> assumption
  right_inv := by
    intro x
    refine IntegerUnitsModPrincipalUnitsAtLevel.inductionOn n
      (motive := fun x =>
        integerUnitsModPrincipalUnitsMapOfIntegerRingEquiv K n e
            (integerUnitsModPrincipalUnitsMapOfIntegerRingEquiv K n e.symm x) = x)
      x ?_
    intro u
    rw [integerUnitsModPrincipalUnitsMapOfIntegerRingEquiv_mk,
      integerUnitsModPrincipalUnitsMapOfIntegerRingEquiv_mk]
    have h :
        Units.mapEquiv e.toMulEquiv (Units.mapEquiv e.symm.toMulEquiv u) = u := by
      ext
      simp
    apply congrArg <;> assumption
  map_mul' := by
    intro x y
    apply map_mul
end


/-- The induced quotient equivalence acts on a class through its unit representative. -/
@[simp]
alias integerUnitsModPrincipalUnitsMapEquivOfIntegerRingEquiv_mk := _root_.CyclicCohomology.integerUnitsModPrincipalUnitsMapOfIntegerRingEquiv_mk

section
variable (K : Type u) [Field K] [ValuativeRel K] (n : Nat)
include K n
/-- The graded quotient `U_K^n/U_K^(n+1)` as the kernel source inside
`𝒪_Kˣ/U_K^(n+1)`. -/
def principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc
      :
    PrincipalUnitsSuccQuot K n →*
      IntegerUnitsModPrincipalUnitsAtLevel K (n + 1) :=
  principalUnitsSuccQuotLift n
    ((integerUnitsModPrincipalUnitsAtLevelMk K (n + 1)).comp
      (principalUnits K n).subtype)
    (by
      intro u hu
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply,
        integerUnitsModPrincipalUnitsAtLevelMk_eq_one_iff]
      exact hu)

/-- The principal-unit quotient map sends a representative to its integer-unit class. -/
@[simp]
theorem principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc_mk
     
    (u : principalUnits K n) :
    principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc K n
        (principalUnitsSuccQuotMk K n u) =
      integerUnitsModPrincipalUnitsAtLevelMk K (n + 1) (u : 𝒪[K]ˣ) :=
  principalUnitsSuccQuotLift_mk n
    ((integerUnitsModPrincipalUnitsAtLevelMk K (n + 1)).comp
      (principalUnits K n).subtype) _ u

/-- The principal-unit inclusion followed by the successor map is the canonical quotient map. -/
theorem integerUnitsSuccMap_comp_principalUnitsSuccQuot
      :
    (integerUnitsModPrincipalUnitsSuccMap K n).comp
        (principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc K n) = 1 := by
  ext q
  refine PrincipalUnitsSuccQuot.inductionOn n
    (motive := fun q =>
      ((integerUnitsModPrincipalUnitsSuccMap K n).comp
        (principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc K n)) q =
          (1 : PrincipalUnitsSuccQuot K n →*
            IntegerUnitsModPrincipalUnitsAtLevel K n) q)
    q ?_
  intro u
  rw [MonoidHom.comp_apply,
    principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc_mk,
    integerUnitsModPrincipalUnitsSuccMap_mk]
  change integerUnitsModPrincipalUnitsAtLevelMk K n (u : 𝒪[K]ˣ) = 1
  rw [integerUnitsModPrincipalUnitsAtLevelMk_eq_one_iff]
  exact u.2

/-- Exactness of `U_K^n/U_K^(n+1) → 𝒪_Kˣ/U_K^(n+1) → 𝒪_Kˣ/U_K^n`
at the middle finite-filtration quotient. -/
theorem principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc_range_eq_ker
      :
    MonoidHom.range (principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc K n) =
      MonoidHom.ker (integerUnitsModPrincipalUnitsSuccMap K n) := by
  ext q
  constructor
  · rintro ⟨x, rfl⟩
    change (integerUnitsModPrincipalUnitsSuccMap K n).comp
        (principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc K n) x = 1
    rw [integerUnitsSuccMap_comp_principalUnitsSuccQuot]
    rfl
  · intro hq
    revert hq
    refine IntegerUnitsModPrincipalUnitsAtLevel.inductionOn (n + 1)
      (motive := fun q =>
        q ∈ MonoidHom.ker (integerUnitsModPrincipalUnitsSuccMap K n) →
          q ∈ MonoidHom.range
            (principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc K n))
      q ?_
    intro x hq
    have hx  := (integerUnitsModPrincipalUnitsAtLevelMk_eq_one_iff K n x).1
        (by simpa using hq)
    let u : principalUnits K n := ⟨x, hx⟩
    exact ⟨principalUnitsSuccQuotMk K n u, rfl⟩
end
































section
variable (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (n : Nat)
include K L n
/-- Integral-closure Galois action on the finite quotient
`𝒪_Lˣ/U_L^n`. -/
def galoisGroupIntegerUnitsModPrincipalUnitsMapEquivOfIsIntegralClosure
      (σ : Gal(L / K))  :=
  integerUnitsModPrincipalUnitsMapEquivOfIntegerRingEquiv L n
    (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ)

/-- The Galois-induced quotient equivalence acts on a class through its representative. -/
@[simp]
theorem galoisGroupIntegerUnitsModPrincipalUnitsMapEquivOfIsIntegralClosure_mk
      (σ : Gal(L / K)) (u : 𝒪[L]ˣ) :
    galoisGroupIntegerUnitsModPrincipalUnitsMapEquivOfIsIntegralClosure K L n σ
        (integerUnitsModPrincipalUnitsAtLevelMk L n u) =
      integerUnitsModPrincipalUnitsAtLevelMk L n
        (Units.mapEquiv
          (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ).toMulEquiv u) :=
  integerUnitsModPrincipalUnitsMapEquivOfIntegerRingEquiv_mk L n
    (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ) u

/-- Integral-closure Galois action on finite principal-unit
quotients as a group homomorphism. -/
def galoisGroupIntegerUnitsModPrincipalUnitsMapEquivHomOfIsIntegralClosure
      :
    Gal(L / K) →*
      (IntegerUnitsModPrincipalUnitsAtLevel L n ≃*
        IntegerUnitsModPrincipalUnitsAtLevel L n) where
  toFun := galoisGroupIntegerUnitsModPrincipalUnitsMapEquivOfIsIntegralClosure K L n
  map_one' := by
    ext x
    refine IntegerUnitsModPrincipalUnitsAtLevel.inductionOn n
      (motive := fun x =>
        galoisGroupIntegerUnitsModPrincipalUnitsMapEquivOfIsIntegralClosure
            K L n 1 x = x)
      x ?_
    intro u
    rw [galoisGroupIntegerUnitsModPrincipalUnitsMapEquivOfIsIntegralClosure_mk]
    congr 1
  map_mul' := by
    intro σ τ
    ext x
    refine IntegerUnitsModPrincipalUnitsAtLevel.inductionOn n
      (motive := fun x =>
        galoisGroupIntegerUnitsModPrincipalUnitsMapEquivOfIsIntegralClosure
            K L n (σ * τ) x =
          (galoisGroupIntegerUnitsModPrincipalUnitsMapEquivOfIsIntegralClosure
              K L n σ *
            galoisGroupIntegerUnitsModPrincipalUnitsMapEquivOfIsIntegralClosure
              K L n τ) x)
      x ?_
    intro u
    rw [galoisGroupIntegerUnitsModPrincipalUnitsMapEquivOfIsIntegralClosure_mk]
    change
      integerUnitsModPrincipalUnitsAtLevelMk L n
          (Units.mapEquiv
            (galoisGroupIntegerRingEquivOfIsIntegralClosure K L (σ * τ)).toMulEquiv u) =
        galoisGroupIntegerUnitsModPrincipalUnitsMapEquivOfIsIntegralClosure K L n σ
          (galoisGroupIntegerUnitsModPrincipalUnitsMapEquivOfIsIntegralClosure K L n τ
            (integerUnitsModPrincipalUnitsAtLevelMk L n u))
    rw [
      galoisGroupIntegerUnitsModPrincipalUnitsMapEquivOfIsIntegralClosure_mk,
      galoisGroupIntegerUnitsModPrincipalUnitsMapEquivOfIsIntegralClosure_mk]
    congr 1

/-- Integral-closure Galois action on finite principal-unit
quotients, packaged for low-degree Herbrand quotients. -/
@[implicit_reducible]
def galoisGroupIntegerUnitsModPrincipalUnitsMulDistribMulActionOfIsIntegralClosure
      :
    MulDistribMulAction (Gal(L / K)) (IntegerUnitsModPrincipalUnitsAtLevel L n) where
  smul σ x := galoisGroupIntegerUnitsModPrincipalUnitsMapEquivOfIsIntegralClosure K L n σ x
  one_smul := by
    intro x
    change galoisGroupIntegerUnitsModPrincipalUnitsMapEquivOfIsIntegralClosure K L n 1 x = x
    have h := congrArg (fun e : IntegerUnitsModPrincipalUnitsAtLevel L n ≃*
        IntegerUnitsModPrincipalUnitsAtLevel L n => e x)
      (map_one (galoisGroupIntegerUnitsModPrincipalUnitsMapEquivHomOfIsIntegralClosure K L n))
    exact h
  mul_smul := by
    intro σ τ x
    change galoisGroupIntegerUnitsModPrincipalUnitsMapEquivOfIsIntegralClosure K L n
        (σ * τ) x =
      galoisGroupIntegerUnitsModPrincipalUnitsMapEquivOfIsIntegralClosure K L n σ
        (galoisGroupIntegerUnitsModPrincipalUnitsMapEquivOfIsIntegralClosure K L n τ x)
    have h := congrArg (fun e : IntegerUnitsModPrincipalUnitsAtLevel L n ≃*
        IntegerUnitsModPrincipalUnitsAtLevel L n => e x)
      (map_mul (galoisGroupIntegerUnitsModPrincipalUnitsMapEquivHomOfIsIntegralClosure K L n)
        σ τ)
    exact h
  smul_mul := by
    intro σ x y
    apply map_mul
  smul_one := by
    intro σ
    apply map_one

/-- The Galois action on integer units modulo principal units is induced on representatives. -/
theorem galoisGroupIntegerUnitsModPrincipalUnitsMulDistribMulActionOfIsIntegralClosure_smul
      (σ : Gal(L / K)) (x : IntegerUnitsModPrincipalUnitsAtLevel L n) :
    letI := galoisGroupIntegerUnitsModPrincipalUnitsMulDistribMulActionOfIsIntegralClosure
      K L n
    σ • x = galoisGroupIntegerUnitsModPrincipalUnitsMapEquivOfIsIntegralClosure K L n σ x :=
  rfl
end
































































section
variable (K : Type u) [Field K] [ValuativeRel K]
include K
/-- The quotient `𝒪_Kˣ/U_K^0` is finite because `U_K^0 = 𝒪_Kˣ`. -/
theorem integerUnitsModPrincipalUnitsAtLevel_finite_zero
      :
    Finite (IntegerUnitsModPrincipalUnitsAtLevel K 0) := by
  let : Finite (𝒪[K]ˣ ⧸ principalUnits K 0) := by
    rw [principalUnits_zero]
    infer_instance
  exact Finite.of_equiv (𝒪[K]ˣ ⧸ principalUnits K 0)
    (integerUnitsModPrincipalUnitsAtLevelConcreteEquiv K 0).symm.toEquiv

/-- The initial nontrivial quotient `𝒪_Kˣ/U_K^1` is finite via
`𝒪_Kˣ/U_K^1 ≃ 𝓀_Kˣ`. -/
theorem integerUnitsModPrincipalUnitsAtLevel_finite_one_of_isNonarchimedeanLocalField
      [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    Finite (IntegerUnitsModPrincipalUnitsAtLevel K 1) := by
  let e  :=
    (integerUnitsModPrincipalUnitsAtLevelConcreteEquiv K 1).trans
      ((integerUnitsModPrincipalUnitsConcreteEquiv K).symm.trans
        (integerUnitsModPrincipalUnitsEquivResidueUnits K))
  exact Finite.of_equiv (ResidueUnits K) e.symm.toEquiv

/-- If the previous finite quotient and the graded quotient are finite, then
the next finite quotient is finite. -/
theorem integerUnitsModPrincipalUnitsAtLevel_finite_succ_of_finite
      (n : Nat)
    [Finite (PrincipalUnitsSuccQuot K n)]
    [Finite (IntegerUnitsModPrincipalUnitsAtLevel K n)] :
    Finite (IntegerUnitsModPrincipalUnitsAtLevel K (n + 1)) := by
  let i := principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc K n
  have  :=
    Finite.of_surjective
      (fun a : PrincipalUnitsSuccQuot K n => (⟨i a, ⟨a, rfl⟩⟩ : i.range))
      (by
        intro x
        rcases x with ⟨b, ⟨a, ha⟩⟩
        exact ⟨a, Subtype.ext ha⟩)
  let f := integerUnitsModPrincipalUnitsSuccMap K n
  exact (f.finite_iff_finite_ker_range).2 (by
    constructor
    · rw [← principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc_range_eq_ker K n]
      infer_instance
    · infer_instance)

/-- Every finite principal-unit quotient `𝒪_Kˣ/U_K^n` is finite over a
nonarchimedean local field. -/
theorem integerUnitsModPrincipalUnitsAtLevel_finite_of_isNonarchimedeanLocalField
      [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : Nat) :
    Finite (IntegerUnitsModPrincipalUnitsAtLevel K n) := by
  induction n with
  | zero =>
      exact integerUnitsModPrincipalUnitsAtLevel_finite_zero K
  | succ n ih =>
      cases n with
      | zero =>
          exact integerUnitsModPrincipalUnitsAtLevel_finite_one_of_isNonarchimedeanLocalField K
      | succ k =>
          have : Finite (PrincipalUnitsSuccQuot K (k + 1)) :=
            finite_principalUnitsSuccQuot K (k + 1) (Nat.succ_le_succ (Nat.zero_le k))
          exact integerUnitsModPrincipalUnitsAtLevel_finite_succ_of_finite K (k + 1)
end
































/-- Actual finite-cyclic-module endpoint for the finite quotient
`𝒪_Lˣ/U_L^n`. -/
theorem integerUnitsModPrincipalUnitsAtLevel_herbrandQuotient_eq_one_of_isNonarchimedeanLocalField
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Fintype (Gal(L / K))] (n : Nat) (σ : Gal(L / K))
    (hgen : ∀ g : Gal(L / K), g ∈ Subgroup.zpowers σ) :
    letI := galoisGroupIntegerUnitsModPrincipalUnitsMulDistribMulActionOfIsIntegralClosure K L n
    letI : Finite (IntegerUnitsModPrincipalUnitsAtLevel L n) :=
      integerUnitsModPrincipalUnitsAtLevel_finite_of_isNonarchimedeanLocalField L n
    CyclicCohomology.ProfiniteCohomology.Herbrand.herbrandQuotient
      (G := Gal(L / K)) (A := IntegerUnitsModPrincipalUnitsAtLevel L n) σ = 1 := by
  let := galoisGroupIntegerUnitsModPrincipalUnitsMulDistribMulActionOfIsIntegralClosure K L n
  let  :=
    integerUnitsModPrincipalUnitsAtLevel_finite_of_isNonarchimedeanLocalField L n
  apply CyclicCohomology.ProfiniteCohomology.Herbrand.herbrandQuotient_finite_module_eq_one <;> assumption



















































































































































































end
end CyclicCohomology
