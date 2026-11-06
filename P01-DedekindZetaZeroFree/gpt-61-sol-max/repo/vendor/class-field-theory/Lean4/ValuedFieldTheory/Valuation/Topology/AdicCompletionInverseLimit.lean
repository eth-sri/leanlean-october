module

public import Mathlib

public import ValuedFieldTheory.Valuation.Topology.AdicCompletionInverseLimitRing

@[expose] public section


/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/



set_option autoImplicit false

/-!
# Adic unit and higher-unit inverse limits

This file contains the algebraic and topological projective-limit descriptions
of unit groups of adically complete rings and complete discrete valuation
rings.  The underlying adic ring inverse-limit theory lives in
`AdicCompletionInverseLimitRing`.
-/

noncomputable section

namespace LubinTate
namespace Valuations

universe u v

open ValuationTheory.DiscreteValuationField
open ValuationTheory.Valuations
open Filter Set Topology
open scoped Valued

/-- The adic inverse-limit equivalence, unit form of the canonical adic-completion isomorphism. -/
def adicCompletionUnitsEquiv
    {R : Type*} [CommRing R] (I : Ideal R) [IsAdicComplete I R]  :=
  Units.mapEquiv (adicCompletionAlgEquiv I).toRingEquiv.toMulEquiv















































































































/-- The opaque projective-limit object `lim_n (R/I^n)^*` for quotient-unit
groups. -/
def adicUnitInverseLimit
    {R : Type*} [CommRing R] (I : Ideal R) : Type _ :=
  compatibleGroupFamilies (fun n : ℕ => (R ⧸ I ^ n)ˣ)
    (fun {_ _} hmn =>
      Units.map (Ideal.Quotient.factorPow I hmn).toMonoidHom)

/-- Defines `adicUnitInverseLimitCompatibleFamiliesEquiv`. -/
def adicUnitInverseLimitCompatibleFamiliesEquiv
    {R : Type*} [CommRing R] (I : Ideal R) :
    adicUnitInverseLimit I ≃
      compatibleGroupFamilies (fun n : ℕ => (R ⧸ I ^ n)ˣ)
        (fun {_ _} hmn =>
          Units.map (Ideal.Quotient.factorPow I hmn).toMonoidHom) := by
  unfold adicUnitInverseLimit
  exact Equiv.refl _

/-- Compatible unit families form a commutative group under coordinatewise multiplication. -/
instance adicUnitInverseLimit.instCommGroup
    {R : Type*} [CommRing R] (I : Ideal R) :
    CommGroup (adicUnitInverseLimit I) :=
  (adicUnitInverseLimitCompatibleFamiliesEquiv I).commGroup










section
variable {R : Type*} [CommRing R] (I : Ideal R)
include R I
section
variable (x : ∀ n : ℕ, (R ⧸ I ^ n)ˣ)
    (compatible : ∀ {m n : ℕ} (hmn : m ≤ n),
      Units.map (Ideal.Quotient.factorPow I hmn).toMonoidHom (x n) = x m)
include x compatible in
/-- Defines `adicUnitInverseLimit_mk`. -/
def adicUnitInverseLimit_mk
     
       :=
  (adicUnitInverseLimitCompatibleFamiliesEquiv I).symm ⟨x, compatible⟩

/-- Defines `adicUnitInverseLimit_eval`. -/
def adicUnitInverseLimit_eval
      (n : ℕ) :
    adicUnitInverseLimit I →* (R ⧸ I ^ n)ˣ where
  toFun x := (adicUnitInverseLimitCompatibleFamiliesEquiv I x).1 n
  map_one' := rfl
  map_mul' _ _ := rfl

include x compatible in
/-- Evaluation of a compatible unit family returns its component at the selected level. -/
@[simp]
theorem adicUnitInverseLimit_eval_mk
     
     
    (n : ℕ) :
    adicUnitInverseLimit_eval I n (adicUnitInverseLimit_mk I x compatible) =
      x n := rfl
end


/-- Two adic unit inverse-limit elements are equal when all evaluations agree. -/
@[ext]
theorem adicUnitInverseLimit_ext
     
    {x y : adicUnitInverseLimit I}
    (h : ∀ n : ℕ, adicUnitInverseLimit_eval I n x =
      adicUnitInverseLimit_eval I n y) :
    x = y := by
  apply (adicUnitInverseLimitCompatibleFamiliesEquiv I).injective
  apply Subtype.ext
  funext n
  exact h n

/-- Evaluation commutes with the transition map between adic quotient levels. -/
theorem adicUnitInverseLimit_eval_transition
     
    {m n : ℕ} (hmn : m ≤ n) (x : adicUnitInverseLimit I) :
    Units.map (Ideal.Quotient.factorPow I hmn).toMonoidHom
        (adicUnitInverseLimit_eval I n x) =
      adicUnitInverseLimit_eval I m x :=
  (adicUnitInverseLimitCompatibleFamiliesEquiv I x).2 hmn

/-- Units of the explicit projective-limit ring are the same as compatible
families of units in the finite quotient rings. -/
def adicQuotientInverseLimitUnitsEquiv
      :
    (adicQuotientInverseLimit I)ˣ ≃*
      adicUnitInverseLimit I where
  toFun u := adicUnitInverseLimit_mk I
    (fun n => Units.map (adicQuotientInverseLimit_eval I n).toMonoidHom u)
    (fun hmn => by
      ext
      apply adicQuotientInverseLimit_eval_factorPow)
  invFun u :=
    { val := adicQuotientInverseLimit_mk I
        (fun n => (adicUnitInverseLimit_eval I n u : R ⧸ I ^ n))
        (fun hmn => congrArg Units.val
          (adicUnitInverseLimit_eval_transition I hmn u))
      inv := adicQuotientInverseLimit_mk I
        (fun n =>
          (((adicUnitInverseLimit_eval I n u)⁻¹ : (R ⧸ I ^ n)ˣ) :
            R ⧸ I ^ n))
        (fun hmn => by
          have h := congrArg Units.val
            (congrArg Inv.inv
              (adicUnitInverseLimit_eval_transition I hmn u))
          simpa using h)
      val_inv := by
        ext n
        exact Units.mul_inv (adicUnitInverseLimit_eval I n u)
      inv_val := by
        ext n
        exact Units.inv_mul (adicUnitInverseLimit_eval I n u) }
  left_inv u := by
    ext n
    rfl
  right_inv u := by
    ext n
    rfl
  map_mul' u v := by
    ext n
    rfl

/-- The adic inverse-limit equivalence, units of the adic completion are the projective limit of
the units of the finite quotient rings. -/
def adicCompletionUnitsEquivUnitInverseLimit
       :=
  (Units.mapEquiv
      (adicCompletion_equiv_quotientInverseLimit I).toMulEquiv).trans
    (adicQuotientInverseLimitUnitsEquiv I)

/-- The adic inverse-limit equivalence, unit projective-limit form for a complete ring. -/
def unitsEquivUnitInverseLimit
      [IsAdicComplete I R]  :=
  (adicCompletionUnitsEquiv I).trans
    (adicCompletionUnitsEquivUnitInverseLimit I)











/-- The opaque positive-indexed unit inverse limit
`lim_n (R/I^(n+1))ˣ`. -/
def adicPositiveUnitInverseLimit
      : Type _ :=
  compatibleGroupFamilies (fun n : ℕ => (R ⧸ I ^ (n + 1))ˣ)
    (fun {_ _} hmn =>
      Units.map
        (Ideal.Quotient.factorPow I (Nat.succ_le_succ hmn)).toMonoidHom)

/-- Defines `adicPositiveUnitInverseLimitCompatibleFamiliesEquiv`. -/
def adicPositiveUnitInverseLimitCompatibleFamiliesEquiv
      :
    adicPositiveUnitInverseLimit I ≃
      compatibleGroupFamilies (fun n : ℕ => (R ⧸ I ^ (n + 1))ˣ)
        (fun {_ _} hmn =>
          Units.map
            (Ideal.Quotient.factorPow I
              (Nat.succ_le_succ hmn)).toMonoidHom) := by
  unfold adicPositiveUnitInverseLimit
  exact Equiv.refl _
end


/-- Positive-level compatible unit families form a commutative group. -/
instance adicPositiveUnitInverseLimit.instCommGroup
    {R : Type*} [CommRing R] (I : Ideal R) :
    CommGroup (adicPositiveUnitInverseLimit I) :=
  (adicPositiveUnitInverseLimitCompatibleFamiliesEquiv I).commGroup

/-- Defines `adicPositiveUnitInverseLimitRepresentation`. -/
def adicPositiveUnitInverseLimitRepresentation
    {R : Type*} [CommRing R] (I : Ideal R) :
    adicPositiveUnitInverseLimit I ≃*
      compatibleGroupFamilies (fun n : ℕ => (R ⧸ I ^ (n + 1))ˣ)
        (fun {_ _} hmn =>
          Units.map
            (Ideal.Quotient.factorPow I
              (Nat.succ_le_succ hmn)).toMonoidHom) :=
  (adicPositiveUnitInverseLimitCompatibleFamiliesEquiv I).mulEquiv

/-- Defines `adicPositiveUnitInverseLimit_mk`. -/
def adicPositiveUnitInverseLimit_mk
    {R : Type*} [CommRing R] (I : Ideal R)
    (x : ∀ n : ℕ, (R ⧸ I ^ (n + 1))ˣ)
    (compatible : ∀ {m n : ℕ} (hmn : m ≤ n),
      Units.map
          (Ideal.Quotient.factorPow I
            (Nat.succ_le_succ hmn)).toMonoidHom (x n) = x m)  :=
  (adicPositiveUnitInverseLimitCompatibleFamiliesEquiv I).symm
    ⟨x, compatible⟩

/-- Defines `adicPositiveUnitInverseLimit_eval`. -/
def adicPositiveUnitInverseLimit_eval
    {R : Type*} [CommRing R] (I : Ideal R) (n : ℕ) :
    adicPositiveUnitInverseLimit I →* (R ⧸ I ^ (n + 1))ˣ where
  toFun x :=
    (adicPositiveUnitInverseLimitCompatibleFamiliesEquiv I x).1 n
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Evaluation of a positive-level unit family returns its chosen component. -/
@[simp]
theorem adicPositiveUnitInverseLimit_eval_mk
    {R : Type*} [CommRing R] (I : Ideal R)
    (x : ∀ n : ℕ, (R ⧸ I ^ (n + 1))ˣ)
    (compatible : ∀ {m n : ℕ} (hmn : m ≤ n),
      Units.map
          (Ideal.Quotient.factorPow I
            (Nat.succ_le_succ hmn)).toMonoidHom (x n) = x m)
    (n : ℕ) :
    adicPositiveUnitInverseLimit_eval I n
        (adicPositiveUnitInverseLimit_mk I x compatible) = x n := rfl

/-- Positive adic unit families are determined by all of their components. -/
@[ext]
theorem adicPositiveUnitInverseLimit_ext
    {R : Type*} [CommRing R] (I : Ideal R)
    {x y : adicPositiveUnitInverseLimit I}
    (h : ∀ n : ℕ, adicPositiveUnitInverseLimit_eval I n x =
      adicPositiveUnitInverseLimit_eval I n y) :
    x = y := by
  apply (adicPositiveUnitInverseLimitCompatibleFamiliesEquiv I).injective
  apply Subtype.ext
  funext n
  exact h n

/-- Positive-level evaluation respects the adic transition maps. -/
theorem adicPositiveUnitInverseLimit_eval_transition
    {R : Type*} [CommRing R] (I : Ideal R)
    {m n : ℕ} (hmn : m ≤ n) (x : adicPositiveUnitInverseLimit I) :
    Units.map
        (Ideal.Quotient.factorPow I
          (Nat.succ_le_succ hmn)).toMonoidHom
        (adicPositiveUnitInverseLimit_eval I n x) =
      adicPositiveUnitInverseLimit_eval I m x :=
  (adicPositiveUnitInverseLimitCompatibleFamiliesEquiv I x).2 hmn

/-- Defines `adicUnitInverseLimit_toPositive`. -/
def adicUnitInverseLimit_toPositive
    {R : Type*} [CommRing R] (I : Ideal R)  :=
  fun u =>
    adicPositiveUnitInverseLimit_mk I
      (fun n => adicUnitInverseLimit_eval I (n + 1) u)
      (fun hmn => adicUnitInverseLimit_eval_transition I
        (Nat.succ_le_succ hmn) u)

/-- Defines `adicPositiveUnitInverseLimit_toAll`. -/
def adicPositiveUnitInverseLimit_toAll
    {R : Type*} [CommRing R] (I : Ideal R) :
    adicPositiveUnitInverseLimit I →
      adicUnitInverseLimit I :=
  fun u =>
    adicUnitInverseLimit_mk I (fun n => match n with
      | 0 => 1
      | k + 1 => adicPositiveUnitInverseLimit_eval I k u)
    (by
      intro m n hmn
      cases m with
      | zero =>
          ext
          have : Subsingleton (R ⧸ I ^ 0) := by
            simpa only [pow_zero, Ideal.one_eq_top] using
              (inferInstance : Subsingleton (R ⧸ (⊤ : Ideal R)))
          exact Subsingleton.elim _ _
      | succ m =>
          cases n with
          | zero => cases hmn
          | succ n =>
              apply adicPositiveUnitInverseLimit_eval_transition <;> aesop)

/-- Restricting an all-level unit family to positive levels and extending back is the identity. -/
theorem adicPositiveUnitInverseLimit_toPositive_toAll
    {R : Type*} [CommRing R] (I : Ideal R)
    (u : adicPositiveUnitInverseLimit I) :
    adicUnitInverseLimit_toPositive I
        (adicPositiveUnitInverseLimit_toAll I u) = u := by
  ext n
  rfl

/-- Extending a positive-level unit family and restricting again is the identity. -/
theorem adicUnitInverseLimit_toAll_toPositive
    {R : Type*} [CommRing R] (I : Ideal R)
    (u : adicUnitInverseLimit I) :
    adicPositiveUnitInverseLimit_toAll I
        (adicUnitInverseLimit_toPositive I u) = u := by
  ext n
  cases n with
  | zero =>
      have : Subsingleton (R ⧸ I ^ 0) := by
        simpa only [pow_zero, Ideal.one_eq_top] using
          (inferInstance : Subsingleton (R ⧸ (⊤ : Ideal R)))
      exact Subsingleton.elim _ _
  | succ n =>
      rfl

/-- The all-level unit inverse limit is equivalent to the positive-indexed
one.  This removes the degenerate `I^0` coordinate used by mathlib's adic
completion API. -/
def adicUnitInverseLimitEquivPositive
    {R : Type*} [CommRing R] (I : Ideal R) :
    adicUnitInverseLimit I ≃*
      adicPositiveUnitInverseLimit I where
  toFun := adicUnitInverseLimit_toPositive I
  invFun := adicPositiveUnitInverseLimit_toAll I
  left_inv := adicUnitInverseLimit_toAll_toPositive I
  right_inv := adicPositiveUnitInverseLimit_toPositive_toAll I
  map_mul' u v := by
    ext n
    rfl

/-- Complete-ring unit projective-limit form with the positive indexing. -/
def unitsEquivPositiveUnitInverseLimit
    {R : Type*} [CommRing R] (I : Ideal R) [IsAdicComplete I R]  :=
  (unitsEquivUnitInverseLimit I).trans
    (adicUnitInverseLimitEquivPositive I)











section
variable {O : Type*} [CommRing O] (π : O)
include O π
/-- The first principal ideal generated by `π` has powers `π^nO`. -/
theorem dvrPowerIdeal_one_pow
      (n : ℕ) :
    (uniformizerPowerIdeal π 1) ^ n = uniformizerPowerIdeal π n := by
  simp [uniformizerPowerIdeal, Ideal.span_singleton_pow]

/-- The principal-power ideals form a decreasing filtration. -/
theorem dvrPowerIdeal_le_of_le
      {m n : ℕ} (hmn : m ≤ n) :
    uniformizerPowerIdeal π n ≤ uniformizerPowerIdeal π m := by
  rw [← dvrPowerIdeal_one_pow π m,
    ← dvrPowerIdeal_one_pow π n]
  exact Ideal.pow_le_pow_right hmn

/-- Transition map on the finite unit quotients `(O/π^(n+1)O)ˣ`. -/
def dvrPowerIdealUnitTransition
      {m n : ℕ} (hmn : m ≤ n) :
    O ⧸ uniformizerPowerIdeal π (n + 1) →+*
      O ⧸ uniformizerPowerIdeal π (m + 1) :=
  Ideal.Quotient.factor
    (dvrPowerIdeal_le_of_le π (Nat.succ_le_succ hmn))

/-- The opaque positive-indexed projective limit
`lim_n (O/π^(n+1)O)ˣ`. -/
def dvrPowerIdealUnitInverseLimit
      : Type _ :=
  compatibleGroupFamilies
    (fun n : ℕ => (O ⧸ uniformizerPowerIdeal π (n + 1))ˣ)
    (fun {_ _} hmn =>
      Units.map
        (dvrPowerIdealUnitTransition π hmn).toMonoidHom)

/-- Defines `dvrPowerIdealUnitInverseLimitCompatibleFamiliesEquiv`. -/
def dvrPowerIdealUnitInverseLimitCompatibleFamiliesEquiv
      :
    dvrPowerIdealUnitInverseLimit π ≃
      compatibleGroupFamilies
        (fun n : ℕ => (O ⧸ uniformizerPowerIdeal π (n + 1))ˣ)
        (fun {_ _} hmn =>
          Units.map
            (dvrPowerIdealUnitTransition π hmn).toMonoidHom) := by
  unfold dvrPowerIdealUnitInverseLimit
  exact Equiv.refl _
end


/-- Compatible units modulo powers of a DVR element form a commutative group. -/
instance dvrPowerIdealUnitInverseLimit.instCommGroup
    {O : Type*} [CommRing O] (π : O) :
    CommGroup (dvrPowerIdealUnitInverseLimit π) :=
  (dvrPowerIdealUnitInverseLimitCompatibleFamiliesEquiv π).commGroup

section
variable {O : Type*} [CommRing O] (π : O)
include O π
/-- Defines `dvrPowerIdealUnitInverseLimitRepresentation`. -/
def dvrPowerIdealUnitInverseLimitRepresentation
      :
    dvrPowerIdealUnitInverseLimit π ≃*
      compatibleGroupFamilies
        (fun n : ℕ => (O ⧸ uniformizerPowerIdeal π (n + 1))ˣ)
        (fun {_ _} hmn =>
          Units.map
            (dvrPowerIdealUnitTransition π hmn).toMonoidHom) :=
  (dvrPowerIdealUnitInverseLimitCompatibleFamiliesEquiv π).mulEquiv











/-- Defines `dvrPowerIdealUnitInverseLimit_eval`. -/
def dvrPowerIdealUnitInverseLimit_eval
      (n : ℕ) :
    dvrPowerIdealUnitInverseLimit π →*
      (O ⧸ uniformizerPowerIdeal π (n + 1))ˣ where
  toFun x :=
    (dvrPowerIdealUnitInverseLimitCompatibleFamiliesEquiv π x).1 n
  map_one' := rfl
  map_mul' _ _ := rfl














/-- The finite quotient-unit stage for `(π)^(n+1)` agrees with the canonical
stage `π^(n+1)O`. -/
def powerIdealStageEquiv
      (n : ℕ) :
    (O ⧸ (uniformizerPowerIdeal π 1) ^ (n + 1))ˣ ≃*
      (O ⧸ uniformizerPowerIdeal π (n + 1))ˣ :=
  Units.mapEquiv
    (Ideal.quotientEquivAlgOfEq O
      (dvrPowerIdeal_one_pow π (n + 1))).toRingEquiv.toMulEquiv












/-- The stage equivalences commute with the projective transition maps. -/
theorem powerIdealStageEquiv_factorPow
      {m n : ℕ} (hmn : m ≤ n)
    (x : O ⧸ (uniformizerPowerIdeal π 1) ^ (n + 1)) :
    (Ideal.quotientEquivAlgOfEq O
      (dvrPowerIdeal_one_pow π (m + 1)))
        (Ideal.Quotient.factorPow (uniformizerPowerIdeal π 1)
          (Nat.succ_le_succ hmn) x) =
      dvrPowerIdealUnitTransition π hmn
        ((Ideal.quotientEquivAlgOfEq O
          (dvrPowerIdeal_one_pow π (n + 1))) x) := by
  refine Quotient.inductionOn' x ?_
  intro r
  rfl

/-- The positive-indexed unit inverse limit for the principal ideal `(π)` is
the finite quotient-unit inverse limit `lim_n (O/π^(n+1)O)ˣ`. -/
def adicPositiveUnitInverseLimitEquivDVRPowerIdealUnitInverseLimit
      :
    adicPositiveUnitInverseLimit (uniformizerPowerIdeal π 1) ≃*
      dvrPowerIdealUnitInverseLimit π :=
  (adicPositiveUnitInverseLimitRepresentation
      (uniformizerPowerIdeal π 1)).trans
    ((compatibleGroupFamiliesMulEquiv
      (fun n : ℕ => (O ⧸ (uniformizerPowerIdeal π 1) ^ (n + 1))ˣ)
      (fun n : ℕ => (O ⧸ uniformizerPowerIdeal π (n + 1))ˣ)
      (fun {_ _} hmn =>
        Units.map
          (Ideal.Quotient.factorPow (uniformizerPowerIdeal π 1)
            (Nat.succ_le_succ hmn)).toMonoidHom)
      (fun {_ _} hmn =>
        Units.map
          (dvrPowerIdealUnitTransition π hmn).toMonoidHom)
      (fun n => powerIdealStageEquiv π n)
      (by
        intro m n hmn u
        apply Units.ext
        exact (powerIdealStageEquiv_factorPow π hmn (u : _)).symm)).trans
      (dvrPowerIdealUnitInverseLimitRepresentation π).symm)

/-- Transition map on the positive-indexed quotients `Oˣ/U^(n+1)`. -/
def dvrHigherUnitQuotientTransition
      {m n : ℕ} (hmn : m ≤ n) :
    Oˣ ⧸ higherUnitSubgroup π (n + 1) →*
      Oˣ ⧸ higherUnitSubgroup π (m + 1) :=
  QuotientGroup.map _ _ (MonoidHom.id Oˣ) <| by
    intro u hu
    exact higherUnitSubgroup_le_of_le π (Nat.succ_le_succ hmn) hu

 theorem dvrHigherUnitQuotientTransition_mk
      {m n : ℕ} (hmn : m ≤ n) (u : Oˣ) :
    dvrHigherUnitQuotientTransition π hmn
        (u : Oˣ ⧸ higherUnitSubgroup π (n + 1)) =
      (u : Oˣ ⧸ higherUnitSubgroup π (m + 1)) := by
  rfl
end


/-- A higher-unit quotient with discreteness fixed in its type. -/
structure DiscreteHigherUnitQuotient
    {O : Type*} [CommRing O] (π : O) (n : ℕ) where
  /-- The underlying higher-unit quotient class. -/
  val : Oˣ ⧸ higherUnitSubgroup π n

namespace DiscreteHigherUnitQuotient

/-- Defines `equiv`. -/
def equiv {O : Type*} [CommRing O] (π : O) (n : ℕ) :
    DiscreteHigherUnitQuotient π n ≃
      Oˣ ⧸ higherUnitSubgroup π n where
  toFun := val
  invFun := fun x => ⟨x⟩
  left_inv := fun x => by cases x; rfl
  right_inv := fun _ => rfl

/-- A discrete higher-unit quotient inherits its commutative group structure
from the concrete quotient. -/
instance {O : Type*} [CommRing O] (π : O) (n : ℕ) :
    CommGroup (DiscreteHigherUnitQuotient π n) :=
  (equiv π n).commGroup

/-- Each higher-unit quotient is equipped with the discrete topology. -/
instance {O : Type*} [CommRing O] (π : O) (n : ℕ) :
    TopologicalSpace (DiscreteHigherUnitQuotient π n) := ⊥

/-- The chosen topology on a higher-unit quotient is discrete. -/
instance {O : Type*} [CommRing O] (π : O) (n : ℕ) :
    DiscreteTopology (DiscreteHigherUnitQuotient π n) :=
  ⟨rfl⟩

section
variable {O : Type*} [CommRing O] (π : O) (n : ℕ)
include O π n
/-- Defines `of`. -/
def of  
    (x : Oˣ ⧸ higherUnitSubgroup π n) :
    DiscreteHigherUnitQuotient π n :=
  ⟨x⟩

/-- Forgetting the discrete wrapper after inserting a quotient element recovers that element. -/
@[simp]
theorem val_of  
    (x : Oˣ ⧸ higherUnitSubgroup π n) : (of π n x).val = x :=
  rfl

/-- Defines `homeomorph`. -/
def homeomorph   :
    @Homeomorph (DiscreteHigherUnitQuotient π n)
      (Oˣ ⧸ higherUnitSubgroup π n)
      (inferInstance : TopologicalSpace
        (DiscreteHigherUnitQuotient π n))
      (⊥ : TopologicalSpace (Oˣ ⧸ higherUnitSubgroup π n)) := by
  letI : TopologicalSpace (Oˣ ⧸ higherUnitSubgroup π n) := ⊥
  letI : DiscreteTopology (Oˣ ⧸ higherUnitSubgroup π n) := ⟨rfl⟩
  exact
    { toEquiv := equiv π n
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := continuous_of_discreteTopology }

/-- The discrete comparison homeomorphism acts as the underlying quotient equivalence. -/
@[simp]
theorem homeomorph_apply  
    (x : DiscreteHigherUnitQuotient π n) : homeomorph π n x = x.val :=
  rfl

/-- The inverse discrete quotient equivalence wraps the concrete quotient element. -/
@[simp]
theorem equiv_symm_apply   (x : Oˣ ⧸ higherUnitSubgroup π n) :
    (equiv π n).symm x = of π n x :=
  rfl
end


end DiscreteHigherUnitQuotient

/-- The opaque direct quotient-system object `lim_n Oˣ/U^(n+1)`. -/
def dvrHigherUnitQuotientInverseLimit
    {O : Type*} [CommRing O] (π : O) : Type _ :=
  compatibleGroupFamilies
    (fun n : ℕ => Oˣ ⧸ higherUnitSubgroup π (n + 1))
    (fun {_ _} hmn => dvrHigherUnitQuotientTransition π hmn)

/-- Defines `dvrHigherUnitQuotientInverseLimitCompatibleFamiliesEquiv`. -/
def dvrHigherUnitQuotientInverseLimitCompatibleFamiliesEquiv
    {O : Type*} [CommRing O] (π : O) :
    dvrHigherUnitQuotientInverseLimit π ≃
      compatibleGroupFamilies
        (fun n : ℕ => Oˣ ⧸ higherUnitSubgroup π (n + 1))
        (fun {_ _} hmn => dvrHigherUnitQuotientTransition π hmn) := by
  unfold dvrHigherUnitQuotientInverseLimit
  exact Equiv.refl _

/-- The inverse limit of higher-unit quotients is a commutative group. -/
instance dvrHigherUnitQuotientInverseLimit.instCommGroup
    {O : Type*} [CommRing O] (π : O) :
    CommGroup (dvrHigherUnitQuotientInverseLimit π) :=
  (dvrHigherUnitQuotientInverseLimitCompatibleFamiliesEquiv π).commGroup

section
variable {O : Type*} [CommRing O] (π : O)
include O π
/-- Defines `dvrHigherUnitQuotientInverseLimitRepresentation`. -/
def dvrHigherUnitQuotientInverseLimitRepresentation
      :
    dvrHigherUnitQuotientInverseLimit π ≃*
      compatibleGroupFamilies
        (fun n : ℕ => Oˣ ⧸ higherUnitSubgroup π (n + 1))
        (fun {_ _} hmn => dvrHigherUnitQuotientTransition π hmn) :=
  (dvrHigherUnitQuotientInverseLimitCompatibleFamiliesEquiv π).mulEquiv

section
variable (x : ∀ n : ℕ, Oˣ ⧸ higherUnitSubgroup π (n + 1))
    (compatible : ∀ {m n : ℕ} (hmn : m ≤ n),
      dvrHigherUnitQuotientTransition π hmn (x n) = x m)
include x compatible in
/-- Defines `dvrHigherUnitQuotientInverseLimit_mk`. -/
def dvrHigherUnitQuotientInverseLimit_mk
     
       :=
  (dvrHigherUnitQuotientInverseLimitCompatibleFamiliesEquiv π).symm
    ⟨x, compatible⟩

/-- Defines `dvrHigherUnitQuotientInverseLimit_eval`. -/
def dvrHigherUnitQuotientInverseLimit_eval
      (n : ℕ) :
    dvrHigherUnitQuotientInverseLimit π →*
      Oˣ ⧸ higherUnitSubgroup π (n + 1) where
  toFun x :=
    (dvrHigherUnitQuotientInverseLimitCompatibleFamiliesEquiv π x).1 n
  map_one' := rfl
  map_mul' _ _ := rfl

include x compatible in
/-- Evaluation of a higher-unit inverse-limit family returns its selected quotient component. -/
@[simp]
theorem dvrHigherUnitQuotientInverseLimit_eval_mk
     
     
    (n : ℕ) :
    dvrHigherUnitQuotientInverseLimit_eval π n
        (dvrHigherUnitQuotientInverseLimit_mk π x compatible) = x n := rfl
end


/-- Higher-unit inverse-limit elements are determined by their evaluations at every level. -/
@[ext]
theorem dvrHigherUnitQuotientInverseLimit_ext
     
    {x y : dvrHigherUnitQuotientInverseLimit π}
    (h : ∀ n : ℕ, dvrHigherUnitQuotientInverseLimit_eval π n x =
      dvrHigherUnitQuotientInverseLimit_eval π n y) :
    x = y := by
  apply (dvrHigherUnitQuotientInverseLimitCompatibleFamiliesEquiv π).injective
  apply Subtype.ext
  funext n
  exact h n
end












/-- The higher-unit inverse limit carries the topology induced by its discrete coordinates. -/
noncomputable instance dvrHigherUnitQuotientInverseLimit.instTopologicalSpace
    {O : Type*} [CommRing O] (π : O) :
    TopologicalSpace (dvrHigherUnitQuotientInverseLimit π) := by
  letI : (n : ℕ) → TopologicalSpace
      (Oˣ ⧸ higherUnitSubgroup π (n + 1)) := fun _ => ⊥
  exact
    (dvrHigherUnitQuotientInverseLimitCompatibleFamiliesEquiv π).topologicalSpace

 noncomputable def
    dvrHigherUnitQuotientInverseLimitRepresentationHomeomorph
    {O : Type*} [CommRing O] (π : O) :
    letI : (n : ℕ) → TopologicalSpace
      (Oˣ ⧸ higherUnitSubgroup π (n + 1)) := fun _ => ⊥
    dvrHigherUnitQuotientInverseLimit π ≃ₜ
      compatibleGroupFamilies
        (fun n : ℕ => Oˣ ⧸ higherUnitSubgroup π (n + 1))
        (fun {_ _} hmn => dvrHigherUnitQuotientTransition π hmn) := by
  letI : (n : ℕ) → TopologicalSpace
      (Oˣ ⧸ higherUnitSubgroup π (n + 1)) := fun _ => ⊥
  exact
    (dvrHigherUnitQuotientInverseLimitCompatibleFamiliesEquiv π).homeomorph

/-- Defines `dvrHigherUnitQuotientInverseLimit_discreteEval`. -/
def dvrHigherUnitQuotientInverseLimit_discreteEval
    {O : Type*} [CommRing O] (π : O) (n : ℕ)  :=
  fun x => DiscreteHigherUnitQuotient.of π (n + 1)
    (dvrHigherUnitQuotientInverseLimit_eval π n x)

/-- Every coordinate evaluation from the higher-unit inverse limit to its
discrete quotient is continuous. -/
theorem dvrHigherUnitQuotientInverseLimit_discreteEval_continuous
    {O : Type*} [CommRing O] (π : O) (n : ℕ) :
    Continuous (dvrHigherUnitQuotientInverseLimit_discreteEval π n) := by
  let : (n : ℕ) → TopologicalSpace
      (Oˣ ⧸ higherUnitSubgroup π (n + 1)) := fun _ => ⊥
  let representation :=
    dvrHigherUnitQuotientInverseLimitRepresentationHomeomorph π
  have hraw : Continuous fun x : dvrHigherUnitQuotientInverseLimit π =>
      (dvrHigherUnitQuotientInverseLimitCompatibleFamiliesEquiv π x).1 n :=
    (continuous_apply n).comp
      (continuous_subtype_val.comp representation.continuous)
  have hmodel :=
    (DiscreteHigherUnitQuotient.homeomorph π (n + 1)).symm.continuous.comp
      hraw
  assumption

/-- A map into the higher-unit inverse limit is continuous exactly when all
of its named discrete coordinates are continuous.  This is the public
universal property of the canonical prodiscrete topology; raw quotient
topology instances remain confined to the proof. -/
theorem dvrHigherUnitQuotientInverseLimit_continuous_iff
    {O : Type*} [CommRing O] {α : Type*} [TopologicalSpace α]
    (π : O) (f : α → dvrHigherUnitQuotientInverseLimit π) :
    Continuous f ↔
      ∀ n : ℕ, Continuous fun x =>
        dvrHigherUnitQuotientInverseLimit_discreteEval π n (f x) := by
  constructor
  · intro hf n
    exact
      (dvrHigherUnitQuotientInverseLimit_discreteEval_continuous π n).comp hf
  · intro h
    let : (n : ℕ) → TopologicalSpace
        (Oˣ ⧸ higherUnitSubgroup π (n + 1)) := fun _ => ⊥
    let : (n : ℕ) → DiscreteTopology
        (Oˣ ⧸ higherUnitSubgroup π (n + 1)) := fun _ => ⟨rfl⟩
    let representation :=
      dvrHigherUnitQuotientInverseLimitRepresentationHomeomorph π
    have hrepresentation : Continuous fun x => representation (f x) :=
      Continuous.subtype_mk
        (continuous_pi fun n => by
          have hraw :=
            (DiscreteHigherUnitQuotient.homeomorph π (n + 1)).continuous.comp
              (h n)
          change Continuous fun x =>
            dvrHigherUnitQuotientInverseLimit_eval π n (f x)
          exact hraw)
        (fun x => by
          grind)
    have hback := representation.symm.continuous.comp hrepresentation
    apply hback.congr <;> aesop

/-- The canonical homomorphism
`Oˣ → lim_n Oˣ/U^(n+1)`. -/
def unitsToHigherUnitQuotientInverseLimit
    {O : Type*} [CommRing O] (π : O) :
    Oˣ →* dvrHigherUnitQuotientInverseLimit π where
  toFun u := dvrHigherUnitQuotientInverseLimit_mk π
    (fun _ => QuotientGroup.mk u)
    (fun {m n} hmn =>
      dvrHigherUnitQuotientTransition_mk π (m := m) (n := n) hmn u)
  map_one' := by ext n; rfl
  map_mul' u v := by ext n; rfl

section
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {π : O} (hπ : Irreducible π)
include O π hπ
/-- The finite-stage isomorphisms
`Oˣ/U^(n+1) ≃ (O/π^(n+1)O)ˣ` commute with the projective transition maps. -/
theorem higherUnitQuotient_finiteStage_compat
      {m n : ℕ} (hmn : m ≤ n)
    (q : Oˣ ⧸ higherUnitSubgroup π (n + 1)) :
    units_quotient_equiv hπ
        (Nat.succ_pos m)
        (dvrHigherUnitQuotientTransition π hmn q) =
      Units.map (dvrPowerIdealUnitTransition π hmn).toMonoidHom
        (units_quotient_equiv hπ
          (Nat.succ_pos n) q) := by
  refine QuotientGroup.induction_on q ?_
  intro u
  rw [dvrHigherUnitQuotientTransition_mk]
  ext
  simp [units_quotient_equiv_mk,
    dvrPowerIdealUnitTransition, unitReduction]

/-- The direct quotient-system `lim Oˣ/U^(n+1)` is equivalent to the finite
quotient-unit limit `lim (O/π^(n+1)O)ˣ`. -/
def higherUnitQuotientInverseLimitEquivPowerIdealUnitInverseLimit
      :
    dvrHigherUnitQuotientInverseLimit π ≃*
      dvrPowerIdealUnitInverseLimit π :=
  (dvrHigherUnitQuotientInverseLimitRepresentation π).trans
    ((compatibleGroupFamiliesMulEquiv
      (fun n : ℕ => Oˣ ⧸ higherUnitSubgroup π (n + 1))
      (fun n : ℕ => (O ⧸ uniformizerPowerIdeal π (n + 1))ˣ)
      (fun {_ _} hmn => dvrHigherUnitQuotientTransition π hmn)
      (fun {_ _} hmn =>
        Units.map
          (dvrPowerIdealUnitTransition π hmn).toMonoidHom)
      (fun n => units_quotient_equiv hπ
        (Nat.succ_pos n))
      (by
        intro m n hmn q
        exact (higherUnitQuotient_finiteStage_compat
          hπ hmn q).symm)).trans
      (dvrPowerIdealUnitInverseLimitRepresentation π).symm)

/-- The adic inverse-limit equivalence, direct unit-quotient form:
if `O` is complete for the `(π)`-adic topology, then `Oˣ` is isomorphic to
the projective limit `lim_n Oˣ/U^(n+1)`. -/
def dvrUnitsEquivHigherUnitQuotientInverseLimit
      [IsAdicComplete (uniformizerPowerIdeal π 1) O]  :=
  ((unitsEquivPositiveUnitInverseLimit (uniformizerPowerIdeal π 1)).trans
    (adicPositiveUnitInverseLimitEquivDVRPowerIdealUnitInverseLimit π)).trans
    (higherUnitQuotientInverseLimitEquivPowerIdealUnitInverseLimit hπ).symm

/-- The direct unit-quotient inverse-limit isomorphism is the canonical
map, coordinatewise `u ↦ u mod U^(n+1)`. -/
theorem dvrUnitsEquivHigherUnitQuotientInverseLimit_apply
      [IsAdicComplete (uniformizerPowerIdeal π 1) O]
    (u : Oˣ) (n : ℕ) :
    dvrHigherUnitQuotientInverseLimit_eval π n
        (dvrUnitsEquivHigherUnitQuotientInverseLimit hπ u) =
      QuotientGroup.mk u := by
  apply
    (units_quotient_equiv hπ
      (Nat.succ_pos n)).injective
  change units_quotient_equiv hπ (Nat.succ_pos n)
      (dvrHigherUnitQuotientInverseLimit_eval π n
        (dvrUnitsEquivHigherUnitQuotientInverseLimit hπ u)) =
    units_quotient_equiv hπ (Nat.succ_pos n)
      (QuotientGroup.mk u)
  rw [units_quotient_equiv_mk]
  change dvrPowerIdealUnitInverseLimit_eval π n
      ((higherUnitQuotientInverseLimitEquivPowerIdealUnitInverseLimit hπ)
        (dvrUnitsEquivHigherUnitQuotientInverseLimit hπ u)) =
    unitReduction (uniformizerPowerIdeal π (n + 1)) u
  simp [dvrUnitsEquivHigherUnitQuotientInverseLimit,
    adicPositiveUnitInverseLimitEquivDVRPowerIdealUnitInverseLimit,
    unitReduction]
  ext
  change (Ideal.quotientEquivAlgOfEq O
      (dvrPowerIdeal_one_pow π (n + 1)))
        (Ideal.Quotient.mk ((uniformizerPowerIdeal π 1) ^ (n + 1)) (u : O)) =
    Ideal.Quotient.mk (uniformizerPowerIdeal π (n + 1)) (u : O)
  rw [Ideal.quotientEquivAlgOfEq_mk]
end


section
variable {O : Type*} [CommRing O]
include O
/-- Equality in the finite higher-unit quotient is exactly congruence modulo
`π^nO` on the underlying elements. -/
theorem higherUnitQuotient_mk_eq_mk_iff_sub_mem
      (π : O) (n : ℕ) (u v : Oˣ) :
    (QuotientGroup.mk v : Oˣ ⧸ higherUnitSubgroup π n) =
        QuotientGroup.mk u ↔
      (v : O) - (u : O) ∈ uniformizerPowerIdeal π n := by
  constructor
  · intro h
    have hdiv : v / u ∈ higherUnitSubgroup π n := (QuotientGroup.eq_iff_div_mem
        (N := higherUnitSubgroup π n) (x := v) (y := u)).1 h
    have hmem  :=
      (mem_higherUnitSubgroup_iff_sub_one_mem_powerIdeal
        (π := π) (n := n) (u := v / u)).1 hdiv
    have hmul  :=
      (uniformizerPowerIdeal π n).mul_mem_right (u : O) hmem
    have hcalc :
        (((v / u : Oˣ) : O) - 1) * (u : O) = (v : O) - (u : O) := by
      calc
        (((v / u : Oˣ) : O) - 1) * (u : O)
            = ((v : O) * ((u⁻¹ : Oˣ) : O) - 1) * (u : O) := rfl
        _ = (v : O) * (((u⁻¹ : Oˣ) : O) * (u : O)) - (u : O) := by ring
        _ = (v : O) - (u : O) := by simp
    simpa [hcalc] using hmul
  · intro hsub
    have hmem :
        ((v / u : Oˣ) : O) - 1 ∈ uniformizerPowerIdeal π n := by
      have hmul  :=
        (uniformizerPowerIdeal π n).mul_mem_right ((u⁻¹ : Oˣ) : O) hsub
      convert hmul using 1
      calc
        ((v / u : Oˣ) : O) - 1
            = (v : O) * ((u⁻¹ : Oˣ) : O) - 1 := rfl
        _ = (v : O) * ((u⁻¹ : Oˣ) : O) -
              (u : O) * ((u⁻¹ : Oˣ) : O) := by simp
        _ = ((v : O) - (u : O)) * ((u⁻¹ : Oˣ) : O) := by ring
    have hdiv  :=
      (mem_higherUnitSubgroup_iff_sub_one_mem_powerIdeal
        (π := π) (n := n) (u := v / u)).2 hmem
    exact (QuotientGroup.eq_iff_div_mem
      (N := higherUnitSubgroup π n) (x := v) (y := u)).2 hdiv

/-- The topology on a unit group induced by an explicitly chosen adic
topology on its ring. -/
@[reducible]
noncomputable def adicUnitsTopology
      (I : Ideal O) : TopologicalSpace Oˣ := by
  letI  := I.adicTopology
  exact inferInstance

/-- Reduction to a higher-unit quotient is continuous for the adic topology
on `Oˣ` and the discrete topology on the finite quotient. -/
 theorem higherUnitQuotient_mk_continuous_adic_raw
      (π : O) (n : ℕ) :
    @Continuous Oˣ (Oˣ ⧸ higherUnitSubgroup π n)
      (adicUnitsTopology (uniformizerPowerIdeal π 1))
      (⊥ : TopologicalSpace (Oˣ ⧸ higherUnitSubgroup π n))
      (fun u : Oˣ =>
        (QuotientGroup.mk u : Oˣ ⧸ higherUnitSubgroup π n)) := by
  let  := (uniformizerPowerIdeal π 1).adicTopology
  let : TopologicalSpace (Oˣ ⧸ higherUnitSubgroup π n) := ⊥
  let : DiscreteTopology (Oˣ ⧸ higherUnitSubgroup π n) := ⟨rfl⟩
  rw [continuous_iff_continuousAt]
  intro u
  change Filter.Tendsto
    (fun v : Oˣ => (QuotientGroup.mk v :
      Oˣ ⧸ higherUnitSubgroup π n)) (𝓝 u)
    (𝓝 (QuotientGroup.mk u : Oˣ ⧸ higherUnitSubgroup π n))
  rw [@nhds_discrete (Oˣ ⧸ higherUnitSubgroup π n) _ _]
  rw [Filter.tendsto_def]
  intro s hs
  rw [mem_pure] at hs
  let ball  :=
    (fun y => (u : O) + y) ''
      (((uniformizerPowerIdeal π 1) ^ n : Ideal O) : Set O)
  have hball : ball ∈ 𝓝 (u : O) :=
    (Ideal.hasBasis_nhds_adic (uniformizerPowerIdeal π 1) (u : O)).mem_iff.mpr
      ⟨n, trivial, subset_rfl⟩
  have hpre : {v : Oˣ | (v : O) ∈ ball} ∈ 𝓝 u :=
    Units.continuous_val.continuousAt hball
  exact mem_of_superset hpre (by
    intro v hv
    rcases hv with ⟨z, hz, hzv⟩
    have hsub : (v : O) - (u : O) ∈ uniformizerPowerIdeal π n := by
      rw [← dvrPowerIdeal_one_pow π n]
      have hz_eq : (v : O) - (u : O) = z := by
        rw [← hzv]
        ring
      simpa [hz_eq] using hz
    have hq  :=
      (higherUnitQuotient_mk_eq_mk_iff_sub_mem
        π n u v).2 hsub
    simpa [hq] using hs)
end





























 section
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {π : O} (hπ : Irreducible π) [IsAdicComplete (uniformizerPowerIdeal π 1) O]
include O π hπ
noncomputable def unitsCompatibleFamiliesHomeomorph
      :
    letI : TopologicalSpace O := (uniformizerPowerIdeal π 1).adicTopology
    letI : (n : ℕ) →
      TopologicalSpace (Oˣ ⧸ higherUnitSubgroup π (n + 1)) := fun _ => ⊥
    Oˣ ≃ₜ compatibleGroupFamilies
      (fun n : ℕ => Oˣ ⧸ higherUnitSubgroup π (n + 1))
      (fun {_ _} hmn => dvrHigherUnitQuotientTransition π hmn) := by
  letI  := (uniformizerPowerIdeal π 1).adicTopology
  letI : (n : ℕ) →
      TopologicalSpace (Oˣ ⧸ higherUnitSubgroup π (n + 1)) := fun _ => ⊥
  letI : (n : ℕ) →
      DiscreteTopology (Oˣ ⧸ higherUnitSubgroup π (n + 1)) :=
    fun _ => ⟨rfl⟩
  let e := (dvrUnitsEquivHigherUnitQuotientInverseLimit hπ).trans
    (dvrHigherUnitQuotientInverseLimitRepresentation π)
  let c := (dvrHigherUnitQuotientInverseLimitRepresentation π).toMonoidHom.comp
    (unitsToHigherUnitQuotientInverseLimit π)
  refine
    { toFun := fun u => c u
      invFun := fun q => e.symm q
      left_inv := ?_
      right_inv := ?_
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · intro u
    have hc : c u = e u := by
      ext n
      exact (dvrUnitsEquivHigherUnitQuotientInverseLimit_apply
        hπ u n).symm
    change e.symm (c u) = u
    rw [hc]
    exact e.left_inv u
  · intro q
    ext n
    change (QuotientGroup.mk (e.symm q) :
        Oˣ ⧸ higherUnitSubgroup π (n + 1)) = q.1 n
    calc
      (QuotientGroup.mk (e.symm q) :
          Oˣ ⧸ higherUnitSubgroup π (n + 1)) =
          (e (e.symm q)).1 n :=
        (dvrUnitsEquivHigherUnitQuotientInverseLimit_apply
          hπ (e.symm q) n).symm
      _ = q.1 n := by simp [e.apply_symm_apply q]
  · change Continuous fun u : Oˣ => c u
    exact Continuous.subtype_mk
      (continuous_pi fun n => by
        apply higherUnitQuotient_mk_continuous_adic_raw)
      (by
        intro u m n hmn
        apply dvrHigherUnitQuotientTransition_mk)
  · apply Units.continuous_iff.mpr
    constructor
    · rw [continuous_iff_continuousAt]
      intro q
      rw [ContinuousAt, Filter.tendsto_def]
      intro s hs
      rcases (Ideal.hasBasis_nhds_adic (uniformizerPowerIdeal π 1)
          ((e.symm q : Oˣ) : O)).mem_iff.mp hs with
        ⟨n, _hn, hns⟩
      let cylinder : Set (compatibleGroupFamilies
          (fun n : ℕ => Oˣ ⧸ higherUnitSubgroup π (n + 1))
          (fun {_ _} hmn => dvrHigherUnitQuotientTransition π hmn)) :=
        {q' | q'.1 n = q.1 n}
      have hcont_coord :
          Continuous fun q' : compatibleGroupFamilies
              (fun n : ℕ => Oˣ ⧸ higherUnitSubgroup π (n + 1))
              (fun {_ _} hmn => dvrHigherUnitQuotientTransition π hmn) =>
            q'.1 n := (continuous_apply n).comp continuous_subtype_val
      have hcyl_open : IsOpen cylinder := (isOpen_discrete
            ({q.1 n} : Set (Oˣ ⧸ higherUnitSubgroup π (n + 1)))).preimage
              hcont_coord
      have hqmem : q ∈ cylinder := rfl
      exact mem_of_superset (hcyl_open.mem_nhds hqmem) (by
        intro q' hq'
        apply hns
        have hmk :
            (QuotientGroup.mk (e.symm q') :
                Oˣ ⧸ higherUnitSubgroup π (n + 1)) =
              QuotientGroup.mk (e.symm q) := by
          calc
            (QuotientGroup.mk (e.symm q') :
                Oˣ ⧸ higherUnitSubgroup π (n + 1)) =
                (e (e.symm q')).1 n :=
              (dvrUnitsEquivHigherUnitQuotientInverseLimit_apply
                hπ (e.symm q') n).symm
            _ = q'.1 n := by simp [e.apply_symm_apply q']
            _ = q.1 n := hq'
            _ = (e (e.symm q)).1 n := by simp [e.apply_symm_apply q]
            _ = QuotientGroup.mk (e.symm q) :=
              dvrUnitsEquivHigherUnitQuotientInverseLimit_apply
                hπ (e.symm q) n
        have hsub_succ  :=
          (higherUnitQuotient_mk_eq_mk_iff_sub_mem
            π (n + 1) (e.symm q) (e.symm q')).1 hmk
        have hsub :
            ((e.symm q' : Oˣ) : O) - ((e.symm q : Oˣ) : O) ∈
              (uniformizerPowerIdeal π 1) ^ n := by
          rw [dvrPowerIdeal_one_pow π n]
          exact dvrPowerIdeal_le_of_le π (Nat.le_succ n) hsub_succ
        refine ⟨((e.symm q' : Oˣ) : O) - ((e.symm q : Oˣ) : O), hsub, ?_⟩
        change ((e.symm q : Oˣ) : O) +
            (((e.symm q' : Oˣ) : O) - ((e.symm q : Oˣ) : O)) =
          ((e.symm q' : Oˣ) : O)
        ring)
    · rw [continuous_iff_continuousAt]
      intro q
      rw [ContinuousAt, Filter.tendsto_def]
      intro s hs
      rcases (Ideal.hasBasis_nhds_adic (uniformizerPowerIdeal π 1)
          (((e.symm q)⁻¹ : Oˣ) : O)).mem_iff.mp hs with
        ⟨n, _hn, hns⟩
      let cylinder : Set (compatibleGroupFamilies
          (fun n : ℕ => Oˣ ⧸ higherUnitSubgroup π (n + 1))
          (fun {_ _} hmn => dvrHigherUnitQuotientTransition π hmn)) :=
        {q' | q'.1 n = q.1 n}
      have hcont_coord :
          Continuous fun q' : compatibleGroupFamilies
              (fun n : ℕ => Oˣ ⧸ higherUnitSubgroup π (n + 1))
              (fun {_ _} hmn => dvrHigherUnitQuotientTransition π hmn) =>
            q'.1 n := (continuous_apply n).comp continuous_subtype_val
      have hcyl_open : IsOpen cylinder := (isOpen_discrete
            ({q.1 n} : Set (Oˣ ⧸ higherUnitSubgroup π (n + 1)))).preimage
              hcont_coord
      have hqmem : q ∈ cylinder := rfl
      exact mem_of_superset (hcyl_open.mem_nhds hqmem) (by
        intro q' hq'
        apply hns
        have hmk :
            (QuotientGroup.mk (e.symm q') :
                Oˣ ⧸ higherUnitSubgroup π (n + 1)) =
              QuotientGroup.mk (e.symm q) := by
          calc
            (QuotientGroup.mk (e.symm q') :
                Oˣ ⧸ higherUnitSubgroup π (n + 1)) =
                (e (e.symm q')).1 n :=
              (dvrUnitsEquivHigherUnitQuotientInverseLimit_apply
                hπ (e.symm q') n).symm
            _ = q'.1 n := by simp [e.apply_symm_apply q']
            _ = q.1 n := hq'
            _ = (e (e.symm q)).1 n := by simp [e.apply_symm_apply q]
            _ = QuotientGroup.mk (e.symm q) :=
              dvrUnitsEquivHigherUnitQuotientInverseLimit_apply
                hπ (e.symm q) n
        have hinv_mk :
            (QuotientGroup.mk ((e.symm q')⁻¹ : Oˣ) :
                Oˣ ⧸ higherUnitSubgroup π (n + 1)) =
              QuotientGroup.mk ((e.symm q)⁻¹ : Oˣ) := congrArg Inv.inv hmk
        have hinv_sub_succ  :=
          (higherUnitQuotient_mk_eq_mk_iff_sub_mem
            π (n + 1) ((e.symm q)⁻¹ : Oˣ) ((e.symm q')⁻¹ : Oˣ)).1 hinv_mk
        have hinv_sub :
            (((e.symm q')⁻¹ : Oˣ) : O) - (((e.symm q)⁻¹ : Oˣ) : O) ∈
              (uniformizerPowerIdeal π 1) ^ n := by
          rw [dvrPowerIdeal_one_pow π n]
          exact dvrPowerIdeal_le_of_le π (Nat.le_succ n)
            hinv_sub_succ
        refine
          ⟨(((e.symm q')⁻¹ : Oˣ) : O) - (((e.symm q)⁻¹ : Oˣ) : O),
            hinv_sub, ?_⟩
        change (((e.symm q)⁻¹ : Oˣ) : O) +
            ((((e.symm q')⁻¹ : Oˣ) : O) - (((e.symm q)⁻¹ : Oˣ) : O)) =
          (((e.symm q')⁻¹ : Oˣ) : O)
        ring)

/-- The unit-group inverse-limit homeomorphism with the adic source and
prodiscrete target fixed at the type level. -/
noncomputable def unitsEquivHigherUnitQuotientInverseLimitHomeomorph
      :
    WithTopology Oˣ
        (adicUnitsTopology (uniformizerPowerIdeal π 1)) ≃ₜ
      dvrHigherUnitQuotientInverseLimit π := by
  letI  := (uniformizerPowerIdeal π 1).adicTopology
  letI : (n : ℕ) → TopologicalSpace
      (Oˣ ⧸ higherUnitSubgroup π (n + 1)) := fun _ => ⊥
  let source := WithTopology.homeomorph
    (α := Oˣ)
    (topology := adicUnitsTopology (uniformizerPowerIdeal π 1))
  let algebraic := unitsCompatibleFamiliesHomeomorph hπ
  let target := dvrHigherUnitQuotientInverseLimitRepresentationHomeomorph π
  exact source.trans (algebraic.trans target.symm)
end



























































































































































/-! ### Direct complete-valued-field form of the adic inverse-limit equivalence -/























































































































































































































































end Valuations
end LubinTate

end
