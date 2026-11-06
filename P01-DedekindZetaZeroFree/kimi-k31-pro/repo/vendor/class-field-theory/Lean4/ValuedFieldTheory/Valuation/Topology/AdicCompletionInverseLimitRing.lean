module

public import ValuedFieldTheory.Valuation.ValuedAdicComplete
public import ValuedFieldTheory.Valuation.Topology.CompatibleInverseLimit
public import ValuedFieldTheory.Valuation.AbsoluteValue.Theory.Core
public import ValuedFieldTheory.Valuation.Topology.Models
public import Mathlib.Algebra.Ring.TransferInstance
public import Mathlib.Topology.Homeomorph.TransferInstance

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/








set_option autoImplicit false

/-!
# Adic completion and inverse limits

This file contains the algebraic and topological projective-limit descriptions
of adically complete rings, complete discrete valuation rings, and their unit
groups.
-/

noncomputable section

namespace LubinTate
namespace Valuations

open ValuationTheory.DiscreteValuationField
open ValuationTheory.Valuations
open Filter Set Topology
open scoped Valued

/-- The adic inverse-limit equivalence, algebraic form: an adically complete ring is canonically
isomorphic to its adic completion. -/
def adicCompletionAlgEquiv
    {R : Type*} [CommRing R] (I : Ideal R) [IsAdicComplete I R] :
    R ≃ₐ[R] AdicCompletion I R :=
  AdicCompletion.ofAlgEquiv I









/-- A finite adic quotient with its discrete topology fixed in the type. -/
structure DiscreteAdicQuotient
    {R : Type*} [CommRing R] (I : Ideal R) (n : ℕ) where
  /-- The underlying residue class modulo `I ^ n`. -/
  val : R ⧸ I ^ n

namespace DiscreteAdicQuotient

/-- Defines `equiv`. -/
def equiv {R : Type*} [CommRing R] (I : Ideal R) (n : ℕ) :
    DiscreteAdicQuotient I n ≃ R ⧸ I ^ n where
  toFun := val
  invFun := fun x => ⟨x⟩
  left_inv := fun x => by cases x; rfl
  right_inv := fun _ => rfl

/-- A discrete adic quotient inherits its commutative ring structure from the concrete quotient. -/
instance {R : Type*} [CommRing R] (I : Ideal R) (n : ℕ) :
    CommRing (DiscreteAdicQuotient I n) :=
  (equiv I n).commRing

/-- Each adic quotient is equipped with the discrete topology. -/
instance {R : Type*} [CommRing R] (I : Ideal R) (n : ℕ) :
    TopologicalSpace (DiscreteAdicQuotient I n) := ⊥

/-- The selected topology on an adic quotient is discrete. -/
instance {R : Type*} [CommRing R] (I : Ideal R) (n : ℕ) :
    DiscreteTopology (DiscreteAdicQuotient I n) :=
  ⟨rfl⟩

/-- Defines `of`. -/
def of {R : Type*} [CommRing R] (I : Ideal R) (n : ℕ)
    (x : R ⧸ I ^ n) : DiscreteAdicQuotient I n :=
  ⟨x⟩

/-- Forgetting the discrete adic wrapper after insertion recovers the original quotient element. -/
@[simp]
theorem val_of {R : Type*} [CommRing R] (I : Ideal R) (n : ℕ)
    (x : R ⧸ I ^ n) : (of I n x).val = x :=
  rfl

/-- The explicit boundary homeomorphism to the raw quotient equipped with
the discrete topology. -/
def homeomorph {R : Type*} [CommRing R] (I : Ideal R) (n : ℕ) :
    @Homeomorph (DiscreteAdicQuotient I n) (R ⧸ I ^ n)
      (inferInstance : TopologicalSpace (DiscreteAdicQuotient I n))
      (⊥ : TopologicalSpace (R ⧸ I ^ n)) := by
  letI : TopologicalSpace (R ⧸ I ^ n) := ⊥
  letI : DiscreteTopology (R ⧸ I ^ n) := ⟨rfl⟩
  exact
    { toEquiv := equiv I n
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := continuous_of_discreteTopology }

/-- The discrete adic homeomorphism evaluates as the underlying quotient equivalence. -/
@[simp]
theorem homeomorph_apply {R : Type*} [CommRing R] (I : Ideal R) (n : ℕ)
    (x : DiscreteAdicQuotient I n) : homeomorph I n x = x.val :=
  rfl

/-- The inverse quotient equivalence inserts a concrete quotient into its discrete copy. -/
@[simp]
theorem equiv_symm_apply {R : Type*} [CommRing R]
    (I : Ideal R) (n : ℕ) (x : R ⧸ I ^ n) :
    (equiv I n).symm x = of I n x :=
  rfl

end DiscreteAdicQuotient

/-- The adic inverse-limit object `lim_n R/I^n`.  This is an opaque public
type; its compatible-family implementation is exposed only through the named
equivalence and coordinate API below. -/
def adicQuotientInverseLimit
    {R : Type*} [CommRing R] (I : Ideal R) : Type _ :=
  compatibleRingFamilies (fun n : ℕ => R ⧸ I ^ n)
    (fun {_ _} hmn => Ideal.Quotient.factorPow I hmn)

/-- The implementation representation of the all-level adic inverse limit. -/
def adicQuotientInverseLimitCompatibleFamiliesEquiv
    {R : Type*} [CommRing R] (I : Ideal R) :
    adicQuotientInverseLimit I ≃
      compatibleRingFamilies (fun n : ℕ => R ⧸ I ^ n)
        (fun {_ _} hmn => Ideal.Quotient.factorPow I hmn) := by
  unfold adicQuotientInverseLimit
  exact Equiv.refl _

/-- Compatible adic quotient families form a commutative ring coordinatewise. -/
instance adicQuotientInverseLimit.instCommRing
    {R : Type*} [CommRing R] (I : Ideal R) :
    CommRing (adicQuotientInverseLimit I) :=
  (adicQuotientInverseLimitCompatibleFamiliesEquiv I).commRing



/-- Build an all-level adic inverse-limit point from a compatible family. -/
def adicQuotientInverseLimit_mk
    {R : Type*} [CommRing R] (I : Ideal R)
    (x : ∀ n : ℕ, R ⧸ I ^ n)
    (compatible : ∀ {m n : ℕ} (hmn : m ≤ n),
      Ideal.Quotient.factorPow I hmn (x n) = x m) :
    adicQuotientInverseLimit I :=
  (adicQuotientInverseLimitCompatibleFamiliesEquiv I).symm
    ⟨x, compatible⟩

/-- Coordinate evaluation from the explicit projective limit. -/
def adicQuotientInverseLimit_eval
    {R : Type*} [CommRing R] (I : Ideal R) (n : ℕ) :
    adicQuotientInverseLimit I →+* R ⧸ I ^ n where
  toFun x := (adicQuotientInverseLimitCompatibleFamiliesEquiv I x).1 n
  map_one' := by rfl
  map_mul' _ _ := by rfl
  map_zero' := by rfl
  map_add' _ _ := by rfl

/-- Evaluation of an adic inverse-limit family returns its component at the selected level. -/
@[simp]
theorem adicQuotientInverseLimit_eval_mk
    {R : Type*} [CommRing R] (I : Ideal R)
    (x : ∀ n : ℕ, R ⧸ I ^ n)
    (compatible : ∀ {m n : ℕ} (hmn : m ≤ n),
      Ideal.Quotient.factorPow I hmn (x n) = x m)
    (n : ℕ) :
    adicQuotientInverseLimit_eval I n
        (adicQuotientInverseLimit_mk I x compatible) = x n := by
  rfl

/-- Adic inverse-limit elements are equal when all coordinate evaluations agree. -/
@[ext]
theorem adicQuotientInverseLimit_ext
    {R : Type*} [CommRing R] (I : Ideal R)
    {x y : adicQuotientInverseLimit I}
    (h : ∀ n : ℕ, adicQuotientInverseLimit_eval I n x =
      adicQuotientInverseLimit_eval I n y) :
    x = y := by
  apply (adicQuotientInverseLimitCompatibleFamiliesEquiv I).injective
  apply Subtype.ext
  funext n
  exact h n

/-- The explicit projective-limit coordinates are compatible with quotient
transition maps. -/
theorem adicQuotientInverseLimit_eval_factorPow
    {R : Type*} [CommRing R] (I : Ideal R)
    {m n : ℕ} (hmn : m ≤ n)
    (x : adicQuotientInverseLimit I) :
    Ideal.Quotient.factorPow I hmn
        (adicQuotientInverseLimit_eval I n x) =
      adicQuotientInverseLimit_eval I m x :=
  (adicQuotientInverseLimitCompatibleFamiliesEquiv I x).2 hmn

/-- The canonical prodiscrete topology on the all-level inverse limit.  The
finite quotient stages are discrete inside this one representation boundary;
their raw topology instances do not escape into public theorem statements. -/
noncomputable instance adicQuotientInverseLimit.instTopologicalSpace
    {R : Type*} [CommRing R] (I : Ideal R) :
    TopologicalSpace (adicQuotientInverseLimit I) := by
  letI : (n : ℕ) → TopologicalSpace (R ⧸ I ^ n) := fun _ => ⊥
  exact (adicQuotientInverseLimitCompatibleFamiliesEquiv I).topologicalSpace

 





/-- The quotient algebra equivalence induced by equal ideals sends inverse
representatives as expected. -/
theorem quotientEquivAlgOfEq_apply_symm
    {R : Type*} [CommRing R] {I J : Ideal R}
    (h₁ h₂ : I = J) (y : R ⧸ J) :
    (Ideal.quotientEquivAlgOfEq R h₁)
      ((Ideal.quotientEquivAlgOfEq R h₂).symm y) = y := by
  refine Quotient.inductionOn' y ?_
  intro r
  rw [Ideal.quotientEquivAlgOfEq_symm]
  change (Ideal.quotientEquivAlgOfEq R h₁)
      ((Ideal.quotientEquivAlgOfEq R h₂.symm) (Ideal.Quotient.mk J r)) =
    Ideal.Quotient.mk J r
  rw [Ideal.quotientEquivAlgOfEq_mk]
  rw [Ideal.quotientEquivAlgOfEq_mk]

/-- Adic transition maps commute with quotient equivalences arising from equal powers. -/
theorem transitionMap_quotientEquivAlgOfEq
    {R : Type*} [CommRing R] (I : Ideal R)
    {m n : ℕ} (hmn : m ≤ n)
    (hm : (I ^ m • ⊤ : Ideal R) = I ^ m)
    (hn : (I ^ n • ⊤ : Ideal R) = I ^ n)
    (y : R ⧸ I ^ n) :
    (Ideal.quotientEquivAlgOfEq R hm)
      (AdicCompletion.transitionMap I R hmn
        ((Ideal.quotientEquivAlgOfEq R hn).symm y)) =
      Ideal.Quotient.factorPow I hmn y := by
  refine Quotient.inductionOn' y ?_
  intro r
  rw [Ideal.quotientEquivAlgOfEq_symm]
  change (Ideal.quotientEquivAlgOfEq R hm)
      (AdicCompletion.transitionMap I R hmn
        ((Ideal.quotientEquivAlgOfEq R hn.symm)
          (Ideal.Quotient.mk (I ^ n) r))) =
    Ideal.Quotient.factorPow I hmn (Ideal.Quotient.mk (I ^ n) r)
  rw [Ideal.quotientEquivAlgOfEq_mk]
  rw [AdicCompletion.transitionMap_ideal_mk]
  rw [Ideal.quotientEquivAlgOfEq_mk]
  rfl

/-- The finite quotient coordinates of an adic-completion point are compatible
under the transition maps. -/
theorem adicCompletion_eval_factorPow
    {R : Type*} [CommRing R] (I : Ideal R)
    {m n : ℕ} (hmn : m ≤ n) (z : AdicCompletion I R) :
    Ideal.Quotient.factorPow I hmn (AdicCompletion.evalₐ I n z) =
      AdicCompletion.evalₐ I m z := by
  rcases AdicCompletion.mk_surjective I R z with ⟨seq, rfl⟩
  simpa [AdicCompletion.evalₐ_mk, Ideal.Quotient.factorPow] using
    (AdicCompletion.Ideal.mk_eq_mk I hmn seq)

/-- The map from the adic completion to the explicit projective limit
`lim_n R/I^n`. -/
def adicCompletion_toQuotientInverseLimit
    {R : Type*} [CommRing R] (I : Ideal R) :
    AdicCompletion I R → adicQuotientInverseLimit I :=
  fun z =>
    adicQuotientInverseLimit_mk I
      (fun n => AdicCompletion.evalₐ I n z)
      (fun hmn => adicCompletion_eval_factorPow I hmn z)

/-- The inverse map from the explicit projective limit `lim_n R/I^n` to the
adic completion. -/
def adicQuotientInverseLimit_toCompletion
    {R : Type*} [CommRing R] (I : Ideal R) :
    adicQuotientInverseLimit I → AdicCompletion I R :=
  fun x =>
    ⟨fun n =>
      let h : (I ^ n • ⊤ : Ideal R) = I ^ n := by ext r; simp
      (Ideal.quotientEquivAlgOfEq R h).symm
        (adicQuotientInverseLimit_eval I n x),
    by
      intro m n hmn
      let hm : (I ^ m • ⊤ : Ideal R) = I ^ m := by ext r; simp
      let hn : (I ^ n • ⊤ : Ideal R) = I ^ n := by ext r; simp
      apply (Ideal.quotientEquivAlgOfEq R hm).injective
      rw [transitionMap_quotientEquivAlgOfEq I hmn hm hn]
      rw [quotientEquivAlgOfEq_apply_symm]
      exact adicQuotientInverseLimit_eval_factorPow I hmn x⟩

/-- The map from the adic inverse limit to the completion has the prescribed
residue at every level. -/
theorem adicQuotientInverseLimit_toCompletion_eval
    {R : Type*} [CommRing R] (I : Ideal R)
    (x : adicQuotientInverseLimit I) (n : ℕ) :
    AdicCompletion.evalₐ I n
        (adicQuotientInverseLimit_toCompletion I x) =
      adicQuotientInverseLimit_eval I n x := by
  change (Ideal.quotientEquivAlgOfEq R (by ext r; simp))
      ((adicQuotientInverseLimit_toCompletion I x).val n) =
    adicQuotientInverseLimit_eval I n x
  dsimp [adicQuotientInverseLimit_toCompletion]
  rw [quotientEquivAlgOfEq_apply_symm]

/-- Mapping an inverse-limit family to the completion and back recovers the family. -/
theorem adicQuotientInverseLimit_left_inverse
    {R : Type*} [CommRing R] (I : Ideal R) (z : AdicCompletion I R) :
    adicQuotientInverseLimit_toCompletion I
        (adicCompletion_toQuotientInverseLimit I z) = z := by
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [adicQuotientInverseLimit_toCompletion_eval]
  rfl

/-- Mapping a completion element to its residue family and back recovers the element. -/
theorem adicQuotientInverseLimit_right_inverse
    {R : Type*} [CommRing R] (I : Ideal R)
    (x : adicQuotientInverseLimit I) :
    adicCompletion_toQuotientInverseLimit I
        (adicQuotientInverseLimit_toCompletion I x) = x := by
  ext n
  change AdicCompletion.evalₐ I n
      (adicQuotientInverseLimit_toCompletion I x) =
    adicQuotientInverseLimit_eval I n x
  rw [adicQuotientInverseLimit_toCompletion_eval]

/-- The adic inverse-limit equivalence, algebraic projective-limit form:
the adic completion is canonically isomorphic to `lim_n R/I^n`. -/
def adicCompletion_equiv_quotientInverseLimit
    {R : Type*} [CommRing R] (I : Ideal R) :
    AdicCompletion I R ≃+* adicQuotientInverseLimit I where
  toFun := adicCompletion_toQuotientInverseLimit I
  invFun := adicQuotientInverseLimit_toCompletion I
  left_inv := adicQuotientInverseLimit_left_inverse I
  right_inv := adicQuotientInverseLimit_right_inverse I
  map_mul' x y := by
    ext n
    change AdicCompletion.evalₐ I n (x * y) =
      AdicCompletion.evalₐ I n x * AdicCompletion.evalₐ I n y
    simp
  map_add' x y := by
    ext n
    change AdicCompletion.evalₐ I n (x + y) =
      AdicCompletion.evalₐ I n x + AdicCompletion.evalₐ I n y
    simp











 



/-- The opaque positive-indexed projective-limit object
`lim_n R/I^(n+1)`. -/
def adicPositiveQuotientInverseLimit
    {R : Type*} [CommRing R] (I : Ideal R) : Type _ :=
  compatibleRingFamilies (fun n : ℕ => R ⧸ I ^ (n + 1))
    (fun {_ _} hmn =>
      Ideal.Quotient.factorPow I (Nat.succ_le_succ hmn))

/-- The implementation representation of the positive-indexed ring limit. -/
def adicPositiveQuotientInverseLimitCompatibleFamiliesEquiv
    {R : Type*} [CommRing R] (I : Ideal R) :
    adicPositiveQuotientInverseLimit I ≃
      compatibleRingFamilies (fun n : ℕ => R ⧸ I ^ (n + 1))
        (fun {_ _} hmn =>
          Ideal.Quotient.factorPow I (Nat.succ_le_succ hmn)) := by
  unfold adicPositiveQuotientInverseLimit
  exact Equiv.refl _

/-- Positive-level compatible adic quotient families form a commutative ring. -/
instance adicPositiveQuotientInverseLimit.instCommRing
    {R : Type*} [CommRing R] (I : Ideal R) :
    CommRing (adicPositiveQuotientInverseLimit I) :=
  (adicPositiveQuotientInverseLimitCompatibleFamiliesEquiv I).commRing



/-- Defines `adicPositiveQuotientInverseLimit_mk`. -/
def adicPositiveQuotientInverseLimit_mk
    {R : Type*} [CommRing R] (I : Ideal R)
    (x : ∀ n : ℕ, R ⧸ I ^ (n + 1))
    (compatible : ∀ {m n : ℕ} (hmn : m ≤ n),
      Ideal.Quotient.factorPow I (Nat.succ_le_succ hmn) (x n) = x m) :
    adicPositiveQuotientInverseLimit I :=
  (adicPositiveQuotientInverseLimitCompatibleFamiliesEquiv I).symm
    ⟨x, compatible⟩

/-- Defines `adicPositiveQuotientInverseLimit_eval`. -/
def adicPositiveQuotientInverseLimit_eval
    {R : Type*} [CommRing R] (I : Ideal R) (n : ℕ) :
    adicPositiveQuotientInverseLimit I →+* R ⧸ I ^ (n + 1) where
  toFun x :=
    (adicPositiveQuotientInverseLimitCompatibleFamiliesEquiv I x).1 n
  map_one' := by rfl
  map_mul' _ _ := by rfl
  map_zero' := by rfl
  map_add' _ _ := by rfl

/-- Positive-level evaluation returns the selected adic quotient component. -/
@[simp]
theorem adicPositiveQuotientInverseLimit_eval_mk
    {R : Type*} [CommRing R] (I : Ideal R)
    (x : ∀ n : ℕ, R ⧸ I ^ (n + 1))
    (compatible : ∀ {m n : ℕ} (hmn : m ≤ n),
      Ideal.Quotient.factorPow I (Nat.succ_le_succ hmn) (x n) = x m)
    (n : ℕ) :
    adicPositiveQuotientInverseLimit_eval I n
        (adicPositiveQuotientInverseLimit_mk I x compatible) = x n := by
  rfl

/-- Positive adic inverse-limit elements are determined by all of their components. -/
@[ext]
theorem adicPositiveQuotientInverseLimit_ext
    {R : Type*} [CommRing R] (I : Ideal R)
    {x y : adicPositiveQuotientInverseLimit I}
    (h : ∀ n : ℕ, adicPositiveQuotientInverseLimit_eval I n x =
      adicPositiveQuotientInverseLimit_eval I n y) :
    x = y := by
  apply (adicPositiveQuotientInverseLimitCompatibleFamiliesEquiv I).injective
  apply Subtype.ext
  funext n
  exact h n



/-- The positive adic inverse limit carries the topology induced by its discrete coordinates. -/
noncomputable instance adicPositiveQuotientInverseLimit.instTopologicalSpace
    {R : Type*} [CommRing R] (I : Ideal R) :
    TopologicalSpace (adicPositiveQuotientInverseLimit I) := by
  letI : (n : ℕ) → TopologicalSpace (R ⧸ I ^ (n + 1)) := fun _ => ⊥
  exact
    (adicPositiveQuotientInverseLimitCompatibleFamiliesEquiv I).topologicalSpace

 





















 



end Valuations
end LubinTate

end
