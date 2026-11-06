module

public import Mathlib

public import ValuedFieldTheory.LocalField.NormUnits
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.RingTheory.Norm.Basic

@[expose] public section


/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/









set_option autoImplicit false
/-!
# Quotients by local norm subgroups

Constructs `Kˣ/N(Lˣ)`, its universal maps and comparison equivalences, and
relates its finite cardinality to the index of the norm subgroup.
-/

namespace LocalFieldTheory

noncomputable section

universe u v

/-- The norm subgroup N_{L/K}(Lˣ) ≤ Kˣ. -/
def localNormSubgroup (K L : Type u) [Field K] [Field L] [Algebra K L]  :=
  (normUnits K L).range

/-- Units modulo field norms. -/
def NormQuotient (K L : Type u) [Field K] [Field L] [Algebra K L]  :=
  Kˣ ⧸ localNormSubgroup K L

/-- Field units modulo the local norm subgroup form a commutative group. -/
instance normQuotientCommGroup (K L : Type u) [Field K] [Field L] [Algebra K L] :
    CommGroup (NormQuotient K L) := by
  change CommGroup (Kˣ ⧸ localNormSubgroup K L)
  infer_instance

section
variable (K L : Type u) [Field K] [Field L] [Algebra K L]
include K L
/-- The explicit boundary to the concrete quotient implementation.  Clients
that need quotient-level constructions should use this equivalence instead of
unfolding `NormQuotient`. -/
def normQuotientConcreteEquiv
      :
    NormQuotient K L ≃* Kˣ ⧸ localNormSubgroup K L := by
  change (Kˣ ⧸ localNormSubgroup K L) ≃* Kˣ ⧸ localNormSubgroup K L
  exact MulEquiv.refl _

/-- Defines `normClass`. -/
def normClass   :
    Kˣ →* NormQuotient K L := by
  change Kˣ →* Kˣ ⧸ localNormSubgroup K L
  let N := localNormSubgroup K L
  exact QuotientGroup.mk' N

/-- The concrete quotient equivalence sends a norm class to the quotient class of its
representative. -/
@[simp]
theorem normQuotientConcreteEquiv_normClass
      (x : Kˣ) :
    normQuotientConcreteEquiv K L (normClass K L x) =
      QuotientGroup.mk x := rfl
end


section
variable {K L : Type u} {M : Type v} [Field K] [Field L] [Algebra K L]
    [Group M] (f : Kˣ →* M) (h : localNormSubgroup K L ≤ f.ker)
include K L M f h
/-- Define a homomorphism out of a norm quotient from a homomorphism on
`Kˣ` that kills every local norm. -/
def normQuotientLift   :
    NormQuotient K L →* M := by
  change (Kˣ ⧸ localNormSubgroup K L) →* M
  let N := localNormSubgroup K L
  exact QuotientGroup.lift N f h

/-- A homomorphism descended through the norm quotient agrees with the original homomorphism on
representatives. -/
@[simp]
theorem normQuotientLift_normClass   (x : Kˣ) :
    normQuotientLift f h (normClass K L x) = f x := rfl

/-- A map obtained by descending a surjective homomorphism through the norm
quotient is still surjective. -/
theorem normQuotientLift_surjective   (hf : Function.Surjective f) :
    Function.Surjective (normQuotientLift f h) := by
  intro y
  obtain ⟨x, rfl⟩ := hf y
  exact ⟨normClass K L x, normQuotientLift_normClass f h x⟩
end


section
variable (K L : Type u) [Field K] [Field L] [Algebra K L]
    (N : Subgroup Kˣ) (h : localNormSubgroup K L = N)
include K L N h
/-- Identify a norm quotient with any concrete quotient once its defining
subgroup has been identified.  This is the sole public boundary for such
representation changes. -/
def normQuotientEquivOfSubgroupEq
      :
    NormQuotient K L ≃* Kˣ ⧸ N := by
  change (Kˣ ⧸ localNormSubgroup K L) ≃* (Kˣ ⧸ N)
  exact QuotientGroup.quotientMulEquivOfEq h

/-- After identifying the norm subgroup with another subgroup, a norm class maps to the
corresponding quotient class. -/
@[simp]
theorem normQuotientEquivOfSubgroupEq_normClass
      (x : Kˣ) :
    normQuotientEquivOfSubgroupEq K L N h (normClass K L x) =
      QuotientGroup.mk x := by
  change QuotientGroup.quotientMulEquivOfEq h (QuotientGroup.mk x) =
    QuotientGroup.mk x
  exact QuotientGroup.quotientMulEquivOfEq_mk h x
end


section
variable (K L M : Type u) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M]
    (h : localNormSubgroup K L = localNormSubgroup K M)
include K L M h
/-- Identify two norm quotients when their defining norm subgroups agree. -/
def normQuotientEquivOfNormSubgroupEq
      :
    NormQuotient K L ≃* NormQuotient K M := by
  change (Kˣ ⧸ localNormSubgroup K L) ≃* (Kˣ ⧸ localNormSubgroup K M)
  exact QuotientGroup.quotientMulEquivOfEq h

/-- An equality of norm subgroups identifies norm classes represented by the same base-field unit.
An equality of norm subgroups identifies norm classes represented by the same base-field unit. -/
@[simp]
theorem normQuotientEquivOfNormSubgroupEq_normClass
      (x : Kˣ) :
    normQuotientEquivOfNormSubgroupEq K L M h (normClass K L x) =
      normClass K M x := by
  change QuotientGroup.quotientMulEquivOfEq h (QuotientGroup.mk x) =
    QuotientGroup.mk x
  exact QuotientGroup.quotientMulEquivOfEq_mk h x
end


/-- First isomorphism theorem with an opaque norm quotient as its source. -/
def normQuotientEquivOfSurjective
    {K L : Type u} {M : Type v} [Field K] [Field L] [Algebra K L]
    [Group M] (f : Kˣ →* M) (hf : Function.Surjective f)
    (hker : f.ker = localNormSubgroup K L) : NormQuotient K L ≃* M := by
  change (Kˣ ⧸ localNormSubgroup K L) ≃* M
  exact (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)















/-- Eliminate a norm-quotient class through the canonical quotient map,
without exposing the quotient representation to clients. -/
protected theorem NormQuotient.inductionOn {K L : Type u} [Field K] [Field L]
    [Algebra K L] {motive : NormQuotient K L → Prop}
    (q : NormQuotient K L)
    (h : ∀ x : Kˣ, motive (normClass K L x)) : motive q := by
  change motive (show Kˣ ⧸ localNormSubgroup K L from q)
  refine QuotientGroup.induction_on q ?_
  intro x
  exact h x

section
variable (K L : Type u) [Field K] [Field L] [Algebra K L]
include K L
/-- The quotient class of any extension-unit norm is the identity norm class. -/
theorem mk_normUnits_eq_one   (x : Lˣ) :
    normClass K L (normUnits K L x) = 1 := (QuotientGroup.eq_one_iff (normUnits K L x)).2 ⟨x, rfl⟩

/-- A base-field unit has trivial norm class exactly when it lies in the local norm subgroup. -/
theorem normClass_eq_one_iff   (x : Kˣ) :
    normClass K L x = 1 ↔ ∃ y : Lˣ, normUnits K L y = x := by
  rw [← MonoidHom.mem_range]
  exact QuotientGroup.eq_one_iff x

/-- Two units have the same norm class exactly when their quotient is a local norm. -/
theorem normClass_eq_iff_div_mem   (x y : Kˣ) :
    normClass K L x = normClass K L y ↔
      x / y ∈ localNormSubgroup K L :=
  by
    let N := localNormSubgroup K L
    apply QuotientGroup.eq_iff_div_mem

/-- The kernel of the norm-class homomorphism is the local norm subgroup. -/
theorem normClass_ker   :
    MonoidHom.ker (normClass K L) = localNormSubgroup K L :=
  by
    let N := localNormSubgroup K L
    apply QuotientGroup.ker_mk'

/-- Membership in the kernel of the norm-class map is equivalent to membership in the local norm
subgroup. -/
theorem normClass_mem_ker_iff   (x : Kˣ) :
    x ∈ MonoidHom.ker (normClass K L) ↔ x ∈ localNormSubgroup K L := by
  rw [normClass_ker K L]

/-- A norm class is one exactly when its representative is a local norm. -/
theorem normClass_eq_one_iff_mem   (x : Kˣ) :
    normClass K L x = 1 ↔ x ∈ localNormSubgroup K L := by
  rw [← normClass_mem_ker_iff K L x]
  rfl






























































/-- Two norm classes agree exactly when their representatives differ by a unit norm. -/
theorem normClass_eq_iff_exists_norm_div   (x y : Kˣ) :
    normClass K L x = normClass K L y ↔
      ∃ z : Lˣ, x / y = normUnits K L z := by
  rw [normClass_eq_iff_div_mem K L x y]
  change x / y ∈ (normUnits K L).range ↔ _
  rw [MonoidHom.mem_range]
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z, hz.symm⟩
  · rintro ⟨z, hz⟩
    exact ⟨z, hz.symm⟩
end
































/-! ### Surjectivity and equality refinements for norm quotients -/





























































end
end LocalFieldTheory
