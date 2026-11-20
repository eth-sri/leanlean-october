module

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

section

variable (K L : Type u) [Field K] [Field L] [Algebra K L]

/-- The norm subgroup N_{L/K}(Lˣ) ≤ Kˣ. -/
def localNormSubgroup : Subgroup Kˣ :=
  (normUnits K L).range

/-- Units modulo field norms. -/
def NormQuotient : Type u :=
  Kˣ ⧸ localNormSubgroup K L

end

/-- Field units modulo the local norm subgroup form a commutative group. -/
instance normQuotientCommGroup (K L : Type u) [Field K] [Field L] [Algebra K L] :
    CommGroup (NormQuotient K L) := by
  change CommGroup (Kˣ ⧸ localNormSubgroup K L)
  infer_instance

section

variable (K L : Type u) [Field K] [Field L] [Algebra K L]

/-- The explicit boundary to the concrete quotient implementation.  Clients
that need quotient-level constructions should use this equivalence instead of
unfolding `NormQuotient`. -/
def normQuotientConcreteEquiv :
    NormQuotient K L ≃* Kˣ ⧸ localNormSubgroup K L := by
  exact MulEquiv.refl _

/-- Defines `normClass`. -/
def normClass :
    Kˣ →* NormQuotient K L := by
  exact QuotientGroup.mk' (localNormSubgroup K L)

/-- The concrete quotient equivalence sends a norm class to the quotient class of its
representative. -/
@[simp]
theorem normQuotientConcreteEquiv_normClass (x : Kˣ) :
    normQuotientConcreteEquiv K L (normClass K L x) =
      QuotientGroup.mk x := rfl

end

section

variable {K L : Type u} {M : Type v} [Field K] [Field L] [Algebra K L] [Group M] (f : Kˣ →* M)
    (h : localNormSubgroup K L ≤ f.ker)

/-- Define a homomorphism out of a norm quotient from a homomorphism on
`Kˣ` that kills every local norm. -/
def normQuotientLift :
    NormQuotient K L →* M := by
  exact QuotientGroup.lift (localNormSubgroup K L) f h

/-- A homomorphism descended through the norm quotient agrees with the original homomorphism on
representatives. -/
@[simp]
theorem normQuotientLift_normClass (x : Kˣ) :
    normQuotientLift f h (normClass K L x) = f x := rfl

/-- A map obtained by descending a surjective homomorphism through the norm
quotient is still surjective. -/
theorem normQuotientLift_surjective (hf : Function.Surjective f) :
    Function.Surjective (normQuotientLift f h) := by
  intro y
  obtain ⟨x, rfl⟩ := hf y
  exact ⟨normClass K L x, normQuotientLift_normClass f h x⟩

end

section

variable (K L : Type u) [Field K] [Field L] [Algebra K L] (N : Subgroup Kˣ)
    (h : localNormSubgroup K L = N)

/-- Identify a norm quotient with any concrete quotient once its defining
subgroup has been identified.  This is the sole public boundary for such
representation changes. -/
def normQuotientEquivOfSubgroupEq :
    NormQuotient K L ≃* Kˣ ⧸ N := by
  exact QuotientGroup.quotientMulEquivOfEq h

/-- After identifying the norm subgroup with another subgroup, a norm class maps to the
corresponding quotient class. -/
@[simp]
theorem normQuotientEquivOfSubgroupEq_normClass (x : Kˣ) :
    normQuotientEquivOfSubgroupEq K L N h (normClass K L x) =
      QuotientGroup.mk x := by
  rfl

end

section

variable (K L M : Type u) [Field K] [Field L] [Field M] [Algebra K L] [Algebra K M]
    (h : localNormSubgroup K L = localNormSubgroup K M)

/-- Identify two norm quotients when their defining norm subgroups agree. -/
def normQuotientEquivOfNormSubgroupEq :
    NormQuotient K L ≃* NormQuotient K M := by
  exact QuotientGroup.quotientMulEquivOfEq h

/-- An equality of norm subgroups identifies norm classes represented by the same base-field unit.
An equality of norm subgroups identifies norm classes represented by the same base-field unit. -/
@[simp]
theorem normQuotientEquivOfNormSubgroupEq_normClass (x : Kˣ) :
    normQuotientEquivOfNormSubgroupEq K L M h (normClass K L x) =
      normClass K M x := by
  rfl

end

section

variable {K L : Type u} {M : Type v} [Field K] [Field L] [Algebra K L] [Group M] (f : Kˣ →* M)
    (hf : Function.Surjective f) (hker : f.ker = localNormSubgroup K L)

/-- First isomorphism theorem with an opaque norm quotient as its source. -/
def normQuotientEquivOfSurjective : NormQuotient K L ≃* M := by
  exact (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)

/-- The first-isomorphism equivalence sends a norm class to the image of its representative. -/
@[simp]
theorem normQuotientEquivOfSurjective_normClass (x : Kˣ) :
    normQuotientEquivOfSurjective f hf hker (normClass K L x) = f x := by
  rfl

end

/-- Eliminate a norm-quotient class through the canonical quotient map,
without exposing the quotient representation to clients. -/
protected theorem NormQuotient.inductionOn {K L : Type u} [Field K] [Field L]
    [Algebra K L] {motive : NormQuotient K L → Prop}
    (q : NormQuotient K L)
    (h : ∀ x : Kˣ, motive (normClass K L x)) : motive q := by
  exact QuotientGroup.induction_on q fun x ↦ h x

/-- The quotient class of any extension-unit norm is the identity norm class. -/
theorem mk_normUnits_eq_one (K L : Type u) [Field K] [Field L] [Algebra K L] (x : Lˣ) :
    normClass K L (normUnits K L x) = 1 := (QuotientGroup.eq_one_iff (normUnits K L x)).2 ⟨x, rfl⟩

/-- A base-field unit has trivial norm class exactly when it lies in the local norm subgroup. -/
theorem normClass_eq_one_iff (K L : Type u) [Field K] [Field L]
    [Algebra K L] (x : Kˣ) :
    normClass K L x = 1 ↔ ∃ y : Lˣ, normUnits K L y = x := by
  exact QuotientGroup.eq_one_iff x

section

variable (K L : Type u) [Field K] [Field L] [Algebra K L]

/-- Two units have the same norm class exactly when their quotient is a local norm. -/
theorem normClass_eq_iff_div_mem (x y : Kˣ) :
    normClass K L x = normClass K L y ↔
      x / y ∈ localNormSubgroup K L :=
  by
    exact QuotientGroup.eq_iff_div_mem

/-- The kernel of the norm-class homomorphism is the local norm subgroup. -/
theorem normClass_ker :
    MonoidHom.ker (normClass K L) = localNormSubgroup K L :=
  by
    solve_by_elim [localNormSubgroup, QuotientGroup.ker_mk']

end

/-- Membership in the kernel of the norm-class map is equivalent to membership in the local norm
subgroup. -/
theorem normClass_mem_ker_iff (K L : Type u) [Field K] [Field L]
    [Algebra K L] (x : Kˣ) :
    x ∈ MonoidHom.ker (normClass K L) ↔ x ∈ localNormSubgroup K L := by
  rw [normClass_ker K L]

/-- A norm class is one exactly when its representative is a local norm. -/
theorem normClass_eq_one_iff_mem (K L : Type u) [Field K] [Field L]
    [Algebra K L] (x : Kˣ) :
    normClass K L x = 1 ↔ x ∈ localNormSubgroup K L := by
  rw [← normClass_mem_ker_iff K L x]
  rfl

section

variable (K : Type u) [Field K]

/-- Over the identity extension, the unit norm fixes every base-field unit. -/
theorem normUnits_self_apply (x : Kˣ) :
    normUnits K K x = x := by
  simp [normUnits]

/-- For the identity extension, every base-field unit is a norm. -/
theorem localNormSubgroup_self :
    localNormSubgroup K K = ⊤ := by
  ext x
  constructor
  · grind [Subgroup.mem_top]
  · solve_by_elim [normUnits_self_apply]

/-- Every norm class for the identity extension is the identity. -/
theorem normQuotient_self_eq_one (x : NormQuotient K K) :
    x = 1 := by
  refine NormQuotient.inductionOn (motive := fun q => q = 1) x ?_
  intro a
  exact (normClass_eq_one_iff_mem K K a).2 (by
    simp [localNormSubgroup_self])

end

/-- The norm quotient of a field over itself is a subsingleton. -/
instance normQuotient_self_subsingleton (K : Type u) [Field K] :
    Subsingleton (NormQuotient K K) where
  allEq x y := by
    rw [normQuotient_self_eq_one K x, normQuotient_self_eq_one K y]

/-- Two norm classes agree exactly when their representatives differ by a unit norm. -/
theorem normClass_eq_iff_exists_norm_div (K L : Type u)
    [Field K] [Field L] [Algebra K L] (x y : Kˣ) :
    normClass K L x = normClass K L y ↔
      ∃ z : Lˣ, x / y = normUnits K L z := by
  rw [normClass_eq_iff_div_mem K L x y]
  change x / y ∈ (normUnits K L).range ↔ _
  simp
  grind

end
end LocalFieldTheory
