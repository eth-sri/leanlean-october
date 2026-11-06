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

/-- The norm subgroup N_{L/K}(Lˣ) ≤ Kˣ. -/
def localNormSubgroup (K L : Type u) [Field K] [Field L] [Algebra K L] : Subgroup Kˣ :=
  (normUnits K L).range

/-- Units modulo field norms. -/
def NormQuotient (K L : Type u) [Field K] [Field L] [Algebra K L] : Type u :=
  Kˣ ⧸ localNormSubgroup K L

/-- Field units modulo the local norm subgroup form a commutative group. -/
instance normQuotientCommGroup (K L : Type u) [Field K] [Field L] [Algebra K L] :
    CommGroup (NormQuotient K L) := by
  change CommGroup (Kˣ ⧸ localNormSubgroup K L)
  infer_instance

/-- The explicit boundary to the concrete quotient implementation.  Clients
that need quotient-level constructions should use this equivalence instead of
unfolding `NormQuotient`. -/
def normQuotientConcreteEquiv
    (K L : Type u) [Field K] [Field L] [Algebra K L] :
    NormQuotient K L ≃* Kˣ ⧸ localNormSubgroup K L := by
  change (Kˣ ⧸ localNormSubgroup K L) ≃* Kˣ ⧸ localNormSubgroup K L
  exact MulEquiv.refl _

/-- Defines `normClass`. -/
def normClass (K L : Type u) [Field K] [Field L] [Algebra K L] :
    Kˣ →* NormQuotient K L := by
  change Kˣ →* Kˣ ⧸ localNormSubgroup K L
  let N := localNormSubgroup K L
  exact QuotientGroup.mk' N

/-- The concrete quotient equivalence sends a norm class to the quotient class of its
representative. -/
@[simp]
theorem normQuotientConcreteEquiv_normClass
    (K L : Type u) [Field K] [Field L] [Algebra K L] (x : Kˣ) :
    normQuotientConcreteEquiv K L (normClass K L x) =
      QuotientGroup.mk x := by
  aesop

/-- Define a homomorphism out of a norm quotient from a homomorphism on
`Kˣ` that kills every local norm. -/
def normQuotientLift {K L : Type u} {M : Type v} [Field K] [Field L] [Algebra K L]
    [Group M] (f : Kˣ →* M) (h : localNormSubgroup K L ≤ f.ker) :
    NormQuotient K L →* M := by
  change (Kˣ ⧸ localNormSubgroup K L) →* M
  let N := localNormSubgroup K L
  exact QuotientGroup.lift N f h

/-- A homomorphism descended through the norm quotient agrees with the original homomorphism on
representatives. -/
@[simp]
theorem normQuotientLift_normClass {K L : Type u} {M : Type v} [Field K] [Field L]
    [Algebra K L] [Group M] (f : Kˣ →* M)
    (h : localNormSubgroup K L ≤ f.ker) (x : Kˣ) :
    normQuotientLift f h (normClass K L x) = f x := by
  aesop

/-- A map obtained by descending a surjective homomorphism through the norm
quotient is still surjective. -/
theorem normQuotientLift_surjective {K L : Type u} {M : Type v} [Field K] [Field L]
    [Algebra K L] [Group M] (f : Kˣ →* M)
    (h : localNormSubgroup K L ≤ f.ker) (hf : Function.Surjective f) :
    Function.Surjective (normQuotientLift f h) := by
  intro y
  obtain ⟨x, rfl⟩ := hf y
  exact ⟨normClass K L x, normQuotientLift_normClass f h x⟩

/-- Identify a norm quotient with any concrete quotient once its defining
subgroup has been identified.  This is the sole public boundary for such
representation changes. -/
def normQuotientEquivOfSubgroupEq
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    (N : Subgroup Kˣ) (h : localNormSubgroup K L = N) :
    NormQuotient K L ≃* Kˣ ⧸ N := by
  change (Kˣ ⧸ localNormSubgroup K L) ≃* (Kˣ ⧸ N)
  exact QuotientGroup.quotientMulEquivOfEq h

/-- After identifying the norm subgroup with another subgroup, a norm class maps to the
corresponding quotient class. -/
@[simp]
theorem normQuotientEquivOfSubgroupEq_normClass
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    (N : Subgroup Kˣ) (h : localNormSubgroup K L = N) (x : Kˣ) :
    normQuotientEquivOfSubgroupEq K L N h (normClass K L x) =
      QuotientGroup.mk x := by
  aesop

/-- Identify two norm quotients when their defining norm subgroups agree. -/
def normQuotientEquivOfNormSubgroupEq
    (K L M : Type u) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M]
    (h : localNormSubgroup K L = localNormSubgroup K M) :
    NormQuotient K L ≃* NormQuotient K M := by
  change (Kˣ ⧸ localNormSubgroup K L) ≃* (Kˣ ⧸ localNormSubgroup K M)
  exact QuotientGroup.quotientMulEquivOfEq h

/-- An equality of norm subgroups identifies norm classes represented by the same base-field unit.
An equality of norm subgroups identifies norm classes represented by the same base-field unit. -/
@[simp]
theorem normQuotientEquivOfNormSubgroupEq_normClass
    (K L M : Type u) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M]
    (h : localNormSubgroup K L = localNormSubgroup K M) (x : Kˣ) :
    normQuotientEquivOfNormSubgroupEq K L M h (normClass K L x) =
      normClass K M x := by
  aesop

/-- First isomorphism theorem with an opaque norm quotient as its source. -/
def normQuotientEquivOfSurjective
    {K L : Type u} {M : Type v} [Field K] [Field L] [Algebra K L]
    [Group M] (f : Kˣ →* M) (hf : Function.Surjective f)
    (hker : f.ker = localNormSubgroup K L) : NormQuotient K L ≃* M := by
  change (Kˣ ⧸ localNormSubgroup K L) ≃* M
  exact (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)

/-- The first-isomorphism equivalence sends a norm class to the image of its representative. -/
@[simp]
theorem normQuotientEquivOfSurjective_normClass
    {K L : Type u} {M : Type v} [Field K] [Field L] [Algebra K L]
    [Group M] (f : Kˣ →* M) (hf : Function.Surjective f)
    (hker : f.ker = localNormSubgroup K L) (x : Kˣ) :
    normQuotientEquivOfSurjective f hf hker (normClass K L x) = f x := by
  aesop

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

/-- The quotient class of any extension-unit norm is the identity norm class. -/
theorem mk_normUnits_eq_one (K L : Type u) [Field K] [Field L] [Algebra K L] (x : Lˣ) :
    normClass K L (normUnits K L x) = 1 := by
  exact (QuotientGroup.eq_one_iff (normUnits K L x)).2 ⟨x, rfl⟩

/-- A base-field unit has trivial norm class exactly when it lies in the local norm subgroup. -/
theorem normClass_eq_one_iff (K L : Type u) [Field K] [Field L]
    [Algebra K L] (x : Kˣ) :
    normClass K L x = 1 ↔ ∃ y : Lˣ, normUnits K L y = x := by
  rw [← MonoidHom.mem_range]
  exact QuotientGroup.eq_one_iff x

/-- Two units have the same norm class exactly when their quotient is a local norm. -/
theorem normClass_eq_iff_div_mem (K L : Type u) [Field K] [Field L]
    [Algebra K L] (x y : Kˣ) :
    normClass K L x = normClass K L y ↔
      x / y ∈ localNormSubgroup K L :=
  by
    let N := localNormSubgroup K L
    exact QuotientGroup.eq_iff_div_mem (N := N)

/-- The kernel of the norm-class homomorphism is the local norm subgroup. -/
theorem normClass_ker (K L : Type u) [Field K] [Field L] [Algebra K L] :
    MonoidHom.ker (normClass K L) = localNormSubgroup K L :=
  by
    let N := localNormSubgroup K L
    exact QuotientGroup.ker_mk' (N := N)

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

/-- The map of norm quotients induced by inclusion of their norm subgroups. -/
def normQuotientMapOfLE
    (K L M : Type u) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M]
    (h : localNormSubgroup K L ≤ localNormSubgroup K M) :
    NormQuotient K L →* NormQuotient K M :=
  normQuotientLift (normClass K M) fun x hx =>
    (normClass_eq_one_iff_mem K M x).2 (h hx)

/-- The quotient map induced by inclusion of norm subgroups preserves representatives. -/
@[simp]
theorem normQuotientMapOfLE_normClass
    (K L M : Type u) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M]
    (h : localNormSubgroup K L ≤ localNormSubgroup K M) (x : Kˣ) :
    normQuotientMapOfLE K L M h (normClass K L x) = normClass K M x := by
  aesop

/-- Over the identity extension, the unit norm fixes every base-field unit. -/
theorem normUnits_self_apply (K : Type u) [Field K] (x : Kˣ) :
    normUnits K K x = x := by
  aesop

/-- For the identity extension, every base-field unit is a norm. -/
theorem localNormSubgroup_self (K : Type u) [Field K] :
    localNormSubgroup K K = ⊤ := by
  ext x
  constructor
  · intro _
    exact Subgroup.mem_top x
  · intro _
    exact ⟨x, normUnits_self_apply K x⟩

/-- Every norm class for the identity extension is the identity. -/
theorem normQuotient_self_eq_one (K : Type u) [Field K] (x : NormQuotient K K) :
    x = 1 := by
  refine NormQuotient.inductionOn (motive := fun q => q = 1) x ?_
  intro a
  exact (normClass_eq_one_iff_mem K K a).2 (by
    rw [localNormSubgroup_self K]
    exact Subgroup.mem_top a)

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
  rw [MonoidHom.mem_range]
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z, hz.symm⟩
  · rintro ⟨z, hz⟩
    exact ⟨z, hz.symm⟩









/-! ### Surjectivity and equality refinements for norm quotients -/













end
end LocalFieldTheory
