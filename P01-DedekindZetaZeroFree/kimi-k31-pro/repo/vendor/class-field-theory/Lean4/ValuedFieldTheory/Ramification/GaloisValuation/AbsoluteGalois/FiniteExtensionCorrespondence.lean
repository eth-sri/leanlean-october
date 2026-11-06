module

public import Mathlib.SetTheory.Cardinal.Finite
public import ValuedFieldTheory.Ramification.GaloisValuation.AbsoluteGalois.InfiniteGaloisCorrespondence

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false
/-! Provides the public declarations in the `RamificationTheory.GaloisValuation.AbsoluteGalois.FiniteExtensionCorrespondence` Lean module. -/

namespace RamificationTheory

open ValuationTheory

noncomputable section

universe u v w z

namespace Field
namespace absoluteGaloisGroup

open scoped Topology Pointwise
open CategoryTheory

variable (K : Type u) [Field K]

section FiniteExtension

variable {L : Type v} [Field L] [Algebra K L]

local instance fieldRangeIsScalarTower
    (i : L →ₐ[K] AlgebraicClosure K) :
    IsScalarTower K (AlgHom.fieldRange i) (AlgebraicClosure K) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- The image of a finite extension inside `K^al` is finite over `K`. -/
theorem finiteDimensional_fieldRange [FiniteDimensional K L]
    (i : L →ₐ[K] AlgebraicClosure K) :
    FiniteDimensional K (AlgHom.fieldRange i) :=
  (AlgEquiv.ofInjectiveField i).toLinearEquiv.finiteDimensional

/-- The subgroup of `G_K` fixing the embedded copy `i(L)` pointwise.  This
definition does not require `L/K` to be finite; finiteness is only needed to
know that it is open. -/
def fixingSubgroupOfExtension (i : L →ₐ[K] AlgebraicClosure K) :
    Subgroup (Field.absoluteGaloisGroup K) where
  carrier :=
    {σ | ∀ x : L,
      (show Gal(AlgebraicClosure K / K) from σ) (i x) = i x}
  one_mem' := by
    intro x
    rfl
  mul_mem' := by
    intro σ τ hσ hτ x
    change (show Gal(AlgebraicClosure K / K) from σ)
      ((show Gal(AlgebraicClosure K / K) from τ) (i x)) = i x
    rw [hτ x, hσ x]
  inv_mem' := by
    intro σ hσ x
    change (show Gal(AlgebraicClosure K / K) from σ).symm (i x) = i x
    have h :=
      congrArg (fun y =>
        (show Gal(AlgebraicClosure K / K) from σ).symm y) (hσ x)
    exact h.symm.trans
      ((show Gal(AlgebraicClosure K / K) from σ).symm_apply_apply (i x))

/-- States the theorem `mem_fixingSubgroupOfExtension`. -/
@[simp]
theorem mem_fixingSubgroupOfExtension
    (i : L →ₐ[K] AlgebraicClosure K) (σ : Field.absoluteGaloisGroup K) :
    σ ∈ fixingSubgroupOfExtension K i ↔
      ∀ x : L, (show Gal(AlgebraicClosure K / K) from σ) (i x) = i x :=
  Iff.rfl

/-- The concrete pointwise-fixing subgroup is the usual fixing subgroup of
the field range `i(L)`. -/
theorem fixingSubgroupOfExtension_eq_fieldRange_fixingSubgroup
    (i : L →ₐ[K] AlgebraicClosure K) :
    fixingSubgroupOfExtension K i =
      (AlgHom.fieldRange i).fixingSubgroup := by
  change
    (show Subgroup (Gal(AlgebraicClosure K / K)) from
      fixingSubgroupOfExtension K i) =
      (AlgHom.fieldRange i).fixingSubgroup
  ext σ
  constructor
  · intro hσ
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    rcases (AlgHom.mem_fieldRange (f := i)).mp hy with ⟨x, rfl⟩
    exact hσ x
  · intro hσ x
    exact (IntermediateField.mem_fixingSubgroup_iff
      (AlgHom.fieldRange i) σ).1 hσ (i x) ⟨x, rfl⟩

section TwoFiniteExtensions

variable {M : Type w} [Field M] [Algebra K M]



/-- For a tower embedding `L -> M -> K^al`, the subgroup fixing `M` is
contained in the subgroup fixing `L`. -/
theorem fixingSubgroupOfExtension_comp_le
    (i : M →ₐ[K] AlgebraicClosure K) (j : L →ₐ[K] M) :
    fixingSubgroupOfExtension K i ≤
      fixingSubgroupOfExtension K (i.comp j) := by
  intro σ hσ x
  exact hσ (j x)

end TwoFiniteExtensions

/-- For a finite extension `L/K` embedded in `K^al`, this is the concrete
open subgroup of `G_K` identified with `G_L`: it is
`Gal(K^al / i(L))`. -/
def openSubgroupOfFiniteExtension [FiniteDimensional K L]
    (i : L →ₐ[K] AlgebraicClosure K) :
    OpenSubgroup (Field.absoluteGaloisGroup K) := by
  letI := finiteDimensional_fieldRange (K := K) i
  exact openSubgroupOfFiniteIntermediateField K (AlgHom.fieldRange i)

/-- States the theorem `openSubgroupOfFiniteExtension_toSubgroup`. -/
@[simp]
theorem openSubgroupOfFiniteExtension_toSubgroup [FiniteDimensional K L]
    (i : L →ₐ[K] AlgebraicClosure K) :
    (openSubgroupOfFiniteExtension K i :
      Subgroup (Field.absoluteGaloisGroup K)) =
      (AlgHom.fieldRange i).fixingSubgroup := by
  let := finiteDimensional_fieldRange (K := K) i
  rfl

/-- States the theorem `mem_openSubgroupOfFiniteExtension`. -/
@[simp]
theorem mem_openSubgroupOfFiniteExtension [FiniteDimensional K L]
    (i : L →ₐ[K] AlgebraicClosure K) (σ : Field.absoluteGaloisGroup K) :
    σ ∈ openSubgroupOfFiniteExtension K i ↔
      ∀ x ∈ AlgHom.fieldRange i,
        (show Gal(AlgebraicClosure K / K) from σ) x = x := by
  let := finiteDimensional_fieldRange (K := K) i
  exact mem_openSubgroupOfFiniteIntermediateField K (AlgHom.fieldRange i) σ

/-- Concrete membership in the finite-extension open subgroup: an element of
`G_K` lies in the copy of `G_L` exactly when it fixes every embedded element
`i x`. -/
theorem mem_openSubgroupOfFiniteExtension_iff_forall_apply_eq
    [FiniteDimensional K L]
    (i : L →ₐ[K] AlgebraicClosure K) (σ : Field.absoluteGaloisGroup K) :
    σ ∈ openSubgroupOfFiniteExtension K i ↔
      ∀ x : L, (show Gal(AlgebraicClosure K / K) from σ) (i x) = i x := by
  rw [mem_openSubgroupOfFiniteExtension]
  constructor
  · intro hσ x
    exact hσ (i x) ⟨x, rfl⟩
  · intro hσ y hy
    rcases (AlgHom.mem_fieldRange (f := i)).mp hy with ⟨x, rfl⟩
    exact hσ x

/-- The finite-extension open subgroup is exactly the concrete subgroup
fixing the embedded copy `i(L)` pointwise. -/
theorem openSubgroupOfFiniteExtension_toSubgroup_eq_fixingSubgroupOfExtension
    [FiniteDimensional K L] (i : L →ₐ[K] AlgebraicClosure K) :
    (openSubgroupOfFiniteExtension K i :
      Subgroup (Field.absoluteGaloisGroup K)) =
      fixingSubgroupOfExtension K i := by
  rw [openSubgroupOfFiniteExtension_toSubgroup,
    fixingSubgroupOfExtension_eq_fieldRange_fixingSubgroup]



/-- The normal-closure open subgroup attached to an embedded finite extension. -/
def openSubgroupOfNormalClosureFiniteExtension [FiniteDimensional K L]
    (i : L →ₐ[K] AlgebraicClosure K) :
    OpenSubgroup (Field.absoluteGaloisGroup K) := by
  letI := finiteDimensional_fieldRange (K := K) i
  exact openSubgroupOfNormalClosureFiniteIntermediateField K
    (AlgHom.fieldRange i)

/-- States the theorem `openSubgroupOfNormalClosureFiniteExtension_toSubgroup`. -/
@[simp]
theorem openSubgroupOfNormalClosureFiniteExtension_toSubgroup
    [FiniteDimensional K L]
    (i : L →ₐ[K] AlgebraicClosure K) :
    (openSubgroupOfNormalClosureFiniteExtension K i :
      Subgroup (Field.absoluteGaloisGroup K)) =
      (IntermediateField.normalClosure K (AlgHom.fieldRange i)
        (AlgebraicClosure K)).fixingSubgroup := by
  let := finiteDimensional_fieldRange (K := K) i
  rfl



/-- The normal-closure open subgroup attached to an embedded finite extension
is normal in `G_K`. -/
theorem openSubgroupOfNormalClosureFiniteExtension_normal
    [FiniteDimensional K L]
    (i : L →ₐ[K] AlgebraicClosure K) :
    ((openSubgroupOfNormalClosureFiniteExtension K i :
      Subgroup (Field.absoluteGaloisGroup K))).Normal := by
  let := finiteDimensional_fieldRange (K := K) i
  exact openSubgroupOfNormalClosureFiniteIntermediateField_normal K
    (AlgHom.fieldRange i)

/-- Provides the instance `instNormal`. -/
instance openSubgroupOfNormalClosureFiniteExtension.instNormal
    [FiniteDimensional K L]
    (i : L →ₐ[K] AlgebraicClosure K) :
    (openSubgroupOfNormalClosureFiniteExtension K i).toSubgroup.Normal :=
  openSubgroupOfNormalClosureFiniteExtension_normal K i

/-- Quotienting by the normal-closure open subgroup attached to an embedded
finite extension gives the finite Galois group of the normal closure of
`i(L)`. -/
def quotientNormalClosureOpenSubgroupEquivGalOfFiniteExtension
    [FiniteDimensional K L]
    (i : L →ₐ[K] AlgebraicClosure K) :
    Field.absoluteGaloisGroup K ⧸
        (openSubgroupOfNormalClosureFiniteExtension K i :
          Subgroup (Field.absoluteGaloisGroup K)) ≃*
      Gal(IntermediateField.normalClosure K (AlgHom.fieldRange i)
        (AlgebraicClosure K) / K) := by
  letI := finiteDimensional_fieldRange (K := K) i
  exact quotientNormalClosureOpenSubgroupEquivGal K (AlgHom.fieldRange i)

/-- States the theorem `quotientNormalClosureOpenSubgroupEquivGalOfFiniteExtension_mk'`. -/
@[simp]
theorem quotientNormalClosureOpenSubgroupEquivGalOfFiniteExtension_mk'
    [FiniteDimensional K L]
    (i : L →ₐ[K] AlgebraicClosure K)
    (σ : Field.absoluteGaloisGroup K) :
    quotientNormalClosureOpenSubgroupEquivGalOfFiniteExtension K i
        (QuotientGroup.mk'
          (openSubgroupOfNormalClosureFiniteExtension K i :
            Subgroup (Field.absoluteGaloisGroup K)) σ) =
      AlgEquiv.restrictNormalHom
        (IntermediateField.normalClosure K (AlgHom.fieldRange i)
          (AlgebraicClosure K)) σ := by
  let := finiteDimensional_fieldRange (K := K) i
  exact quotientNormalClosureOpenSubgroupEquivGal_mk' K
    (AlgHom.fieldRange i) σ





/-- Provides the instance `instFiniteIndex`. -/
instance openSubgroupOfFiniteExtension.instFiniteIndex [FiniteDimensional K L]
    (i : L →ₐ[K] AlgebraicClosure K) :
    ((openSubgroupOfFiniteExtension K i :
      Subgroup (Field.absoluteGaloisGroup K))).FiniteIndex := by
  let := finiteDimensional_fieldRange (K := K) i
  change ((openSubgroupOfFiniteIntermediateField K (AlgHom.fieldRange i) :
    Subgroup (Gal(AlgebraicClosure K / K)))).FiniteIndex
  infer_instance

/-- Provides the instance `instFiniteIndex`. -/
instance openSubgroupOfNormalClosureFiniteExtension.instFiniteIndex
    [FiniteDimensional K L]
    (i : L →ₐ[K] AlgebraicClosure K) :
    ((openSubgroupOfNormalClosureFiniteExtension K i :
      Subgroup (Field.absoluteGaloisGroup K))).FiniteIndex := by
  let := finiteDimensional_fieldRange (K := K) i
  change ((openSubgroupOfNormalClosureFiniteIntermediateField K
    (AlgHom.fieldRange i) :
      Subgroup (Gal(AlgebraicClosure K / K)))).FiniteIndex
  infer_instance



/-- Conjugate an embedding `i : L -> K^al` by an element of `G_K`. -/
def conjugateEmbedding
    (i : L →ₐ[K] AlgebraicClosure K) (σ : Field.absoluteGaloisGroup K) :
    L →ₐ[K] AlgebraicClosure K :=
  (show Gal(AlgebraicClosure K / K) from σ).toAlgHom.comp i

/-- States the theorem `conjugateEmbedding_apply`. -/
@[simp]
theorem conjugateEmbedding_apply
    (i : L →ₐ[K] AlgebraicClosure K)
    (σ : Field.absoluteGaloisGroup K) (x : L) :
    conjugateEmbedding K i σ x =
      (show Gal(AlgebraicClosure K / K) from σ) (i x) :=
  rfl







section TwoFiniteExtensions

variable {M : Type w} [Field M] [Algebra K M]



/-- For a tower embedding `L -> M -> K^al`, the open subgroup identified with
`G_M` is contained in the one identified with `G_L`. -/
theorem openSubgroupOfFiniteExtension_comp_le
    [FiniteDimensional K L] [FiniteDimensional K M]
    (i : M →ₐ[K] AlgebraicClosure K) (j : L →ₐ[K] M) :
    (openSubgroupOfFiniteExtension K i :
      Subgroup (Field.absoluteGaloisGroup K)) ≤
      openSubgroupOfFiniteExtension K (i.comp j) := by
  rw [openSubgroupOfFiniteExtension_toSubgroup_eq_fixingSubgroupOfExtension,
    openSubgroupOfFiniteExtension_toSubgroup_eq_fixingSubgroupOfExtension]
  exact fixingSubgroupOfExtension_comp_le K i j

/-- The open subgroup corresponding to the compositum of the two embedded
finite extensions `iL(L)` and `iM(M)` inside `K^al`. -/
def openSubgroupOfFiniteExtensionSup
    [FiniteDimensional K L] [FiniteDimensional K M]
    (iL : L →ₐ[K] AlgebraicClosure K)
    (iM : M →ₐ[K] AlgebraicClosure K) :
    OpenSubgroup (Field.absoluteGaloisGroup K) := by
  letI : FiniteDimensional K (AlgHom.fieldRange iL) :=
    finiteDimensional_fieldRange (K := K) iL
  letI : FiniteDimensional K (AlgHom.fieldRange iM) :=
    finiteDimensional_fieldRange (K := K) iM
  exact
    openSubgroupOfFiniteIntermediateFieldSup K
      (AlgHom.fieldRange iL) (AlgHom.fieldRange iM)

/-- States the theorem `openSubgroupOfFiniteExtensionSup_toSubgroup`. -/
@[simp]
theorem openSubgroupOfFiniteExtensionSup_toSubgroup
    [FiniteDimensional K L] [FiniteDimensional K M]
    (iL : L →ₐ[K] AlgebraicClosure K)
    (iM : M →ₐ[K] AlgebraicClosure K) :
    (openSubgroupOfFiniteExtensionSup K iL iM :
      Subgroup (Field.absoluteGaloisGroup K)) =
      (openSubgroupOfFiniteExtension K iL :
        Subgroup (Field.absoluteGaloisGroup K)) ⊓
        openSubgroupOfFiniteExtension K iM := by
  let : FiniteDimensional K (AlgHom.fieldRange iL) :=
    finiteDimensional_fieldRange (K := K) iL
  let : FiniteDimensional K (AlgHom.fieldRange iM) :=
    finiteDimensional_fieldRange (K := K) iM
  change
    (openSubgroupOfFiniteIntermediateFieldSup K
      (AlgHom.fieldRange iL) (AlgHom.fieldRange iM) :
        Subgroup (Gal(AlgebraicClosure K / K))) =
      (openSubgroupOfFiniteIntermediateField K (AlgHom.fieldRange iL) :
        Subgroup (Gal(AlgebraicClosure K / K))) ⊓
        openSubgroupOfFiniteIntermediateField K (AlgHom.fieldRange iM)
  exact openSubgroupOfFiniteIntermediateFieldSup_toSubgroup K
    (AlgHom.fieldRange iL) (AlgHom.fieldRange iM)





end TwoFiniteExtensions

/-- The finite-extension open subgroup fixing `i(L)` is topologically
isomorphic to `Gal(K^al/i(L))`. -/
def openSubgroupOfFiniteExtensionContinuousMulEquiv [FiniteDimensional K L]
    (i : L →ₐ[K] AlgebraicClosure K) :
    openSubgroupOfFiniteExtension K i ≃ₜ*
      Gal(AlgebraicClosure K / AlgHom.fieldRange i) := by
  letI := finiteDimensional_fieldRange (K := K) i
  exact
    openSubgroupOfFiniteIntermediateFieldContinuousMulEquiv K
      (AlgHom.fieldRange i)

/-- The inclusion `Gal(K^al / i(L)) → G_K` attached to an embedded finite
extension. -/
def ofFiniteExtension (i : L →ₐ[K] AlgebraicClosure K) :
    Gal(AlgebraicClosure K / AlgHom.fieldRange i) →*
      Field.absoluteGaloisGroup K :=
  ofIntermediateField K (AlgHom.fieldRange i)

/-- States the theorem `ofFiniteExtension_apply`. -/
@[simp]
theorem ofFiniteExtension_apply
    (i : L →ₐ[K] AlgebraicClosure K)
    (σ : Gal(AlgebraicClosure K / AlgHom.fieldRange i)) :
    ofFiniteExtension K i σ = σ.restrictScalars K :=
  rfl

















/-- Normality of `L/K` transports to the embedded field range `i(L)`. -/
instance normal_fieldRangeOfExtension
    (i : L →ₐ[K] AlgebraicClosure K) [Normal K L] :
    Normal K (AlgHom.fieldRange i) :=
  Normal.of_algEquiv (AlgEquiv.ofInjectiveField i)

/-- The open subgroup attached to an embedded finite extension is normal when
the embedded image is normal over `K`. -/
theorem openSubgroupOfFiniteExtension_normal [FiniteDimensional K L]
    (i : L →ₐ[K] AlgebraicClosure K) [Normal K (AlgHom.fieldRange i)] :
    ((openSubgroupOfFiniteExtension K i :
      Subgroup (Field.absoluteGaloisGroup K))).Normal := by
  let := finiteDimensional_fieldRange (K := K) i
  exact openSubgroupOfFiniteIntermediateField_normal K (AlgHom.fieldRange i)

/-- For a finite normal extension, the concrete copy of `G_L` inside `G_K` is
a normal open subgroup. -/
theorem openSubgroupOfFiniteExtension_normal_of_normal
    [FiniteDimensional K L] [Normal K L]
    (i : L →ₐ[K] AlgebraicClosure K) :
    ((openSubgroupOfFiniteExtension K i :
      Subgroup (Field.absoluteGaloisGroup K))).Normal :=
  openSubgroupOfFiniteExtension_normal K i

/-- Provides the instance `instNormal`. -/
instance openSubgroupOfFiniteExtension.instNormal
    [FiniteDimensional K L] [Normal K L]
    (i : L →ₐ[K] AlgebraicClosure K) :
    (openSubgroupOfFiniteExtension K i).toSubgroup.Normal :=
  openSubgroupOfFiniteExtension_normal_of_normal K i

/-- Provides the instance `instNormal_coe`. -/
instance openSubgroupOfFiniteExtension.instNormal_coe
    [FiniteDimensional K L] [Normal K L]
    (i : L →ₐ[K] AlgebraicClosure K) :
    ((openSubgroupOfFiniteExtension K i :
      Subgroup (Field.absoluteGaloisGroup K))).Normal :=
  openSubgroupOfFiniteExtension_normal_of_normal K i

/-- For an embedded finite normal extension, `G_K/G_L` is the automorphism
group of the embedded field range. -/
def quotientEquivGalFieldRangeOfNormalFiniteExtension [FiniteDimensional K L]
    (i : L →ₐ[K] AlgebraicClosure K) [Normal K (AlgHom.fieldRange i)] :
    Gal(AlgebraicClosure K / K) ⧸ (AlgHom.fieldRange i).fixingSubgroup ≃*
      Gal(AlgHom.fieldRange i / K) :=
  quotientEquivGalOfNormalIntermediateField K (AlgHom.fieldRange i)

/-- States the theorem `quotientEquivGalFieldRangeOfNormalFiniteExtension_mk'`. -/
@[simp]
theorem quotientEquivGalFieldRangeOfNormalFiniteExtension_mk'
    [FiniteDimensional K L] (i : L →ₐ[K] AlgebraicClosure K)
    [Normal K (AlgHom.fieldRange i)] (σ : Gal(AlgebraicClosure K / K)) :
    quotientEquivGalFieldRangeOfNormalFiniteExtension K i
        (QuotientGroup.mk' (AlgHom.fieldRange i).fixingSubgroup σ) =
      AlgEquiv.restrictNormalHom (AlgHom.fieldRange i) σ :=
  quotientEquivGalOfNormalIntermediateField_mk' K (AlgHom.fieldRange i) σ

/-- For an embedded finite normal extension, `G_K/G_L` is the original
automorphism group `Gal(L/K)`, transported across the chosen embedding. -/
def quotientEquivGalOfNormalFiniteExtension [FiniteDimensional K L]
    (i : L →ₐ[K] AlgebraicClosure K) [Normal K (AlgHom.fieldRange i)] :
    Gal(AlgebraicClosure K / K) ⧸ (AlgHom.fieldRange i).fixingSubgroup ≃*
      Gal(L / K) :=
  (quotientEquivGalFieldRangeOfNormalFiniteExtension K i).trans
    (AlgEquiv.autCongr (AlgEquiv.ofInjectiveField i)).symm

/-- States the theorem `quotientEquivGalOfNormalFiniteExtension_mk'`. -/
@[simp]
theorem quotientEquivGalOfNormalFiniteExtension_mk'
    [FiniteDimensional K L] (i : L →ₐ[K] AlgebraicClosure K)
    [Normal K (AlgHom.fieldRange i)] (σ : Gal(AlgebraicClosure K / K)) :
    quotientEquivGalOfNormalFiniteExtension K i
        (QuotientGroup.mk' (AlgHom.fieldRange i).fixingSubgroup σ) =
      (AlgEquiv.autCongr (AlgEquiv.ofInjectiveField i)).symm
        ((@AlgEquiv.restrictNormalHom K _ (AlgebraicClosure K) _ _
          (AlgHom.fieldRange i) _ _ _ (fieldRangeIsScalarTower K i) _) σ) := by
  rfl

/-- For an embedded finite normal extension, the quotient by the concrete open
subgroup attached to `L` is the automorphism group of the embedded field range.
This is the open-subgroup form of
`quotientEquivGalFieldRangeOfNormalFiniteExtension`. -/
def quotientOpenSubgroupEquivGalFieldRangeOfNormalFiniteExtension
    [FiniteDimensional K L] [Normal K L]
    (i : L →ₐ[K] AlgebraicClosure K) :
    Field.absoluteGaloisGroup K ⧸
        (openSubgroupOfFiniteExtension K i :
          Subgroup (Field.absoluteGaloisGroup K)) ≃*
      Gal(AlgHom.fieldRange i / K) :=
  quotientEquivGalFieldRangeOfNormalFiniteExtension K i

/-- States the theorem `quotientOpenSubgroupEquivGalFieldRangeOfNormalFiniteExtension_mk'`. -/
@[simp]
theorem quotientOpenSubgroupEquivGalFieldRangeOfNormalFiniteExtension_mk'
    [FiniteDimensional K L] [Normal K L]
    (i : L →ₐ[K] AlgebraicClosure K)
    (σ : Field.absoluteGaloisGroup K) :
    quotientOpenSubgroupEquivGalFieldRangeOfNormalFiniteExtension K i
        (QuotientGroup.mk'
          (openSubgroupOfFiniteExtension K i :
            Subgroup (Field.absoluteGaloisGroup K)) σ) =
      AlgEquiv.restrictNormalHom (AlgHom.fieldRange i) σ :=
  quotientEquivGalFieldRangeOfNormalFiniteExtension_mk' K i σ

/-- For an embedded finite normal extension, `G_K / G_L` is the original
automorphism group `Gal(L/K)` when `G_L` is written as the concrete open
subgroup of `G_K`. -/
def quotientOpenSubgroupEquivGalOfNormalFiniteExtension
    [FiniteDimensional K L] [Normal K L]
    (i : L →ₐ[K] AlgebraicClosure K) :
    Field.absoluteGaloisGroup K ⧸
        (openSubgroupOfFiniteExtension K i :
          Subgroup (Field.absoluteGaloisGroup K)) ≃*
      Gal(L / K) :=
  (quotientOpenSubgroupEquivGalFieldRangeOfNormalFiniteExtension K i).trans
    (AlgEquiv.autCongr (AlgEquiv.ofInjectiveField i)).symm

/-- States the theorem `quotientOpenSubgroupEquivGalOfNormalFiniteExtension_mk'`. -/
@[simp]
theorem quotientOpenSubgroupEquivGalOfNormalFiniteExtension_mk'
    [FiniteDimensional K L] [Normal K L]
    (i : L →ₐ[K] AlgebraicClosure K)
    (σ : Field.absoluteGaloisGroup K) :
    quotientOpenSubgroupEquivGalOfNormalFiniteExtension K i
        (QuotientGroup.mk'
          (openSubgroupOfFiniteExtension K i :
            Subgroup (Field.absoluteGaloisGroup K)) σ) =
      (AlgEquiv.autCongr (AlgEquiv.ofInjectiveField i)).symm
        ((@AlgEquiv.restrictNormalHom K _ (AlgebraicClosure K) _ _
          (AlgHom.fieldRange i) _ _ _ (fieldRangeIsScalarTower K i) _) σ) := by
  rfl

/-- Rebase automorphisms over an embedded finite extension from `L` to its
field range `i(L)`. -/
 def automorphismsOverFieldRangeEquiv
    (i : L →ₐ[K] AlgebraicClosure K) [Algebra L (AlgebraicClosure K)]
    (hmap : ∀ x, algebraMap L (AlgebraicClosure K) x = i x) :
    (AlgebraicClosure K ≃ₐ[L] AlgebraicClosure K) ≃*
      Gal(AlgebraicClosure K / AlgHom.fieldRange i) where
  toFun σ :=
    { σ.toRingEquiv with
      commutes' := by
        intro y
        obtain ⟨x, hx⟩ := (AlgHom.mem_fieldRange (f := i)).mp y.2
        change σ y.1 = y.1
        rw [← hx]
        change σ (i x) = i x
        rw [← hmap x]
        exact σ.commutes x }
  invFun σ :=
    { σ.toRingEquiv with
      commutes' := by
        intro x
        rw [hmap x]
        exact σ.commutes ⟨i x, ⟨x, rfl⟩⟩ }
  left_inv σ := by
    ext x
    rfl
  right_inv σ := by
    ext x
    rfl
  map_mul' σ τ := by
    ext x
    rfl

private theorem automorphismsOverFieldRangeEquiv_continuous
    (i : L →ₐ[K] AlgebraicClosure K) [Algebra L (AlgebraicClosure K)]
    (hmap : ∀ x, algebraMap L (AlgebraicClosure K) x = i x) :
    Continuous (automorphismsOverFieldRangeEquiv K i hmap :
      (AlgebraicClosure K ≃ₐ[L] AlgebraicClosure K) →
        Gal(AlgebraicClosure K / AlgHom.fieldRange i)) := by
  let : Algebra L (AlgHom.fieldRange i) :=
    (AlgEquiv.ofInjectiveField i).toRingHom.toAlgebra
  have : IsScalarTower L (AlgHom.fieldRange i) (AlgebraicClosure K) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      change algebraMap L (AlgebraicClosure K) x = i x
      exact hmap x
  have : Module.Finite L (AlgHom.fieldRange i) := by
    let eLin : L ≃ₗ[L] AlgHom.fieldRange i :=
      { toFun := fun x => algebraMap L (AlgHom.fieldRange i) x
        invFun := fun y => (AlgEquiv.ofInjectiveField i).symm y
        left_inv := by
          intro x
          change (AlgEquiv.ofInjectiveField i).symm
            ((AlgEquiv.ofInjectiveField i) x) = x
          exact (AlgEquiv.ofInjectiveField i).left_inv x
        right_inv := by
          intro y
          change (AlgEquiv.ofInjectiveField i)
            ((AlgEquiv.ofInjectiveField i).symm y) = y
          exact (AlgEquiv.ofInjectiveField i).right_inv y
        map_add' := by
          intro x y
          exact map_add (algebraMap L (AlgHom.fieldRange i)) x y
        map_smul' := by
          intro a x
          change (algebraMap L (AlgHom.fieldRange i)) (a * x) =
            (algebraMap L (AlgHom.fieldRange i)) a *
              (algebraMap L (AlgHom.fieldRange i)) x
          exact map_mul (algebraMap L (AlgHom.fieldRange i)) a x }
    exact Module.Finite.equiv eLin
  let e := automorphismsOverFieldRangeEquiv K i hmap
  refine continuous_of_continuousAt_one e.toMonoidHom ?_
  rw [ContinuousAt, MonoidHom.map_one, Filter.Tendsto]
  intro s hs
  rw [Filter.mem_map]
  rcases (krullTopology_mem_nhds_one_iff (AlgHom.fieldRange i)
      (AlgebraicClosure K) s).1 hs with
    ⟨F, hF, hFs⟩
  let FL : IntermediateField L (AlgebraicClosure K) := F.restrictScalars L
  have : FiniteDimensional (AlgHom.fieldRange i) F := hF
  have : FiniteDimensional L F :=
    FiniteDimensional.trans L (AlgHom.fieldRange i) F
  have : Module.Finite L FL := by
    let eLin : FL ≃ₗ[L] F :=
      { toFun := fun x => ⟨x.1, x.2⟩
        invFun := fun x => ⟨x.1, x.2⟩
        left_inv := by
          intro x
          ext
          rfl
        right_inv := by
          intro x
          ext
          rfl
        map_add' := by
          intro x y
          ext
          rfl
        map_smul' := by
          intro a x
          ext
          rfl }
    exact Module.Finite.equiv eLin.symm
  refine (krullTopology_mem_nhds_one_iff L (AlgebraicClosure K)
    (e ⁻¹' s)).2 ?_
  refine ⟨FL, inferInstance, ?_⟩
  intro σ hσ
  apply hFs
  change e σ ∈ F.fixingSubgroup
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  change σ x = x
  have hxFL : x ∈ FL := by
    change x ∈ F
    exact hx
  exact (IntermediateField.mem_fixingSubgroup_iff FL σ).1 hσ x hxFL

private theorem automorphismsOverFieldRangeEquiv_symm_continuous
    (i : L →ₐ[K] AlgebraicClosure K) [Algebra L (AlgebraicClosure K)]
    (hmap : ∀ x, algebraMap L (AlgebraicClosure K) x = i x) :
    Continuous ((automorphismsOverFieldRangeEquiv K i hmap).symm :
      Gal(AlgebraicClosure K / AlgHom.fieldRange i) →
        (AlgebraicClosure K ≃ₐ[L] AlgebraicClosure K)) := by
  have : IsScalarTower K L (AlgebraicClosure K) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      rw [hmap]
      exact (i.commutes x).symm
  let : Algebra L (AlgHom.fieldRange i) :=
    (AlgEquiv.ofInjectiveField i).toRingHom.toAlgebra
  have : IsScalarTower L (AlgHom.fieldRange i) (AlgebraicClosure K) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      change algebraMap L (AlgebraicClosure K) x = i x
      exact hmap x
  have : Module.Finite L (AlgHom.fieldRange i) := by
    let eLin : L ≃ₗ[L] AlgHom.fieldRange i :=
      { toFun := fun x => algebraMap L (AlgHom.fieldRange i) x
        invFun := fun y => (AlgEquiv.ofInjectiveField i).symm y
        left_inv := by
          intro x
          change (AlgEquiv.ofInjectiveField i).symm
            ((AlgEquiv.ofInjectiveField i) x) = x
          exact (AlgEquiv.ofInjectiveField i).left_inv x
        right_inv := by
          intro y
          change (AlgEquiv.ofInjectiveField i)
            ((AlgEquiv.ofInjectiveField i).symm y) = y
          exact (AlgEquiv.ofInjectiveField i).right_inv y
        map_add' := by
          intro x y
          exact map_add (algebraMap L (AlgHom.fieldRange i)) x y
        map_smul' := by
          intro a x
          change (algebraMap L (AlgHom.fieldRange i)) (a * x) =
            (algebraMap L (AlgHom.fieldRange i)) a *
              (algebraMap L (AlgHom.fieldRange i)) x
          exact map_mul (algebraMap L (AlgHom.fieldRange i)) a x }
    exact Module.Finite.equiv eLin
  let e := automorphismsOverFieldRangeEquiv K i hmap
  refine continuous_of_continuousAt_one e.symm.toMonoidHom ?_
  rw [ContinuousAt, MonoidHom.map_one, Filter.Tendsto]
  intro s hs
  rw [Filter.mem_map]
  rcases (krullTopology_mem_nhds_one_iff L (AlgebraicClosure K) s).1 hs with
    ⟨F, hF, hFs⟩
  have hFRbase : AlgHom.fieldRange i ≤ F.restrictScalars K := by
    intro y hy
    change y ∈ F
    obtain ⟨x, hx⟩ := (AlgHom.mem_fieldRange (f := i)).mp hy
    rw [← hx, ← hmap x]
    exact F.algebraMap_mem x
  let FR : IntermediateField (AlgHom.fieldRange i) (AlgebraicClosure K) :=
    IntermediateField.extendScalars
      (F := AlgHom.fieldRange i)
      (E := F.restrictScalars K) hFRbase
  have : FiniteDimensional L F := hF
  have : Module.Finite L FR := by
    let eLin : FR ≃ₗ[L] F :=
      { toFun := fun x => ⟨x.1, x.2⟩
        invFun := fun x => ⟨x.1, x.2⟩
        left_inv := by
          intro x
          ext
          rfl
        right_inv := by
          intro x
          ext
          rfl
        map_add' := by
          intro x y
          ext
          rfl
        map_smul' := by
          intro a x
          ext
          rfl }
    exact Module.Finite.equiv eLin.symm
  have : FiniteDimensional (AlgHom.fieldRange i) FR :=
    FiniteDimensional.right L (AlgHom.fieldRange i) FR
  refine (krullTopology_mem_nhds_one_iff (AlgHom.fieldRange i)
    (AlgebraicClosure K) (e.symm ⁻¹' s)).2 ?_
  refine ⟨FR, inferInstance, ?_⟩
  intro σ hσ
  apply hFs
  change e.symm σ ∈ F.fixingSubgroup
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  change σ x = x
  have hxFR : x ∈ FR := by
    change x ∈ F.restrictScalars K
    change x ∈ F
    exact hx
  exact (IntermediateField.mem_fixingSubgroup_iff FR σ).1 hσ x hxFR

/-- For a finite extension `L/K` embedded in `K^al`, the absolute Galois
group `G_L` is canonically (up to the chosen algebraic-closure equivalence)
identified with `Gal(K^al / i(L))`. -/
def equivGalFieldRangeOfFiniteExtension [FiniteDimensional K L]
    (i : L →ₐ[K] AlgebraicClosure K) :
    Field.absoluteGaloisGroup L ≃*
      Gal(AlgebraicClosure K / AlgHom.fieldRange i) := by
  letI : Algebra L (AlgebraicClosure K) := i.toRingHom.toAlgebra
  have hmap : ∀ x, algebraMap L (AlgebraicClosure K) x = i x := fun _ => rfl
  haveI : IsScalarTower K L (AlgebraicClosure K) := .of_algebraMap_eq fun x => by
    simp [RingHom.algebraMap_toAlgebra]
  haveI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  haveI : Algebra.IsAlgebraic L (AlgebraicClosure K) :=
    Algebra.IsAlgebraic.tower_top (K := K) (L := L) (A := AlgebraicClosure K)
  haveI : IsAlgClosure L (AlgebraicClosure K) :=
    { isAlgClosed := inferInstance, isAlgebraic := inferInstance }
  let e : AlgebraicClosure L ≃ₐ[L] AlgebraicClosure K :=
    IsAlgClosure.equiv L (AlgebraicClosure L) (AlgebraicClosure K)
  exact (AlgEquiv.autCongr e).trans
    (automorphismsOverFieldRangeEquiv K i hmap)

/-- The field-range identification `G_L ≃ Gal(K^al/i(L))` is continuous. -/
theorem equivGalFieldRangeOfFiniteExtension_continuous
    [FiniteDimensional K L] (i : L →ₐ[K] AlgebraicClosure K) :
    Continuous (equivGalFieldRangeOfFiniteExtension K i :
      Field.absoluteGaloisGroup L →
        Gal(AlgebraicClosure K / AlgHom.fieldRange i)) := by
  let : Algebra L (AlgebraicClosure K) := i.toRingHom.toAlgebra
  have hmap : ∀ x, algebraMap L (AlgebraicClosure K) x = i x := fun _ => rfl
  have : IsScalarTower K L (AlgebraicClosure K) := .of_algebraMap_eq fun x => by
    simp [RingHom.algebraMap_toAlgebra]
  have : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  have : Algebra.IsAlgebraic L (AlgebraicClosure K) :=
    Algebra.IsAlgebraic.tower_top (K := K) (L := L) (A := AlgebraicClosure K)
  have : IsAlgClosure L (AlgebraicClosure K) :=
    { isAlgClosed := inferInstance, isAlgebraic := inferInstance }
  let e : AlgebraicClosure L ≃ₐ[L] AlgebraicClosure K :=
    IsAlgClosure.equiv L (AlgebraicClosure L) (AlgebraicClosure K)
  change Continuous (((AlgEquiv.autCongr e).trans
    (automorphismsOverFieldRangeEquiv K i hmap)) :
      Field.absoluteGaloisGroup L →
        Gal(AlgebraicClosure K / AlgHom.fieldRange i))
  exact (automorphismsOverFieldRangeEquiv_continuous K i hmap).comp
    (algEquiv_autCongr_continuous e)

/-- The inverse field-range identification `Gal(K^al/i(L)) ≃ G_L` is
continuous. -/
theorem equivGalFieldRangeOfFiniteExtension_symm_continuous
    [FiniteDimensional K L] (i : L →ₐ[K] AlgebraicClosure K) :
    Continuous ((equivGalFieldRangeOfFiniteExtension K i).symm :
      Gal(AlgebraicClosure K / AlgHom.fieldRange i) →
        Field.absoluteGaloisGroup L) := by
  let : Algebra L (AlgebraicClosure K) := i.toRingHom.toAlgebra
  have hmap : ∀ x, algebraMap L (AlgebraicClosure K) x = i x := fun _ => rfl
  have : IsScalarTower K L (AlgebraicClosure K) := .of_algebraMap_eq fun x => by
    simp [RingHom.algebraMap_toAlgebra]
  have : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  have : Algebra.IsAlgebraic L (AlgebraicClosure K) :=
    Algebra.IsAlgebraic.tower_top (K := K) (L := L) (A := AlgebraicClosure K)
  have : IsAlgClosure L (AlgebraicClosure K) :=
    { isAlgClosed := inferInstance, isAlgebraic := inferInstance }
  let e : AlgebraicClosure L ≃ₐ[L] AlgebraicClosure K :=
    IsAlgClosure.equiv L (AlgebraicClosure L) (AlgebraicClosure K)
  change Continuous ((((AlgEquiv.autCongr e).trans
    (automorphismsOverFieldRangeEquiv K i hmap)).symm) :
      Gal(AlgebraicClosure K / AlgHom.fieldRange i) →
        Field.absoluteGaloisGroup L)
  exact (algEquiv_autCongr_symm_continuous e).comp
    (automorphismsOverFieldRangeEquiv_symm_continuous K i hmap)

/-- The field-range identification between `G_L` and `Gal(K^al/i(L))` as a
topological group isomorphism. -/
def equivGalFieldRangeOfFiniteExtensionContinuousMulEquiv
    [FiniteDimensional K L] (i : L →ₐ[K] AlgebraicClosure K) :
    Field.absoluteGaloisGroup L ≃ₜ*
      Gal(AlgebraicClosure K / AlgHom.fieldRange i) :=
  { toMulEquiv := equivGalFieldRangeOfFiniteExtension K i
    continuous_toFun := equivGalFieldRangeOfFiniteExtension_continuous K i
    continuous_invFun := equivGalFieldRangeOfFiniteExtension_symm_continuous K i }

/-- The concrete open subgroup of `G_K` attached to `i : L → K^al` is
identified with the absolute Galois group `G_L`. -/
def equivOpenSubgroupOfFiniteExtension [FiniteDimensional K L]
    (i : L →ₐ[K] AlgebraicClosure K) :
    Field.absoluteGaloisGroup L ≃* openSubgroupOfFiniteExtension K i := by
  letI := finiteDimensional_fieldRange (K := K) i
  exact (equivGalFieldRangeOfFiniteExtension K i).trans
    (openSubgroupOfFiniteIntermediateFieldEquiv K (AlgHom.fieldRange i)).symm

/-- The concrete open subgroup of `G_K` attached to `i : L → K^al` is
topologically identified with `G_L`. -/
def equivOpenSubgroupOfFiniteExtensionContinuousMulEquiv
    [FiniteDimensional K L] (i : L →ₐ[K] AlgebraicClosure K) :
    Field.absoluteGaloisGroup L ≃ₜ* openSubgroupOfFiniteExtension K i :=
  (equivGalFieldRangeOfFiniteExtensionContinuousMulEquiv K i).trans
    (openSubgroupOfFiniteExtensionContinuousMulEquiv K i).symm

/-- The concrete map from `G_L` to the finite-extension open subgroup of
`G_K`.  This is the subgroup-valued form of the identification
`G_L ≃ openSubgroupOfFiniteExtension K i`. -/
def toOpenSubgroupOfFiniteExtension [FiniteDimensional K L]
    (i : L →ₐ[K] AlgebraicClosure K) :
    Field.absoluteGaloisGroup L →* openSubgroupOfFiniteExtension K i :=
  (equivOpenSubgroupOfFiniteExtension K i).toMonoidHom

/-- The subgroup-valued inclusion `G_L -> openSubgroupOfFiniteExtension K i`
as a continuous homomorphism. -/
def toOpenSubgroupOfFiniteExtensionContinuous [FiniteDimensional K L]
    (i : L →ₐ[K] AlgebraicClosure K) :
    Field.absoluteGaloisGroup L →ₜ* openSubgroupOfFiniteExtension K i :=
  (equivOpenSubgroupOfFiniteExtensionContinuousMulEquiv K i :
    Field.absoluteGaloisGroup L →ₜ* openSubgroupOfFiniteExtension K i)

/-- States the theorem `toOpenSubgroupOfFiniteExtension_apply`. -/
@[simp]
theorem toOpenSubgroupOfFiniteExtension_apply
    [FiniteDimensional K L] (i : L →ₐ[K] AlgebraicClosure K)
    (σ : Field.absoluteGaloisGroup L) :
    toOpenSubgroupOfFiniteExtension K i σ =
      equivOpenSubgroupOfFiniteExtension K i σ :=
  rfl

/-- States the theorem `toOpenSubgroupOfFiniteExtensionContinuous_apply`. -/
@[simp]
theorem toOpenSubgroupOfFiniteExtensionContinuous_apply
    [FiniteDimensional K L] (i : L →ₐ[K] AlgebraicClosure K)
    (σ : Field.absoluteGaloisGroup L) :
    toOpenSubgroupOfFiniteExtensionContinuous K i σ =
      equivOpenSubgroupOfFiniteExtension K i σ :=
  rfl

/-- States the theorem `coe_equivOpenSubgroupOfFiniteExtension_apply`. -/
@[simp]
theorem coe_equivOpenSubgroupOfFiniteExtension_apply
    [FiniteDimensional K L] (i : L →ₐ[K] AlgebraicClosure K)
    (σ : Field.absoluteGaloisGroup L) :
    ((equivOpenSubgroupOfFiniteExtension K i σ :
      openSubgroupOfFiniteExtension K i) :
      Field.absoluteGaloisGroup K) =
      ofFiniteExtension K i (equivGalFieldRangeOfFiniteExtension K i σ) := by
  dsimp [equivOpenSubgroupOfFiniteExtension,
    openSubgroupOfFiniteIntermediateFieldEquiv, ofFiniteExtension,
    ofIntermediateField]
  rfl

/-- The inclusion `G_L → G_K` obtained by identifying `G_L` with the open
subgroup fixing the embedded image `i(L) ⊆ K^al`. -/
def ofFiniteExtensionAbsolute [FiniteDimensional K L]
    (i : L →ₐ[K] AlgebraicClosure K) :
    Field.absoluteGaloisGroup L →* Field.absoluteGaloisGroup K :=
  ((openSubgroupOfFiniteExtension K i :
    Subgroup (Field.absoluteGaloisGroup K)).subtype).comp
      (equivOpenSubgroupOfFiniteExtension K i).toMonoidHom

/-- The inclusion `G_L -> G_K` as a continuous homomorphism.  Its range is
the concrete open subgroup fixing `i(L)`. -/
def ofFiniteExtensionAbsoluteContinuous [FiniteDimensional K L]
    (i : L →ₐ[K] AlgebraicClosure K) :
    Field.absoluteGaloisGroup L →ₜ* Field.absoluteGaloisGroup K :=
  { toMonoidHom := ofFiniteExtensionAbsolute K i
    continuous_toFun := by
      change Continuous fun σ =>
        ((equivOpenSubgroupOfFiniteExtension K i σ :
          openSubgroupOfFiniteExtension K i) :
          Field.absoluteGaloisGroup K)
      exact
        (continuous_subtype_val.comp
          (equivOpenSubgroupOfFiniteExtensionContinuousMulEquiv K i).continuous_toFun) }

/-- States the theorem `ofFiniteExtensionAbsolute_apply`. -/
@[simp]
theorem ofFiniteExtensionAbsolute_apply [FiniteDimensional K L]
    (i : L →ₐ[K] AlgebraicClosure K) (σ : Field.absoluteGaloisGroup L) :
    ofFiniteExtensionAbsolute K i σ =
      (equivOpenSubgroupOfFiniteExtension K i σ :
        Field.absoluteGaloisGroup K) :=
  rfl

/-- States the theorem `ofFiniteExtensionAbsoluteContinuous_apply`. -/
@[simp]
theorem ofFiniteExtensionAbsoluteContinuous_apply [FiniteDimensional K L]
    (i : L →ₐ[K] AlgebraicClosure K) (σ : Field.absoluteGaloisGroup L) :
    ofFiniteExtensionAbsoluteContinuous K i σ =
      ofFiniteExtensionAbsolute K i σ :=
  rfl









/-- Every element of `G_L`, viewed inside `G_K`, lies in the finite-extension
open subgroup fixing `i(L)`. -/
theorem ofFiniteExtensionAbsolute_mem_openSubgroup
    [FiniteDimensional K L] (i : L →ₐ[K] AlgebraicClosure K)
    (σ : Field.absoluteGaloisGroup L) :
    ofFiniteExtensionAbsolute K i σ ∈ openSubgroupOfFiniteExtension K i := by
  rw [ofFiniteExtensionAbsolute_apply]
  exact (equivOpenSubgroupOfFiniteExtension K i σ).property



/-- The image of `G_L → G_K` is exactly the finite-extension open subgroup
fixing `i(L)`. -/
theorem range_ofFiniteExtensionAbsolute [FiniteDimensional K L]
    (i : L →ₐ[K] AlgebraicClosure K) :
    MonoidHom.range (ofFiniteExtensionAbsolute K i) =
      (openSubgroupOfFiniteExtension K i :
        Subgroup (Field.absoluteGaloisGroup K)) := by
  rw [ofFiniteExtensionAbsolute, MonoidHom.range_comp]
  rw [MonoidHom.range_eq_top_of_surjective _
    (equivOpenSubgroupOfFiniteExtension K i).surjective]
  rw [← (MonoidHom.range_eq_map
    ((openSubgroupOfFiniteExtension K i :
      Subgroup (Field.absoluteGaloisGroup K)).subtype))]
  exact Subgroup.range_subtype
    (openSubgroupOfFiniteExtension K i : Subgroup (Field.absoluteGaloisGroup K))



















/-- Provides the instance `instNormal`. -/
instance range_ofFiniteExtensionAbsolute.instNormal
    [FiniteDimensional K L] [Normal K L]
    (i : L →ₐ[K] AlgebraicClosure K) :
    (MonoidHom.range (ofFiniteExtensionAbsolute K i)).Normal := by
  rw [range_ofFiniteExtensionAbsolute]
  infer_instance

/-- For a finite normal extension, the quotient by the actual image of
`G_L -> G_K` is the automorphism group of the embedded field range. -/
def quotientRangeEquivGalFieldRangeOfNormalFiniteExtension
    [FiniteDimensional K L] [Normal K L]
    (i : L →ₐ[K] AlgebraicClosure K) :
    Field.absoluteGaloisGroup K ⧸
        MonoidHom.range (ofFiniteExtensionAbsolute K i) ≃*
      Gal(AlgHom.fieldRange i / K) :=
  (QuotientGroup.quotientMulEquivOfEq
      (range_ofFiniteExtensionAbsolute K i)).trans
    (quotientOpenSubgroupEquivGalFieldRangeOfNormalFiniteExtension K i)

/-- States the theorem `quotientRangeEquivGalFieldRangeOfNormalFiniteExtension_mk'`. -/
@[simp]
theorem quotientRangeEquivGalFieldRangeOfNormalFiniteExtension_mk'
    [FiniteDimensional K L] [Normal K L]
    (i : L →ₐ[K] AlgebraicClosure K)
    (σ : Field.absoluteGaloisGroup K) :
    quotientRangeEquivGalFieldRangeOfNormalFiniteExtension K i
        (QuotientGroup.mk'
          (MonoidHom.range (ofFiniteExtensionAbsolute K i)) σ) =
      AlgEquiv.restrictNormalHom (AlgHom.fieldRange i) σ := by
  rw [quotientRangeEquivGalFieldRangeOfNormalFiniteExtension,
    MulEquiv.trans_apply]
  change
    quotientOpenSubgroupEquivGalFieldRangeOfNormalFiniteExtension K i
        (QuotientGroup.mk'
          (openSubgroupOfFiniteExtension K i :
            Subgroup (Field.absoluteGaloisGroup K)) σ) =
      AlgEquiv.restrictNormalHom (AlgHom.fieldRange i) σ
  exact quotientOpenSubgroupEquivGalFieldRangeOfNormalFiniteExtension_mk' K i σ

/-- For a finite normal extension, `G_K/G_L` is `Gal(L/K)` when `G_L` is
written as the actual image of `G_L -> G_K`. -/
def quotientRangeEquivGalOfNormalFiniteExtension
    [FiniteDimensional K L] [Normal K L]
    (i : L →ₐ[K] AlgebraicClosure K) :
    Field.absoluteGaloisGroup K ⧸
        MonoidHom.range (ofFiniteExtensionAbsolute K i) ≃*
      Gal(L / K) :=
  (quotientRangeEquivGalFieldRangeOfNormalFiniteExtension K i).trans
    (AlgEquiv.autCongr (AlgEquiv.ofInjectiveField i)).symm

/-- States the theorem `quotientRangeEquivGalOfNormalFiniteExtension_mk'`. -/
@[simp]
theorem quotientRangeEquivGalOfNormalFiniteExtension_mk'
    [FiniteDimensional K L] [Normal K L]
    (i : L →ₐ[K] AlgebraicClosure K)
    (σ : Field.absoluteGaloisGroup K) :
    quotientRangeEquivGalOfNormalFiniteExtension K i
        (QuotientGroup.mk'
          (MonoidHom.range (ofFiniteExtensionAbsolute K i)) σ) =
      (AlgEquiv.autCongr (AlgEquiv.ofInjectiveField i)).symm
        ((@AlgEquiv.restrictNormalHom K _ (AlgebraicClosure K) _ _
          (AlgHom.fieldRange i) _ _ _ (fieldRangeIsScalarTower K i) _) σ) := by
  exact congrArg (AlgEquiv.autCongr (AlgEquiv.ofInjectiveField i)).symm
    (quotientRangeEquivGalFieldRangeOfNormalFiniteExtension_mk' K i σ)

section TwoFiniteExtensions

variable {M : Type w} [Field M] [Algebra K M]









end TwoFiniteExtensions



/-- States the theorem `ofFiniteExtensionAbsolute_apply_embedding`. -/
@[simp]
theorem ofFiniteExtensionAbsolute_apply_embedding
    [FiniteDimensional K L] (i : L →ₐ[K] AlgebraicClosure K)
    (σ : Field.absoluteGaloisGroup L) (x : L) :
    (show Gal(AlgebraicClosure K / K) from
      ofFiniteExtensionAbsolute K i σ) (i x) = i x := by
  exact (mem_openSubgroupOfFiniteExtension_iff_forall_apply_eq K i
    (ofFiniteExtensionAbsolute K i σ)).1
      (ofFiniteExtensionAbsolute_mem_openSubgroup K i σ) x

/-- States the theorem `coe_toOpenSubgroupOfFiniteExtension_apply_embedding`. -/
@[simp]
theorem coe_toOpenSubgroupOfFiniteExtension_apply_embedding
    [FiniteDimensional K L] (i : L →ₐ[K] AlgebraicClosure K)
    (σ : Field.absoluteGaloisGroup L) (x : L) :
    (show Gal(AlgebraicClosure K / K) from
      ((toOpenSubgroupOfFiniteExtension K i σ :
        openSubgroupOfFiniteExtension K i) :
        Field.absoluteGaloisGroup K)) (i x) = i x := by
  simpa [ofFiniteExtensionAbsolute_apply]
    using ofFiniteExtensionAbsolute_apply_embedding K i σ x



/-- States the theorem `ofFiniteExtensionAbsolute_equivOpenSubgroupOfFiniteExtension_symm`. -/
@[simp]
theorem ofFiniteExtensionAbsolute_equivOpenSubgroupOfFiniteExtension_symm
    [FiniteDimensional K L] (i : L →ₐ[K] AlgebraicClosure K)
    (σ : openSubgroupOfFiniteExtension K i) :
    ofFiniteExtensionAbsolute K i
        ((equivOpenSubgroupOfFiniteExtension K i).symm σ) =
      (σ : Field.absoluteGaloisGroup K) := by
  rw [ofFiniteExtensionAbsolute_apply]
  simp

section TwoFiniteExtensionsTower

variable {M : Type w} [Field M] [Algebra K M]

/-- The tower restriction map `G_M -> G_L` induced by embeddings
`L -> M -> K^al`, constructed through the concrete open-subgroup
identifications inside `G_K`. -/
def ofFiniteExtensionAbsoluteTower
    [FiniteDimensional K L] [FiniteDimensional K M]
    (i : M →ₐ[K] AlgebraicClosure K) (j : L →ₐ[K] M) :
    Field.absoluteGaloisGroup M →* Field.absoluteGaloisGroup L :=
  let hle :
      (openSubgroupOfFiniteExtension K i :
        Subgroup (Field.absoluteGaloisGroup K)) ≤
        openSubgroupOfFiniteExtension K (i.comp j) :=
    openSubgroupOfFiniteExtension_comp_le K i j
  let φ : Field.absoluteGaloisGroup M →*
      openSubgroupOfFiniteExtension K (i.comp j) :=
    { toFun := fun σ =>
        ⟨ofFiniteExtensionAbsolute K i σ,
          hle (ofFiniteExtensionAbsolute_mem_openSubgroup K i σ)⟩
      map_one' := by
        ext
        simp [ofFiniteExtensionAbsolute]
      map_mul' := by
        intro σ τ
        ext
        simp [ofFiniteExtensionAbsolute] }
  ((equivOpenSubgroupOfFiniteExtension K (i.comp j)).symm.toMonoidHom).comp φ

/-- The tower map is natural with respect to the concrete inclusions into
`G_K`: the inclusion `G_L -> G_K` after `G_M -> G_L` is the inclusion
`G_M -> G_K`. -/
@[simp]
theorem ofFiniteExtensionAbsoluteTower_naturality
    [FiniteDimensional K L] [FiniteDimensional K M]
    (i : M →ₐ[K] AlgebraicClosure K) (j : L →ₐ[K] M)
    (σ : Field.absoluteGaloisGroup M) :
    ofFiniteExtensionAbsolute K (i.comp j)
        (ofFiniteExtensionAbsoluteTower K i j σ) =
      ofFiniteExtensionAbsolute K i σ := by
  let hle :
      (openSubgroupOfFiniteExtension K i :
        Subgroup (Field.absoluteGaloisGroup K)) ≤
        openSubgroupOfFiniteExtension K (i.comp j) :=
    openSubgroupOfFiniteExtension_comp_le K i j
  let s : openSubgroupOfFiniteExtension K (i.comp j) :=
    ⟨ofFiniteExtensionAbsolute K i σ,
      hle (ofFiniteExtensionAbsolute_mem_openSubgroup K i σ)⟩
  unfold ofFiniteExtensionAbsoluteTower
  change
    ofFiniteExtensionAbsolute K (i.comp j)
        ((equivOpenSubgroupOfFiniteExtension K (i.comp j)).symm s) =
      ofFiniteExtensionAbsolute K i σ
  exact ofFiniteExtensionAbsolute_equivOpenSubgroupOfFiniteExtension_symm
    K (i.comp j) s





end TwoFiniteExtensionsTower





end FiniteExtension

end absoluteGaloisGroup
end Field

namespace DiscreteValuationField
namespace HenselianDVF

variable {K : Type u} [Field K]



end HenselianDVF
end DiscreteValuationField

end

end RamificationTheory
