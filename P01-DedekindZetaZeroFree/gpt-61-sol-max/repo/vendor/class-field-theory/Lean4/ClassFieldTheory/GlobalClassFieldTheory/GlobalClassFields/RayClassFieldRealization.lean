module

public import ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.AlgEquiv
public import ClassFieldTheory.AlgebraicNumberTheory.Galois.NormalFieldRange
public import ClassFieldTheory.AlgebraicNumberTheory.RayClass.Topology
public import ClassFieldTheory.Definitions.GlobalClassFieldTheory.FiniteAbelianExtension
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ConductorLattice
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.FiniteAbelianClassFieldContainment
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Degree
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Topological.QuotientTransport
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Topological.Construction
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Topological.EvaluationValue
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Topological.EvaluationCore
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Topological.Evaluation
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Algebraic.Construction
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Algebraic.Evaluation
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.GlobalNormResidue
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.TopologicalGlobalNormResidue

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


















set_option autoImplicit false

/-!
# Actual ray class fields

For a modulus `m` of a number field `K`, its ray congruence subgroup
`C_K^m` is closed and has finite index.  The finite-index class-field
construction therefore selects an actual finite abelian extension whose
determinant-norm range is exactly `C_K^m`.

The construction first occurs over the canonical fixed-field copy of `K`
inside the rational separable closure.  We then install the canonical
scalar structure from the original field, identify the norm range over
that original field, and obtain the genuine reciprocity equivalence

`Gal(K^m / K) ≃ C_K / C_K^m`.
-/

open scoped Classical NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open ClassFormation
open LocalClassFieldTheory
open NumberField
open Reciprocity
open CyclicCohomology

variable {K : Type} [Field K] [NumberField K]







































/-- A chosen finite ray-class-field realization attached to `m`, selected
inside the rational separable closure.  Its intrinsic realization in the
fixed separable closure of `K` is `rayClassFieldSubfield`. -/
noncomputable abbrev rayClassField
    (K : Type) [Field K] [NumberField K]
    (m : RayClass.Modulus K) : Type :=
  closedFiniteIndexClassField
    (K := K) (RayClass.Modulus.congruenceSubgroup m)
    (RayClass.isClosed_congruenceSubgroup m)














































































/-- A chosen embedding of the finite ray-class-field realization into the
fixed separable closure of its original base field. -/
noncomputable def rayClassFieldEmbedding
    (K : Type) [Field K] [NumberField K]
    (m : RayClass.Modulus K) :
    rayClassField K m →ₐ[K] SeparableClosure K :=
  IsSepClosed.lift


















/-- Over the original number field, the determinant-norm range of the
selected ray class field is exactly `C_K^m`. -/
theorem rayClassField_ideleClassNorm_range_over_original
    (m : RayClass.Modulus K) :
    (_root_.ideleClassNorm K (rayClassField K m)).range =
      RayClass.Modulus.congruenceSubgroup m := by
  simpa only [rayClassField] using
    (closedFiniteIndexClassField_ideleClassNorm_range
      (K := K) (RayClass.Modulus.congruenceSubgroup m)
      (RayClass.isClosed_congruenceSubgroup m))































































































































































































/-- Global reciprocity for the selected ray class field as a
homeomorphic multiplicative equivalence

`Gal(K^m / K) ≃ₜ* C_K / C_K^m`.

The topology is the genuine finite Krull topology on the Galois group
and the native quotient topology on the ray class group. -/
noncomputable def
    rayClassFieldGaloisContinuousMulEquivRayClassGroup
    (m : RayClass.Modulus K) :
    Gal((rayClassField K m) / K) ≃ₜ*
      RayClass.RayClassGroup m := by
  letI : DiscreteTopology (RayClass.RayClassGroup m) :=
    QuotientGroup.discreteTopology
      (RayClass.isOpen_congruenceSubgroup m)
  exact
    { closedFiniteIndexClassFieldGaloisEquivNormQuotient
        (K := K) (RayClass.Modulus.congruenceSubgroup m)
        (RayClass.isClosed_congruenceSubgroup m) with
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := continuous_of_discreteTopology }

/-- The underlying map of topological ray-class reciprocity is the
general closed-finite-index reciprocity equivalence. -/
@[simp]
theorem
    rayClassFieldGaloisContinuousMulEquivRayClassGroup_apply
    (m : RayClass.Modulus K)
    (σ : Gal((rayClassField K m) / K)) :
    rayClassFieldGaloisContinuousMulEquivRayClassGroup
        (K := K) m σ =
      closedFiniteIndexClassFieldGaloisEquivNormQuotient
        (K := K) (RayClass.Modulus.congruenceSubgroup m)
        (RayClass.isClosed_congruenceSubgroup m) σ := by
  rfl













































/-- Global reciprocity identifies the genuine Galois group of the
selected ray class field with the ray class group `C_K / C_K^m`. -/
noncomputable abbrev rayClassFieldGaloisEquivRayClassGroup
    (m : RayClass.Modulus K) :
    Gal((rayClassField K m) / K) ≃*
      RayClass.RayClassGroup m :=
  closedFiniteIndexClassFieldGaloisEquivNormQuotient
    (K := K) (RayClass.Modulus.congruenceSubgroup m)
    (RayClass.isClosed_congruenceSubgroup m)

/-- The subfield of the ray class field fixed by a prescribed ray-class
subgroup, transported through the genuine reciprocity equivalence. -/
noncomputable def rayClassSubgroupFixedField
    (m : RayClass.Modulus K)
    (H : Subgroup (RayClass.RayClassGroup m)) :
    IntermediateField K (rayClassField K m) :=
  IntermediateField.fixedField
    (H.map (rayClassFieldGaloisEquivRayClassGroup (K := K) m).symm.toMonoidHom)










/-- The fixed field is a finite abelian extension of the original field. -/
noncomputable def rayClassSubgroupSubextension
    (m : RayClass.Modulus K)
    (H : Subgroup (RayClass.RayClassGroup m)) :
    ClassFieldTheory.FiniteAbelianExtension K := by
  let F := rayClassSubgroupFixedField (K := K) m H
  let j := rayClassFieldEmbedding K m
  let E := F.map j
  have hfin : FiniteDimensional K E :=
    (IntermediateField.equivMap F j).toLinearEquiv.finiteDimensional
  have hab : IsAbelianGalois K E :=
    IsAbelianGalois.of_algHom
      (IntermediateField.equivMap F j).symm.toAlgHom
  exact ⟨E, hfin, hab⟩

/-- The ray class group acts on the subfield fixed by `H` by restricting
the reciprocity action on the full ray class field. -/
noncomputable def rayClassSubgroupFixedFieldArtin
    (m : RayClass.Modulus K)
    (H : Subgroup (RayClass.RayClassGroup m)) :
    RayClass.RayClassGroup m →*
      (rayClassSubgroupFixedField (K := K) m H ≃ₐ[K]
        rayClassSubgroupFixedField (K := K) m H) :=
  (AlgEquiv.restrictNormalHom
      (rayClassSubgroupFixedField (K := K) m H)).comp
    (rayClassFieldGaloisEquivRayClassGroup (K := K) m).symm.toMonoidHom

/-- The restricted reciprocity action reaches every automorphism of
the fixed field. -/
theorem rayClassSubgroupFixedFieldArtin_surjective
    (m : RayClass.Modulus K)
    (H : Subgroup (RayClass.RayClassGroup m)) :
    Function.Surjective (rayClassSubgroupFixedFieldArtin (K := K) m H) := by
  intro τ
  obtain ⟨σ, hσ⟩ :=
    AlgEquiv.restrictNormalHom_surjective (E := rayClassField K m) τ
  refine ⟨rayClassFieldGaloisEquivRayClassGroup (K := K) m σ, ?_⟩
  simpa [rayClassSubgroupFixedFieldArtin] using hσ

/-- The exact kernel of the fixed-field reciprocity action is `H`. -/
theorem rayClassSubgroupFixedFieldArtin_ker
    (m : RayClass.Modulus K)
    (H : Subgroup (RayClass.RayClassGroup m)) :
    (rayClassSubgroupFixedFieldArtin (K := K) m H).ker = H := by
  let e := rayClassFieldGaloisEquivRayClassGroup (K := K) m
  let F := rayClassSubgroupFixedField (K := K) m H
  have hfix : F.fixingSubgroup = H.map e.symm.toMonoidHom := by
    exact IntermediateField.fixingSubgroup_fixedField
      (H.map e.symm.toMonoidHom)
  ext x
  change e.symm x ∈ (AlgEquiv.restrictNormalHom F).ker ↔ x ∈ H
  rw [F.restrictNormalHom_ker, hfix]
  constructor
  · rintro ⟨y, hy, hxy⟩
    exact (e.symm.injective hxy) ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

 theorem rayClassGroup_mul_comm
    (m : RayClass.Modulus K)
    (x y : RayClass.RayClassGroup m) : x * y = y * x := by
  refine QuotientGroup.induction_on x ?_
  intro a
  refine QuotientGroup.induction_on y ?_
  intro b
  simpa only [← QuotientGroup.mk_mul, QuotientGroup.mk'_apply] using
    congrArg (QuotientGroup.mk' (RayClass.Modulus.congruenceSubgroup m))
      (mul_comm a b)

/-- Inversion of ray classes is a homomorphism because idèle classes
commute. This form does not require a commutative-group instance on the
quotient presentation. -/
 def rayClassGroupInvHom (m : RayClass.Modulus K) :
    RayClass.RayClassGroup m →* RayClass.RayClassGroup m where
  toFun := Inv.inv
  map_one' := inv_one
  map_mul' x y := by
    rw [mul_inv_rev]
    exact rayClassGroup_mul_comm (K := K) m y⁻¹ x⁻¹

/-- Arithmetic reciprocity on the fixed field, transported to the chosen
subextension of the separable closure of `K`. The ambient ray-class
equivalence is geometrically normalized, so its input is inverted. -/
noncomputable def rayClassSubgroupArtin
    (m : RayClass.Modulus K)
    (H : Subgroup (RayClass.RayClassGroup m)) :
    RayClass.RayClassGroup m →*
      (rayClassSubgroupSubextension (K := K) m H ≃ₐ[K]
        rayClassSubgroupSubextension (K := K) m H) :=
  (AlgEquiv.autCongr
      (IntermediateField.equivMap
        (rayClassSubgroupFixedField (K := K) m H)
        (rayClassFieldEmbedding K m))).toMonoidHom.comp
    ((rayClassSubgroupFixedFieldArtin (K := K) m H).comp
      (rayClassGroupInvHom (K := K) m))

/-- The transported reciprocity map is surjective. -/
theorem rayClassSubgroupArtin_surjective
    (m : RayClass.Modulus K)
    (H : Subgroup (RayClass.RayClassGroup m)) :
    Function.Surjective (rayClassSubgroupArtin (K := K) m H) := by
  let F := rayClassSubgroupFixedField (K := K) m H
  let j := rayClassFieldEmbedding K m
  let α := AlgEquiv.autCongr (IntermediateField.equivMap F j)
  change Function.Surjective
    (α.toMonoidHom.comp
      ((rayClassSubgroupFixedFieldArtin (K := K) m H).comp
        (rayClassGroupInvHom (K := K) m)))
  exact (α.surjective.comp
    (rayClassSubgroupFixedFieldArtin_surjective (K := K) m H)).comp
      (fun x => ⟨x⁻¹, inv_inv x⟩)

/-- The transported reciprocity map has exactly the prescribed kernel. -/
theorem rayClassSubgroupArtin_ker
    (m : RayClass.Modulus K)
    (H : Subgroup (RayClass.RayClassGroup m)) :
    (rayClassSubgroupArtin (K := K) m H).ker = H := by
  let F := rayClassSubgroupFixedField (K := K) m H
  let j := rayClassFieldEmbedding K m
  let α := AlgEquiv.autCongr (IntermediateField.equivMap F j)
  let a := rayClassSubgroupFixedFieldArtin (K := K) m H
  ext x
  change α (a x⁻¹) = 1 ↔ x ∈ H
  have hx : a x⁻¹ = 1 ↔ x⁻¹ ∈ H := by
    change x⁻¹ ∈ a.ker ↔ x⁻¹ ∈ H
    rw [rayClassSubgroupFixedFieldArtin_ker (K := K) m H]
  constructor
  · intro h
    exact H.inv_mem_iff.mp
      (hx.mp (α.injective (h.trans (map_one α).symm)))
  · intro h
    simp only [hx.mpr (H.inv_mem_iff.mpr h), map_one]

/-- The fixed subextension has a norm subgroup containing the ray
congruence subgroup. This is the defining-modulus input for its
unramifiedness away from the modulus. -/
theorem rayClassSubgroupSubextension_norm_range
    (m : RayClass.Modulus K)
    (H : Subgroup (RayClass.RayClassGroup m)) :
    RayClass.Modulus.congruenceSubgroup m ≤
      (_root_.ideleClassNorm K
        (rayClassSubgroupSubextension (K := K) m H)).range := by
  let F := rayClassSubgroupFixedField (K := K) m H
  let j := rayClassFieldEmbedding K m
  let E := rayClassSubgroupSubextension (K := K) m H
  let f : E →ₐ[K] rayClassField K m :=
    (IntermediateField.val F).comp
      (IntermediateField.equivMap F j).symm.toAlgHom
  have hle :
      (_root_.ideleClassNorm K (rayClassField K m)).range ≤
        (_root_.ideleClassNorm K E).range :=
    ideleClassNorm_range_le_of_algHom (K := K) E (rayClassField K m) f
  calc
    RayClass.Modulus.congruenceSubgroup m =
        (_root_.ideleClassNorm K (rayClassField K m)).range :=
      (rayClassField_ideleClassNorm_range_over_original m).symm
    _ ≤ (_root_.ideleClassNorm K E).range := hle
    _ = (_root_.ideleClassNorm K
        (rayClassSubgroupSubextension (K := K) m H)).range := rfl

/-- Under ray-class reciprocity, the actual global norm-residue symbol
is the ray class of its idèle-class representative. -/
@[simp]
theorem rayClassFieldGaloisEquivRayClassGroup_globalNormResidue
    (m : RayClass.Modulus K)
    (c : IdeleClassGroup K) :
    rayClassFieldGaloisEquivRayClassGroup
        (K := K) m
        (globalNormResidueMonoidHom K
          (rayClassField K m) c) =
      QuotientGroup.mk'
        (RayClass.Modulus.congruenceSubgroup m) c := by
  simpa only [rayClassField, rayClassFieldGaloisEquivRayClassGroup] using
    (closedFiniteIndexClassFieldGaloisEquivNormQuotient_globalNormResidue
      (K := K) (RayClass.Modulus.congruenceSubgroup m)
      (RayClass.isClosed_congruenceSubgroup m) c)

end GlobalClassFields
end GlobalClassFieldTheory

end
