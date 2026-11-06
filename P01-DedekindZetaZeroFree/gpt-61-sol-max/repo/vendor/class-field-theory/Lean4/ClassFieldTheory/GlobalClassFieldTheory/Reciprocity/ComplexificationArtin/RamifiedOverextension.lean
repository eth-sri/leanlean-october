module

public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.ComplexificationArtin.InfinitePlaceOverfield

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/



set_option autoImplicit false

/-!
# The quadratic overextension at a ramified real place

This module constructs the real fixed field of complex conjugation, the
quadratic overextension above it, and the faithful cyclotomic restriction.
-/

open scoped Classical IsMulCommutative
open NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

attribute [local instance]
  infinitePlaceComplexificationOverfieldRationalAlgebra

section ComplexConjugationOverextension

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]

/-- The base `K'` in the archimedean overextension: the fixed field
of complex conjugation in `L(i)`. -/

local notation:max "current_infinitePlaceComplexificationOverfield" => infinitePlaceComplexificationOverfield (K := K) (L := L)


local notation:max "current_ramifiedInfinitePlaceOverfieldConjugation" => ramifiedInfinitePlaceOverfieldConjugation (K := K) (L := L)

def ramifiedInfinitePlaceRealFixedField
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :
    IntermediateField ℚ
      (current_infinitePlaceComplexificationOverfield v) :=
  IntermediateField.fixedField
    (Subgroup.zpowers
      (current_ramifiedInfinitePlaceOverfieldConjugation v hRamified))

omit [FiniteDimensional K L] in
/-- Ambient complex conjugation on the overfield fixes the embedded base
field at a ramified real place. -/
theorem ramifiedInfinitePlaceOverfieldConjugation_fixes_base
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K)
    (x : K) :
    current_ramifiedInfinitePlaceOverfieldConjugation v hRamified
        (algebraMap K
          (current_infinitePlaceComplexificationOverfield v) x) =
      algebraMap K
        (current_infinitePlaceComplexificationOverfield v) x := by
  apply Subtype.ext
  let w := chosenInfinitePlaceAbove (L := L) v
  let σ :=
    chosenInfinitePlaceArtinMonoidHom
      (K := K) (L := L) v
      (-1 : v.Completionˣ)
  have hσ :
      NumberField.ComplexEmbedding.IsConj
        (InfinitePlace.embedding w) σ :=
    chosenInfinitePlaceArtinMonoidHom_neg_one_isConj_of_ramified
      (K := K) (L := L) v hRamified
  change
    star
        (InfinitePlace.embedding w
          (algebraMap K L x)) =
      InfinitePlace.embedding w
        (algebraMap K L x)
  calc
    star
        (InfinitePlace.embedding w
          (algebraMap K L x)) =
        InfinitePlace.embedding w
          (σ (algebraMap K L x)) :=
      (hσ.eq (algebraMap K L x)).symm
    _ =
        InfinitePlace.embedding w
          (algebraMap K L x) := by
      exact
        congrArg (InfinitePlace.embedding w)
          (σ.commutes x)

/-- The compatible embedding `K → K'` into the real fixed field. -/

local notation:max "current_ramifiedInfinitePlaceRealFixedField" => ramifiedInfinitePlaceRealFixedField (K := K) (L := L)

noncomputable def ramifiedInfinitePlaceRealFixedFieldEmbedding
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :
    K →ₐ[ℚ]
      current_ramifiedInfinitePlaceRealFixedField v hRamified :=
  (IsScalarTower.toAlgHom ℚ K
      (current_infinitePlaceComplexificationOverfield v)).codRestrict
    (current_ramifiedInfinitePlaceRealFixedField v hRamified).toSubalgebra
    (fun x => by
      apply
        (IntermediateField.mem_fixedField_iff _ _).2
      intro g hg
      have hc :
          current_ramifiedInfinitePlaceOverfieldConjugation v hRamified ∈
            MulAction.stabilizer
              ((current_infinitePlaceComplexificationOverfield v) ≃ₐ[ℚ]
                current_infinitePlaceComplexificationOverfield v)
              (algebraMap K
                (current_infinitePlaceComplexificationOverfield v) x) := by
        exact
          MulAction.mem_stabilizer_iff.mpr
            (ramifiedInfinitePlaceOverfieldConjugation_fixes_base
              (K := K) (L := L) v hRamified x)
      exact
        MulAction.mem_stabilizer_iff.mp
          ((Subgroup.zpowers_le).2 hc hg))

omit [FiniteDimensional K L] in
/-- The fixed-field embedding agrees with the original base-field
algebra map after coercion to the overfield. -/
@[simp]
theorem ramifiedInfinitePlaceRealFixedFieldEmbedding_coe
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K)
    (x : K) :
    ((ramifiedInfinitePlaceRealFixedFieldEmbedding
        (K := K) (L := L) v hRamified x :
      current_ramifiedInfinitePlaceRealFixedField v hRamified) :
      current_infinitePlaceComplexificationOverfield v) =
      algebraMap K
        (current_infinitePlaceComplexificationOverfield v) x := by
  calc
    ((ramifiedInfinitePlaceRealFixedFieldEmbedding
        (K := K) (L := L) v hRamified x :
      current_ramifiedInfinitePlaceRealFixedField v hRamified) :
      current_infinitePlaceComplexificationOverfield v) =
        (IsScalarTower.toAlgHom ℚ K
          (current_infinitePlaceComplexificationOverfield v)) x := by
      exact
        AlgHom.coe_codRestrict
          (IsScalarTower.toAlgHom ℚ K
            (current_infinitePlaceComplexificationOverfield v))
          (current_ramifiedInfinitePlaceRealFixedField v hRamified).toSubalgebra _ x
    _ = algebraMap K
        (current_infinitePlaceComplexificationOverfield v) x :=
      IsScalarTower.toAlgHom_apply ℚ K
        (current_infinitePlaceComplexificationOverfield v) x

@[reducible]
noncomputable instance
    ramifiedInfinitePlaceRealFixedField_algebra
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :
    Algebra K
      (current_ramifiedInfinitePlaceRealFixedField v hRamified) :=
  (ramifiedInfinitePlaceRealFixedFieldEmbedding
    (K := K) (L := L) v hRamified).toRingHom.toAlgebra

instance ramifiedInfinitePlaceRealFixedField_ratScalarTower
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :
    IsScalarTower ℚ K
      (current_ramifiedInfinitePlaceRealFixedField v hRamified) :=
  IsScalarTower.of_algHom
    (ramifiedInfinitePlaceRealFixedFieldEmbedding
      (K := K) (L := L) v hRamified)

instance ramifiedInfinitePlaceRealFixedField_scalarTower
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :
    IsScalarTower K
      (current_ramifiedInfinitePlaceRealFixedField v hRamified)
      (current_infinitePlaceComplexificationOverfield v) :=
  IsScalarTower.of_algHom
    { (current_ramifiedInfinitePlaceRealFixedField v hRamified).val.toRingHom with
      commutes' := fun x =>
        ramifiedInfinitePlaceRealFixedFieldEmbedding_coe
          (K := K) (L := L) v hRamified x }

omit [NumberField K] [FiniteDimensional K L] in
theorem
    ramifiedInfinitePlaceRealFixedField_finiteDimensional
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :
    FiniteDimensional ℚ
      (current_ramifiedInfinitePlaceRealFixedField v hRamified) :=
  FiniteDimensional.left ℚ
    (current_ramifiedInfinitePlaceRealFixedField v hRamified)
    (current_infinitePlaceComplexificationOverfield v)

noncomputable instance ramifiedInfinitePlaceRealFixedField_numberField
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :
    NumberField
      (current_ramifiedInfinitePlaceRealFixedField v hRamified) :=
  by
    let : FiniteDimensional ℚ
        (current_ramifiedInfinitePlaceRealFixedField v hRamified) :=
      ramifiedInfinitePlaceRealFixedField_finiteDimensional
        (K := K) (L := L) v hRamified
    exact
      NumberField.of_module_finite ℚ
        (current_ramifiedInfinitePlaceRealFixedField v hRamified)














noncomputable instance
    ramifiedInfinitePlaceRealFixedField_isAbelianGalois_over_base
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :
    IsAbelianGalois K
      (current_ramifiedInfinitePlaceRealFixedField v hRamified) :=
  IsAbelianGalois.tower_bot K
    (current_ramifiedInfinitePlaceRealFixedField v hRamified)
    (current_infinitePlaceComplexificationOverfield v)


















omit [NumberField K] [FiniteDimensional K L] in
theorem ramifiedInfinitePlaceOverextension_isGalois
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :
    IsGalois
      (current_ramifiedInfinitePlaceRealFixedField v hRamified)
      (current_infinitePlaceComplexificationOverfield v) := by
  unfold ramifiedInfinitePlaceRealFixedField
  exact
    IsGalois.of_fixed_field
      (current_infinitePlaceComplexificationOverfield v)
      (Subgroup.zpowers
        (current_ramifiedInfinitePlaceOverfieldConjugation v hRamified))

noncomputable instance
    ramifiedInfinitePlaceOverextension_isAbelianGalois
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :
    IsAbelianGalois
      (current_ramifiedInfinitePlaceRealFixedField v hRamified)
      (current_infinitePlaceComplexificationOverfield v) := by
  let : IsGalois
      (current_ramifiedInfinitePlaceRealFixedField v hRamified)
      (current_infinitePlaceComplexificationOverfield v) :=
    ramifiedInfinitePlaceOverextension_isGalois
      (K := K) (L := L) v hRamified
  let H :=
    Subgroup.zpowers
      (current_ramifiedInfinitePlaceOverfieldConjugation v hRamified)
  let e :=
    IntermediateField.subgroupEquivAlgEquiv H
  let :
      IsCyclic
        Gal(
          (current_infinitePlaceComplexificationOverfield v) /
          (current_ramifiedInfinitePlaceRealFixedField v hRamified)) :=
    e.isCyclic.mp
      (Subgroup.isCyclic_zpowers
        (current_ramifiedInfinitePlaceOverfieldConjugation v hRamified))
  exact IsAbelianGalois.of_isCyclic _ _

/-- The distinguished nontrivial automorphism of the quadratic
overextension `L(i)/K'`, obtained from ambient complex conjugation. -/
noncomputable def ramifiedInfinitePlaceOverextensionConjugation
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :
    Gal(
      (current_infinitePlaceComplexificationOverfield v) /
      (current_ramifiedInfinitePlaceRealFixedField v hRamified)) :=
  IntermediateField.subgroupEquivAlgEquiv
    (Subgroup.zpowers
      (current_ramifiedInfinitePlaceOverfieldConjugation v hRamified))
    ⟨ramifiedInfinitePlaceOverfieldConjugation
        (K := K) (L := L) v hRamified,
      Subgroup.mem_zpowers
        (current_ramifiedInfinitePlaceOverfieldConjugation v hRamified)⟩

omit [NumberField K] [FiniteDimensional K L] in
/-- The distinguished overextension automorphism is the restriction
of ambient complex conjugation. -/
@[simp]
theorem ramifiedInfinitePlaceOverextensionConjugation_apply
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K)
    (z :
      current_infinitePlaceComplexificationOverfield v) :
    ramifiedInfinitePlaceOverextensionConjugation
        (K := K) (L := L) v hRamified z =
      current_ramifiedInfinitePlaceOverfieldConjugation v hRamified z := by
  rfl

omit [NumberField K] [FiniteDimensional K L] in
/-- Every automorphism of the overextension is either the identity or
the distinguished complex conjugation. -/
theorem ramifiedInfinitePlaceOverextension_eq_one_or_conjugation
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K)
    (σ :
      Gal(
        (current_infinitePlaceComplexificationOverfield v) /
        (current_ramifiedInfinitePlaceRealFixedField v hRamified))) :
    σ = 1 ∨
      σ =
        ramifiedInfinitePlaceOverextensionConjugation
          (K := K) (L := L) v hRamified := by
  let c :=
    current_ramifiedInfinitePlaceOverfieldConjugation v hRamified
  let H := Subgroup.zpowers c
  let e :=
    IntermediateField.subgroupEquivAlgEquiv H
  let cH : H :=
    ⟨c, Subgroup.mem_zpowers c⟩
  have hcSq : c ^ 2 = 1 :=
    (pow_two c).trans
      (ramifiedInfinitePlaceOverfieldConjugation_sq
        (K := K) (L := L) v hRamified)
  have hσCases :
      (e.symm σ).1 = 1 ∨
        (e.symm σ).1 = c := by
    obtain ⟨n, hσ⟩ :=
      Subgroup.mem_zpowers_iff.mp (e.symm σ).property
    have hσPower :
        (e.symm σ).1 = c ^ (n % (2 : ℤ)) :=
      hσ.symm.trans
        (zpow_eq_zpow_emod' n hcSq)
    rcases Int.emod_two_eq_zero_or_one n with hn | hn
    · left
      exact
        hσPower.trans
          ((congrArg (fun m : ℤ => c ^ m) hn).trans
            (zpow_zero c))
    · right
      exact
        hσPower.trans
          ((congrArg (fun m : ℤ => c ^ m) hn).trans
            (zpow_one c))
  rcases hσCases with hσ | hσ
  · left
    have hσSub : e.symm σ = 1 :=
      Subtype.ext hσ
    exact
      e.symm.injective
        (hσSub.trans
          (map_one e.symm).symm)
  · right
    have hσSub : e.symm σ = cH :=
      Subtype.ext hσ
    change σ = e cH
    exact
      (e.apply_symm_apply σ).symm.trans
        (congrArg e hσSub)

attribute [local instance]
  rationalComplexificationCyclotomicField_isAbelianGalois

/-- Restriction of the quadratic overextension Galois group to the
rational fourth-root factor. -/
noncomputable def
    ramifiedInfinitePlaceOverextensionCyclotomicRestriction
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :
    Gal(
      (current_infinitePlaceComplexificationOverfield v) /
      (current_ramifiedInfinitePlaceRealFixedField v hRamified)) →*
      Gal(rationalComplexificationCyclotomicField / ℚ) :=
  (AlgEquiv.restrictNormalHom
    rationalComplexificationCyclotomicField).comp
      (AlgEquiv.restrictScalarsHom ℚ)

omit [NumberField K] [FiniteDimensional K L] in
/-- The mapped primitive fourth root in the overfield is not fixed by
ambient complex conjugation. -/
theorem ramifiedInfinitePlaceOverfieldConjugation_map_zeta_ne
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :
    current_ramifiedInfinitePlaceOverfieldConjugation v hRamified
        (algebraMap rationalComplexificationCyclotomicField
          (current_infinitePlaceComplexificationOverfield v)
          (IsCyclotomicExtension.zeta
            4 ℚ rationalComplexificationCyclotomicField)) ≠
      algebraMap rationalComplexificationCyclotomicField
        (current_infinitePlaceComplexificationOverfield v)
        (IsCyclotomicExtension.zeta
          4 ℚ rationalComplexificationCyclotomicField) := by
  let ζ :=
    IsCyclotomicExtension.zeta
      4 ℚ rationalComplexificationCyclotomicField
  let j :
      current_infinitePlaceComplexificationOverfield v :=
    algebraMap rationalComplexificationCyclotomicField
      (current_infinitePlaceComplexificationOverfield v) ζ
  have hζ :
      IsPrimitiveRoot ζ 4 :=
    IsCyclotomicExtension.zeta_spec
      4 ℚ rationalComplexificationCyclotomicField
  have hj :
      IsPrimitiveRoot j 4 :=
    hζ.map_of_injective
      (algebraMap rationalComplexificationCyclotomicField
        (current_infinitePlaceComplexificationOverfield v)).injective
  have hj2 : j ^ 2 = -1 :=
    (hj.pow (by norm_num : 0 < 4)
      (show 4 = 2 * 2 by norm_num)).eq_neg_one_of_two_right
  intro hfixed
  have hfixedComplex :
      star (j : ℂ) = (j : ℂ) := by
    simpa only [j,
      ramifiedInfinitePlaceOverfieldConjugation_apply] using
      congrArg Subtype.val hfixed
  have hj2Complex : (j : ℂ) ^ 2 = -1 :=
    congrArg Subtype.val hj2
  have hjIm : (j : ℂ).im = 0 :=
    Complex.conj_eq_iff_im.mp hfixedComplex
  have hjRe := congrArg Complex.re hj2Complex
  simp only [pow_two, Complex.mul_re,
    Complex.neg_re, Complex.one_re] at hjRe
  nlinarith [hjIm, sq_nonneg (j : ℂ).re]

omit [NumberField K] [FiniteDimensional K L] in
/-- The distinguished overextension conjugation restricts
nontrivially to the rational fourth-root factor. -/
theorem
    ramifiedInfinitePlaceOverextensionCyclotomicRestriction_conjugation_ne_one
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :
    ramifiedInfinitePlaceOverextensionCyclotomicRestriction
        (K := K) (L := L) v hRamified
        (ramifiedInfinitePlaceOverextensionConjugation
          (K := K) (L := L) v hRamified) ≠
      1 := by
  intro h
  apply
    ramifiedInfinitePlaceOverfieldConjugation_map_zeta_ne
      (K := K) (L := L) v hRamified
  have hz :=
    DFunLike.congr_fun h
      (IsCyclotomicExtension.zeta
        4 ℚ rationalComplexificationCyclotomicField)
  change
    ramifiedInfinitePlaceOverextensionCyclotomicRestriction
        (K := K) (L := L) v hRamified
        (ramifiedInfinitePlaceOverextensionConjugation
          (K := K) (L := L) v hRamified)
        (IsCyclotomicExtension.zeta
          4 ℚ rationalComplexificationCyclotomicField) =
      IsCyclotomicExtension.zeta
        4 ℚ rationalComplexificationCyclotomicField at hz
  have hz' :=
    congrArg
      (algebraMap rationalComplexificationCyclotomicField
        (current_infinitePlaceComplexificationOverfield v))
      hz
  change
    (algebraMap rationalComplexificationCyclotomicField
      (current_infinitePlaceComplexificationOverfield v))
        (((AlgEquiv.restrictNormalHom
          rationalComplexificationCyclotomicField)
            ((ramifiedInfinitePlaceOverextensionConjugation
              (K := K) (L := L) v hRamified).restrictScalars ℚ))
          (IsCyclotomicExtension.zeta
            4 ℚ rationalComplexificationCyclotomicField)) =
      (algebraMap rationalComplexificationCyclotomicField
        (current_infinitePlaceComplexificationOverfield v))
        (IsCyclotomicExtension.zeta
          4 ℚ rationalComplexificationCyclotomicField) at hz'
  calc
    current_ramifiedInfinitePlaceOverfieldConjugation v hRamified
        (algebraMap rationalComplexificationCyclotomicField
          (current_infinitePlaceComplexificationOverfield v)
          (IsCyclotomicExtension.zeta
            4 ℚ rationalComplexificationCyclotomicField)) =
      (ramifiedInfinitePlaceOverextensionConjugation
        (K := K) (L := L) v hRamified).restrictScalars ℚ
        (algebraMap rationalComplexificationCyclotomicField
          (current_infinitePlaceComplexificationOverfield v)
          (IsCyclotomicExtension.zeta
            4 ℚ rationalComplexificationCyclotomicField)) := by
      exact
        (ramifiedInfinitePlaceOverextensionConjugation_apply
          (K := K) (L := L) v hRamified _).symm
    _ =
        (algebraMap rationalComplexificationCyclotomicField
          (current_infinitePlaceComplexificationOverfield v))
          (((AlgEquiv.restrictNormalHom
            rationalComplexificationCyclotomicField)
              ((ramifiedInfinitePlaceOverextensionConjugation
                (K := K) (L := L) v hRamified).restrictScalars ℚ))
            (IsCyclotomicExtension.zeta
              4 ℚ rationalComplexificationCyclotomicField)) := by
      exact
        (AlgEquiv.restrictNormal_commutes
          ((ramifiedInfinitePlaceOverextensionConjugation
            (K := K) (L := L) v hRamified).restrictScalars ℚ)
          rationalComplexificationCyclotomicField
          (IsCyclotomicExtension.zeta
            4 ℚ rationalComplexificationCyclotomicField)).symm
    _ =
        (algebraMap rationalComplexificationCyclotomicField
          (current_infinitePlaceComplexificationOverfield v))
          (IsCyclotomicExtension.zeta
            4 ℚ rationalComplexificationCyclotomicField) := hz'

omit [NumberField K] [FiniteDimensional K L] in
/-- Restriction to the rational fourth-root factor is injective on the
quadratic overextension. -/
theorem
    ramifiedInfinitePlaceOverextensionCyclotomicRestriction_injective
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :
    Function.Injective
      (ramifiedInfinitePlaceOverextensionCyclotomicRestriction
        (K := K) (L := L) v hRamified) := by
  apply
    (injective_iff_map_eq_one
      (ramifiedInfinitePlaceOverextensionCyclotomicRestriction
        (K := K) (L := L) v hRamified)).2
  intro σ hσ
  rcases
      ramifiedInfinitePlaceOverextension_eq_one_or_conjugation
        (K := K) (L := L) v hRamified σ with hσOne | hσConj
  · exact hσOne
  · subst σ
    exact
      (ramifiedInfinitePlaceOverextensionCyclotomicRestriction_conjugation_ne_one
        (K := K) (L := L) v hRamified hσ).elim

end ComplexConjugationOverextension

end Reciprocity
end GlobalClassFieldTheory

end
