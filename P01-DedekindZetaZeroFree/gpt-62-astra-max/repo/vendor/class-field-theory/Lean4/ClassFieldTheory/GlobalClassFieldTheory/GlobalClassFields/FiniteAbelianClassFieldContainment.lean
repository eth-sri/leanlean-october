module

public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Degree
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Topological.QuotientTransport
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Topological.Construction
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Topological.EvaluationValue
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Topological.EvaluationCore
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Topological.Evaluation
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Algebraic.Construction
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Algebraic.Evaluation
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.GlobalNormResidue
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.EmbeddedAbelianSubextension
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.NormTowerConductor

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

/-!
# Containment of finite abelian class fields

For actual finite abelian extensions of a number field, containment is
exactly reverse containment of their genuine idèle-class norm ranges.

The proof first realizes an arbitrary extension in the same rational
separable closure as the class field selected by a closed finite-index
subgroup.  The abstract finite-abelian classification then gives a
literal inclusion of fixing subgroups, which restricts the chosen
ambient embedding to an actual algebra embedding into the selected
class field.  Applying this construction to the norm range of a second
extension yields the intrinsic containment criterion over the original
number field.
-/

open scoped Classical NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open ClassFormation
open LocalClassFieldTheory
open NumberField
open RamificationTheory
open Reciprocity

variable {K : Type} [Field K] [NumberField K]

private theorem subgroup_map_toAddSubgroup_mulEquiv_eq
    {G G₂ : Type*} [Group G] [Group G₂]
    (S : Subgroup G) (T : Subgroup G₂) (e : G ≃* G₂)
    (hmap : S.map e.toMonoidHom = T) :
    T.toAddSubgroup =
      S.toAddSubgroup.map
        (MulEquiv.toAdditive e).toAddMonoidHom := by
  rw [← hmap]
  exact (MonoidHom.coe_toAdditive_map e.toMonoidHom S).symm

section

variable (H : Subgroup (IdeleClassGroup K)) (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex]

/-- The distinguished embedding of the original number field into the
rational separable closure underlying the class field selected by
`H`. -/
noncomputable def closedFiniteIndexClassFieldBaseEmbedding :
    K →ₐ[ℚ] SeparableClosure ℚ :=
  numberFieldTowerLowerEmbedding K
    (closedFiniteIndexClassFieldNormAmbient
      (K := K) H hclosed)

/-- The canonical fixed-field equivalence has the distinguished base
embedding as its underlying map into the rational separable closure. -/
@[simp]
theorem closedFiniteIndexClassFieldBaseEquiv_coe
    (x : K) :
    ((closedFiniteIndexClassFieldBaseEquiv
        (K := K) H hclosed x :
      closedFiniteIndexClassFieldBase
        (K := K) H hclosed) :
      SeparableClosure ℚ) =
      closedFiniteIndexClassFieldBaseEmbedding
        (K := K) H hclosed x := rfl

 noncomputable def
    finiteAbelianClassFieldContainmentIdeleClassEquiv :
    IdeleClassGroup K ≃*
      IdeleClassGroup
        (closedFiniteIndexClassFieldBase
          (K := K) H hclosed) :=
  ideleClassCongr
    (closedFiniteIndexClassFieldBaseEquiv
      (K := K) H hclosed)

end

section

variable (H : Subgroup (IdeleClassGroup K)) (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex] (E : Type) [Field E] [NumberField E] [Algebra K E] [FiniteDimensional K E]

/-- An actual finite extension of `K`, embedded into the rational
separable closure compatibly with the selected class-field copy of
`K`. -/
noncomputable def closedFiniteIndexClassFieldCompatibleEmbedding :
    E →ₐ[ℚ] SeparableClosure ℚ :=
  Classical.choose
    (IsAlgClosed.surjective_domRestrict_of_isAlgebraic
      (K := ℚ) (L := K) (E := E)
      (M := SeparableClosure ℚ)
      (closedFiniteIndexClassFieldBaseEmbedding
        (K := K) H hclosed))

/-- The compatible top embedding restricts to the distinguished
embedding of the original base field. -/
@[simp]
theorem
    closedFiniteIndexClassFieldCompatibleEmbedding_restrictDomain :
    (closedFiniteIndexClassFieldCompatibleEmbedding
      (K := K) H hclosed E).domRestrict K =
      closedFiniteIndexClassFieldBaseEmbedding
        (K := K) H hclosed :=
  Classical.choose_spec
    (IsAlgClosed.surjective_domRestrict_of_isAlgebraic
      (K := ℚ) (L := K) (E := E)
      (M := SeparableClosure ℚ)
      (closedFiniteIndexClassFieldBaseEmbedding
        (K := K) H hclosed))

/-- Evaluation on the original scalar map agrees with the
distinguished base embedding. -/
@[simp]
theorem closedFiniteIndexClassFieldCompatibleEmbedding_algebraMap
    (x : K) :
    closedFiniteIndexClassFieldCompatibleEmbedding
        (K := K) H hclosed E
        (algebraMap K E x) =
      closedFiniteIndexClassFieldBaseEmbedding
        (K := K) H hclosed x := by
  exact DFunLike.congr_fun
    (closedFiniteIndexClassFieldCompatibleEmbedding_restrictDomain
       H hclosed E) x

/-- The fixing subgroup of the compatible embedded copy of `K` is the
base subgroup used by the selected class field. -/
@[simp]
theorem closedFiniteIndexClassFieldCompatibleEmbedding_baseSubgroup :
    numberFieldEmbeddedBaseSubgroup K E
        (closedFiniteIndexClassFieldCompatibleEmbedding
          (K := K) H hclosed E) =
      closedFiniteIndexClassFieldBaseSubgroup
        (K := K) H hclosed := by
  change
    closedFixingSubgroup ℚ (SeparableClosure ℚ)
        ((closedFiniteIndexClassFieldCompatibleEmbedding
           H hclosed E).domRestrict K).fieldRange =
      closedFixingSubgroup ℚ (SeparableClosure ℚ)
        (closedFiniteIndexClassFieldBaseEmbedding
           H hclosed).fieldRange
  rw [
    closedFiniteIndexClassFieldCompatibleEmbedding_restrictDomain
       H hclosed E]

/-- An actual finite abelian extension, represented inside the same
rational absolute Galois group as the class field selected by `H`. -/
noncomputable def
    closedFiniteIndexClassFieldEmbeddedAbelianSubextension
    [IsAbelianGalois K E] :
    FiniteAbelianSubextension
      (closedFiniteIndexClassFieldBaseSubgroup
        (K := K) H hclosed) :=
  numberFieldEmbeddedAbelianSubextension K E
    (closedFiniteIndexClassFieldCompatibleEmbedding
      (K := K) H hclosed E)
    (closedFiniteIndexClassFieldBaseSubgroup
      (K := K) H hclosed)
    (closedFiniteIndexClassFieldCompatibleEmbedding_baseSubgroup
      (K := K) H hclosed E)

/-- The top subgroup of the embedded abelian subextension is exactly
the fixing subgroup of the compatible embedded copy of `E`. -/
@[simp]
theorem
    closedFiniteIndexClassFieldEmbeddedAbelianSubextension_field
    [IsAbelianGalois K E] :
    (closedFiniteIndexClassFieldEmbeddedAbelianSubextension
      (K := K) H hclosed E).field =
      numberFieldEmbeddedTopSubgroup K E
        (closedFiniteIndexClassFieldCompatibleEmbedding
          (K := K) H hclosed E) := numberFieldEmbeddedAbelianSubextension_field K E
      (closedFiniteIndexClassFieldCompatibleEmbedding
         H hclosed E)
      (closedFiniteIndexClassFieldBaseSubgroup
         H hclosed)
      (closedFiniteIndexClassFieldCompatibleEmbedding_baseSubgroup
         H hclosed E)

/-- The abstract norm subgroup of the compatibly embedded extension is
the genuine idèle-class norm range of the original extension,
transported through the selected base-field equivalence. -/
private theorem
    ordinaryIdeleClassNormSubgroup_embeddedAbelianSubextension_named
    [IsAbelianGalois K E] :
    ordinaryIdeleClassNormSubgroup
        (numberFieldTowerFiniteAbstractField K
          (closedFiniteIndexClassFieldNormAmbient
            (K := K) H hclosed))
        (closedFiniteIndexClassFieldEmbeddedAbelianSubextension
          (K := K) H hclosed E) =
      (_root_.ideleClassNorm K E).range.toAddSubgroup.map
        (MulEquiv.toAdditive
          (finiteAbelianClassFieldContainmentIdeleClassEquiv
            (K := K) H hclosed)).toAddMonoidHom := by
  let Q :=
    numberFieldTowerFiniteAbstractField K
      (closedFiniteIndexClassFieldNormAmbient
         H hclosed)
  let P :=
    closedFiniteIndexClassFieldEmbeddedAbelianSubextension
       H hclosed E
  let A :=
    ordinaryIdeleClassNormExtension Q P
  let j :=
    closedFiniteIndexClassFieldCompatibleEmbedding
       H hclosed E
  let eK :=
    closedFiniteIndexClassFieldBaseEquiv
       H hclosed
  let hANumberField :=
    ordinaryIdeleClassNormExtensionNumberField Q P
  have hPField :
      P.field = numberFieldEmbeddedTopSubgroup K E j := by
    simpa only [P, j] using
      (closedFiniteIndexClassFieldEmbeddedAbelianSubextension_field
        (K := K) H hclosed E)
  let eRestrict : ((abstractRelativeFixedField ℚ (SeparableClosure ℚ)
    (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K E j)).restrictScalars ℚ) ≃+* A :=
    { toFun := fun x =>
        ⟨x.1, by
          change x.1 ∈
            abstractFixedField ℚ (SeparableClosure ℚ) P.field
          rw [hPField]
          exact x.2⟩
      invFun := fun x =>
        ⟨x.1, by
          change x.1 ∈
            abstractFixedField ℚ (SeparableClosure ℚ)
              (numberFieldEmbeddedTopSubgroup K E j)
          rw [← hPField]
          exact x.2⟩
      left_inv := fun x => Subtype.ext rfl
      right_inv := fun x => Subtype.ext rfl
      map_mul' := fun x y => Subtype.ext rfl
      map_add' := fun x y => Subtype.ext rfl }
  let eERing := (numberFieldEmbeddedAbstractTopFieldEquiv K E j).toRingEquiv.trans eRestrict
  let eE : E ≃ₐ[ℚ] A :=
    AlgEquiv.ofRingEquiv (f := eERing)
      (fun x => DFunLike.congr_fun
        (RingHom.ext_rat
          (eERing.toRingHom.comp (algebraMap ℚ E))
          (algebraMap ℚ A)) x)
  have hcompat :
      ∀ x : K,
        eE (algebraMap K E x) =
          algebraMap
            (closedFiniteIndexClassFieldBase
               H hclosed) A (eK x) := by
    intro x
    apply Subtype.ext
    change
      ((eERing (algebraMap K E x) : A) : SeparableClosure ℚ) =
        ((eK x : closedFiniteIndexClassFieldBase
           H hclosed) : SeparableClosure ℚ)
    calc
      _ =
          j (algebraMap K E x) := rfl
      _ = ((eK x : closedFiniteIndexClassFieldBase
          (K := K) H hclosed) : SeparableClosure ℚ) := by
        rw [
          closedFiniteIndexClassFieldCompatibleEmbedding_algebraMap
            (K := K) H hclosed E,
          closedFiniteIndexClassFieldBaseEquiv_coe
            (K := K) H hclosed]
  have hRange :
      (_root_.ideleClassNorm K E).range.map
          (finiteAbelianClassFieldContainmentIdeleClassEquiv
            (K := K) H hclosed).toMonoidHom =
        (_root_.ideleClassNorm
          (closedFiniteIndexClassFieldBase
            (K := K) H hclosed) A).range := by
    change
      (_root_.ideleClassNorm K E).range.map
          (ideleClassCongr eK).toMonoidHom =
        (_root_.ideleClassNorm
          (closedFiniteIndexClassFieldBase
            (K := K) H hclosed) A).range
    exact
      ordinaryIdeleClassNorm_range_map_congrOfAlgEquiv
        eK eE hcompat
  calc
    ordinaryIdeleClassNormSubgroup Q P =
        (_root_.ideleClassNorm
          (closedFiniteIndexClassFieldBase
            (K := K) H hclosed) A).range.toAddSubgroup :=
      ordinaryIdeleClassNormSubgroup_eq_namedNormRange Q P
    _ =
        (_root_.ideleClassNorm K E).range.toAddSubgroup.map
          (MulEquiv.toAdditive
            (finiteAbelianClassFieldContainmentIdeleClassEquiv
              (K := K) H hclosed)).toAddMonoidHom :=
      subgroup_map_toAddSubgroup_mulEquiv_eq
        (_root_.ideleClassNorm K E).range
        (_root_.ideleClassNorm
          (closedFiniteIndexClassFieldBase
            (K := K) H hclosed) A).range
        (finiteAbelianClassFieldContainmentIdeleClassEquiv
          (K := K) H hclosed) hRange

end

private theorem
    ordinaryIdeleClassNormSubgroup_closedFiniteIndexClassFieldSubextension_named
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex] :
    ordinaryIdeleClassNormSubgroup
        (numberFieldTowerFiniteAbstractField K
          (closedFiniteIndexClassFieldNormAmbient
            (K := K) H hclosed))
        (closedFiniteIndexClassFieldSubextension
          (K := K) H hclosed) =
      H.toAddSubgroup.map
        (MulEquiv.toAdditive
          (finiteAbelianClassFieldContainmentIdeleClassEquiv
            (K := K) H hclosed)).toAddMonoidHom := by
  change
    ordinaryIdeleClassNormSubgroup
        (closedFiniteIndexClassFieldReciprocityFiniteAbstractField
           H hclosed)
        (closedFiniteIndexClassFieldSubextension
           H hclosed) =
      H.toAddSubgroup.map
        (MulEquiv.toAdditive
          (ideleClassCongr
            (closedFiniteIndexClassFieldBaseEquiv
               H hclosed))).toAddMonoidHom
  exact
    ordinaryIdeleClassNormSubgroup_closedFiniteIndexClassFieldSubextension
       H hclosed

/-- If `H` is contained in the genuine norm range of an actual finite
abelian extension, its compatible embedded subextension lies below the
finite abelian subextension selected by `H`. -/
theorem
    embeddedAbelianSubextension_le_closedFiniteIndexClassFieldSubextension
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex]
    (E : Type) [Field E] [NumberField E]
    [Algebra K E] [FiniteDimensional K E]
    [IsAbelianGalois K E]
    (hH :
      H ≤ (_root_.ideleClassNorm K E).range) :
    closedFiniteIndexClassFieldEmbeddedAbelianSubextension
        (K := K) H hclosed E ≤
      closedFiniteIndexClassFieldSubextension
        (K := K) H hclosed := by
  apply
    (le_iff_ordinaryIdeleClassNormSubgroup_le
      (numberFieldTowerFiniteAbstractField K
        (closedFiniteIndexClassFieldNormAmbient
           H hclosed))
      (closedFiniteIndexClassFieldEmbeddedAbelianSubextension
         H hclosed E)
      (closedFiniteIndexClassFieldSubextension
         H hclosed)).2
  calc
    ordinaryIdeleClassNormSubgroup
        (numberFieldTowerFiniteAbstractField K
          (closedFiniteIndexClassFieldNormAmbient
             H hclosed))
        (closedFiniteIndexClassFieldSubextension
           H hclosed) =
        H.toAddSubgroup.map
          (MulEquiv.toAdditive
            (finiteAbelianClassFieldContainmentIdeleClassEquiv
               H hclosed)).toAddMonoidHom :=
      ordinaryIdeleClassNormSubgroup_closedFiniteIndexClassFieldSubextension_named
         H hclosed
    _ ≤
        (_root_.ideleClassNorm K E).range.toAddSubgroup.map
          (MulEquiv.toAdditive
            (finiteAbelianClassFieldContainmentIdeleClassEquiv
               H hclosed)).toAddMonoidHom :=
      (AddSubgroup.map_mono hH)
    _ =
        ordinaryIdeleClassNormSubgroup
          (numberFieldTowerFiniteAbstractField K
            (closedFiniteIndexClassFieldNormAmbient
               H hclosed))
          (closedFiniteIndexClassFieldEmbeddedAbelianSubextension
             H hclosed E) :=
      (ordinaryIdeleClassNormSubgroup_embeddedAbelianSubextension_named
         H hclosed E).symm

section

variable (H : Subgroup (IdeleClassGroup K)) (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex] (E : Type) [Field E] [NumberField E] [Algebra K E] [FiniteDimensional K E]

/-- The compatible ambient embedding agrees with the selected base
equivalence on scalars from the original number field. -/
 theorem
    finiteAbelianExtensionEmbedding_ambient_algebraMap_eq_baseEquiv
    (x : K) :
    closedFiniteIndexClassFieldCompatibleEmbedding
        (K := K) H hclosed E (algebraMap K E x) =
      ((closedFiniteIndexClassFieldBaseEquiv
          (K := K) H hclosed x :
        closedFiniteIndexClassFieldBase
          (K := K) H hclosed) :
        SeparableClosure ℚ) := by
  rw [
    closedFiniteIndexClassFieldCompatibleEmbedding_algebraMap
       H hclosed E,
    closedFiniteIndexClassFieldBaseEquiv_coe
       H hclosed]

/-- A point of a compatibly embedded subextension belongs to the
selected class field whenever the corresponding finite abelian
subextension lies below the selected one. -/
 theorem
    finiteAbelianExtensionEmbedding_codRestrict_mem
    [IsAbelianGalois K E]
    (hcontain :
      closedFiniteIndexClassFieldEmbeddedAbelianSubextension
          (K := K) H hclosed E ≤
        closedFiniteIndexClassFieldSubextension
          (K := K) H hclosed)
    (x : E) :
    closedFiniteIndexClassFieldCompatibleEmbedding
        (K := K) H hclosed E x ∈
      abstractFixedField ℚ (SeparableClosure ℚ)
        (closedFiniteIndexClassFieldSubextension
          (K := K) H hclosed).field := by
  refine
    (abstractFixedField_le
      ℚ (SeparableClosure ℚ) hcontain) ?_
  rw [closedFiniteIndexClassFieldEmbeddedAbelianSubextension_field]
  change
    closedFiniteIndexClassFieldCompatibleEmbedding
         H hclosed E x ∈
      IntermediateField.fixedField
        (closedFiniteIndexClassFieldCompatibleEmbedding
           H hclosed E).fieldRange.fixingSubgroup
  rw [InfiniteGalois.fixedField_fixingSubgroup]
  exact ⟨x, rfl⟩

/-- Every finite abelian extension whose genuine norm range contains
`H` admits an actual `K`-algebra embedding into the class field selected
by `H`. -/
noncomputable def
    finiteAbelianExtensionEmbeddingIntoClosedFiniteIndexClassField
    [IsAbelianGalois K E]
    (hH :
      H ≤ (_root_.ideleClassNorm K E).range) :
    E →ₐ[K]
      closedFiniteIndexClassField
        (K := K) H hclosed := by
  let jClassField :=
    (closedFiniteIndexClassFieldCompatibleEmbedding
      H hclosed E).toRingHom.codRestrict
      (abstractRelativeFixedField ℚ (SeparableClosure ℚ)
        (closedFiniteIndexClassFieldSubextension
           H hclosed).below).toSubring
      (finiteAbelianExtensionEmbedding_codRestrict_mem
         H hclosed E (embeddedAbelianSubextension_le_closedFiniteIndexClassFieldSubextension
          H hclosed E hH))
  exact
    { jClassField with
      commutes' := fun x =>
        Subtype.ext
          (finiteAbelianExtensionEmbedding_ambient_algebraMap_eq_baseEquiv
             H hclosed E x)}

end

/-- A finite abelian extension is isomorphic over the original base to
the class field selected by its own genuine idèle-class norm range. -/
noncomputable def
    finiteAbelianExtensionEquivClosedFiniteIndexNormClassField
    (E : Type) [Field E] [NumberField E]
    [Algebra K E] [FiniteDimensional K E]
    [IsAbelianGalois K E] :
    E ≃ₐ[K]
      closedFiniteIndexClassField
        (K := K)
        (_root_.ideleClassNorm K E).range
        (ideleClassNorm_range_isClosed
          (K := K) (L := E)) := by
  let H :=
    (_root_.ideleClassNorm K E).range
  let hclosed :
      IsClosed (H : Set (IdeleClassGroup K)) :=
    ideleClassNorm_range_isClosed
      (K := K) (L := E)
  let f :=
    finiteAbelianExtensionEmbeddingIntoClosedFiniteIndexClassField
       H hclosed E le_rfl
  have hdim :
      Module.finrank K E =
        Module.finrank K
          (closedFiniteIndexClassField
             H hclosed) := by
    calc
      Module.finrank K E =
          H.index :=
        (ideleClassNorm_index_eq_finrank_abelian K E).symm
      _ =
          Module.finrank K
            (closedFiniteIndexClassField
               H hclosed) :=
        (closedFiniteIndexClassField_finrank_eq_index
           H hclosed).symm
  have hsurjective :
      Function.Surjective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      hdim (f := f.toLinearMap)).mp f.injective
  simpa only [H, hclosed] using
    AlgEquiv.ofBijective f
      ⟨f.injective, hsurjective⟩

variable (L₁ L₂ : Type) [Field L₁] [NumberField L₁] [Field L₂] [NumberField L₂] [Algebra K L₁]
    [Algebra K L₂] [FiniteDimensional K L₁] [FiniteDimensional K L₂] [IsAbelianGalois K L₁]
    [IsAbelianGalois K L₂]

/-- An algebra embedding of finite extensions reverses inclusion of
their genuine idèle-class norm ranges. -/
theorem ideleClassNorm_range_le_of_algHom
    (f : L₁ →ₐ[K] L₂) :
    (_root_.ideleClassNorm K L₂).range ≤
      (_root_.ideleClassNorm K L₁).range := by
  let :=
    f.toRingHom.toAlgebra
  let :=
    IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm
  let :=
    FiniteDimensional.right K L₁ L₂
  exact
    ideleClassNorm_range_le_of_tower

/-- Reverse inclusion of genuine idèle-class norm ranges constructs an
actual algebra embedding of the corresponding finite abelian
extensions over the original base field. -/
noncomputable def finiteAbelianExtensionEmbeddingOfNormRangeLE
    (h :
      (_root_.ideleClassNorm K L₂).range ≤
        (_root_.ideleClassNorm K L₁).range) :
    L₁ →ₐ[K] L₂ := by
  let H :=
    (_root_.ideleClassNorm K L₂).range
  let hclosed :
      IsClosed (H : Set (IdeleClassGroup K)) :=
    ideleClassNorm_range_isClosed
      (K := K) (L := L₂)
  let e₂ :
      L₂ ≃ₐ[K]
        closedFiniteIndexClassField
           H hclosed := by
    simpa using
      finiteAbelianExtensionEquivClosedFiniteIndexNormClassField
         L₂
  exact
    e₂.symm.toAlgHom.comp (finiteAbelianExtensionEmbeddingIntoClosedFiniteIndexClassField
      H hclosed L₁ h)

/-- Reverse norm-range inclusion implies actual field containment over
the original number field. -/
theorem finiteAbelianExtension_nonempty_algHom_of_normRange_le
    (h :
      (_root_.ideleClassNorm K L₂).range ≤
        (_root_.ideleClassNorm K L₁).range) :
    Nonempty (L₁ →ₐ[K] L₂) :=
  ⟨finiteAbelianExtensionEmbeddingOfNormRangeLE
    (K := K) L₁ L₂ h⟩

end GlobalClassFields
end GlobalClassFieldTheory

end
