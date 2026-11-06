module

public import Mathlib.FieldTheory.Galois.Abelian
public import Mathlib.FieldTheory.Galois.GaloisClosure
public import ClassFieldTheory.AlgebraicNumberTheory.SeparableClosureEmbedding

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/





set_option autoImplicit false

/-!
# Finite abelian composita

This file gives a common realization, in a chosen separable closure, of the
compositum of two finite abelian Galois extensions.  It also records the
canonical factor embeddings and their elementary degree bounds.
-/

noncomputable section

namespace AlgebraicNumberTheory

open scoped IsMulCommutative

universe u v

/-- The chosen copy of a finite Galois extension in the separable closure. -/
def finiteGaloisFieldRange
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    IntermediateField K (SeparableClosure K) :=
  AlgHom.fieldRange
    (AlgebraicNumberTheory.separableEmbeddingIntoSeparableClosure K L)

/-- The chosen embedding identifies the extension with its field range. -/
def finiteGaloisFieldRangeEquiv
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    L ≃ₐ[K] finiteGaloisFieldRange K L :=
  AlgEquiv.ofInjectiveField
    (AlgebraicNumberTheory.separableEmbeddingIntoSeparableClosure K L)

/-- The chosen field-range model is finite-dimensional over the base. -/
instance finiteGaloisFieldRange_finiteDimensional
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    FiniteDimensional K (finiteGaloisFieldRange K L) :=
  (finiteGaloisFieldRangeEquiv K L).toLinearEquiv.finiteDimensional

/-- The chosen field-range model is Galois over the base. -/
instance finiteGaloisFieldRange_isGalois
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    IsGalois K (finiteGaloisFieldRange K L) :=
  IsGalois.of_algEquiv (finiteGaloisFieldRangeEquiv K L)

section AbelianCompositum

variable (K : Type u) [Field K]
variable {Omega : Type v} [Field Omega] [Algebra K Omega]

/-- The compositum, inside a common overfield, of two abelian Galois
intermediate fields is again abelian Galois over the base. -/
theorem isAbelianGalois_sup
    (A B : IntermediateField K Omega)
    [FiniteDimensional K A] [FiniteDimensional K B]
    [IsAbelianGalois K A] [IsAbelianGalois K B] :
    IsAbelianGalois K (A ⊔ B : IntermediateField K Omega) := by
  let M : IntermediateField K Omega := A ⊔ B
  let j : M →ₐ[K] Omega := M.val
  let A' : IntermediateField K M := A.comap j
  let B' : IntermediateField K M := B.comap j

  have hjrange : j.fieldRange = M :=
    IntermediateField.fieldRange_val M
  have hAmap : A'.map j = A := by
    apply IntermediateField.map_comap_eq_self
    rw [hjrange]
    exact le_sup_left
  have hBmap : B'.map j = B := by
    apply IntermediateField.map_comap_eq_self
    rw [hjrange]
    exact le_sup_right
  have hsup : A' ⊔ B' = ⊤ := by
    apply IntermediateField.map_injective j
    rw [IntermediateField.map_sup, hAmap, hBmap,
      ← AlgHom.fieldRange_eq_map, hjrange]

  let eA : A' →ₐ[K] A :=
    ((j.comp A'.val).codRestrict A.toSubalgebra fun x ↦ x.2)
  let eB : B' →ₐ[K] B :=
    ((j.comp B'.val).codRestrict B.toSubalgebra fun x ↦ x.2)
  let : IsAbelianGalois K A' := IsAbelianGalois.of_algHom eA
  let : IsAbelianGalois K B' := IsAbelianGalois.of_algHom eB
  let : IsGalois K M := inferInstance

  let rA : (M ≃ₐ[K] M) →* (A' ≃ₐ[K] A') :=
    AlgEquiv.restrictNormalHom A'
  let rB : (M ≃ₐ[K] M) →* (B' ≃ₐ[K] B') :=
    AlgEquiv.restrictNormalHom B'
  let r : (M ≃ₐ[K] M) →* (A' ≃ₐ[K] A') × (B' ≃ₐ[K] B') :=
    rA.prod rB
  have hr : Function.Injective r := by
    rw [injective_iff_map_eq_one]
    intro sigma hsigma
    have hAone : rA sigma = 1 := congrArg Prod.fst hsigma
    have hBone : rB sigma = 1 := congrArg Prod.snd hsigma
    have hmemA : sigma ∈ A'.fixingSubgroup := by
      rw [← IntermediateField.restrictNormalHom_ker]
      exact hAone
    have hmemB : sigma ∈ B'.fixingSubgroup := by
      rw [← IntermediateField.restrictNormalHom_ker]
      exact hBone
    have hmem : sigma ∈ (A' ⊔ B').fixingSubgroup := by
      rw [IntermediateField.fixingSubgroup_sup]
      exact ⟨hmemA, hmemB⟩
    simpa [hsup] using hmem

  exact
    { is_comm.comm := fun sigma tau ↦ by
        apply hr
        rw [map_mul, map_mul]
        apply Prod.ext
        · change rA sigma * rA tau = rA tau * rA sigma
          exact mul_comm (rA sigma) (rA tau)
        · change rB sigma * rB tau = rB tau * rB sigma
          exact mul_comm (rB sigma) (rB tau) }

end AbelianCompositum

section ConcreteAbelianCompositum

variable (K L E : Type)
variable [Field K]
variable [Field L] [Field E] [Algebra K L] [Algebra K E]
variable [FiniteDimensional K L] [FiniteDimensional K E]
variable [IsAbelianGalois K L] [IsAbelianGalois K E]

/-- A concrete common realization of the compositum of two finite abelian
extensions in the chosen separable closure of the base. -/
def finiteAbelianCompositumField :
    IntermediateField K (SeparableClosure K) :=
  finiteGaloisFieldRange K L ⊔ finiteGaloisFieldRange K E

/-- The concrete compositum is finite-dimensional over the base. -/
instance finiteAbelianCompositumField_finiteDimensional :
    FiniteDimensional K (finiteAbelianCompositumField K L E) :=
  IntermediateField.finiteDimensional_sup
    (finiteGaloisFieldRange K L) (finiteGaloisFieldRange K E)

/-- The concrete compositum is abelian Galois over the base. -/
instance finiteAbelianCompositumField_isAbelianGalois :
    IsAbelianGalois K (finiteAbelianCompositumField K L E) := by
  let : IsAbelianGalois K (finiteGaloisFieldRange K L) :=
    IsAbelianGalois.of_algHom
      (finiteGaloisFieldRangeEquiv K L).symm.toAlgHom
  let : IsAbelianGalois K (finiteGaloisFieldRange K E) :=
    IsAbelianGalois.of_algHom
      (finiteGaloisFieldRangeEquiv K E).symm.toAlgHom
  exact isAbelianGalois_sup K
    (finiteGaloisFieldRange K L) (finiteGaloisFieldRange K E)

/-- The given left extension embeds into its concrete compositum. -/
def finiteAbelianCompositumEmbeddingLeft :
    L →ₐ[K] finiteAbelianCompositumField K L E :=
  (IntermediateField.inclusion le_sup_left).comp
    (finiteGaloisFieldRangeEquiv K L).toAlgHom









end ConcreteAbelianCompositum

end AlgebraicNumberTheory

end
