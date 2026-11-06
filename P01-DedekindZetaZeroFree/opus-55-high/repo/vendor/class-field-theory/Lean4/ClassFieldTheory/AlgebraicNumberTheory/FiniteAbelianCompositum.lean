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


/-!
# Finite abelian composita

This file gives a common realization, in a chosen separable closure, of the
compositum of two finite abelian Galois extensions.  It also records the
canonical factor embeddings and their elementary degree bounds.
-/


namespace AlgebraicNumberTheory

open scoped IsMulCommutative

universe u v

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
