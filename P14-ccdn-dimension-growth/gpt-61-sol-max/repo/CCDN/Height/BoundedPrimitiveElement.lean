/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

import Mathlib

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import CCDN.Algebra.BoundedLinearSeparation
import Mathlib.FieldTheory.PrimitiveElement

/-! Quantitative primitive elements and separation by affine coordinates. -/

public section
namespace CCDN

/-- A finite separating coordinate tuple has a primitive integer linear
combination with coefficients (1,k,...), where k<=n*[F:R]^2. -/
theorem exists_bounded_primitive_element {R F : Type*} [Field R] [CharZero R] [Field F]
    [Algebra R F] [Module.Finite R F] {n : ℕ} (a : Fin n → F)
    (hsep : Function.Injective (fun φ : F →ₐ[R] AlgebraicClosure R => fun j => φ (a j))) :
    ∃ k : ℕ, k ≤ n * (Module.finrank R F) ^ 2 ∧
      IntermediateField.adjoin R {∑ j : Fin n, a j * (k : F) ^ j.val} = ⊤ := by
  classical
  obtain ⟨k, hk, hinj⟩ := exists_bounded_moment_separation
    (fun φ : F →ₐ[R] AlgebraicClosure R => fun j => φ (a j)) hsep
  refine ⟨k, ?_, ?_⟩
  · simp_all
  · grind [Field.primitive_element_iff_algHom_eq_of_eval', IsAlgClosed.splits, map_sum,   map_natCast]


/-- The quantitative primitive element applies to the original coordinates of
a curve's function field, with no coordinate-generation hypothesis left over. -/
theorem exists_bounded_curve_primitive_element {K R F : Type*}
    [Field K] [Field R] [CharZero R] [Field F]
    [Algebra K R] [Algebra K F] [Algebra R F] [IsScalarTower K R F]
    [Module.Finite R F] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    [Algebra (MvPolynomial (Fin n) K ⧸ I) F]
    [IsScalarTower K (MvPolynomial (Fin n) K ⧸ I) F]
    [IsFractionRing (MvPolynomial (Fin n) K ⧸ I) F] :
    ∃ k : ℕ, k ≤ n * (Module.finrank R F) ^ 2 ∧
      IntermediateField.adjoin R
        {∑ j : Fin n, algebraMap (MvPolynomial (Fin n) K ⧸ I) F
          ((Ideal.Quotient.mk I) (MvPolynomial.X j)) * (k : F) ^ j.val} = ⊤ := exists_bounded_primitive_element _ ((by
                                                                                                                     let inline_σ := Fin n
                                                                                                                     intro φ ψ he
                                                                                                                     let q := (IsScalarTower.toAlgHom K (MvPolynomial inline_σ K ⧸ I) F).comp (Ideal.Quotient.mkₐ K I)
                                                                                                                     have hpoly : (φ.restrictScalars K).comp q = (ψ.restrictScalars K).comp q := by
                                                                                                                       solve_by_elim [MvPolynomial.algHom_ext, congrFun]
                                                                                                                     have hfield : φ.toRingHom = ψ.toRingHom := by
                                                                                                                       apply IsFractionRing.ringHom_ext (A := MvPolynomial inline_σ K ⧸ I)
                                                                                                                       intro a
                                                                                                                       obtain ⟨h, rfl⟩ := Ideal.Quotient.mk_surjective a
                                                                                                                       exact AlgHom.congr_fun hpoly h
                                                                                                                     ext x
                                                                                                                     exact RingHom.congr_fun hfield x))

end CCDN
