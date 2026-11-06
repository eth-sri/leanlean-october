/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import CCDN.Algebra.BoundedLinearSeparation
import Mathlib.FieldTheory.PrimitiveElement

/-! Quantitative primitive elements and separation by affine coordinates. -/

@[expose] public section
namespace CCDN
noncomputable section

/- A finite separating coordinate tuple has a primitive integer linear
combination with coefficients (1,k,...), where k<=n*[F:R]^2. -/

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
          ((Ideal.Quotient.mk I) (MvPolynomial.X j)) * (k : F) ^ j.val} = ⊤ := by
  /- Maps from a fraction field are determined by the images of the
  original affine coordinates, even when the scalar field contains a parameter. -/
  classical
  let a : Fin n → F := fun j => algebraMap (MvPolynomial (Fin n) K ⧸ I) F
    ((Ideal.Quotient.mk I) (MvPolynomial.X j))
  obtain ⟨k, hk, hinj⟩ := exists_bounded_moment_separation
    (fun φ : F →ₐ[R] AlgebraicClosure R => fun j => φ (a j)) fun φ ψ he => by
      let q := (IsScalarTower.toAlgHom K (MvPolynomial (Fin n) K ⧸ I) F).comp (Ideal.Quotient.mkₐ K I)
      have hpoly : (φ.restrictScalars K).comp q = (ψ.restrictScalars K).comp q :=
        MvPolynomial.algHom_ext (congrFun he)
      have hfield : φ.toRingHom = ψ.toRingHom :=
        IsFractionRing.ringHom_ext (A := MvPolynomial (Fin n) K ⧸ I) fun x => by
          obtain ⟨h, rfl⟩ := Ideal.Quotient.mk_surjective x
          exact AlgHom.congr_fun hpoly h
      exact AlgHom.ext (RingHom.congr_fun hfield)
  refine ⟨k, by simpa only [AlgHom.card R F (AlgebraicClosure R)] using hk,
    (Field.primitive_element_iff_algHom_eq_of_eval' R (AlgebraicClosure R)
      (fun _ => IsAlgClosed.splits _) _).mpr fun φ ψ he =>
      hinj (by simpa only [map_sum, map_mul, map_pow, map_natCast] using he)⟩

end
end CCDN
