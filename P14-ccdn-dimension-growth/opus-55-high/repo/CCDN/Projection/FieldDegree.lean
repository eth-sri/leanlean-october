/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Hilbert.LinearProjectionFiltration
import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Mathlib.FieldTheory.Minpoly.Basic
import Mathlib.RingTheory.Algebraic.Defs
import CCDN.Hilbert.FunctionFieldRank
import CCDN.Hilbert.PlaneHilbert
import CCDN.Projection.PlaneProjectionDegree
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.FieldTheory.PrimitiveElement

/-! A primitive plane coordinate gives a lower bound for the image equation's
 degree. Combined with the filtered upper bound, a parameter of full field
 degree forces a linear projection to preserve the affine Hilbert degree. -/

namespace CCDN
section
open MvPolynomial

section
variable {K R F : Type*} [Field K] [Field R] [Field F] [Algebra K R] [Algebra R F] [Algebra K F] [IsScalarTower K R F]

/-- The degree of a plane equation is at least the degree of a function-field
extension when its second coordinate is primitive over the parameter field. -/
theorem primitive_field_degree_le_plane_relation
    [Module.Finite R F]
    (ψ : MvPolynomial (Fin 2) K →ₐ[K] F)
    (f : MvPolynomial (Fin 2) K) (hf : f ≠ 0) (hzero : ψ f = 0)
    (j k : Fin 2) (u : R) (hu : Transcendental K u)
    (he : ψ (X j) = algebraMap R F u)
    (hprim : IntermediateField.adjoin R {ψ (X k)} = ⊤) :
    Module.finrank R F ≤ f.totalDegree := by
  rw [← (Field.primitive_element_iff_minpoly_natDegree_eq R (ψ (X k))).mp hprim]
  let I : Ideal (MvPolynomial (Fin 2) K) := Ideal.span {f}
  have hI : ∀ g ∈ I, ψ g = 0 := by
    intro g hg
    obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton.mp hg
    grind
  let φ : (MvPolynomial (Fin 2) K ⧸ I) →ₐ[K] F := Ideal.Quotient.liftₐ I ψ hI
  have hφ (g : MvPolynomial (Fin 2) K) : φ ((Ideal.Quotient.mk I) g) = ψ g := rfl
  have hdegree : HasFilteredCurveDegree I f.totalDegree :=
    ⟨f.totalDegree, f.totalDegree - f.totalDegree.choose 2,
      fun n hn => principal_plane_hilbert_function f hf hn⟩
  have hi : LinearIndependent R (fun i : Fin (minpoly R (ψ (X k))).natDegree =>
      φ ((Ideal.Quotient.mk I) ((X k) ^ i.val))) := by
    simpa [hφ, map_pow] using (linearIndependent_pow (ψ (X k)))
  have h := polynomial_parameter_rank_le
    (ι := Fin (minpoly R (ψ (X k))).natDegree) I f.totalDegree hdegree φ (X j)
    (by simp) u hu (by grind)
    (fun i : Fin (minpoly R (ψ (X k))).natDegree => (X k) ^ i.val) hi
  simpa using h

end

