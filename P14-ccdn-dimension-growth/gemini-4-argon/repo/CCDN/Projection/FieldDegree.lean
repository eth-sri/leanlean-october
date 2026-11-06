/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Hilbert.LinearProjectionFiltration
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.RingTheory.Algebraic.Defs
import CCDN.Hilbert.FunctionFieldRank
import CCDN.Hilbert.PlaneHilbert
import CCDN.Projection.PlaneProjectionDegree
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.FieldTheory.PrimitiveElement

/-! A primitive plane coordinate gives a lower bound for the image equation's
 degree. Combined with the filtered upper bound, a parameter of full field
 degree forces a linear projection to preserve the affine Hilbert degree. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Once the linear parameter has full field degree and the other coordinate
is primitive, the irreducible image equation preserves degree. -/
theorem plane_projection_degree_eq_of_full_parameter {K R F τ : Type*}
    [Field K] [Field R] [Field F] [Algebra K R] [Algebra R F] [Algebra K F]
    [IsScalarTower K R F] [Module.Finite R F] [Fintype τ]
    (I : Ideal (MvPolynomial τ K)) (a : Fin 2 → MvPolynomial τ K)
    (ha : ∀ i, (a i).totalDegree ≤ 1) (d : ℕ)
    (hdegree : HasFilteredCurveDegree I d)
    (φ : (MvPolynomial τ K ⧸ I) →ₐ[K] F)
    (f : MvPolynomial (Fin 2) K) (hf : f ≠ 0)
    (hker : RingHom.ker (projectionCoordinateMap I a) = Ideal.span {f})
    (j k : Fin 2) (u : R) (hu : Transcendental K u)
    (he : φ ((Ideal.Quotient.mk I) (a j)) = algebraMap R F u)
    (hprim : IntermediateField.adjoin R {φ ((Ideal.Quotient.mk I) (a k))} = ⊤)
    (hrank : Module.finrank R F = d) : f.totalDegree = d := by
  apply Nat.le_antisymm (plane_projection_equation_degree_le I a ha d hdegree f hf hker)
  let ψ := φ.comp (projectionCoordinateMap I a)
  have hψ (i : Fin 2) : ψ (X i) = φ ((Ideal.Quotient.mk I) (a i)) := by
    simp [ψ, projectionCoordinateMap]
  have hz : projectionCoordinateMap I a f = 0 :=
    RingHom.mem_ker.mp (hker ▸ Ideal.subset_span (Set.mem_singleton f))
  rw [← hrank, ← (Field.primitive_element_iff_minpoly_natDegree_eq R (ψ (X k))).mp (by rwa [hψ])]
  let J : Ideal (MvPolynomial (Fin 2) K) := Ideal.span {f}
  let η : (MvPolynomial (Fin 2) K ⧸ J) →ₐ[K] F := Ideal.Quotient.liftₐ J ψ fun g hg => by
    obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton.mp hg
    simp [ψ, hz]
  have hη (g : MvPolynomial (Fin 2) K) : η ((Ideal.Quotient.mk J) g) = ψ g := rfl
  have hi : LinearIndependent R (fun i : Fin (minpoly R (ψ (X k))).natDegree =>
      η ((Ideal.Quotient.mk J) ((X k) ^ i.val))) := by
    simpa only [hη, map_pow] using linearIndependent_pow (K := R) (ψ (X k))
  simpa only [Fintype.card_fin] using polynomial_parameter_rank_le (K := K) (R := R) (F := F)
    (ι := Fin (minpoly R (ψ (X k))).natDegree) J f.totalDegree
    ⟨f.totalDegree, (f.totalDegree : ℤ) - f.totalDegree.choose 2,
      fun n hn => principal_plane_hilbert_function f hf hn⟩
    η (X j) (by simp) u hu (by rw [hη, hψ]; exact he)
    (fun i => (X k) ^ i.val) hi

end
end CCDN
