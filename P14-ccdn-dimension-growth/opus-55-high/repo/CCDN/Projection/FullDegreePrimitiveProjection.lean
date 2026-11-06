/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Hilbert.FilteredIntersection
import CCDN.Projection.CurvePrimitivePair
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.SimpleRing.Principal
import CCDN.Algebra.ParameterRecurrenceGrowth
import CCDN.Height.BoundedPrimitiveElement
import CCDN.Hilbert.CurveFunctionField
import CCDN.Projection.FieldDegree
import CCDN.Projection.PlaneProjectionKernel

/-!
Once a linear parameter generates the degree filtration, a bounded moment
coordinate produces a degree-preserving plane equation. This combines
full function-field degree with the quantitative primitive-element theorem.

Eventual generation of the affine degree filtration by a linear parameter
forces the function-field extension to have the full Hilbert degree.
-/

namespace CCDN
section

open MvPolynomial

/-- Build the bounded second projection coordinate and a plane equation of
exactly degree d from a parameter satisfying eventual filtered generation. -/
theorem exists_full_degree_primitive_projection {K F : Type*}
    [Field K] [CharZero K] [Field F] [Algebra K F]
    [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    {n : ℕ} (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    [Algebra (MvPolynomial (Fin n) K ⧸ I) F]
    [IsScalarTower K (MvPolynomial (Fin n) K ⧸ I) F]
    [IsFractionRing (MvPolynomial (Fin n) K ⧸ I) F]
    (d : ℕ) (hdegree : HasFilteredCurveDegree I d)
    (l : MvPolynomial (Fin n) K) (hl : l.totalDegree ≤ 1)
    (he : algebraMap (MvPolynomial (Fin n) K ⧸ I) F ((Ideal.Quotient.mk I) l) =
      algebraMap (RatFunc K) F RatFunc.X)
    (N : ℕ) (hrec : ∀ m ≥ N, filteredCoordinateSpace I (m + 1) =
      filteredCoordinateSpace I m ⊔ (filteredCoordinateSpace I m).map
        (LinearMap.mulLeft K ((Ideal.Quotient.mk I) l))) :
    ∃ (k : ℕ) (f : MvPolynomial (Fin 2) K), k ≤ n * d ^ 2 ∧
      Irreducible f ∧ f.totalDegree = d ∧
      ∀ g, aeval (![l, momentCoordinate K n k]) g ∈ I ↔ f ∣ g := by
  obtain ⟨hfinite, hupper⟩ := curve_functionField_finite_rank_le I d hdegree l hl
    RatFunc.X RatFunc.transcendental_X he
  let : Module.Finite (RatFunc K) F := hfinite
  let φ := IsScalarTower.toAlgHom K (MvPolynomial (Fin n) K ⧸ I) F
  have hcomm (x : MvPolynomial (Fin n) K ⧸ I) :
      φ.toLinearMap ((LinearMap.mulLeft K ((Ideal.Quotient.mk I) l)) x) =
        algebraMap (RatFunc K) F RatFunc.X * φ.toLinearMap x := by
    change φ (((Ideal.Quotient.mk I) l) * x) = _
    rw [map_mul]
    exact congrArg (fun y => y * φ x) he
  have hlower := parameter_recurrence_slope_le (filteredCoordinateSpace I)
    (LinearMap.mulLeft K ((Ideal.Quotient.mk I) l)) φ.toLinearMap
    (IsFractionRing.injective _ _) hcomm N hrec d hdegree
  have hfull := Nat.le_antisymm hupper hlower
  obtain ⟨k, hk, hprim⟩ := exists_bounded_primitive_element _ (curve_coordinate_embeddings_injective (R := RatFunc K) (F := F) I)
  let a : Fin 2 → MvPolynomial (Fin n) K := ![l, momentCoordinate K n k]
  have ha (i : Fin 2) : (a i).totalDegree ≤ 1 := by
    fin_cases i
    · exact hl
    · exact momentCoordinate_degree K n k
  obtain ⟨f, hf, hker⟩ := exists_plane_projection_equation I a ha d hdegree 0 (by
    intro h
    have hh := (isAlgebraic_algHom_iff φ (IsFractionRing.injective _ _)).mpr h
    change IsAlgebraic K (algebraMap (MvPolynomial (Fin n) K ⧸ I) F ((Ideal.Quotient.mk I) l)) at hh
    rw [he] at hh
    exact RatFunc.transcendental_X ((isAlgebraic_algHom_iff
      (IsScalarTower.toAlgHom K (RatFunc K) F) (algebraMap (RatFunc K) F).injective).mp hh))
  have hp : IntermediateField.adjoin (RatFunc K) {φ ((Ideal.Quotient.mk I) (a 1))} = ⊤ := by
    change IntermediateField.adjoin (RatFunc K)
      {algebraMap (MvPolynomial (Fin n) K ⧸ I) F
        ((Ideal.Quotient.mk I) (momentCoordinate K n k))} = ⊤
    rwa [momentCoordinate_fraction]
  refine ⟨k, f, by grind, hf, (by
    refine Nat.le_antisymm (plane_projection_equation_degree_le I a ha d hdegree f hf.ne_zero hker) ?_
    rw [← hfull]
    let ψ := φ.comp (projectionCoordinateMap I a)
    have hψ (i : Fin 2) : ψ (X i) = φ ((Ideal.Quotient.mk I) (a i)) := by
      simp [ψ, projectionCoordinateMap]
    have hz : projectionCoordinateMap I a f = 0 := by
      rw [← RingHom.mem_ker, hker]
      exact Ideal.mem_span_singleton_self f
    exact primitive_field_degree_le_plane_relation ψ f hf.ne_zero (by simp [ψ, hz])
      0 1 RatFunc.X RatFunc.transcendental_X (by rw [hψ]; exact he) (by rw [hψ]; exact hp)), ?_⟩
  intro g
  have hg : aeval a g ∈ I ↔ g ∈ RingHom.ker (projectionCoordinateMap I a) :=
    Ideal.Quotient.eq_zero_iff_mem.symm
  rw [hg, hker, Ideal.mem_span_singleton]

