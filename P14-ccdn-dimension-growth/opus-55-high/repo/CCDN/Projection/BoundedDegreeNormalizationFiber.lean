/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Algebra.IdealZeroLocus
import CCDN.Hilbert.FilteredHilbertPolynomial
import CCDN.Hilbert.LinearProjectionFiltration
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import CCDN.Hilbert.BoundedDegreeFunctionFieldRank
import CCDN.Hilbert.LinearCoordinates
import CCDN.Projection.IntegralFiberRank
import CCDN.Projection.PrimitiveCoordinateField
import Mathlib.RingTheory.AlgebraicIndependent.Basic

/-! Sharp fibers of integral polynomial parameters of degree at most q.
The Hilbert multiplicity bounds the field degree by d*q^dimension;
a separating integral element gives the same bound for every finite fiber. -/

namespace CCDN
section
open MvPolynomial

theorem bounded_degree_normalization_fiber_card_le_of_fractionField
    {K E : Type*} [Field K] [CharZero K] [Field E] [Algebra K E]
    {n m : ℕ} (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    [Algebra (MvPolynomial (Fin n) K ⧸ I) E]
    [IsScalarTower K (MvPolynomial (Fin n) K ⧸ I) E]
    [IsFractionRing (MvPolynomial (Fin n) K ⧸ I) E]
    (q : ℕ) (hq : 0 < q)
    (l : Fin (m + 1) → MvPolynomial (Fin n) K)
    (hl : ∀ i, (l i).totalDegree ≤ q)
    (hi : Function.Injective (projectionCoordinateMap I l))
    (hint : (projectionCoordinateMap I l).IsIntegral)
    (d : ℕ) (hdimdeg : HasProjectiveDimensionDegree I m d)
    (z : Fin (m + 1) → K) (s : Finset (Fin n → K))
    (hzero : ∀ x ∈ s, x ∈ idealZeroLocus I)
    (hproj : ∀ x ∈ s, ∀ i, eval x (l i) = z i) :
    s.card ≤ d * q ^ (m + 1) := by
  let A := MvPolynomial (Fin n) K ⧸ I
  let η : A →ₐ[K] E := IsScalarTower.toAlgHom K A E
  let v : Fin (m + 1) → E := fun i => η ((Ideal.Quotient.mk I) (l i))
  let R := IntermediateField.adjoin K (Set.range v)
  let u : Fin (m + 1) → R := fun i =>
    ⟨v i, IntermediateField.subset_adjoin K _ ⟨i, rfl⟩⟩
  have hiA :=
    injective_projectionCoordinateMap_iff.mp hi
  have hiR :=
    AlgebraicIndependent.of_comp (x := u) R.val (hiA.map' (IsFractionRing.injective A E))
  obtain ⟨hfinite, hrank⟩ :=
    bounded_degree_hilbert_functionField_finite_rank_le (R := R) (F := E) I d q hq
      (by simp_all) l hl u hiR (fun _ => rfl)
  let : Module.Finite R E := hfinite
  let P := MvPolynomial (Fin (m + 1)) K
  let ψ : P →ₐ[K] A := projectionCoordinateMap I l
  let ρ : P →ₐ[K] R := aeval u
  have hcomp : R.val.comp ρ = η.comp ψ := by
    ext i
    simp [AlgHom.comp_apply, ρ, ψ, projectionCoordinateMap, aeval_X,
      Ideal.Quotient.mkₐ_eq_mk]
    rfl
  let : Algebra P A := ψ.toRingHom.toAlgebra
  let : Algebra P R := ρ.toRingHom.toAlgebra
  let : Algebra P E := (η.comp ψ).toRingHom.toAlgebra
  let : IsScalarTower P A E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : IsScalarTower P R E := IsScalarTower.of_algebraMap_eq
    (fun p => congrArg (fun f => f p) hcomp.symm)
  have hgen : IntermediateField.adjoin K (Set.range u) = ⊤ := by
    apply IntermediateField.lift_injective R
    rw [IntermediateField.lift_adjoin, IntermediateField.lift_top, ← Set.range_comp]
    rfl
  let : IsFractionRing P R := isFractionRing_of_generating_tuple ρ hiR
    (fun i => X i) (by
      convert hgen using 2
      congr 1
      funext i
      rw [aeval_X])
  let : Algebra P K := (aeval z).toRingHom.toAlgebra
  have hbound := integral_coordinate_tuple_count_le_finrank P A R E
    (fun i => Ideal.Quotient.mk I (X i)) (fun i => hint _) s
    fun x hx => exists_projection_fiber_specialization I l rfl z x (hzero x hx) (hproj x hx)
  simpa using
    hbound.trans hrank

variable {K : Type*} [Field K] [CharZero K] {n m : ℕ} (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]

/-- The linear case `q = 1` of `bounded_degree_normalization_fiber_card_le`:
a fiber of a linear normalization has at most `d` points. -/
theorem linear_normalization_fiber_card_le
    (l : Fin (m + 1) → MvPolynomial (Fin n) K)
    (hl : ∀ i, (l i).totalDegree ≤ 1)
    (hi : Function.Injective (projectionCoordinateMap I l))
    (hint : (projectionCoordinateMap I l).IsIntegral)
    (d : ℕ) (hdimdeg : HasProjectiveDimensionDegree I m d)
    (z : Fin (m + 1) → K) (s : Finset (Fin n → K))
    (hzero : ∀ x ∈ s, x ∈ idealZeroLocus I)
    (hproj : ∀ x ∈ s, ∀ i, eval x (l i) = z i) :
    s.card ≤ d := by
  simpa using bounded_degree_normalization_fiber_card_le_of_fractionField
    (E := FractionRing (MvPolynomial (Fin n) K ⧸ I)) I 1 one_pos l hl
    hi hint d hdimdeg z s hzero hproj

