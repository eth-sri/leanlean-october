/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Algebra.IdealZeroLocus
import CCDN.Projection.CurvePrimitivePair
import CCDN.Projection.InfinityParameterReduction
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import CCDN.Hilbert.RecurrenceParameterTranscendence
import CCDN.Projection.BoundedInfinityAvoidance
import CCDN.Projection.BoundedInfinityParameter
import CCDN.Projection.DegreePreservingProjectionCount
import CCDN.Projection.FullDegreePrimitiveProjection

/-!
Every positive-degree prime affine curve in characteristic zero admits
an explicitly bounded integral linear plane projection preserving its degree.
The first coordinate is constructed by infinity avoidance and the second by
the quantitative primitive-element theorem.

Construct the rational-function field embedding from a transcendental
coordinate, and prove the degree bound for the resulting field extension.
-/

namespace CCDN
noncomputable section

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (u : F) (hu : Transcendental K u)

/-- Send the rational-function variable to a transcendental element. -/
def transcendentalRatFuncMap
    : RatFunc K →ₐ[K] F :=
  RatFunc.liftAlgHom (Polynomial.aeval u)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ (transcendental_iff_injective.mp hu))

end

section

section

/-! An infinity-avoiding linear form gives a degree-preserving plane
projection. The parameter field and the second coordinate are constructed. -/

open MvPolynomial

end

open MvPolynomial

variable {K : Type*} [Field K] [CharZero K] {n : ℕ}

/-- An integral affine curve of degree `d` has a projection to the plane by two moment
coordinates of bounded index whose image is cut out by an irreducible equation of degree `d`,
and which identifies at most `d(d-1)` points of any finite subset of the curve. -/
theorem exists_bounded_projection_card_le
    [DecidableEq (Fin 2 → K)]
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (d : ℕ) (hd : 0 < d) (hdegree : HasFilteredCurveDegree I d) :
    ∃ (k₀ k₁ : ℕ) (f : MvPolynomial (Fin 2) K),
      k₀ ≤ n ^ 2 * d ∧ k₁ ≤ n * d ^ 2 ∧ Irreducible f ∧ f.totalDegree = d ∧
      (∀ g, aeval (![momentCoordinate K n k₀, momentCoordinate K n k₁]) g ∈ I ↔ f ∣ g) ∧
      ∀ S : Finset (Fin n → K), (∀ z ∈ S, z ∈ idealZeroLocus I) →
        S.card ≤ (S.image (fun z =>
          ![eval z (momentCoordinate K n k₀), eval z (momentCoordinate K n k₁)])).card +
            d * (d - 1) := by
  obtain ⟨k₀, k₁, f, hk₀, hk₁, hf, hfd, hu, hker⟩ : ∃ (k₀ k₁ : ℕ) (f : MvPolynomial (Fin 2) K),
      k₀ ≤ n ^ 2 * d ∧ k₁ ≤ n * d ^ 2 ∧ Irreducible f ∧ f.totalDegree = d ∧
      Transcendental K ((Ideal.Quotient.mk I) (momentCoordinate K n k₀)) ∧
      ∀ g, aeval (![momentCoordinate K n k₀, momentCoordinate K n k₁]) g ∈ I ↔ f ∣ g := by
    obtain ⟨k₀, hk₀, havoid⟩ :=
      exists_bounded_infinity_parameter (L := AlgebraicClosure K) I d hdegree
    obtain ⟨N, hrec⟩ := filtration_recurrence_of_infinity_avoidance I
      (momentCoordinate K n k₀) (momentCoordinate_homogeneous K n k₀) havoid
    have htrans := recurrence_parameter_transcendental I d hd hdegree _ N hrec
    let F := FractionRing (MvPolynomial (Fin n) K ⧸ I)
    let u := algebraMap (MvPolynomial (Fin n) K ⧸ I) F
      ((Ideal.Quotient.mk I) (momentCoordinate K n k₀))
    have huF : Transcendental K u := fun h => htrans ((isAlgebraic_algHom_iff
      (IsScalarTower.toAlgHom K (MvPolynomial (Fin n) K ⧸ I) F)
      (IsFractionRing.injective _ _)).mp h)
    let φ := transcendentalRatFuncMap u huF
    let : Algebra (RatFunc K) F := φ.toRingHom.toAlgebra
    let : IsScalarTower K (RatFunc K) F := IsScalarTower.of_algHom φ
    obtain ⟨k₁, f, hk₁, hf, hfd, hker⟩ := exists_full_degree_primitive_projection I d
      hdegree _ (momentCoordinate_homogeneous K n k₀).totalDegree_le
      (show transcendentalRatFuncMap u huF RatFunc.X = u by
          exact (RatFunc.liftRingHom_X (Polynomial.aeval u).toRingHom _).trans (Polynomial.aeval_X u)).symm N hrec
    exact ⟨k₀, k₁, f, hk₀, hk₁, hf, hfd, htrans, hker⟩
  refine ⟨k₀, k₁, f, hk₀, hk₁, hf, hfd, hker, ?_⟩
  intro S hS
  let a := ![momentCoordinate K n k₀, momentCoordinate K n k₁]
  have ha (j : Fin 2) : (a j).totalDegree ≤ 1 := by
    fin_cases j <;> exact momentCoordinate_degree _ _ _
  choose P hP using fun i => exists_derivative_reconstruction I a ha d hdegree hu
    f hf.ne_zero hfd hker (X i) (by simp)
  have hc := (projection_card_le_image_add I d hdegree a ha (pderiv 1 f) P
    (fun hbad => not_dvd_pderiv_of_pderiv_ne_zero hf.ne_zero (plane_relation_pderiv_ne_zero
      (projectionCoordinateMap I a) f hf.ne_zero (Ideal.Quotient.eq_zero_iff_mem.mpr
        ((hker f).mpr dvd_rfl)) 0 1 (by decide) (by
        change Transcendental K ((Ideal.Quotient.mk I) (aeval a (X 0)))
        rw [aeval_X]
        exact hu))
      ((hker _).mp hbad))
    (fun i => (hP i).2) S hS).trans (Nat.add_le_add_left (Nat.mul_le_mul_left d
      (show (pderiv 1 f).totalDegree ≤ d - 1 by simpa [hfd] using pderiv_totalDegree_le f 1)) _)
  convert hc using 1
  congr 3
  funext z j
  fin_cases j <;> rfl

