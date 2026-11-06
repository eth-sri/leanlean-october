/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Algebra.PolynomialPredicates
import CCDN.Hilbert.FilteredHilbertPolynomial
import CCDN.Hilbert.LinearProjectionFiltration
import CCDN.ForMathlib.FractionRing
import CCDN.Projection.HomogeneousBirationalDegree
import CCDN.Projection.IntegralProjectionHilbert
import CCDN.Projection.PrimitiveCoordinateField

/-! A homogeneous finite birational linear projection preserves the
Hilbert multiplicity. Both the conductor and the dimension equality
are consequences of the algebraic hypotheses. -/

namespace CCDN
section
open MvPolynomial

/-- A homogeneous linear projection of a homogeneous prime quotient that is integral and birational
(its coordinates generate the function field) preserves the leading coefficient of the filtered
Hilbert polynomial, and hence the degree. -/
theorem homogeneous_finite_birational_projection_leadingCoeff_eq
    {K F σ τ : Type*} [Field K] [Field F] [Algebra K F]
    [Fintype σ] [Fintype τ] [LinearOrder σ] [LinearOrder τ]
    (I : Ideal (MvPolynomial τ K)) [I.IsPrime]
    [Algebra (MvPolynomial τ K ⧸ I) F]
    [IsScalarTower K (MvPolynomial τ K ⧸ I) F]
    [IsFractionRing (MvPolynomial τ K ⧸ I) F]
    (hI : IsHomogeneousIdeal I)
    (a : σ → MvPolynomial τ K) (ha : ∀ i, (a i).IsHomogeneous 1)
    (hint : (projectionCoordinateMap I a).IsIntegral)
    (hfield : IntermediateField.adjoin K
      (Set.range (fun i => algebraMap (MvPolynomial τ K ⧸ I) F
        ((Ideal.Quotient.mk I) (a i)))) = ⊤) :
    (filteredHilbertPolynomial (RingHom.ker (projectionCoordinateMap I a))).leadingCoeff =
      (filteredHilbertPolynomial I).leadingCoeff := by
  let A := MvPolynomial τ K ⧸ I
  let ψ := projectionCoordinateMap I a
  let J := RingHom.ker ψ
  have : J.IsPrime := RingHom.ker_isPrime ψ.toRingHom
  let R := MvPolynomial σ K ⧸ J
  let φ : R →ₐ[K] A := Ideal.kerLiftAlg ψ
  let η : A →ₐ[K] F := IsScalarTower.toAlgHom K A F
  let : Algebra R A := φ.toRingHom.toAlgebra
  let : IsScalarTower K R A := IsScalarTower.of_algHom φ
  let : Algebra R F := (η.comp φ).toRingHom.toAlgebra
  let : IsScalarTower R A F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hinj :=
    (IsFractionRing.injective A F).comp (Ideal.kerLiftAlg_injective ψ)
  let : IsFractionRing R F := isFractionRing_of_generating_tuple
    (η.comp φ) hinj (fun i => (Ideal.Quotient.mk J) (X i)) (by
      convert hfield using 2
      congr 1
      funext i
      change algebraMap A F ((Ideal.Quotient.mk I) (aeval a (X i))) =
        algebraMap A F ((Ideal.Quotient.mk I) (a i))
      simp_all)
  let : Algebra.IsIntegral R A := ⟨hint.kerLift⟩
  let : Algebra.FiniteType R A :=
    Algebra.FiniteType.of_restrictScalars_finiteType K R A
  let : Module.Finite R A := Algebra.IsIntegral.finite
  obtain ⟨c, hc, hconductor⟩ : ∃ c : R, c ≠ 0 ∧ ∀ a : A, ∃ r : R,
      algebraMap R A r = algebraMap R A c * a := by
    obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule R A).FG)
    let φ : A →ₐ[R] F := IsScalarTower.toAlgHom R A F
    obtain ⟨c, hc⟩ := IsLocalization.exist_integer_multiples
      (nonZeroDivisors R) s (fun a => φ a)
    let N : Submodule R A :=
      Submodule.comap ((c : R) • φ.toLinearMap) (LinearMap.range (Algebra.linearMap R F))
    have hspan : Submodule.span R s ≤ N := by
      apply Submodule.span_le.mpr
      intro a ha
      exact hc a ha
    have hall (a : A) : a ∈ N := by simp_all
    refine ⟨c, mem_nonZeroDivisors_iff_ne_zero.mp c.2, ?_⟩
    intro a
    obtain ⟨r, hr⟩ := hall a
    refine ⟨r, ?_⟩
    apply IsFractionRing.injective A F
    change algebraMap A F (algebraMap R A r) =
      algebraMap A F (algebraMap R A c * a)
    rw [map_mul, ← IsScalarTower.algebraMap_apply R A F,
      ← IsScalarTower.algebraMap_apply R A F]
    simpa [LinearMap.smul_apply, Algebra.smul_def, Algebra.linearMap_apply,
      AlgHom.toLinearMap_apply, φ, IsScalarTower.toAlgHom_apply] using hr
  obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective c
  let q := aeval a p
  have hq : (Ideal.Quotient.mk I) q = φ c := by
    rw [← hp]
    rfl
  have hqne : (Ideal.Quotient.mk I) q ≠ 0 := by
    rw [hq]
    exact (map_ne_zero_iff φ (Ideal.kerLiftAlg_injective ψ)).mpr hc
  have hdim := integral_projection_hilbert_dimension_eq I ψ hint
  refine le_antisymm (filteredHilbertPolynomial_leadingCoeff_le _ _ (RingHom.ker_ne_top _)
    (Ideal.IsPrime.ne_top ‹_›) hdim (linear_projection_filtered_finrank_le I a
      fun i => (ha i).totalDegree_le)) (filteredHilbertPolynomial_leadingCoeff_le_of_shift _ _
    (Ideal.IsPrime.ne_top ‹_›) (RingHom.ker_ne_top _) hdim.symm q.totalDegree
    (conductor_filtered_finrank_le I hI a ha q hqne ?_))
  intro x
  obtain ⟨r, hr⟩ := hconductor x
  obtain ⟨p', hp'⟩ := Ideal.Quotient.mk_surjective r
  refine ⟨p', ?_⟩
  rw [hq]
  change φ ((Ideal.Quotient.mk J) p') = φ c * x
  rwa [hp']

