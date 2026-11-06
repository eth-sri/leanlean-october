/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Hilbert.FilteredHilbertPolynomial
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import CCDN.Hilbert.BoundedDegreeFunctionFieldRank
import CCDN.Hilbert.CoordinateIndependence
import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

/-!
The constructed Hilbert dimension equals transcendence-basis cardinality.
Consequently integral embeddings preserve Hilbert dimension.

Construct a finite linear parameter field from coordinate
functions, in arbitrary Hilbert dimension.
-/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- For a prime ideal `I`, some set of coordinate functions, of size the Hilbert dimension of `I`,
is a transcendence basis of `K[X] ⧸ I` over `K`. -/
theorem exists_hilbert_coordinate_transcendence_basis
    {K σ : Type*} [Field K] [Fintype σ] [LinearOrder σ]
    (I : Ideal (MvPolynomial σ K)) [I.IsPrime] :
    ∃ U : Set σ, Nat.card U = (filteredHilbertPolynomial I).natDegree ∧
      IsTranscendenceBasis K (fun i : U => (Ideal.Quotient.mk I) (X i.val)) := by
  classical
  let A := MvPolynomial σ K ⧸ I
  let F := FractionRing A
  let φ := IsScalarTower.toAlgHom K A F
  obtain ⟨d, _, _, hd⟩ := filteredHilbertPolynomial_positive_multiplicity I
    (Ideal.IsPrime.ne_top ‹I.IsPrime›)
  obtain ⟨U, hU, hAI⟩ := exists_hilbert_dimension_independent_coordinates I
    (Ideal.IsPrime.ne_top ‹I.IsPrime›)
  let R : IntermediateField K F := IntermediateField.adjoin K
    (Set.range fun i : U => algebraMap A F ((Ideal.Quotient.mk I) (X i.val)))
  let u : U → R := fun i => ⟨φ ((Ideal.Quotient.mk I) (X i.val)),
    IntermediateField.subset_adjoin K _ ⟨i, rfl⟩⟩
  have huF : AlgebraicIndependent K (fun i : U => φ ((Ideal.Quotient.mk I) (X i.val))) :=
    hAI.map' (IsFractionRing.injective _ _)
  have hu : AlgebraicIndependent K u := AlgebraicIndependent.of_comp R.val huF
  have hdim : (filteredHilbertPolynomial I).natDegree = Fintype.card U := by
    simpa only [Nat.card_eq_fintype_card] using hU.symm
  have hfinite : Module.Finite R F :=
    (hilbert_functionField_finite_rank_le I d ⟨hdim, by simpa only [← hdim] using hd⟩
      (fun i : U => X i.val) (fun _ => by simp) u hu (fun _ => rfl)).1
  have hfieldalg : Algebra.IsAlgebraic R F := ⟨fun x => (IsIntegral.of_finite R x).isAlgebraic⟩
  have hBF : IsTranscendenceBasis K (fun i : U => φ ((Ideal.Quotient.mk I) (X i.val))) :=
    huF.isTranscendenceBasis_iff_isAlgebraic.mpr
      (IntermediateField.isAlgebraic_adjoin_iff_top.mp hfieldalg)
  exact ⟨U, hU, IsTranscendenceBasis.of_comp φ (IsFractionRing.injective _ _) hBF⟩

/-- Integral embeddings preserve the filtered Hilbert dimension,
without assuming a normalization or a Hilbert polynomial. -/
theorem integral_embedding_hilbert_dimension_eq
    {K σ τ : Type*} [Field K] [Fintype σ] [Fintype τ]
    [LinearOrder σ] [LinearOrder τ]
    (I : Ideal (MvPolynomial σ K)) [I.IsPrime]
    (J : Ideal (MvPolynomial τ K)) [J.IsPrime]
    (ψ : (MvPolynomial σ K ⧸ I) →ₐ[K] (MvPolynomial τ K ⧸ J))
    (hψ : Function.Injective ψ) (hint : ψ.IsIntegral) :
    (filteredHilbertPolynomial I).natDegree = (filteredHilbertPolynomial J).natDegree := by
  classical
  let A := MvPolynomial σ K ⧸ I
  let B := MvPolynomial τ K ⧸ J
  let : Algebra A B := ψ.toRingHom.toAlgebra
  let : IsScalarTower K A B := IsScalarTower.of_algHom ψ
  let : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr hψ
  let : Algebra.IsAlgebraic A B := ⟨fun x => (show IsIntegral A x from hint x).isAlgebraic⟩
  obtain ⟨U, hU, hBU⟩ := exists_hilbert_coordinate_transcendence_basis I
  obtain ⟨V, hV, hBV⟩ := exists_hilbert_coordinate_transcendence_basis J
  have hc := hBV.lift_cardinalMk_eq (hBU.algebraMap_comp (A := B))
  have hcard : Fintype.card V = Fintype.card U := by
    simpa only [Cardinal.mk_fintype, Cardinal.lift_natCast, Nat.cast_inj] using hc
  rw [Nat.card_eq_fintype_card] at hU hV
  omega

end
end CCDN
