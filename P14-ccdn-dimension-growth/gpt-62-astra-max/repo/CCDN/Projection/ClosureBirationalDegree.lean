/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module
public import CCDN.Projection.ClosureProjectionFiltration
public import CCDN.Hilbert.FilteredHilbertPolynomial
public import CCDN.Projection.ImageFractionField
import CCDN.ForMathlib.FractionRing
import CCDN.Projection.PrimitiveCoordinateField
import CCDN.Projection.IntegralProjectionHilbert
import CCDN.Hilbert.PolynomialComparison
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

private theorem projection_conductor
    {K F σ τ : Type*} [Field K] [Field F] [Algebra K F]
    [Fintype τ]
    (I : Ideal (MvPolynomial τ K)) [I.IsPrime]
    [Algebra (MvPolynomial τ K ⧸ I) F]
    [IsScalarTower K (MvPolynomial τ K ⧸ I) F]
    [IsFractionRing (MvPolynomial τ K ⧸ I) F]
    (a : σ → MvPolynomial τ K)
    (hint : (projectionCoordinateMap I a).IsIntegral)
    (hfield : IntermediateField.adjoin K
      (Set.range (fun i => algebraMap (MvPolynomial τ K ⧸ I) F
        ((Ideal.Quotient.mk I) (a i)))) = ⊤) :
    ∃ c : MvPolynomial τ K ⧸ I, c ≠ 0 ∧ ∀ x, ∃ p, projectionCoordinateMap I a p = c * x := by
  let A := MvPolynomial τ K ⧸ I
  let ψ := projectionCoordinateMap I a
  let J := RingHom.ker ψ
  have : J.IsPrime := RingHom.ker_isPrime ψ.toRingHom
  let R := MvPolynomial σ K ⧸ J
  let φ := Ideal.kerLiftAlg ψ
  let η := IsScalarTower.toAlgHom K A F
  let := φ.toRingHom.toAlgebra
  let := (η.comp φ).toRingHom.toAlgebra
  let : IsScalarTower R A F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hinj :=
    (IsFractionRing.injective A F).comp (Ideal.kerLiftAlg_injective ψ)
  let := isFractionRing_of_generating_tuple
    (η.comp φ) hinj (fun i => (Ideal.Quotient.mk J) _) (by
      convert hfield using 2
      congr 1
      funext i
      change algebraMap A F ((Ideal.Quotient.mk I) (aeval a (X i))) =
        algebraMap A F _
      rw [aeval_X])
  let : Algebra.IsIntegral R A := ⟨hint.kerLift⟩
  let :=
    Algebra.FiniteType.of_restrictScalars_finiteType K R A
  let : Module.Finite R A := Algebra.IsIntegral.finite
  obtain ⟨c, hc, hconductor⟩ := IsFractionRing.exists_ne_zero_mul_mem_range_of_finite R A F
  refine ⟨φ c, (map_ne_zero_iff φ (Ideal.kerLiftAlg_injective ψ)).mpr hc, fun x => ?_⟩
  obtain ⟨r, hr⟩ := hconductor x
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective r
  exact ⟨p, hr⟩

variable {K L σ τ : Type*} [Field K]

private theorem filteredHilbertPolynomial_leadingCoeff_le_of_shift [Field L] [Fintype σ] [Fintype τ]
    [LinearOrder σ] [LinearOrder τ]
    (I : Ideal (MvPolynomial σ K)) (J : Ideal (MvPolynomial τ L))
    (hI : I ≠ ⊤) (hJ : J ≠ ⊤)
    (hd : (filteredHilbertPolynomial I).natDegree = (filteredHilbertPolynomial J).natDegree)
    (D : ℕ)
    (hle : ∀ N, Module.finrank K (filteredCoordinateSpace I N) ≤
      Module.finrank L (filteredCoordinateSpace J (D + N))) :
    (filteredHilbertPolynomial I).leadingCoeff ≤
      (filteredHilbertPolynomial J).leadingCoeff := by
  let Q := (filteredHilbertPolynomial J).comp (Polynomial.X + Polynomial.C (D : ℚ))
  have hQdeg : Q.natDegree = (filteredHilbertPolynomial J).natDegree := by
    simp_rw [Q, Polynomial.natDegree_comp, Polynomial.natDegree_X_add_C, mul_one]
  have hQlc : Q.leadingCoeff = (filteredHilbertPolynomial J).leadingCoeff := by
    rw [Polynomial.leadingCoeff_comp (by rw [Polynomial.natDegree_X_add_C]; exact one_ne_zero),
      Polynomial.leadingCoeff_X_add_C, one_pow, mul_one]
  have hh := polynomial_leadingCoeff_le_of_eventual_nat_eval_le
    _ Q (filteredHilbertPolynomial_leadingCoeff_pos I hI)
    (by simp_all [filteredHilbertPolynomial_leadingCoeff_pos])
    (hd.trans hQdeg.symm) (by
      obtain ⟨M, hM⟩ := filteredHilbertPolynomial_spec I
      obtain ⟨N, hN⟩ := filteredHilbertPolynomial_spec J
      refine ⟨max M N, fun n hn => ?_⟩
      rw [hM n (by omega)]
      simp only [Q, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X,
        Polynomial.eval_C]
      rw [show n + D = ((D + n : ℕ) : ℚ) by push_cast; ring,
        hN _ (by omega)]
      exact_mod_cast hle n)
  grind

/-- An affine birational linear projection that is finite also on the projective
closures preserves the Hilbert degree, without homogeneity of the affine ideal. -/
theorem closure_finite_birational_leadingCoeff_eq {K : Type*} [Field K] {n m : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (a : Fin m → MvPolynomial (Fin n) K) (ha : ∀ i, (a i).IsHomogeneous 1)
    (hfin : (projectionCoordinateMap (projectiveClosureIdeal I) (closureProjectionCoordinates a)).IsIntegral)
    (hfield : projectionImageField (F := FractionRing (MvPolynomial (Fin n) K ⧸ I)) I a = ⊤) :
    (filteredHilbertPolynomial (RingHom.ker (projectionCoordinateMap I a))).leadingCoeff =
      (filteredHilbertPolynomial I).leadingCoeff := by
  let ψ := projectionCoordinateMap I a
  let J := RingHom.ker ψ
  have hfin' := affine_projection_integral_of_closure_integral I a hfin
  have hd := integral_projection_hilbert_dimension_eq I ψ hfin'
  have hI := Ideal.IsPrime.ne_top ‹I.IsPrime›
  have hJ : J ≠ ⊤ := RingHom.ker_ne_top _
  obtain ⟨c,hc,hcond⟩ := projection_conductor I a hfin' hfield
  obtain ⟨D,hD⟩ := closure_projection_conductor_shift I a ha hfin c hcond
  apply le_antisymm (filteredHilbertPolynomial_leadingCoeff_le J I hJ hI hd
    (linear_projection_filtered_finrank_le I a fun i => (ha i).totalDegree_le))
  apply filteredHilbertPolynomial_leadingCoeff_le_of_shift I J hI hJ hd.symm D
  intro N
  let V := filteredCoordinateSpace I N
  let W := filteredCoordinateSpace J (D+N)
  let φ := Ideal.kerLiftAlg ψ
  let T := ((LinearMap.mulLeft K c).comp V.subtype).codRestrict _ (fun x => hD N _ x.property)
  have hi : Function.Injective T := fun x y he => Subtype.ext (mul_left_cancel₀ hc (congrArg Subtype.val he))
  have hmap : W.map φ.toLinearMap = imagePiece ψ (D+N) := by
    dsimp only [W, filteredCoordinateSpace, imagePiece]
    rw [← Submodule.map_comp]
    rfl
  let : Module.Finite K (imagePiece ψ _) := by rw [← hmap]; infer_instance
  exact (LinearMap.finrank_le_finrank_of_injective hi).trans (hmap ▸ Submodule.finrank_map_le _ _)

end
end CCDN
