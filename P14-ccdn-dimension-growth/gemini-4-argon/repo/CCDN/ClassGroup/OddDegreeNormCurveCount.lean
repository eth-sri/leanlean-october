/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.AuxiliaryPolynomial.AffineHypersurfaceAuxiliary
public import CCDN.ClassGroup.NormPolynomial
import CCDN.ClassGroup.OddDegreeNormCurveBaseChange
import CCDN.ClassGroup.OddDegreeNormCurves
import CCDN.Plane.AffinePlaneBadPrimeCount

/-! Signed norm curves in odd field degree have no bad reduction primes.
Their integral point count has no logarithmic loss, as required
by the odd-degree branch of CCDN Theorem 6. -/

@[expose] public section
namespace CCDN
noncomputable section
open scoped NumberField

variable (K : Type*) [Field K] [NumberField K]

/-- The constant is absolute and the degree dependence polynomial.
The sign can be either unit of the integers, and the generator is arbitrary. -/
theorem signed_norm_curve_log_free_count
    (β : 𝓞 K) {ε : ℤ} (hε : IsUnit ε)
    (hn : 2 ≤ Module.finrank ℚ K) (hodd : Odd (Module.finrank ℚ K))
    {B : ℝ} (hB : 1 ≤ B) :
    (count (zeroLocus (MvPolynomial.map (Int.castRingHom ℚ)
      (signedNormCurvePolynomial K β ε))) B : ℝ) ≤
      (3 * affineHypersurfaceAuxiliaryConstant 0) *
        (Module.finrank ℚ K : ℝ) ^ 4 * B ^ (1 / (Module.finrank ℚ K : ℝ)) := by
  let f := signedNormCurvePolynomial K β ε
  have hprim : PrimitiveIntegerPolynomial f := fun c hc => by
    have hcoef : f.coeff (Finsupp.cons 2 (Finsupp.single 0 0)) = 1 := by
      rw [← bivariatePolynomialEquiv_coeff, show f = signedNormCurvePolynomial K β ε from rfl,
        signedNormCurvePolynomial, AlgEquiv.apply_symm_apply]
      simp only [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C]
      norm_num
    exact isUnit_iff_dvd_one.mpr (hcoef ▸ hc (Finsupp.cons 2 (Finsupp.single 0 0)))
  have hdegree : f.totalDegree = Module.finrank ℚ K :=
    signedNormCurvePolynomial_totalDegree K β hε.ne_zero hn
  have hbad_eq : hypersurfaceBadPrimeFactor f = 1 := by
    have hir_alg := signedNormCurvePolynomial_map_irreducible_in_every_characteristic K
      (AlgebraicClosure ℚ) β (hε.map (Int.castRingHom (AlgebraicClosure ℚ))).ne_zero hodd
    have hbad (p : ℕ) : p ∈ (∅ : Finset ℕ) ↔
        stepanovThreshold f.totalDegree < p ∧ HypersurfaceBadReduction f p := by
      simp only [Finset.notMem_empty, false_iff, not_and]
      rintro _ ⟨hp, hbad⟩
      let : Fact p.Prime := ⟨hp⟩
      have hεp : (ε : AlgebraicClosure (ZMod p)) ≠ 0 :=
        (hε.map (Int.castRingHom (AlgebraicClosure (ZMod p)))).ne_zero
      exact hbad.elim
        (fun h => h ((signedNormCurvePolynomial_map_totalDegree K
          (AlgebraicClosure (ZMod p)) β hεp hn).trans hdegree.symm))
        (fun h => h (signedNormCurvePolynomial_map_irreducible_in_every_characteristic K
          (AlgebraicClosure (ZMod p)) β hεp hodd))
    rw [hypersurfaceBadPrimeFactor_eq_exp f hir_alg rfl ∅ hbad]; simp
  have hh := affine_plane_count_bad_prime f hprim
    (signedNormCurvePolynomial_map_irreducible_in_every_characteristic K ℚ β
      (hε.map (Int.castRingHom ℚ)).ne_zero hodd) (by omega) hB
  rw [hdegree, hbad_eq] at hh
  convert hh using 1
  ring

end
end CCDN
