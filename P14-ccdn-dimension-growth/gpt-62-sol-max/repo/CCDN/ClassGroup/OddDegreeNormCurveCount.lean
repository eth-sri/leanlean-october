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
import CCDN.Plane.CurveCount

/-! Signed norm curves in odd field degree have no bad reduction primes.
Their integral point count has no logarithmic loss, as required
by the odd-degree branch of CCDN Theorem 6. -/

@[expose] public section
namespace CCDN
noncomputable section
open scoped NumberField

variable (K : Type*) [Field K] [NumberField K]

private theorem signedNormCurvePolynomial_primitive (β : 𝓞 K) (ε : ℤ) :
    PrimitiveIntegerPolynomial (signedNormCurvePolynomial K β ε) := by
  have hcoef : (signedNormCurvePolynomial K β ε).coeff
      (Finsupp.cons 2 (Finsupp.single 0 0)) = 1 := by
    rw [← bivariatePolynomialEquiv_coeff]
    rw [signedNormCurvePolynomial, AlgEquiv.apply_symm_apply]
    simp only [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C]
    norm_num
  intro c hc
  apply isUnit_iff_dvd_one.mpr
  have hh := hc (Finsupp.cons 2 (Finsupp.single 0 0))
  rwa [hcoef] at hh

section

variable (β : 𝓞 K) {ε : ℤ} (hε : IsUnit ε)
  (hn : 2 ≤ Module.finrank ℚ K) (hodd : Odd (Module.finrank ℚ K))
include β ε hε hn hodd

private theorem signedNormCurvePolynomial_no_bad_reduction (p : ℕ) :
    ¬ HypersurfaceBadReduction (signedNormCurvePolynomial K β ε) p := by
  rintro ⟨hp, hbad⟩
  let : Fact p.Prime := ⟨hp⟩
  have hεp : (ε : AlgebraicClosure (ZMod p)) ≠ 0 :=
    (hε.map (Int.castRingHom (AlgebraicClosure (ZMod p)))).ne_zero
  have hd := signedNormCurvePolynomial_map_totalDegree K
    (AlgebraicClosure (ZMod p)) β hεp hn
  have hdZ := signedNormCurvePolynomial_totalDegree K β hε.ne_zero hn
  have hir := signedNormCurvePolynomial_map_irreducible_in_every_characteristic K
    (AlgebraicClosure (ZMod p)) β hεp hodd
  simp_all

private theorem signedNormCurvePolynomial_bad_prime_factor :
    hypersurfaceBadPrimeFactor (signedNormCurvePolynomial K β ε) = 1 := by
  have hir := signedNormCurvePolynomial_map_irreducible_in_every_characteristic K
    (AlgebraicClosure ℚ) β ((hε.map (Int.castRingHom (AlgebraicClosure ℚ))).ne_zero) hodd
  have hbad (p : ℕ) : p ∈ (∅ : Finset ℕ) ↔
      stepanovThreshold (signedNormCurvePolynomial K β ε).totalDegree < p ∧
        HypersurfaceBadReduction (signedNormCurvePolynomial K β ε) p := by
    simp only [Finset.notMem_empty, false_iff, not_and]
    intro _
    exact signedNormCurvePolynomial_no_bad_reduction K β hε hn hodd p
  rw [hypersurfaceBadPrimeFactor_eq_exp (signedNormCurvePolynomial K β ε) hir rfl ∅ hbad]
  simp

/-- The constant is absolute and the degree dependence polynomial.
The sign can be either unit of the integers, and the generator is arbitrary. -/
theorem signed_norm_curve_log_free_count
    {B : ℝ} (hB : 1 ≤ B) :
    (count (zeroLocus (MvPolynomial.map (Int.castRingHom ℚ)
      (signedNormCurvePolynomial K β ε))) B : ℝ) ≤
      (3 * affineHypersurfaceAuxiliaryConstant 0) *
        (Module.finrank ℚ K : ℝ) ^ 4 * B ^ (1 / (Module.finrank ℚ K : ℝ)) := by
  have hir := signedNormCurvePolynomial_map_irreducible_in_every_characteristic K ℚ β ((hε.map (Int.castRingHom ℚ)).ne_zero) hodd
  have hdegree := signedNormCurvePolynomial_totalDegree K β hε.ne_zero hn
  have hh := affine_plane_count_bad_prime (signedNormCurvePolynomial K β ε)
    (signedNormCurvePolynomial_primitive K β ε) hir (by omega) hB
  rw [hdegree, signedNormCurvePolynomial_bad_prime_factor K β hε hn hodd] at hh
  convert hh using 1
  ring

end

end
end CCDN
