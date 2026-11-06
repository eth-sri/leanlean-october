/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.ProjectiveAffineChart
public import CCDN.Algebra.ProjectiveChartDegree

/-! The prime affine-chart ideal and the transport of projective
points and Hilbert degree to that ideal. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The ideal of the standard affine chart `X₀ ≠ 0` of the projective variety cut out by a
homogeneous prime ideal `I`: the polynomials in the affine coordinates vanishing at the ratios
`Xⱼ / X₀` in the fraction field of the coordinate ring of `I`. -/
def projectiveChartIdeal {K : Type*} [Field K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) K)) [I.IsPrime] :
    Ideal (MvPolynomial (Fin n) K) :=
  RingHom.ker (projectiveChartCoordinateMap I
    (IsScalarTower.toAlgHom K (MvPolynomial (Fin (n + 1)) K ⧸ I)
      (FractionRing (MvPolynomial (Fin (n + 1)) K ⧸ I))))

instance projectiveChartIdeal_isPrime {K : Type*} [Field K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) K)) [I.IsPrime] :
    (projectiveChartIdeal I).IsPrime :=
  RingHom.ker_isPrime _

/-- If a prime ideal `I` not containing `X 0` defines a projective curve of degree `d`, then its
standard affine chart ideal defines an affine curve of degree `d`. -/
theorem projectiveChartIdeal_degree {n d : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) ℚ)) [I.IsPrime] (hX : X 0 ∉ I)
    (hdegree : HasProjectiveCurveDegree I d) :
    HasAffineCurveDegree (projectiveChartIdeal I) d :=
  projective_chart_degree I _ (IsFractionRing.injective _ _)
    (fun h => hX (Ideal.Quotient.eq_zero_iff_mem.mp (by simpa using h))) hdegree

/-- If a projective point `x` on the zero locus of a prime ideal `I` (with `X 0 ∉ I`) has
nonzero first coordinate, then its affine coordinates lie on the zero locus of the standard
affine chart ideal of `I`. -/
theorem projectiveChartIdeal_point {n : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) ℚ)) [I.IsPrime] (hX : X 0 ∉ I)
    (x : ProjectivePoint n) (hx : x ∈ projectiveIdealZeroLocus I) (hx0 : x.rep 0 ≠ 0) :
    projectiveAffineCoordinates x ∈ idealZeroLocus (projectiveChartIdeal I) := by
  /- Let `q` embed the coordinate ring of `I` into a field with `q X₀ ≠ 0`. A homogeneous
  polynomial `f` lies in `I` if and only if its dehomogenization `affineChart n f` lies in the
  kernel of the coordinate-ratio map `projectiveChartCoordinateMap I q`. -/
  /- Let `q` embed the coordinate ring of `I` into a field with `q X₀ ≠ 0`. A polynomial `f` of
  total degree at most `M` lies in the kernel of the coordinate-ratio map
  `projectiveChartCoordinateMap I q` if and only if its degree-`M` homogenization lies in `I`. -/
  intro f hf
  let q := IsScalarTower.toAlgHom ℚ (MvPolynomial (Fin (n + 1)) ℚ ⧸ I)
    (FractionRing (MvPolynomial (Fin (n + 1)) ℚ ⧸ I))
  have h0 : q ((Ideal.Quotient.mk I) (X 0)) ≠ 0 :=
    fun h => hX (Ideal.Quotient.eq_zero_iff_mem.mp (by simpa [q] using h))
  have hhom := scaledHomogenize_homogeneous 1 f le_rfl
  change f ∈ RingHom.ker (projectiveChartCoordinateMap I q) at hf
  rw [← affineChart_scaledHomogenize_one f.totalDegree f, RingHom.mem_ker,
    projectiveChartCoordinateMap_chart I q h0 _ hhom,
    mul_eq_zero_iff_left (pow_ne_zero _ (inv_ne_zero h0))] at hf
  have hh : scaledHomogenize f.totalDegree 1 f ∈ I :=
    Ideal.Quotient.eq_zero_iff_mem.mp (by simpa [q] using hf)
  have hz := projectiveAffineCoordinates_zero (scaledHomogenize f.totalDegree 1 f)
    hhom x hx0 (projectiveIdealZeroLocus_rep hx _ hh)
  rwa [affineChart_scaledHomogenize_one] at hz

end
end CCDN
