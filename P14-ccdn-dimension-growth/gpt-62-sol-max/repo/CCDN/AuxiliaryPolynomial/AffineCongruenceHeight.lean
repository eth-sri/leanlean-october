/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.PolynomialPredicates
public import CCDN.Algebra.HomogeneousChart
public import CCDN.Determinant.HypersurfaceDeterminantRank
public import CCDN.Height.CountingHypotheses
public import CCDN.Plane.IntegerPlaneLogHeight
import CCDN.AuxiliaryPolynomial.CongruenceBadPrimeCharge
import CCDN.AuxiliaryPolynomial.ScaledAffineAuxiliary
import CCDN.AuxiliaryPolynomial.UnscaledHypersurfaceBadPrimes
import CCDN.AuxiliaryPolynomial.HypersurfaceBadPrimeCoordinates
import CCDN.Determinant.ProjectiveHypersurfaceLocal
import CCDN.Determinant.PlaneMultiplicitySmooth
import CCDN.Determinant.HypersurfaceMultiplicityEstimate

/-! The affine congruence determinant bound with all bad-prime charges
controlled by the equation's coefficient height and congruence modulus. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Finset

/-- The homogeneous coordinates `(1, x)` of an integer point `x` are primitive: their gcd is `1`. -/
private lemma primitive_affine_integer_coordinates {n : ℕ} (x : Fin n → ℤ) :
    Finset.univ.gcd (Fin.cons 1 x) = 1 := by
  have he : insert (0 : Fin (n + 1)) univ = univ := insert_eq_of_mem (mem_univ _)
  have hh := congrArg (fun S : Finset (Fin (n + 1)) => S.gcd (Fin.cons 1 x)) he
  simpa only [Finset.gcd_insert, Fin.cons_zero, gcd_one_left] using hh.symm

/-- The logarithmic bad-prime charge in the affine congruence determinant estimate for a form
of degree `d` in `m` variables with coefficient height at most `H`, where `Q` is the sum of
the logarithms of the congruence primes. -/
def congruenceHeightCharge (m d : ℕ) (H Q : ℝ) : ℝ :=
  Real.log (1 + 27 * (d : ℝ) ^ 4 *
    (hypersurfaceHeightConstant m * (1 + Real.log H / (d : ℝ) ^ 2)) + Q) +
      2 * mertensError + 1

/-- The lower bound for smooth congruence classes with total prime logarithm `Q`. -/
def affineCongruenceDeterminantLower (n d s : ℕ) (H Q : ℝ) : ℝ :=
  hypersurfaceRankLowerBound n s d (congruenceHeightCharge (n + 3) d H Q) +
    (hypersurfaceDeterminantMain n s - (n + 2 : ℝ) * s) * Q

/-- At a nonsingular reduced point the translated equation has
multiplicity one. -/
private theorem smooth_hypersurface_origin_order {p : ℕ} [Fact p.Prime] {σ : Type*}
    (f : MvPolynomial σ ℤ) (a : σ → ℤ)
    (ha : eval₂ (Int.castRingHom (ZMod p)) (fun j => (a j : ZMod p)) f = 0)
    (hs : ∃ j, eval (fun i => (a i : ZMod p))
      (pderiv j (map (Int.castRingHom (ZMod p)) f)) ≠ 0) :
    map (Int.castRingHom (ZMod p)) (originShift a f) ∈ idealOfVars σ (ZMod p) ^ 1 ∧
    homogeneousComponent 1 (map (Int.castRingHom (ZMod p)) (originShift a f)) ≠ 0 := by
  have hf : map (Int.castRingHom (ZMod p)) f ≠ 0 := by
    grind +ring
  let μ := originMultiplicity (map (Int.castRingHom (ZMod p)) (originShift a f))
  obtain ⟨hμ, _, hpow, hcomp⟩ := reduction_originMultiplicity_spec f a hf ha
  change 0 < μ at hμ
  change _ ∈ _ ^ μ at hpow
  have he := origin_order_eq_one_of_smooth _ _ hμ
    (by simpa only [originShift_map, Int.coe_castRingHom] using hpow) hs
  change homogeneousComponent μ _ ≠ 0 at hcomp
  rw [he] at hpow hcomp
  exact ⟨hpow, hcomp⟩

/-- The logarithmic height and modulus are the only equation-dependent
errors in the affine smooth-congruence determinant estimate. -/
theorem affine_congruence_determinant_log_lower_height {n s M : ℕ} (hs : 0 < s)
    (f : MvPolynomial (Fin (n + 2)) ℤ)
    (hir : AbsolutelyIrreducible f)
    (hd : 0 < f.totalDegree) (H : ℝ) (hH : 1 ≤ H)
    (hcoeff : CoefficientHeightLE f H)
    (G : Fin s → MvPolynomial (Fin (n + 2)) ℤ) (hG : ∀ j, (G j).totalDegree ≤ M)
    (x : Fin s → IntPoint (n + 2)) (hx : ∀ i, eval (x i) f = 0)
    (hdet : (Matrix.of fun i j => eval (x i) (G j)).det ≠ 0)
    (P : Finset ℕ) (a : ℕ → IntPoint (n + 2)) (hres : IsSmoothResidueFamily f P a x) :
    affineCongruenceDeterminantLower n f.totalDegree s H (∑ p ∈ P, Real.log p) ≤
      Real.log |((Matrix.of fun i j => eval (x i) (G j)).det : ℝ)| := by
  classical
  let F := scaledHomogenize f.totalDegree 1 f
  have hf0 := ne_zero_of_irreducible_map hir
  have hF := scaledHomogenize_homogeneous 1 f le_rfl
  have hFir :=
    (unscaledHomogenize_absolute_irreducible_iff f hf0).mpr hir
  let Gh := fun j => scaledHomogenize M 1 (G j)
  have hGh := fun j => scaledHomogenize_homogeneous 1 _ (hG j)
  let z : Fin s → IntPoint (n + 3) := fun i => Fin.cons 1 (x i)
  have hz : ∀ i, eval (z i) F = 0 := by
    intro i
    rw [← affineChart_eval, affineChart_scaledHomogenize_one]
    exact hx i
  have he : (Matrix.of fun i j => eval (z i) (Gh j)) =
      Matrix.of fun i j => eval (x i) (G j) := by
    ext i j
    change eval (Fin.cons 1 (x i)) (scaledHomogenize M 1 (G j)) = _
    rw [← affineChart_eval, affineChart_scaledHomogenize_one]
    rfl
  obtain ⟨bad, hbad⟩ := exists_hypersurface_bad_prime_finset F hF hd hFir
  let v := hypersurfaceMultiplicityExponent (n + 1) 1 s
  have hcong (p : ℕ) (hp : p ∈ P) :
      (p : ℤ) ^ v ∣ minorGcd (Matrix.of fun i j => eval (z i) (Gh j)) := by
    let : Fact p.Prime := ⟨hres.prime p hp⟩
    obtain ⟨hpow, hcomp⟩ := smooth_hypersurface_origin_order f (a p)
      (hres.eval_eq_zero p hp) (hres.smooth p hp)
    rw [he, minorGcd_square, dvd_abs]
    exact hypersurface_residue_pow_dvd_det_mod f (a p) hpow hcomp x
      (hres.dvd_sub p hp) (fun i => hx i ▸ dvd_zero _) G
  have hrows : LinearIndependent ℚ
      ((Matrix.of fun i j => eval (x i) (G j)).map ((↑) : ℤ → ℚ)).row := by
    rw [Matrix.linearIndependent_row_iff_isUnit, Matrix.isUnit_iff_isUnit_det,
      isUnit_iff_ne_zero]
    exact_mod_cast hdet
  have hbound := hypersurface_determinant_log_lower_at_rank hs F hF hd
    ⟨hGh, fun i => primitive_affine_integer_coordinates (x i), hz, he ▸ hrows⟩
    bad hbad P hres.prime v hcong
  rw [he, minorGcd_square, Int.cast_abs] at hbound
  have hF0 : F ≠ 0 := scaledHomogenize_ne_zero _ one_ne_zero hf0
  have hFdegree :=
    (scaledHomogenize_homogeneous 1 f le_rfl).totalDegree hF0
  have hheight : (integerCoefficientHeight F : ℝ) ≤ H := by
    rw [show F = scaledHomogenize f.totalDegree 1 f from rfl,
      integerCoefficientHeight_scaledHomogenize_one]
    exact integerCoefficientHeight_le f (by linarith) hcoeff
  have hc := hypersurface_and_congruence_prime_charge F hFir (hFdegree ▸ hd) H hH
    (fun e => (coefficient_abs_le_integerCoefficientHeight F e).trans hheight) bad P
    (fun p hp => hFdegree ▸ (hbad p).mp hp) hres.prime
  change (∑ p ∈ bad ∪ P, Real.log p / p) ≤
    congruenceHeightCharge (n + 3) F.totalDegree H (∑ p ∈ P, Real.log p) at hc
  rw [hFdegree] at hc
  have hv : hypersurfaceDeterminantMain n s - (n + 2 : ℝ) * s ≤ (v : ℝ) := by
    simpa [v, hypersurfaceDeterminantMain, show (n : ℝ) + 1 + 1 = n + 2 by ring] using
      hypersurfaceMultiplicityExponent_lower_bound (n + 1) s (by omega)
  have hQ : 0 ≤ ∑ p ∈ P, Real.log p :=
    sum_nonneg fun p hp => Real.log_nonneg (by exact_mod_cast (hres.prime p hp).one_le)
  apply le_trans _ hbound
  unfold affineCongruenceDeterminantLower hypersurfaceRankLowerBound
  gcongr

end
end CCDN
