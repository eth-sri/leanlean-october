/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.AuxiliaryPolynomial.AffineCongruenceHeight
public import CCDN.ForMathlib.StandardExponents
import CCDN.AuxiliaryPolynomial.StandardMonomialAuxiliary
import CCDN.AuxiliaryPolynomial.WeightedMonomialDeterminant

/-! Auxiliary polynomials from the competing congruence determinant
lower bound and weighted archimedean upper bound. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Finset

/-- The lower bound for the logarithm of a nonzero `s × s` determinant of monomials evaluated
at integral zeros of an absolutely irreducible affine equation of degree `d` in `n + 2`
variables with coefficient height at most `H`, when the zeros lie in smooth residue classes
modulo primes whose logarithms sum to `Q`. -/
def affineCongruenceDeterminantLower (n d s : ℕ) (H Q : ℝ) : ℝ :=
  ((n + 1).factorial : ℝ) ^ (1 / (n + 1 : ℝ)) / (n + 2 : ℝ) *
    (s : ℝ) ^ (1 + 1 / (n + 1 : ℝ)) *
      (Real.log s - (n + 1 : ℝ) * (4 * Real.log d +
        congruenceHeightCharge (n + 3) d H Q) - hypersurfaceDeterminantError n) +
    (hypersurfaceDeterminantMain n s - (n + 2 : ℝ) * s) * Q

/-- The determinant gap yields an integer auxiliary, proper over
the rationals, for every given finite family of points in the residue classes. -/
theorem exists_affine_congruence_auxiliary_of_gap {n N t M : ℕ} (hN : 0 < N)
    (f : MvPolynomial (Fin (n + 2)) ℤ)
    (hir : AbsolutelyIrreducible f)
    (hd : 0 < f.totalDegree) (H : ℝ) (hH : 1 ≤ H)
    (hcoeff : CoefficientHeightLE f H)
    (mon : Fin N → (Fin (n + 2) →₀ ℕ)) (hmon : Function.Injective mon)
    (hstd : ∀ j, mon j ∈ Ideal.standardExponents
      (Ideal.span {map (Int.castRingHom ℚ) f}) MonomialOrder.degLex)
    (hdegree : ∀ j, Finsupp.degree (mon j) ≤ M)
    {B : ℝ} {x : Fin t → IntPoint (n + 2)} (hxB : IsBoxZeroFamily f B x)
    (P : Finset ℕ) (a : ℕ → IntPoint (n + 2)) (hres : IsSmoothResidueFamily f P a x)
    (hgap : Real.log (N.factorial : ℝ) +
      (∑ j, ((Finsupp.degree (mon j) : ℕ) : ℝ)) * Real.log B <
      affineCongruenceDeterminantLower n f.totalDegree N H (∑ p ∈ P, Real.log p)) :
    ∃ g : MvPolynomial (Fin (n + 2)) ℤ, g ≠ 0 ∧
      ¬ map (Int.castRingHom ℚ) f ∣ map (Int.castRingHom ℚ) g ∧
      g.totalDegree ≤ M ∧ ∀ i, eval (x i) g = 0 := by
  classical
  refine exists_standard_auxiliary_of_zero_determinants
    (map (Int.castRingHom ℚ) f) mon hmon hstd hdegree x fun b => ?_
  by_contra hne
  let y := x ∘ b
  let G : Fin N → MvPolynomial (Fin (n + 2)) ℤ := fun j => monomial (mon j) 1
  have hmat : (Matrix.of fun i j => eval (y i) (G j)) = evaluationMatrix mon y := by
    ext i j; simp only [Matrix.of_apply, G, eval_monomial, one_mul]; rfl
  have hrows : LinearIndependent ℚ
      ((Matrix.of fun i j => eval (y i) (G j)).map ((↑) : ℤ → ℚ)).row := by
    rw [hmat, Matrix.linearIndependent_row_iff_isUnit, Matrix.isUnit_iff_isUnit_det,
      isUnit_iff_ne_zero]
    change ((Int.castRingHom ℚ).mapMatrix (evaluationMatrix mon y)).det ≠ 0
    rw [← RingHom.map_det (Int.castRingHom ℚ)]
    change ((evaluationMatrix mon (x ∘ b)).det : ℚ) ≠ 0
    exact_mod_cast hne
  have hlo := affine_congruence_determinant_log_lower_height hN f hir hd H hH hcoeff
    G (fun j => (totalDegree_monomial_le _ _).trans (hdegree j)) y
    (fun i => hxB.eval_eq_zero (b i)) hrows P a
    ⟨hres.prime, hres.eval_eq_zero, hres.smooth, fun p hp i j => hres.dvd_sub p hp (b i) j⟩
  let : Nonempty (Set.powersetCard (Fin N) N) := ⟨⟨univ, by simp⟩⟩
  have hcd : Int.Matrix.minorGcd (evaluationMatrix mon y) = |(evaluationMatrix mon y).det| := by
    rw [minorGcd_eq_gcd_plucker,
      show exteriorPower.plucker N (evaluationMatrix mon y).row = fun _ => (evaluationMatrix mon y).det
        from funext (exteriorPower.plucker_fin_eq_det _),
      Finset.gcd_eq_gcd_image, Finset.image_const univ_nonempty]
    simp only [Finset.gcd_singleton, id_eq, ← Int.abs_eq_normalize]
  rw [hmat, hcd, Int.cast_abs] at hlo
  exact (not_lt_of_ge (hlo.trans (weighted_evaluation_det_log_bound mon y
    hxB.one_le_radius (fun i j => hxB.abs_le (b i) j) hne))) hgap

end
end CCDN
