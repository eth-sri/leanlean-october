/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.Equations
public import CCDN.Algebra.PolynomialPredicates
public import CCDN.Algebra.ScaledHomogenization
public import CCDN.Determinant.HypersurfaceDeterminantRank
public import CCDN.Height.CountingHypotheses
import CCDN.AuxiliaryPolynomial.UnscaledHypersurfaceBadPrimes
import CCDN.Determinant.SmoothCongruenceDeterminant

/-! Congruence-refined determinant estimates for affine zeros and
arbitrary bounded-degree polynomial evaluation columns. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Finset

/-- The homogeneous coordinates `(1, x)` of an integer point `x` are primitive: their gcd is `1`. -/
lemma primitive_affine_integer_coordinates {n : ℕ} (x : Fin n → ℤ) :
    Finset.univ.gcd (Fin.cons 1 x) = 1 := by
  have he : insert (0 : Fin (n + 1)) univ = univ := insert_eq_of_mem (mem_univ _)
  have hh := congrArg (fun S : Finset (Fin (n + 1)) => S.gcd (Fin.cons 1 x)) he
  simpa only [Finset.gcd_insert, Fin.cons_zero, gcd_one_left] using hh.symm

/-- Homogenization transfers the proved global-plus-congruence estimate
without changing a single affine evaluation. -/
theorem affine_congruence_determinant_log_lower {n s N M : ℕ} (hs : 0 < s)
    (f : IntegerPolynomial (n + 2))
    (hf0 : f ≠ 0) (bad : Finset ℕ)
    (hbad : ∀ p, stepanovThreshold f.totalDegree < p → HypersurfaceBadReduction f p → p ∈ bad)
    (hd : 0 < f.totalDegree)
    (G : Fin N → IntegerPolynomial (n + 2)) (hG : ∀ j, (G j).totalDegree ≤ M)
    (x : Fin s → IntPoint (n + 2)) (hx : ∀ i, eval (x i) f = 0)
    (hrows : LinearIndependent ℚ
      ((valueMatrix x G).map ((↑) : ℤ → ℚ)).row)
    (P : Finset ℕ) (a : ℕ → IntPoint (n + 2)) (hres : IsSmoothResidueFamily f P a x) :
    hypersurfaceRankLowerBound n s f.totalDegree (∑ p ∈ bad ∪ P, Real.log p / p) +
        (hypersurfaceDeterminantMain n s - (n + 2 : ℝ) * s) *
          (∑ p ∈ P, Real.log p) ≤
        Real.log (Int.Matrix.minorGcd (valueMatrix x G)) := by
  classical
  let F := scaledHomogenize f.totalDegree 1 f
  have hF := scaledHomogenize_homogeneous 1 f le_rfl
  let H := fun j => scaledHomogenize M 1 (G j)
  have hH := fun j => scaledHomogenize_homogeneous 1 _ (hG j)
  let z : Fin s → IntPoint (n + 3) := fun i => Fin.cons 1 (x i)
  have hz : ∀ i, eval (z i) F = 0 := by
    intro i
    rw [← affineChart_eval, affineChart_scaledHomogenize_one]
    exact hx i
  have he : (valueMatrix z H) =
      valueMatrix x G := by
    ext i j
    change eval (Fin.cons 1 (x i)) (scaledHomogenize M 1 (G j)) = _
    simp [← affineChart_eval, affineChart_scaledHomogenize_one]
  have hrows' : LinearIndependent ℚ
      ((valueMatrix z H).map ((↑) : ℤ → ℚ)).row := by
    rw [he]
    exact hrows
  have hchart : projectiveHypersurfaceChart (0 : Fin (n + 3)) F = f := by
    simp only [projectiveHypersurfaceChart, Equiv.swap_self, Equiv.coe_refl, rename_id_apply, F,
      affineChart_scaledHomogenize_one]
  apply he ▸ smooth_congruence_determinant_log_lower hs F hF hd bad
    (fun p hc hb => hbad p hc (hypersurfaceBadReduction_unscaledHomogenize_imp f hf0 p hb))
    ⟨hH, fun i => primitive_affine_integer_coordinates (x i), hz, hrows'⟩ P hres.prime
    (fun _ => 0) a (by simpa [hchart] using hres.eval_eq_zero)
    (by simpa only [hchart] using hres.smooth)
    (by solve_by_elim [isCoprime_one_right])
    (by intro p hp i j; simpa using hres.dvd_sub p hp i j)

end
end CCDN
