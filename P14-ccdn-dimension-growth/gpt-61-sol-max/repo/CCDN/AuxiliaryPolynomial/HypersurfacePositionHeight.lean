/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.AuxiliaryPolynomial.RankNumerics

public import CCDN.Algebra.Coordinates

import Mathlib

public import CCDN.Algebra.HomogeneousTranslation
public import CCDN.Height.IntegerCoefficientHeight
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.RingTheory.MvPolynomial.MonomialOrder
import CCDN.Algebra.HomogeneousChart
import CCDN.Height.MultivariateGridHeight
import CCDN.Height.PolynomialBoxHeight
import CCDN.Plane.HomogeneousLeadingCoefficient

/-!
The bounded shear has a dimension-uniform logarithmic positioning cost.

Bounded integer shears placing a large coefficient first, in all dimensions.
-/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial


end
end CCDN

namespace CCDN
noncomputable section
open MvPolynomial

private def hypersurfacePositionHeightFactor (n d : ℕ) : ℝ :=
  (↑d + 1) ^ ((n + 1) * (d + 1) + (n + 1) + n * (d + 1) + 2 * d)

private lemma hypersurfacePositionHeightFactor_one_le (n d : ℕ) :
    1 ≤ hypersurfacePositionHeightFactor n d := by
  apply one_le_pow₀
  linarith


variable {r d : ℕ}

/-- For positive integers `r` and `d`, `log (d + 1) ≤ (r + 1) * d ^ (1/r)`. -/
lemma log_nat_add_one_le_root  (hr : 0 < r) (hd : 0 < d) :
    Real.log (↑d + 1) ≤ (↑r + 1) * dimensionRoot r d := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hroot : 1 ≤ dimensionRoot r d :=
    Real.one_le_rpow hd1 (by positivity)
  have hlog := Real.log_le_rpow_div (by linarith : (0 : ℝ) ≤ d)
    (show 0 < 1 / ↑r by positivity)
  have h2 : Real.log 2 ≤ 1 := by
    grind [Real.log_le_sub_one_of_pos]
  have hh := Real.log_le_log (by positivity : (0 : ℝ) < d + 1)
    (show (d : ℝ) + 1 ≤ 2 * d by linarith)
  rw [Real.log_mul (by norm_num) (by positivity)] at hh
  rw [div_div_eq_mul_div, div_one] at hlog
  nlinarith


/-- Integer coordinates supply the logarithmic positioning condition,
and the chosen height bounds both the original and translated coefficients. -/
theorem exists_hypersurface_coefficient_position {n r d : ℕ} (hr : 0 < r) (hd : 0 < d)
    (f : CCDN.IntegerPolynomial (n + 1)) (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) :
    ∃ (a : CCDN.IntPoint n) (H : ℝ), (∀ j, 0 ≤ a j ∧ a j ≤ d) ∧ 1 ≤ H ∧
      CoefficientHeightLE f H ∧
      CoefficientHeightLE (homogeneousTranslation ℤ a f) H ∧
      Real.log H ≤
        Real.log |((MonomialOrder.lex.leadingCoeff (homogeneousTranslation ℤ a f) : ℤ) : ℝ)| +
          ((5 * ↑n + 5) * (↑r + 1)) * d * dimensionRoot r d := by
  obtain ⟨a, ha, hne, hc⟩ := (show ∃ a,
                                 (∀ (j : Fin n), (0 : ℤ) ≤ a j ∧ a j ≤ ↑d) ∧
                                   MonomialOrder.lex.leadingCoeff ((homogeneousTranslation ℤ a) f) ≠ (0 : ℤ) ∧
                                     CoefficientHeightLE f
                                       ((↑d + (1 : ℝ)) ^ (n * (d + (1 : ℕ))) * |↑(MonomialOrder.lex.leadingCoeff ((homogeneousTranslation ℤ a) f))|) from (by
                               have hc0 : affineChart n f ≠ 0 := by
                                 intro hz
                                 exact hf0 (affineChart_injective_on_homogeneous hf (isHomogeneous_zero _ _ d)
                                   (by simpa only [map_zero] using hz))
                               obtain ⟨a, ha, hval, hcoeff⟩ := exists_integer_multivariate_grid_height_witness (affineChart n f)
                                 hc0 ((affineChart_totalDegree_le f).trans hf.totalDegree_le)
                               have he : (homogeneousTranslation ℤ a f).coeff (Finsupp.single 0 d) =
                                   eval a (affineChart n f) := by
                                 rw [homogeneousTranslation_pure_first a f hf, affineChart_eval]
                               have hlc := lex_leadingCoeff_eq_pure_first (homogeneousTranslation ℤ a f)
                                 (homogeneousTranslation_homogeneous a hf).totalDegree_le (he ▸ hval)
                               refine ⟨a, ha, by rw [hlc, he]; exact hval, ?_⟩
                               intro m
                               by_cases hm : m.degree = d
                               · obtain ⟨j, rfl⟩ := homogeneousMonomials_surjective n d m hm
                                 rw [← affineChart_homogeneous_coefficient f hf j, hlc, he]
                                 exact hcoeff _
                               · rw [hf.coeff_eq_zero hm, Int.cast_zero, abs_zero]
                                 positivity))
  let L := |((MonomialOrder.lex.leadingCoeff (homogeneousTranslation ℤ a f) : ℤ) : ℝ)|
  have hL : 1 ≤ L := by dsimp only [L]; exact_mod_cast Int.one_le_abs hne
  have hL0 : 0 < L := by linarith
  have hP := hypersurfacePositionHeightFactor_one_le n d
  refine ⟨a, hypersurfacePositionHeightFactor n d * L, ha,
    one_le_mul_of_one_le_of_one_le hP hL, ?_,
    (show ∀ (m : Fin (n + (1 : ℕ)) →₀ ℕ), |↑(((homogeneousTranslation ℤ a) f).coeff m)| ≤ hypersurfacePositionHeightFactor n d * L from (by
      intro m
      let K := ((d : ℝ) + 1) ^ (n * (d + 1))
      let V := (↑d + 1) ^ (n + 1) * (K * L) * ((↑d + 1) ^ 2) ^ d
      have heval (z : Fin (n + 1) → ℕ) (hz : ∀ j, z j ≤ d) :
          |(eval (fun i => (z i : ℤ)) (homogeneousTranslation ℤ a f) : ℝ)| ≤ V := by
        let w : CCDN.IntPoint (n + 1) := Fin.cons (z 0 : ℤ)
          (fun j => (z j.succ : ℤ) + a j * (z 0 : ℤ))
        have hbox : InBox w ((↑d + 1) ^ 2) := by
          intro j
          have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
          refine Fin.cases ?_ (fun k => ?_) j
          · have hz0 : (z 0 : ℝ) ≤ d := by exact_mod_cast hz 0
            simp only [w, Fin.cons_zero, Int.cast_natCast,
              abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (z 0))]
            nlinarith
          · have hz1 : (z k.succ : ℝ) ≤ d := by exact_mod_cast hz k.succ
            have hz0 : (z 0 : ℝ) ≤ d := by exact_mod_cast hz 0
            have ha0 : 0 ≤ a k := by exact_mod_cast (ha k).1
            have had : (a k : ℝ) ≤ d := by exact_mod_cast (ha k).2
            simp only [w, Fin.cons_succ, Int.cast_add, Int.cast_mul, Int.cast_natCast]
            rw [abs_of_nonneg (by positivity)]
            nlinarith [mul_le_mul had hz0 (Nat.cast_nonneg (z 0)) hd0]
        have hh := polynomial_eval₂_box_bound f (K * L) ((↑d + 1) ^ 2)
          (by dsimp [K]; positivity) (one_le_pow₀ (by simp_all))
          hc (fun j => (w j : ℝ)) hbox
        rw [hf.totalDegree hf0] at hh
        rw [homogeneousTranslation_eval]
        have he : eval₂ (Int.castRingHom ℝ) (fun j => (w j : ℝ)) f = (eval w f : ℝ) :=
          (eval₂_comp (Int.castRingHom ℝ) w f).symm
        simpa only [he, Fintype.card_fin, V] using hh
      have hh := integer_multivariate_coefficient_bound_of_grid (homogeneousTranslation ℤ a f)
        (homogeneousTranslation_homogeneous a hf).totalDegree_le
        (show 0 ≤ V by dsimp [V, K]; positivity)
        heval m
      convert hh using 1
      dsimp only [hypersurfacePositionHeightFactor, V, K]
      simp only [pow_add, pow_mul]
      ring)), ?_⟩
  · intro m
    exact (hc m).trans
      (mul_le_mul_of_nonneg_right ((by
                                     apply pow_le_pow_right₀ (by simp_all)
                                     omega)) hL0.le)
  · rw [Real.log_mul (by linarith) hL0.ne']
    have hh := (show Real.log (hypersurfacePositionHeightFactor n d) ≤ ((5 : ℝ) * ↑n + (5 : ℝ)) * (↑r + (1 : ℝ)) * ↑d * dimensionRoot r d from (by
                 have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
                 have hlog := log_nat_add_one_le_root hr hd
                 have he : (((n + 1) * (d + 1) + (n + 1) + n * (d + 1) + 2 * d : ℕ) : ℝ) ≤
                     (5 * ↑n + 5) * d := by push_cast; nlinarith
                 unfold hypersurfacePositionHeightFactor
                 rw [Real.log_pow]
                 have hmul := mul_le_mul he hlog (Real.log_nonneg (by linarith : (1 : ℝ) ≤ d + 1))
                   (show 0 ≤ (5 * (n : ℝ) + 5) * d by positivity)
                 nlinarith))
    dsimp only [L]
    linarith

end
end CCDN
