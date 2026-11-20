/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.HomogeneousTranslation
public import CCDN.Height.IntegerCoefficientHeight
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.RingTheory.MvPolynomial.MonomialOrder
public import CCDN.AuxiliaryPolynomial.DegreeBound
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

/-- For positive integers `r` and `d`, `log (d + 1) ≤ (r + 1) * d ^ (1/r)`. -/
lemma log_nat_add_one_le_root {r d : ℕ} (hr : 0 < r) (hd : 0 < d) :
    Real.log ((d : ℝ) + 1) ≤ ((r : ℝ) + 1) * (d : ℝ) ^ (1 / (r : ℝ)) := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hroot : (1 : ℝ) ≤ (d : ℝ) ^ (1 / (r : ℝ)) :=
    Real.one_le_rpow hd1 (by positivity)
  have hlog := Real.log_le_rpow_div (by linarith : (0 : ℝ) ≤ d)
    (show (0 : ℝ) < 1 / (r : ℝ) by positivity)
  have h2 : Real.log (2 : ℝ) ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hh := Real.log_le_log (by positivity : (0 : ℝ) < d + 1)
    (show (d : ℝ) + 1 ≤ 2 * d by linarith)
  rw [Real.log_mul (by norm_num) (by positivity)] at hh
  linarith

lemma log_nat_add_one_le_degreeRoot {n d : ℕ} (hd : 0 < d) :
    Real.log ((d : ℝ) + 1) ≤ (n + 2 : ℝ) * degreeRoot n d := by
  have hn : (n : ℝ) + 1 + 1 = n + 2 := by ring
  simpa only [degreeRoot, Nat.cast_add, Nat.cast_one, hn] using log_nat_add_one_le_root (r := n + 1) (by omega) hd

/-- The degree root absorbs any fixed weight in a power of `d + 1`. -/
lemma degreeRoot_weight_power_le {n d : ℕ} (hd : 0 < d) {c : ℝ} (hc : 0 ≤ c) :
    ((d : ℝ) + 1) ^ (c / degreeRoot n d) ≤ Real.exp (c * (n + 2 : ℝ)) := by
  rw [Real.rpow_def_of_pos (by positivity), Real.exp_le_exp]
  calc
    _ = c * (Real.log ((d : ℝ) + 1) / degreeRoot n d) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left ((div_le_iff₀ (by positivity)).mpr (log_nat_add_one_le_degreeRoot hd)) hc

/-- Integer coordinates supply the logarithmic positioning condition,
and the chosen height bounds both the original and translated coefficients. -/
theorem exists_hypersurface_coefficient_position {n r d : ℕ} (hr : 0 < r) (hd : 0 < d)
    (f : MvPolynomial (Fin (n + 1)) ℤ) (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) :
    ∃ (a : Fin n → ℤ) (H : ℝ), (∀ j, 0 ≤ a j ∧ a j ≤ d) ∧ 1 ≤ H ∧
      CoefficientHeightLE f H ∧
      CoefficientHeightLE (homogeneousTranslation ℤ a f) H ∧
      Real.log H ≤
        Real.log |((MonomialOrder.lex.leadingCoeff (homogeneousTranslation ℤ a f) : ℤ) : ℝ)| +
          ((5 * (n : ℝ) + 5) * ((r : ℝ) + 1)) * d * (d : ℝ) ^ (1 / (r : ℝ)) := by
  let p := affineChart n f
  have hp : p.totalDegree ≤ d := (affineChart_totalDegree_le f).trans hf.totalDegree_le
  obtain ⟨a, ha, hval, hmax⟩ := exists_integer_multivariate_grid_height_witness p
    (affineChart_ne_zero_of_homogeneous hf hf0) hp
  let g := homogeneousTranslation ℤ a f
  have hg := homogeneousTranslation_homogeneous a hf
  have he : g.coeff (Finsupp.single 0 d) = eval a p := by
    rw [homogeneousTranslation_pure_first a f hf, affineChart_eval]
  have hlead := lex_leadingCoeff_eq_pure_first g hg.totalDegree_le (he ▸ hval)
  rw [he] at hlead
  let L := |(eval a p : ℝ)|
  let D := (d : ℝ) + 1
  let k := n * (d + 1)
  let j := (5 * n + 5) * d
  let H := D ^ j * L
  have hD : 1 ≤ D := le_add_of_nonneg_left (Nat.cast_nonneg d)
  have hL : 1 ≤ L := by
    change 1 ≤ |(eval a p : ℝ)|
    exact_mod_cast Int.one_le_abs hval
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hj : k ≤ j := by dsimp [k, j]; nlinarith [Nat.mul_le_mul_left n hd]
  have htransfer (b : Fin n → ℤ) (hb : ∀ i, 0 ≤ b i ∧ b i ≤ d) :
      CoefficientHeightLE (homogeneousTranslation ℤ b f) H := by
    let F := homogeneousTranslation ℤ b f
    have hF := homogeneousTranslation_homogeneous b hf
    intro m
    by_cases hm : m.degree = d
    · rw [← affineChart_homogeneous_coefficient F hF m hm]
      refine (integer_multivariate_coefficient_bound_of_shifted_grid _
        ((affineChart_totalDegree_le F).trans hF.totalDegree_le) b hb (abs_nonneg _) ?_ _).trans
        (show D ^ k * L ≤ D ^ j * L by gcongr)
      intro v hv
      dsimp only [F]
      rw [affineChart_eval, homogeneousTranslation_eval_chart, ← affineChart_eval,
        show (fun i => (v i : ℤ) - b i) + b = fun i => (v i : ℤ) by funext i; simp]
      exact hmax v hv
    · simp [hF.coeff_eq_zero hm, show 0 ≤ H by positivity]
  refine ⟨a, H, ha, one_le_mul_of_one_le_of_one_le (one_le_pow₀ hD) hL, ?_, htransfer a ha, ?_⟩
  · have hh := htransfer 0 (by simp)
    change CoefficientHeightLE (homogeneousTranslationHom ℤ (0 : Fin n → ℤ) f) H at hh
    simpa using hh
  · rw [hlead, show H = D ^ j * L from rfl, Real.log_mul (by positivity) hL0.ne', Real.log_pow]
    have hlog := mul_le_mul_of_nonneg_left (log_nat_add_one_le_root hr hd)
      (show (0 : ℝ) ≤ j by positivity)
    dsimp only [j, D, L] at hlog ⊢
    push_cast at hlog ⊢
    nlinarith only [hlog]

end
end CCDN
