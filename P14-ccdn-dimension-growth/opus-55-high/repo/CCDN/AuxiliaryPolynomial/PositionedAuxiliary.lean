/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.AuxiliaryPolynomial.HypersurfaceLargeHeightDegree
import CCDN.AuxiliaryPolynomial.HypersurfaceNormalizedComparison
import CCDN.AuxiliaryPolynomial.HypersurfaceSmallHeightAuxiliary
import CCDN.AuxiliaryPolynomial.HypersurfaceLargeHeightAuxiliary

/-! Combine the two height ranges under the paper's explicit leading-coefficient
position condition. The main term retains the bad-prime factor of any finite prime
set whose normalized comparison holds. -/

namespace CCDN
noncomputable section
open MvPolynomial

lemma inverse_rpow_le_of_log_position {H L q D : ℝ} (hH : 0 < H) (hL : 0 < L)
    (hq : 0 ≤ q) (hposition : Real.log H ≤ Real.log L + D) :
    1 / L ^ q ≤ Real.exp (q * D) / H ^ q := by
  apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
  rw [Real.log_div one_ne_zero (by positivity), Real.log_div (Real.exp_pos _).ne' (by positivity),
    Real.log_one, Real.log_exp, Real.log_rpow hL, Real.log_rpow hH]
  nlinarith

/-- Replacing the coefficient height `H` by the leading height `L` in the small-height threshold
costs at most a factor `exp (T / (n + 1))`, provided `log H ≤ log L + T d d^(1/(n+1))`. -/
lemma hypersurfaceSmallThreshold_position {n d : ℕ} {B H L A T : ℝ}
    (hd : 0 < d) (hB : 0 ≤ B) (hH : 0 < H) (hL : 0 < L) (hA : 0 ≤ A)
    (hposition : Real.log H ≤ Real.log L + T * d * degreeRoot n d) :
    hypersurfaceSmallThreshold n d B L A ≤
      Real.exp (T / (n + 1 : ℝ)) * hypersurfaceSmallThreshold n d B H A := by
  have hd0 : (0 : ℝ) < d := mod_cast hd
  have hX : (0 : ℝ) < d ^ (1 / (n + 1 : ℝ)) := by positivity
  have hh := inverse_rpow_le_of_log_position hH hL
    (show 0 ≤ 1 / ((n + 1 : ℝ) * d * (d : ℝ) ^ (1 / (n + 1 : ℝ))) by positivity) hposition
  have he : (1 / ((n + 1 : ℝ) * d * d ^ (1 / (n + 1 : ℝ)))) *
      (T * d * (d : ℝ) ^ (1 / (n + 1 : ℝ))) = T / (n + 1 : ℝ) := by field_simp
  rw [he] at hh
  have hm := mul_le_mul_of_nonneg_left hh
    (show 0 ≤
      Real.exp (hypersurfaceSmallHeightError (n + 1) (hypersurfaceBadPrimeNormalizedError n)) *
      (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) * A *
        B ^ ((n + 2 : ℝ) / ((n + 1 : ℝ) * d ^ (1 / (n + 1 : ℝ)))) by positivity)
  simpa [hypersurfaceSmallThreshold, div_eq_mul_inv, one_mul, mul_assoc, mul_left_comm,
    mul_comm] using hm

/-- Explicit constant for the positioned absolutely irreducible case. -/
def hypersurfacePositionedAuxiliaryConstant (n : ℕ) (T : ℝ) : ℝ :=
  4 + 8 * (n + 2 : ℝ) +
    Real.exp (hypersurfaceLargeHeightError (n + 1) (hypersurfaceNormalizedError n) T) +
    Real.exp (T / (n + 1 : ℝ)) *
      Real.exp (hypersurfaceSmallHeightError (n + 1) (hypersurfaceBadPrimeNormalizedError n))

section
variable {n d : ℕ} (hd : 0 < d) {B b H T : ℝ} (hB : 1 ≤ B) (hb : 0 ≤ b) (hH : 0 ≤ H)
include hd hB hb hH

/-- The small-height degree bound fits under the positioned bound. -/
lemma small_height_bound_le_positioned
    :
    2 * d + (d : ℝ) ^ (1 - 1 / (n + 1 : ℝ)) * Real.log B +
        Real.exp (T / (n + 1 : ℝ)) * Real.exp (hypersurfaceSmallHeightError (n + 1)
          (hypersurfaceBadPrimeNormalizedError n)) * auxMainTerm n d B b H + 2 ≤
      hypersurfacePositionedAuxiliaryConstant n T * auxDegreeBound n d B b H := by
  have hd0 : (0 : ℝ) < d := mod_cast hd
  have hd1 : (1 : ℝ) ≤ d := mod_cast hd
  let Q := auxMainTerm n d B b H
  let l := (d : ℝ) ^ (1 - 1 / (n + 1 : ℝ)) * Real.log B
  let D := (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ))
  let C := hypersurfacePositionedAuxiliaryConstant n T
  let Cs := Real.exp (T / (n + 1 : ℝ)) *
    Real.exp (hypersurfaceSmallHeightError (n + 1) (hypersurfaceBadPrimeNormalizedError n))
  have hQ : 0 ≤ Q := by
    dsimp [Q, auxMainTerm]; positivity
  have hl : 0 ≤ l := mul_nonneg (Real.rpow_nonneg hd0.le _) (Real.log_nonneg hB)
  have hD : 0 ≤ D := Real.rpow_nonneg hd0.le _
  have hlarge := Real.exp_pos
    (hypersurfaceLargeHeightError (n + 1) (hypersurfaceNormalizedError n) T)
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hCs : Cs ≤ C := by
    dsimp [Cs, C, hypersurfacePositionedAuxiliaryConstant]
    linarith
  have hC4 : 4 ≤ C := by
    have : 0 < Cs := by positivity
    dsimp [C, hypersurfacePositionedAuxiliaryConstant]
    grind
  have hdD : d ≤ D := le_rpow_four_sub_inv hd
  change 2 * d + l + Cs * Q + 2 ≤ C * (Q + l + D)
  have h1 := mul_le_mul_of_nonneg_right hCs hQ
  have h2 := mul_le_mul_of_nonneg_right (show 1 ≤ C by linarith) hl
  have h3 := mul_le_mul_of_nonneg_right hC4 hD
  nlinarith

/-- The large-height degree bound fits under the positioned bound. -/
lemma large_height_bound_le_positioned
    :
    (8 * (n + 2 : ℝ) + Real.exp (hypersurfaceLargeHeightError (n + 1)
        (hypersurfaceNormalizedError n) T) + 2) * (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) ≤
      hypersurfacePositionedAuxiliaryConstant n T * auxDegreeBound n d B b H := by
  have hd0 : (0 : ℝ) < d := mod_cast hd
  have hD : 0 ≤ (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) := Real.rpow_nonneg hd0.le _
  have hQl : 0 ≤ auxMainTerm n d B b H + (d : ℝ) ^ (1 - 1 / (n + 1 : ℝ)) * Real.log B := by
    have := Real.log_nonneg hB
    unfold auxMainTerm; positivity
  have hS : 0 < Real.exp (T / (n + 1 : ℝ)) *
      Real.exp (hypersurfaceSmallHeightError (n + 1) (hypersurfaceBadPrimeNormalizedError n)) :=
    mul_pos (Real.exp_pos _) (Real.exp_pos _)
  have hlarge := Real.exp_pos
    (hypersurfaceLargeHeightError (n + 1) (hypersurfaceNormalizedError n) T)
  have hCl : 8 * (n + 2 : ℝ) + Real.exp (hypersurfaceLargeHeightError (n + 1)
      (hypersurfaceNormalizedError n) T) + 2 ≤ hypersurfacePositionedAuxiliaryConstant n T := by
    unfold hypersurfacePositionedAuxiliaryConstant
    linarith
  have hC : 0 ≤ hypersurfacePositionedAuxiliaryConstant n T := by grind
  unfold auxDegreeBound
  nlinarith

end

/-- The coefficient-sensitive auxiliary theorem for an absolutely irreducible
homogeneous equation satisfying explicit leading-coefficient positioning, for any
finite prime set `bad` for which the normalized comparison holds. Both height ranges
and the degree are constructed. -/
theorem positioned_auxiliary_degree_of_comparison
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] {n d t : ℕ}
    (order : MonomialOrder (Fin (n + 3))) (f : MvPolynomial (Fin (n + 3)) ℤ)
    (hf : f.IsHomogeneous d) (hd : 0 < d)
    (hir : Irreducible (map (Int.castRingHom K) f))
    (H : ℝ) (hH : 1 ≤ H) (hcoeff : CoefficientHeightLE f H)
    {B : ℝ} {z : Fin t → IntPoint (n + 3)} (hzB : IsPrimitiveBoxZeroFamily f B z)
    (bad : Finset ℕ) (hcomp : AuxiliaryRankComparison order f d z bad)

    (T : ℝ) (hT : 0 ≤ T)
    (hposition : Real.log H ≤ Real.log |((order.leadingCoeff f : ℤ) : ℝ)| +
      T * d * degreeRoot n d) :
    ∃ M : ℕ,
      (M : ℝ) ≤ hypersurfacePositionedAuxiliaryConstant n T *
        auxDegreeBound n d B (primeSetFactor bad) H ∧
      ∃ g, IsPointAuxiliary f g M z := by
  have ⟨⟨hB, _, hbox⟩, _⟩ := hzB
  have hf0 := ne_zero_of_irreducible_map hir
  have hL : 0 < |((order.leadingCoeff f : ℤ) : ℝ)| :=
    abs_pos.mpr (Int.cast_ne_zero.mpr (order.leadingCoeff_ne_zero_iff.mpr hf0))
  have hb : 0 ≤ primeSetFactor bad := (Real.exp_pos _).le
  by_cases hsmall : Real.log H ≤ 2 * d * (n + 2 : ℝ) * Real.log B
  · have hheight := (Real.log_le_log hL (hcoeff (order.degree f))).trans hsmall
    have hp := hypersurfaceSmallThreshold_position hd (by linarith : 0 ≤ B)
      (by grind) hL hb hposition
    have hp' : hypersurfaceSmallThreshold n d B |((order.leadingCoeff f : ℤ) : ℝ)|
        (primeSetFactor bad) ≤ Real.exp (T / (n + 1 : ℝ)) *
          Real.exp (hypersurfaceSmallHeightError (n + 1) (hypersurfaceBadPrimeNormalizedError n)) *
          auxMainTerm n d B (primeSetFactor bad) H := by
      convert hp using 1
      unfold hypersurfaceSmallThreshold auxMainTerm
      ring
    have hdR : (0 : ℝ) < d := mod_cast hd
    let R := hypersurfaceSmallThreshold n d B |((order.leadingCoeff f : ℤ) : ℝ)|
      (primeSetFactor bad)
    have hR : 0 ≤ R := by dsimp [R, hypersurfaceSmallThreshold]; positivity
    let l := (d : ℝ) ^ (1 - 1 / (n + 1 : ℝ)) * Real.log B
    have hl : 0 ≤ l := mul_nonneg (Real.rpow_nonneg hdR.le _) (Real.log_nonneg hB)
    obtain ⟨M, hM, hscale, hthreshold, hbound⟩ := auxiliary_integer_degree_selection (2 * d) hl hR
    refine ⟨M, le_trans ?_ (small_height_bound_le_positioned hd hB hb (by linarith)), ?_⟩
    · grind
    have hscale2 : (d : ℝ) * Real.log B ≤ degreeRoot n d * M := by
      have hX : 0 < (d : ℝ) ^ (1 / (n + 1 : ℝ)) := by positivity
      dsimp [l] at hscale
      rw [Real.rpow_sub hdR, Real.rpow_one] at hscale
      have hh := mul_le_mul_of_nonneg_right hscale hX.le
      have he : (d : ℝ) / (d : ℝ) ^ (1 / (n + 1 : ℝ)) * Real.log B *
          (d : ℝ) ^ (1 / (n + 1 : ℝ)) = d * Real.log B := by field_simp
      rw [he] at hh
      nlinarith
    have hdM : d ≤ M := by omega
    by_contra hnone
    obtain ⟨s, _, hr, hc⟩ := hcomp hB hbox hdM (dvd_of_not_exists_isPointAuxiliary hnone)
    have hL : 1 ≤ |((order.leadingCoeff f : ℤ) : ℝ)| := by
      exact_mod_cast Int.one_le_abs (order.leadingCoeff_ne_zero_iff.mpr hf0)
    have hnR : (n : ℝ) + 1 + 1 = n + 2 := by ring
    have hb := hypersurface_small_height_log_degree_bound (by omega) hd hM hr
      B |((order.leadingCoeff f : ℤ) : ℝ)| (primeSetFactor bad)
      (hypersurfaceBadPrimeNormalizedError n) hB hL (Real.exp_pos _)
      (by grind)
      (by grind)
      (by simpa only [Nat.cast_add, Nat.cast_one, hnR, Real.log_exp] using hc)
    have hb' : (M : ℝ) ≤ hypersurfaceSmallThreshold n d B |((order.leadingCoeff f : ℤ) : ℝ)|
        (primeSetFactor bad) := by
      simpa [hypersurfaceSmallThreshold, Nat.cast_add, Nat.cast_one, hnR] using hb
    exact (not_lt_of_ge hb') hthreshold
  · have hheight := le_of_not_ge hsmall
    have hdR : (0 : ℝ) < d := mod_cast hd
    have hd1 : (1 : ℝ) ≤ d := mod_cast hd
    have hR : 0 ≤ hypersurfaceLargeThreshold n d T := by unfold hypersurfaceLargeThreshold; positivity
    obtain ⟨M, hMlarge, _, hthreshold, hbound⟩ := auxiliary_integer_degree_selection (8 * d * (n + 2))
      (show (0 : ℝ) ≤ 0 from le_rfl) hR
    have hdPow : (d : ℝ) ≤ (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) := le_rpow_four_sub_inv hd
    have hPow1 := hd1.trans hdPow
    refine ⟨M, le_trans ?_ (large_height_bound_le_positioned hd hB hb (by linarith)), ?_⟩
    · unfold hypersurfaceLargeThreshold at hbound
      push_cast at hbound
      have hh := mul_le_mul_of_nonneg_left hdPow (show 0 ≤ 8 * (n + 2 : ℝ) by positivity)
      nlinarith
    have hdM : d ≤ M := by nlinarith
    by_contra hnone
    obtain ⟨s, a, hr, hi, hupper⟩ :=
      homogeneous_no_auxiliary_box_comparison order f hf hf0 hdM z hzB.eval_eq_zero
        hzB.one_le_radius hzB.abs_le (dvd_of_not_exists_isPointAuxiliary hnone)
    have hs := hypersurface_homogeneous_rank_pos hd hdM hr
    let F := fun j => (monomial (homogeneousMonomials (n + 2) M j) 1 : MvPolynomial (Fin (n + 3)) ℤ)
    have hF : ∀ j, (F j).IsHomogeneous M := fun j =>
      isHomogeneous_monomial _ (homogeneousMonomials_degree (n + 2) M j)
    have he : (Matrix.of fun i j => eval ((z ∘ a) i) (F j)) =
        evaluationMatrix (homogeneousMonomials (n + 2) M) (z ∘ a) := by
      ext i j
      simp [F, evaluationMatrix, eval_monomial]
    have hi' : LinearIndependent ℚ
        ((Matrix.of fun i j => eval ((z ∘ a) i) (F j)).map ((↑) : ℤ → ℚ)).row := by
      rwa [he]
    have hlower := hypersurface_determinant_log_lower_height (z := z ∘ a) hs f hf hd hir H hH
      hcoeff ⟨hF, fun i => hzB.primitive (a i), fun i => hzB.eval_eq_zero (a i), hi'⟩
    rw [he] at hlower
    have hnN : n + 1 + 1 = n + 2 := by omega
    have hnR : (n : ℝ) + 1 + 1 = n + 2 := by ring
    have hh := hypersurface_rank_comparison_normalized (by omega) hd hdM hr
      B |((order.leadingCoeff f : ℤ) : ℝ)| (1 + Real.log H / (d : ℝ) ^ 2)
      (hypersurfaceHeightDeterminantError n) (by simpa [factorialRoot, hnN, Nat.cast_add, Nat.cast_one,
        hnR] using (hlower.trans hupper))
    have hL : 1 ≤ |((order.leadingCoeff f : ℤ) : ℝ)| := by
      exact_mod_cast Int.one_le_abs (order.leadingCoeff_ne_zero_iff.mpr hf0)
    have hlog := hypersurface_large_height_log_degree_bound (by omega) hd hMlarge hr
      B |((order.leadingCoeff f : ℤ) : ℝ)| H _ T hB hL hH hT
      (by grind)
      (by grind)
      hh
    have hb := hypersurface_large_degree_bound_of_log_bound hd (hd.trans_le hdM) hlog
    exact (not_lt_of_ge (by
      simpa [hypersurfaceLargeThreshold, hypersurfaceNormalizedError, hnN, hnR, Nat.cast_add, Nat.cast_one] using hb)) hthreshold
