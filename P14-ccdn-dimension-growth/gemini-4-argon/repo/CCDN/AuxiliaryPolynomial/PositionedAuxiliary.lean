/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.AuxiliaryPolynomial.HypersurfaceLargeHeightDegree
public import CCDN.AuxiliaryPolynomial.HypersurfaceNormalizedComparison
public import CCDN.AuxiliaryPolynomial.HypersurfaceSmallHeightAuxiliary
import CCDN.AuxiliaryPolynomial.HypersurfaceLargeHeightAuxiliary

/-! Combine the two height ranges under the paper's explicit leading-coefficient
position condition. The main term retains the bad-prime factor of any finite prime
set whose normalized comparison holds. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Explicit constant for the positioned absolutely irreducible case. -/
def hypersurfacePositionedAuxiliaryConstant (n : ℕ) (T : ℝ) : ℝ :=
  4 + 8 * (n + 2 : ℝ) +
    Real.exp (hypersurfaceLargeHeightError (n + 1) (hypersurfaceNormalizedError n) T) +
    Real.exp (T / (n + 1 : ℝ)) *
      Real.exp (hypersurfaceSmallHeightError (n + 1) (hypersurfaceBadPrimeNormalizedError n))

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
  obtain ⟨⟨hB, hz, hbox⟩, hprim⟩ := hzB
  have hf0 := ne_zero_of_irreducible_map hir
  let L := |((order.leadingCoeff f : ℤ) : ℝ)|
  let b := primeSetFactor bad
  have hL : 0 < L := abs_pos.mpr (Int.cast_ne_zero.mpr (order.leadingCoeff_ne_zero_iff.mpr hf0))
  have hb : 0 ≤ b := (Real.exp_pos _).le
  have hd0 : (0 : ℝ) < d := mod_cast hd
  have hB0 : 0 ≤ B := by linarith
  have hH0 : 0 < H := by linarith
  let Q := auxMainTerm n d B b H
  let l := (d : ℝ) ^ (1 - 1 / (n + 1 : ℝ)) * Real.log B
  let D := (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ))
  let C := hypersurfacePositionedAuxiliaryConstant n T
  let Cs := Real.exp (T / (n + 1 : ℝ)) *
    Real.exp (hypersurfaceSmallHeightError (n + 1) (hypersurfaceBadPrimeNormalizedError n))
  have hQ : 0 ≤ Q := by dsimp [Q, auxMainTerm]; positivity
  have hl : 0 ≤ l := mul_nonneg (Real.rpow_nonneg hd0.le _) (Real.log_nonneg hB)
  have hD : 0 ≤ D := Real.rpow_nonneg hd0.le _
  have hlarge := Real.exp_pos (hypersurfaceLargeHeightError (n + 1) (hypersurfaceNormalizedError n) T)
  have hS : 0 < Cs := mul_pos (Real.exp_pos _) (Real.exp_pos _)
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  by_cases hsmall : Real.log H ≤ 2 * d * (n + 2 : ℝ) * Real.log B
  · obtain ⟨M, hbound, hg⟩ := auxiliary_small_height_degree_of_comparison order f hf0 hd z hB
      hbox bad hcomp ((Real.log_le_log hL (hcoeff (order.degree f))).trans hsmall)
    let q := 1 / ((n + 1 : ℝ) * d * (d : ℝ) ^ (1 / (n + 1 : ℝ)))
    have hq : 0 ≤ q := by dsimp [q]; positivity
    have hinv : 1 / L ^ q ≤ Real.exp (T / (n + 1 : ℝ)) / H ^ q := by
      have hX : (0 : ℝ) < (d : ℝ) ^ (1 / (n + 1 : ℝ)) := by positivity
      rw [show T / (n + 1 : ℝ) = q * (T * d * degreeRoot n d) by
        dsimp [q, degreeRoot]; field_simp]
      apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
      rw [Real.log_div one_ne_zero (by positivity), Real.log_div (Real.exp_pos _).ne' (by positivity),
        Real.log_one, Real.log_exp, Real.log_rpow hL, Real.log_rpow hH0]
      nlinarith [mul_le_mul_of_nonneg_left hposition hq]
    have hp := mul_le_mul_of_nonneg_left hinv
      (show 0 ≤ Real.exp (hypersurfaceSmallHeightError (n + 1) (hypersurfaceBadPrimeNormalizedError n)) *
        D * b * B ^ ((n + 2 : ℝ) / ((n + 1 : ℝ) * (d : ℝ) ^ (1 / (n + 1 : ℝ)))) by positivity)
    have hp' : hypersurfaceSmallThreshold n d B L b ≤ Cs * Q := by
      unfold hypersurfaceSmallThreshold
      convert hp using 1 <;> (dsimp only [Q, auxMainTerm, Cs, D, q, boxExponent, heightExponent]; ring)
    have hCs : Cs ≤ C := by dsimp only [Cs, C, hypersurfacePositionedAuxiliaryConstant]; linarith
    have hC4 : 4 ≤ C := by dsimp only [C, hypersurfacePositionedAuxiliaryConstant]; linarith
    have hdD : (d : ℝ) ≤ D := le_rpow_four_sub_inv hd
    have hd1 : (1 : ℝ) ≤ d := mod_cast hd
    refine ⟨M, ?_, hg⟩
    change (M : ℝ) ≤ 2 * d + l + hypersurfaceSmallThreshold n d B L b + 2 at hbound
    change (M : ℝ) ≤ C * (Q + l + D)
    nlinarith [mul_le_mul_of_nonneg_right hCs hQ,
      mul_le_mul_of_nonneg_right (show 1 ≤ C by linarith) hl,
      mul_le_mul_of_nonneg_right hC4 hD]
  · obtain ⟨M, hbound, g, hg⟩ := hypersurface_auxiliary_large_height_degree order f hf hd hir H hH
      hcoeff z hprim hz hB hbox T hT (le_of_not_ge hsmall) hposition
    have hCl : 8 * (n + 2 : ℝ) + Real.exp (hypersurfaceLargeHeightError (n + 1)
        (hypersurfaceNormalizedError n) T) + 2 ≤ C := by
      dsimp only [C, hypersurfacePositionedAuxiliaryConstant]; linarith
    have hC0 : 0 ≤ C := by dsimp only [C, hypersurfacePositionedAuxiliaryConstant]; linarith
    refine ⟨M, hbound.trans ?_, g, isPointAuxiliary_iff.mpr hg⟩
    change _ * D ≤ C * (Q + l + D)
    nlinarith [mul_le_mul_of_nonneg_right hCl hD, mul_nonneg hC0 (add_nonneg hQ hl)]

end
end CCDN
