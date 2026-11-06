/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.AuxiliaryPolynomial.PrimeScaledAffineMinimum
import CCDN.AuxiliaryPolynomial.AffineHeightCutoff
import CCDN.AuxiliaryPolynomial.HypersurfaceHeightTransfer
import CCDN.AuxiliaryPolynomial.UnscaledHypersurfaceAuxiliary
import CCDN.Height.ScaledHypersurfaceHeight

/-! The ordinary homogenization attains the affine box exponent on every
polynomial range in the degree, with both terms of the minimum retained. -/

namespace CCDN
open MvPolynomial

section
variable {n : ℕ}

end

variable {n k : ℕ} (f : MvPolynomial (Fin (n + 2)) ℤ) {S B : ℝ}

/-- An affine auxiliary with the minimum degree bound in the
polynomial box range. The constant coefficient is arbitrary. -/
theorem unscaled_affine_auxiliary_minimum
    (hprim : PrimitiveIntegerPolynomial f)
    (hir : Irreducible f) (hd : 0 < f.totalDegree)
    (hS : 1 ≤ S) (hB : 1 ≤ B)
    (hbound : B ≤ S * ((f.totalDegree : ℝ) + 1) ^ k) :
    ∃ g, IsBoxAuxiliary f g B ∧
      (g.totalDegree : ℝ) ≤ affineMinimumAuxiliaryBound n f.totalDegree
        (Real.exp (Real.log S + (k : ℝ) * (n + 2 : ℝ))) B
        (integerCoefficientHeight (homogeneousComponent f.totalDegree f) : ℝ)
        (hypersurfaceBadPrimeFactor (scaledHomogenize f.totalDegree 1 f)) := by
  obtain ⟨g, hg, hgdeg⟩ : ∃ g, IsBoxAuxiliary f g B ∧
      (g.totalDegree : ℝ) ≤ hypersurfaceAuxiliaryDegreeBound n f.totalDegree B
        (hypersurfaceBadPrimeFactor (scaledHomogenize f.totalDegree 1 f))
        (integerCoefficientHeight f : ℝ) := by
    let F := scaledHomogenize f.totalDegree 1 f
    obtain ⟨M, hM, G, hGhom, hGzero, hGnd⟩ := hypersurface_projective_auxiliary F (scaledHomogenize_homogeneous _ _ le_rfl) hd (by
      apply (hprim.scaledHomogenize_one _).irreducible_of_rational_map
      rw [scaledHomogenize_map]
      have hdeg : (map (Int.castRingHom ℚ) f).totalDegree = f.totalDegree :=
          totalDegree_map_of_injective Int.cast_injective _
      rw [← hdeg]
      exact scaledHomogenize_irreducible _ (rational_map_irreducible_of_integer f hir hd)
        (by simp)) hB
    let g := homogeneousSlice (n + 2) 1 G
    have hgnd : ¬ f ∣ g := unscaled_auxiliary_not_dvd f hir.ne_zero hprim G hGhom hGnd
    refine ⟨g, ⟨fun h => hgnd (by rw [h]; exact dvd_zero _), hgnd,
      unscaled_auxiliary_vanishes f G hGhom hB hGzero⟩, ?_⟩
    have hgM : (g.totalDegree : ℝ) ≤ M := by
      exact_mod_cast homogeneousSlice_degree_le (1 : ℤ) hGhom
    have hh := hgM.trans hM
    simpa [F, integerCoefficientHeight_scaledHomogenize_one,
      hypersurfaceAuxiliaryDegreeBound, auxDegreeBound, auxMainTerm] using hh
  exact ⟨g, hg, hgdeg.trans
    (show hypersurfaceAuxiliaryDegreeBound n f.totalDegree B
            (hypersurfaceBadPrimeFactor (scaledHomogenize f.totalDegree 1 f))
            (integerCoefficientHeight f : ℝ) ≤
          affineMinimumAuxiliaryBound n f.totalDegree
            (Real.exp (Real.log S + (k : ℝ) * (n + 2 : ℝ))) B
            (integerCoefficientHeight (homogeneousComponent f.totalDegree f) : ℝ)
            (hypersurfaceBadPrimeFactor (scaledHomogenize f.totalDegree 1 f)) by
        let d := f.totalDegree
        let b := hypersurfaceBadPrimeFactor (scaledHomogenize d 1 f)
        let H := (integerCoefficientHeight f : ℝ)
        let L := (integerCoefficientHeight (homogeneousComponent d f) : ℝ)
        let K := max (affineHeightTransferConstant n) (Real.exp 1)
        let E := Real.exp (Real.log S + (k : ℝ) * (n + 2 : ℝ))
        let T := min (Real.log L + d * Real.log B + (d : ℝ) ^ 2) ((d : ℝ) ^ 2 * b)
        let α := (n + 2 : ℝ) / ((n + 1 : ℝ) * (d : ℝ) ^ (1 / (n + 1 : ℝ)))
        let β := 1 / (d : ℝ) ^ (1 / (n + 1 : ℝ))
        let q := 1 / ((n + 1 : ℝ) * d * (d : ℝ) ^ (1 / (n + 1 : ℝ)))
        have hcoef : d ^ (4 - 1 / (n + 1 : ℝ)) * b / H ^ q ≤
            K * d ^ (2 - 1 / (n + 1 : ℝ)) * T / L ^ q := by
          let F := scaledHomogenize d 1 f
          let T0 := Real.log L + d * Real.log B + d ^ 2
          have hd0 : (0 : ℝ) < d := by positivity
          have hL := leading_height_one_le f hir.ne_zero
          have hLH : (integerCoefficientHeight (homogeneousComponent f.totalDegree f) : ℝ) ≤
              (integerCoefficientHeight f : ℝ) := by
            simpa [Int.cast_one, one_pow, one_mul,
              integerCoefficientHeight_scaledHomogenize_one] using
                scaledHomogenize_leading_height_lower f le_rfl
          have hL0 : 0 < L := by linarith
          have hH0 : 0 < H := by linarith
          have hb := hypersurfaceBadPrimeFactor_nonneg F
          have hF0 := scaledHomogenize_ne_zero d one_ne_zero hir.ne_zero
          have hFdegree :=
            (scaledHomogenize_homogeneous (1 : ℤ) f le_rfl).totalDegree hF0
          have hKheight : affineHeightTransferConstant n ≤ K := le_max_left _ _
          have hK1 : 1 ≤ K := by aesop
          have hT : 0 ≤ T0 := by bound
          have hlog : d ^ (4 - 1 / (n + 1 : ℝ)) * b / H ^ q ≤
              K * d ^ (2 - 1 / (n + 1 : ℝ)) * T0 / L ^ q := by
            have htransfer := hypersurface_badPrime_height_transfer F hF0 hFdegree hd hL
              (by simp_all [F, integerCoefficientHeight_scaledHomogenize_one])
            have ht : Real.log L + d ^ 2 ≤ T0 := by bound
            have hheight0 : 0 ≤ affineHeightTransferConstant n :=
              mul_nonneg (by positivity) (zero_le_one.trans (hypersurfaceHeightConstant_one_le _))
            calc
              _ ≤ affineHeightTransferConstant n *
                  (d : ℝ) ^ (2 - 1 / (n + 1 : ℝ)) * (Real.log L + (d : ℝ) ^ 2) / L ^ q := by
                simpa [F, b, H, q, affineHeightTransferConstant,
                  integerCoefficientHeight_scaledHomogenize_one] using htransfer
              _ ≤ K * d ^ (2 - 1 / (n + 1 : ℝ)) * T0 / L ^ q := by bound
          have hfactor : d ^ (4 - 1 / (n + 1 : ℝ)) * b / H ^ q ≤
              K * d ^ (2 - 1 / (n + 1 : ℝ)) * (d ^ 2 * b) / L ^ q := by
            have hpow : L ^ q ≤ H ^ q :=
              Real.rpow_le_rpow hL0.le hLH (by positivity)
            have he :=
              rpow_four_sub_eq_mul_sq hd0 n
            calc
              _ ≤ d ^ (4 - 1 / (n + 1 : ℝ)) * b / L ^ q :=
                div_le_div_of_nonneg_left (by positivity) (by positivity) hpow
              _ = d ^ (2 - 1 / (n + 1 : ℝ)) * (d ^ 2 * b) / L ^ q := by grind
              _ ≤ _ := by
                have hh := mul_le_mul_of_nonneg_right hK1
                  (show 0 ≤ (d : ℝ) ^ (2 - 1 / (n + 1 : ℝ)) * ((d : ℝ) ^ 2 * b) / L ^ q by positivity)
                grind
          rcases le_total T0 (d ^ 2 * b) with h | h
          · grind
          · grind
        have hpower : B ^ α ≤ E * B ^ β := by
          have hh := polynomial_box_projective_power_bound (r := n + 1) (by omega) hd hS hB hbound
          grind
        have hcoefficient : 0 ≤ d ^ (4 - 1 / (n + 1 : ℝ)) * b / H ^ q :=
          div_nonneg (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _) (hypersurfaceBadPrimeFactor_nonneg _))
            (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        have hmain : d ^ (4 - 1 / (n + 1 : ℝ)) * b * B ^ α / H ^ q ≤
            K * E * d ^ (2 - 1 / (n + 1 : ℝ)) * T * B ^ β / L ^ q := by
          convert mul_le_mul hcoef hpower (Real.rpow_nonneg (by linarith : 0 ≤ B) α)
            (hcoefficient.trans hcoef) using 1 <;> ring
        exact mul_le_mul_of_nonneg_left (add_le_add (add_le_add hmain le_rfl) le_rfl)
          (hypersurfaceAbsoluteAuxiliaryConstant_pos n).le)⟩

