/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.AuxiliaryPolynomial.PrimeScaledAffineHeight
import CCDN.AuxiliaryPolynomial.ScalingPrime
import CCDN.AuxiliaryPolynomial.HypersurfaceHeightTransfer
import CCDN.AuxiliaryPolynomial.PrimeScaledAffineAuxiliary
import CCDN.AuxiliaryPolynomial.ScaledHypersurfaceBadPrimes
import CCDN.Height.ScaledHypersurfaceHeight

/-! Both bounds for the bad-prime factor apply to the same homogeneous
auxiliary. Their minimum therefore survives the affine exponent saving. -/

namespace CCDN
noncomputable section
open MvPolynomial

/-- The affine auxiliary degree bound in which the coefficient-sensitive main term involves the
minimum of `log L + d log B + d²` and `d² b`, where `L` is the height of the leading form and
`b` a bad-prime factor, with box exponent `1 / d^(1/(n+1))` up to the factor `A`. -/
def affineMinimumAuxiliaryBound (n d : ℕ) (A B L b : ℝ) : ℝ :=
  hypersurfaceAbsoluteAuxiliaryConstant n *
    (max (affineHeightTransferConstant n) (Real.exp 1) * A *
        (d : ℝ) ^ (2 - 1 / (n + 1 : ℝ)) *
        min (Real.log L + d * Real.log B + (d : ℝ) ^ 2) ((d : ℝ) ^ 2 * b) *
        B ^ (1 / (d : ℝ) ^ (1 / (n + 1 : ℝ))) /
          L ^ (1 / ((n + 1 : ℝ) * d * (d : ℝ) ^ (1 / (n + 1 : ℝ)))) +
      (d : ℝ) ^ (1 - 1 / (n + 1 : ℝ)) * Real.log B +
        (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)))

section
variable {n : ℕ} (f : MvPolynomial (Fin (n + 2)) ℤ) (hf : f ≠ 0) (hd : 0 < f.totalDegree) {p : ℕ} (hp : p.Prime) {A B : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B)
include hf hd hp hA hB

/-- The auxiliary degree bound of the `p`-scaled homogenization is at most
`affineMinimumAuxiliaryBound`, the minimum of the two coefficient estimates, so the auxiliary
polynomial satisfies the better of the two without changing its zero set. -/
theorem scaled_hypersurface_auxiliary_minimum_bound
    (hpB : (p : ℝ) ≤ B) (hBp : B / A ≤ p) :
    hypersurfaceAuxiliaryDegreeBound n f.totalDegree B
        (hypersurfaceBadPrimeFactor (scaledHomogenize f.totalDegree (p : ℤ) f))
        (integerCoefficientHeight (scaledHomogenize f.totalDegree (p : ℤ) f) : ℝ) ≤
      affineMinimumAuxiliaryBound n f.totalDegree A B
        (integerCoefficientHeight (homogeneousComponent f.totalDegree f) : ℝ)
        (hypersurfaceBadPrimeFactor (scaledHomogenize f.totalDegree 1 f)) := by
  let d := f.totalDegree
  let L := (integerCoefficientHeight (homogeneousComponent d f) : ℝ)
  let b := hypersurfaceBadPrimeFactor (scaledHomogenize d 1 f)
  let T := Real.log L + d * Real.log B + d ^ 2
  let K := max (affineHeightTransferConstant n) (Real.exp 1)
  have hL := leading_height_one_le f hf
  have hT : 0 ≤ T := add_nonneg
    (add_nonneg (Real.log_nonneg hL) (mul_nonneg (Nat.cast_nonneg d) (Real.log_nonneg hB)))
    (sq_nonneg _)
  have hb : 0 ≤ b := hypersurfaceBadPrimeFactor_nonneg _
  have hA0 := zero_le_one.trans hA
  by_cases hmin : T ≤ d ^ 2 * b
  · apply (scaled_hypersurface_auxiliary_bound f hf hd
      (mod_cast hp.one_lt.le : (1 : ℤ) ≤ p) hA hB
      (by simp_all)
      (by simp_all)).trans
    unfold affineLogarithmicAuxiliaryBound affineMinimumAuxiliaryBound
    rw [min_eq_left hmin]
    apply mul_le_mul_of_nonneg_left _ (hypersurfaceAbsoluteAuxiliaryConstant_pos n).le
    bound
  · unfold hypersurfaceAuxiliaryDegreeBound affineMinimumAuxiliaryBound
    rw [min_eq_right (le_of_not_ge hmin)]
    apply mul_le_mul_of_nonneg_left _ (hypersurfaceAbsoluteAuxiliaryConstant_pos n).le
    let c := hypersurfaceBadPrimeFactor (scaledHomogenize d (p : ℤ) f)
    have hFbad : 0 ≤ c := hypersurfaceBadPrimeFactor_nonneg _
    have hbad := hypersurfaceBadPrimeFactor_scaledHomogenize_le f hf hp
    let F := scaledHomogenize d (p : ℤ) f
    let H := (integerCoefficientHeight F : ℝ)
    let Y := p ^ d * L
    let α := (n + 2 : ℝ) / ((n + 1 : ℝ) * d ^ (1 / (n + 1 : ℝ)))
    let β := 1 / ((n + 1 : ℝ) * d ^ (1 / (n + 1 : ℝ)))
    let q := 1 / ((n + 1 : ℝ) * d * d ^ (1 / (n + 1 : ℝ)))
    have hd0 : (0 : ℝ) < d := by positivity
    have hpZ : (1 : ℤ) ≤ p := mod_cast hp.one_lt.le
    have hp0 : (0 : ℝ) < p := mod_cast hp.pos
    have hL0 : 0 < L := by linarith
    have hY0 : 0 < Y := mul_pos (pow_pos hp0 _) hL0
    have hYH : Y ≤ H := by
      simpa using scaledHomogenize_leading_height_lower f hpZ
    have hH0 := hY0.trans_le hYH
    have hq : 0 ≤ q := by positivity
    have hYpow : Y ^ q = p ^ β * L ^ q := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        scaled_height_rpow (r := n + 1) (by omega) hd hp0 hL0
    have hdenom := Real.rpow_le_rpow hY0.le hYH hq
    have hnR : (n : ℝ) + 1 + 1 = n + 2 := by ring
    have hpower : B ^ α / (p : ℝ) ^ β ≤ A * B ^ (1 / (d : ℝ) ^ (1 / (n + 1 : ℝ))) := by
      simpa only [Nat.cast_add, Nat.cast_one, hnR] using
        affine_scaling_box_power (r := n + 1) (by omega) hd hB hA hp0 hBp
    have hpowers :=
      rpow_four_sub_eq_mul_sq hd0 n
    have hmain : (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) * c * B ^ α / H ^ q ≤
        Real.exp 1 * A * (d : ℝ) ^ (2 - 1 / (n + 1 : ℝ)) * ((d : ℝ) ^ 2 * b) *
          B ^ (1 / (d : ℝ) ^ (1 / (n + 1 : ℝ))) / L ^ q := by
      calc
        _ ≤ d ^ (4 - 1 / (n + 1 : ℝ)) * c * B ^ α / Y ^ q :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hdenom
        _ ≤ d ^ (4 - 1 / (n + 1 : ℝ)) * (Real.exp 1 * b) * B ^ α / Y ^ q := by bound
        _ = (Real.exp 1 * d ^ (4 - 1 / (n + 1 : ℝ)) * b / L ^ q) *
            (B ^ α / (p : ℝ) ^ β) := by grind
        _ ≤ (Real.exp 1 * d ^ (4 - 1 / (n + 1 : ℝ)) * b / L ^ q) *
            (A * B ^ (1 / (d : ℝ) ^ (1 / (n + 1 : ℝ)))) :=
          mul_le_mul_of_nonneg_left hpower (by positivity)
        _ = _ := by grind
    refine add_le_add (add_le_add (hmain.trans ?_) le_rfl) le_rfl
    bound

end

variable {n : ℕ} (f : MvPolynomial (Fin (n + 2)) ℤ) (hprim : PrimitiveIntegerPolynomial f) (hir : Irreducible f) (hd : 0 < f.totalDegree)
include hprim hir hd

theorem prime_scaled_affine_auxiliary_minimum
    {p : ℕ} (hp : p.Prime) (hp0 : ¬ (p : ℤ) ∣ f.coeff 0)
    {A B : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hpB : (p : ℝ) ≤ B) (hBp : B / A ≤ p) :
    ∃ g, IsBoxAuxiliary f g B ∧
      (g.totalDegree : ℝ) ≤ affineMinimumAuxiliaryBound n f.totalDegree A B
        (integerCoefficientHeight (homogeneousComponent f.totalDegree f) : ℝ)
        (hypersurfaceBadPrimeFactor (scaledHomogenize f.totalDegree 1 f)) := by
  obtain ⟨g, hg, hgdegree⟩ : ∃ g, IsBoxAuxiliary f g B ∧
      (g.totalDegree : ℝ) ≤ hypersurfaceAuxiliaryDegreeBound n f.totalDegree B
        (hypersurfaceBadPrimeFactor (scaledHomogenize f.totalDegree (p : ℤ) f))
        (integerCoefficientHeight (scaledHomogenize f.totalDegree (p : ℤ) f) : ℝ) := by
    let F := scaledHomogenize f.totalDegree (p : ℤ) f
    have hFhom : F.IsHomogeneous f.totalDegree := scaledHomogenize_homogeneous _ _ le_rfl
    obtain ⟨M, hM, G, hGhom, hGzero, hGnd⟩ := hypersurface_projective_auxiliary F hFhom hd (by
      apply (hprim.scaledHomogenize f.totalDegree hp hp0).irreducible_of_rational_map
      rw [scaledHomogenize_map]
      have hdeg : (map (Int.castRingHom ℚ) f).totalDegree = f.totalDegree :=
          totalDegree_map_of_injective Int.cast_injective _
      rw [← hdeg]
      exact scaledHomogenize_irreducible _ (rational_map_irreducible_of_integer f hir hd)
        (by simpa using
          (show (p : ℚ) ≠ 0 by exact_mod_cast hp.ne_zero))) hB
    let g := homogeneousSlice (n + 2) (p : ℤ) G
    have hgndQ := scaled_auxiliary_rational_not_dvd f hir.ne_zero hprim hp hp0 G hGhom hGnd
    have hgnd : ¬ f ∣ g := fun h => hgndQ (map_dvd (map (Int.castRingHom ℚ)) h)
    refine ⟨g, ⟨(fun h => hgnd (by simp_all)), hgnd, ?_⟩, ?_⟩
    swap
    · have hgM : (g.totalDegree : ℝ) ≤ M := mod_cast homogeneousSlice_degree_le (p : ℤ) hGhom
      grind
    · intro x hx hxf
      let v : IntPoint (n + 3) := Fin.cons p x
      have hv0 : v ≠ 0 := by
        intro hz
        have hh := congrFun hz 0
        have hpZ : (p : ℤ) ≠ 0 := mod_cast hp.ne_zero
        exact hpZ hh
      let P := Projectivization.mk ℚ (rationalPoint v) (rationalPoint_ne_zero hv0)
      have hvbox (j : Fin (n + 3)) : |(v j : ℝ)| ≤ B := by
        refine Fin.cases ?_ (fun k => hx k) j
        simpa [v, Fin.cons_zero, Int.cast_natCast,
          abs_of_nonneg (Nat.cast_nonneg (α := ℝ) p)] using hpB
      have hPB := projective_integer_height_le v hv0 hvbox
      have hvF : eval v F = 0 := by
        rw [scaledHomogenize_eval _ _ le_rfl, hxf, mul_zero]
      have hPF : P ∈ projectiveZeroLocus (map (Int.castRingHom ℚ) F) := by
        apply (mem_projectiveZeroLocus_mk (hFhom.map _) _ _).mpr
        have hh := congrArg (Int.castRingHom ℚ) hvF
        rwa [map_eval, map_zero] at hh
      have hPG := hGzero P hPB hPF
      have hcast := (mem_projectiveZeroLocus_mk (hGhom.map _) _ _).mp hPG
      have hvG : eval v G = 0 := by
        apply Int.cast_injective (α := ℚ)
        have he := map_eval (Int.castRingHom ℚ) v G
        change (Int.castRingHom ℚ) (eval v G) = (Int.castRingHom ℚ) 0
        rwa [he, map_zero]
      rwa [homogeneousSlice_eval]
  exact ⟨g, hg, hgdegree.trans
    (scaled_hypersurface_auxiliary_minimum_bound f hir.ne_zero hd hp hA hB hpB hBp)⟩

/-- If the constant coefficient `c` of a primitive irreducible integer polynomial `f` is nonzero
and `log |c| < B / scalingPrimeRatio`, with `B ≥ scalingPrimeRatio`, then `f` has a box
auxiliary polynomial of degree at most `affineMinimumAuxiliaryBound`, with ratio
`scalingPrimeRatio` and the bad-prime factor of the homogenization of `f`. -/
theorem affine_auxiliary_minimum_of_small_constant_coefficient
    (hc : f.coeff 0 ≠ 0)
    {B : ℝ} (hB : scalingPrimeRatio ≤ B)
    (hheight : Real.log |(f.coeff 0 : ℝ)| < B / scalingPrimeRatio) :
    ∃ g, IsBoxAuxiliary f g B ∧
      (g.totalDegree : ℝ) ≤ affineMinimumAuxiliaryBound n f.totalDegree scalingPrimeRatio B
        (integerCoefficientHeight (homogeneousComponent f.totalDegree f) : ℝ)
        (hypersurfaceBadPrimeFactor (scaledHomogenize f.totalDegree 1 f)) := by
  obtain ⟨p, hp, hlo, hhi, hnd⟩ := exists_scaling_prime hB hc hheight
  exact prime_scaled_affine_auxiliary_minimum f hprim hir hd hp hnd
    scalingPrimeRatio_one_le (scalingPrimeRatio_one_le.trans hB) hhi hlo.le

