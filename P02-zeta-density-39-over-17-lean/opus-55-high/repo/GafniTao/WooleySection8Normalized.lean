module
public import GafniTao.WooleyNormalization
import WeylPort.Analytic.RealLaplace

public section

/-!
# Wooley Lemma 8.2, normalized branch `r >= 2`

The first theorem is the direct quotient form of (8.4).  The second rewrites
both quotient powers into the exact bracket notation defined in (3.24).
-/

namespace GafniTao


section
variable {k : ℕ} (phi : WooleyPolynomialSystem k) (p B H r a b bPrime nu : ℕ) [NeZero p] [NeZero (p ^ B)] (Delta D : ℝ) (hr : 2 ≤ r) (hrk : r < k) (hnub : nu ≤ b) (hnuPrime : nu ≤ bPrime) (gamma : WooleySourceSequence) (hscale : 0 < wooleySourceNormalizationScale phi p B H (wooleyTriangular k) Delta gamma) (hD : 0 ≤ D) (hsection7 : wooleySourcePolynomialMixedMean phi (wooleyTriangular k) r p B a b nu gamma ≤ D * wooleySourcePolynomialMixedMean phi (wooleyTriangular k) r p B bPrime b nu gamma)
include k phi p B H r a b bPrime nu Delta D hr hrk hnub hnuPrime gamma hscale hD hsection7
/-- Direct equation-(3.24) normalization of the `r >= 2` branch of Lemma
8.1. -/
theorem wooleySourcePolynomial_equation_8_4_quotient :
    (wooleySourcePolynomialMixedMean
        phi (wooleyTriangular k) r p B a b nu gamma /
      wooleySourceNormalizationScale
        phi p B H (wooleyTriangular k) Delta gamma) ^
        wooleyNormalizationExponent k r ≤
      D ^ wooleyNormalizationExponent k r *
        (wooleySourcePolynomialMixedMean
            phi (wooleyTriangular k) (k - r) p B b bPrime nu gamma /
          wooleySourceNormalizationScale
            phi p B H (wooleyTriangular k) Delta gamma) ^
          ((1 / ((k - r + 1 : ℕ) : ℝ)) *
            wooleyNormalizationExponent k r) *
        (wooleySourcePolynomialMixedMean
            phi (wooleyTriangular k) (r - 1) p B bPrime b nu gamma /
          wooleySourceNormalizationScale
            phi p B H (wooleyTriangular k) Delta gamma) ^
          ((((k - r : ℕ) : ℝ) / ((k - r + 1 : ℕ) : ℝ)) *
            wooleyNormalizationExponent k r) := by
  have hraw := wooleySourcePolynomial_equation_8_1_of_section7_mul
    phi p B r a b bPrime nu hr hrk hnub hnuPrime gamma D hD hsection7
  apply wooley_normalized_two_factor
    (hZ := hscale) (hD := hD)
    (he := (wooleyNormalizationExponent_pos (show 1 ≤ r by omega) hrk).le)
    (huv := ?_) (hmain := hraw)
  · exact wooleySourcePolynomialMixedMean_nonneg
      phi (wooleyTriangular k) r p B a b nu gamma
  · exact wooleySourcePolynomialMixedMean_nonneg
      phi (wooleyTriangular k) (k - r) p B b bPrime nu gamma
  · exact wooleySourcePolynomialMixedMean_nonneg
      phi (wooleyTriangular k) (r - 1) p B bPrime b nu gamma
  grind

/-- Wooley equation (8.4) in the literal bracket normalization (3.24),
with the exact Lemma-7.1 multiplier `D` still visible. -/
theorem wooleySourcePolynomial_equation_8_4 :
    wooleySourceNormalizedMixedMean
        phi p B H (wooleyTriangular k) r a b nu Delta gamma ≤
      D ^ wooleyNormalizationExponent k r *
        (wooleySourceNormalizedMixedMean
          phi p B H (wooleyTriangular k) (k - r) b bPrime nu Delta gamma) ^
            (1 / ((k - r + 1 : ℕ) : ℝ)) *
        (wooleySourceNormalizedMixedMean
          phi p B H (wooleyTriangular k) (r - 1) bPrime b nu Delta gamma) ^
            (1 - 1 / (r : ℝ)) := by
  pm_7207
  let X := wooleySourcePolynomialMixedMean
    phi (wooleyTriangular k) (k - r) p B b bPrime nu gamma
  let Y := wooleySourcePolynomialMixedMean
    phi (wooleyTriangular k) (r - 1) p B bPrime b nu gamma
  pm_2799
  let e : ℝ := wooleyNormalizationExponent k r
  have hq := wooleySourcePolynomial_equation_8_4_quotient
    phi p B H r a b bPrime nu Delta D hr hrk hnub hnuPrime gamma
      hscale hD hsection7
  have hXZ : 0 ≤ X / Z := div_nonneg
    (wooleySourcePolynomialMixedMean_nonneg
      phi (wooleyTriangular k) (k - r) p B b bPrime nu gamma) hscale.le
  have hYZ : 0 ≤ Y / Z := div_nonneg
    (wooleySourcePolynomialMixedMean_nonneg
      phi (wooleyTriangular k) (r - 1) p B bPrime b nu gamma) hscale.le
  have hx :
      (X / Z) ^ (u * e) =
        ((X / Z) ^ wooleyNormalizationExponent k (k - r)) ^ u := by
    calc
      (X / Z) ^ (u * e) =
          (X / Z) ^ (wooleyNormalizationExponent k (k - r) * u) := by
        rw [wooleyNormalizationExponent_symm hrk.le]
        congr 1
        ring
      _ = ((X / Z) ^ wooleyNormalizationExponent k (k - r)) ^ u :=
        Real.rpow_mul hXZ _ _
  have hy :
      (Y / Z) ^ (v * e) =
        ((Y / Z) ^ wooleyNormalizationExponent k (r - 1)) ^
          (1 - 1 / (r : ℝ)) := by
    calc
      (Y / Z) ^ (v * e) =
          (Y / Z) ^
            (wooleyNormalizationExponent k (r - 1) *
              (1 - 1 / (r : ℝ))) := by
        congr 1
        rw [wooley_normalization_pred_exponent hr hrk]
        ring
      _ = ((Y / Z) ^ wooleyNormalizationExponent k (r - 1)) ^
          (1 - 1 / (r : ℝ)) := Real.rpow_mul hYZ _ _
  unfold wooleySourceNormalizedMixedMean
  change _ ≤ D ^ e * ((X / Z) ^
      wooleyNormalizationExponent k (k - r)) ^ u *
    ((Y / Z) ^ wooleyNormalizationExponent k (r - 1)) ^
      (1 - 1 / (r : ℝ))
  change _ ≤ D ^ e * (X / Z) ^ (u * e) * (Y / Z) ^ (v * e) at hq
  simpa only [hx, hy] using hq
end

section
variable {k : ℕ} (phi : WooleyPolynomialSystem k) (p B H a b nu : ℕ) [NeZero p] [NeZero (p ^ B)]
include k phi p B H a b nu
/-- The normalized `r=1` conclusion before the Section-6 estimate for the
conditioned mean is inserted. -/
theorem wooleySourcePolynomial_equation_8_5_pre
    (Delta D : ℝ) (hk : 2 ≤ k)
    (hnub : nu ≤ b) (hnukb : nu ≤ k * b)
    (gamma : WooleySourceSequence)
    (hscale : 0 < wooleySourceNormalizationScale
      phi p B H (wooleyTriangular k) Delta gamma)
    (hD : 0 ≤ D)
    (hsection7 :
      wooleySourcePolynomialMixedMean
          phi (wooleyTriangular k) 1 p B a b nu gamma ≤
        D * wooleySourcePolynomialMixedMean
          phi (wooleyTriangular k) 1 p B (k * b) b nu gamma) :
    wooleySourceNormalizedMixedMean
        phi p B H (wooleyTriangular k) 1 a b nu Delta gamma ≤
      D *
        (wooleySourceNormalizedMixedMean
          phi p B H (wooleyTriangular k) (k - 1) b (k * b) nu Delta gamma) ^
            (1 / (k : ℝ)) *
        (wooleySourcePolynomialConditionedMean
            (wooleyTriangular k) (p ^ B) (p ^ b) phi gamma /
          wooleySourceNormalizationScale
            phi p B H (wooleyTriangular k) Delta gamma) ^
              (1 - 1 / (k : ℝ)) := by
  pm_7207
  let X := wooleySourcePolynomialMixedMean
    phi (wooleyTriangular k) (k - 1) p B b (k * b) nu gamma
  pm_7637 Y b
  let u : ℝ := 1 / (k : ℝ)
  pm_5500 k
  have hraw := wooleySourcePolynomial_equation_8_2_of_section7_mul
    phi p B a b nu hk hnub hnukb gamma D hD hsection7
  have huv : u + v = 1 := by dsimp [u, v]; ring
  have hq := wooley_normalized_two_factor
    (A := wooleySourcePolynomialMixedMean
      phi (wooleyTriangular k) 1 p B a b nu gamma)
    (X := X) (Y := Y) (Z := Z) (D := D) (u := u) (v := v) (e := 1)
    (wooleySourcePolynomialMixedMean_nonneg
      phi (wooleyTriangular k) 1 p B a b nu gamma)
    (wooleySourcePolynomialMixedMean_nonneg
      phi (wooleyTriangular k) (k - 1) p B b (k * b) nu gamma)
    (wooleySourcePolynomialConditionedMean_nonneg
      phi (wooleyTriangular k) (p ^ B) (p ^ b) gamma)
    hscale hD (by norm_num) huv hraw
  have hXZ : 0 ≤ X / Z := div_nonneg
    (wooleySourcePolynomialMixedMean_nonneg
      phi (wooleyTriangular k) (k - 1) p B b (k * b) nu gamma) hscale.le
  unfold wooleySourceNormalizedMixedMean
  rw [wooleyNormalizationExponent_one hk,
    wooleyNormalizationExponent_pred hk]
  change _ ≤ D * ((X / Z) ^ 1) ^ u * (Y / Z) ^ v
  change _ ≤ D ^ (1 : ℝ) * (X / Z) ^ (u * 1) * (Y / Z) ^ (v * 1) at hq
  simpa only [Real.rpow_one, mul_one] using hq

/-- Equation (8.5) with an explicit upper bound for the conditioned-mean
ratio.  The next module derives that ratio from Wooley (6.4), (6.5), and
the hierarchy instead of taking it as an asymptotic convention. -/
theorem wooleySourcePolynomial_equation_8_5_of_ratio
    (Delta D E : ℝ) (hk : 2 ≤ k)
    (hnub : nu ≤ b) (hnukb : nu ≤ k * b)
    (gamma : WooleySourceSequence)
    (hscale : 0 < wooleySourceNormalizationScale
      phi p B H (wooleyTriangular k) Delta gamma)
    (hD : 0 ≤ D)
    (hsection7 :
      wooleySourcePolynomialMixedMean
          phi (wooleyTriangular k) 1 p B a b nu gamma ≤
        D * wooleySourcePolynomialMixedMean
          phi (wooleyTriangular k) 1 p B (k * b) b nu gamma)
    (hratio :
      wooleySourcePolynomialConditionedMean
          (wooleyTriangular k) (p ^ B) (p ^ b) phi gamma /
        wooleySourceNormalizationScale
          phi p B H (wooleyTriangular k) Delta gamma ≤ E) :
    wooleySourceNormalizedMixedMean
        phi p B H (wooleyTriangular k) 1 a b nu Delta gamma ≤
      D *
        (wooleySourceNormalizedMixedMean
          phi p B H (wooleyTriangular k) (k - 1) b (k * b) nu Delta gamma) ^
            (1 / (k : ℝ)) * E ^ (1 - 1 / (k : ℝ)) := by
  have hpre := wooleySourcePolynomial_equation_8_5_pre
    phi p B H a b nu Delta D hk hnub hnukb gamma hscale hD hsection7
  have hv : 0 ≤ 1 - 1 / (k : ℝ) := by
    pm_279 hkR k hk
    pm_117 hkPos k
    rw [sub_nonneg, div_le_iff₀ hkPos]
    linarith
  have hratio0 : 0 ≤
      wooleySourcePolynomialConditionedMean
          (wooleyTriangular k) (p ^ B) (p ^ b) phi gamma /
        wooleySourceNormalizationScale
          phi p B H (wooleyTriangular k) Delta gamma := div_nonneg
    (wooleySourcePolynomialConditionedMean_nonneg
      phi (wooleyTriangular k) (p ^ B) (p ^ b) gamma) hscale.le
  have hp := Real.rpow_le_rpow hratio0 hratio hv
  exact hpre.trans (mul_le_mul_of_nonneg_left hp (mul_nonneg hD
    (Real.rpow_nonneg
      (wooleySourceNormalizedMixedMean_nonneg
        phi p B H (wooleyTriangular k) (k - 1) b (k * b) nu Delta gamma) _)))
end



end GafniTao
