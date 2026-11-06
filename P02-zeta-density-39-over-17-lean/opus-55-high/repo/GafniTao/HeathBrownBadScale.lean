module
public import GafniTao.HeathBrownLemmaOneGoodBranch
import WeylPort.Analytic.RealLaplace

public section

/-!
# Quantitative bounds for the complementary Heath-Brown scale branches

These lemmas translate failures of the technical Taylor-block conditions
into explicit lower bounds for `lambda`.  They are the source case splits,
not additional hypotheses in the eventual derivative theorem.
-/

namespace GafniTao


section
variable {k : ℕ}
include k
theorem heathBrown_source_scale_neg_k (hk : 1 ≤ k) {A lambda : ℝ}
    (hA : 0 < A) (hlambda : 0 < lambda) :
    ((A * lambda) ^ (-(1 / (k : ℝ)))) ^ (-(k : ℝ)) =
      A * lambda := by
  pm_300 hk0 k
  rw [← Real.rpow_mul (mul_pos hA hlambda).le]
  simp_all

theorem heathBrown_lambda_lower_of_H_lt_eight (hk : 3 ≤ k) {A lambda : ℝ}
    (hA : 0 < A) (hlambda : 0 < lambda)
    (hH : heathBrownHChoice k A lambda < 8) :
    (8 : ℝ) ^ (-(k : ℝ)) / A < lambda := by
  pm_2850
  let H := heathBrownHChoice k A lambda
  pm_116 hqpos q
  have hqH : q < (H : ℝ) + 1 := by
    simpa only [q, H] using
      (heathBrownHChoice_rpow_lt_cast_add_one
        (k := k) (A := A) (lambda := lambda))
  have hHSeven : H ≤ 7 := by omega
  have hqEight : q < 8 := by
    have hHSevenReal : (H : ℝ) ≤ 7 := by exact_mod_cast hHSeven
    linarith
  pm_117 hkRealPos k
  have hpow : (8 : ℝ) ^ (-(k : ℝ)) < q ^ (-(k : ℝ)) :=
    Real.rpow_lt_rpow_of_neg hqpos hqEight (neg_neg_of_pos hkRealPos)
  have hscale : q ^ (-(k : ℝ)) = A * lambda := by
    simpa only [q] using
      heathBrown_source_scale_neg_k (by omega : 1 ≤ k) hA hlambda
  rw [hscale] at hpow
  exact (div_lt_iff₀ hA).2 (by grind)

theorem heathBrown_source_scale_separated (hk : 1 ≤ k) {A lambda : ℝ}
    (hA : 0 < A) (hlambda : 0 < lambda) :
    A ^ (1 / (k : ℝ)) *
        (A * lambda) ^ (-(1 / (k : ℝ))) =
      lambda ^ (-(1 / (k : ℝ))) := by
  pm_300 hk0 k
  rw [Real.mul_rpow hA.le hlambda.le]
  calc
    A ^ (1 / (k : ℝ)) *
        (A ^ (-(1 / (k : ℝ))) * lambda ^ (-(1 / (k : ℝ)))) =
        (A ^ (1 / (k : ℝ)) * A ^ (-(1 / (k : ℝ)))) *
          lambda ^ (-(1 / (k : ℝ))) := by ring
    _ = A ^ (1 / (k : ℝ) + -(1 / (k : ℝ))) *
          lambda ^ (-(1 / (k : ℝ))) := by rw [Real.rpow_add hA]
    _ = lambda ^ (-(1 / (k : ℝ))) := by
      rw [show 1 / (k : ℝ) + -(1 / (k : ℝ)) = 0 by ring,
        Real.rpow_zero, one_mul]
end

section
variable {N k : ℕ} (hN : 3 ≤ N) (hk : 3 ≤ k) {A lambda : ℝ} (hA : 0 < A) (hlambda : 0 < lambda) (hHN : N - 2 < heathBrownHChoice k A lambda)
include N k hN hk A lambda hA hlambda hHN
theorem heathBrown_lambda_scale_lower_of_H_gt_N_sub_two :
    A ^ (1 / (k : ℝ)) / 2 * (N : ℝ) ≤
      lambda ^ (-(1 / (k : ℝ))) := by
  let H := heathBrownHChoice k A lambda
  pm_2850
  have hHLower : N - 1 ≤ H := by omega
  have hNHalf : (N : ℝ) / 2 ≤ (H : ℝ) := by
    have hcast : ((N - 1 : ℕ) : ℝ) ≤ H := by exact_mod_cast hHLower
    pm_8256 N
    norm_num at hcast ⊢
    pm_5012 hNReal N hN
    linarith
  have hHq : (H : ℝ) ≤ q := by
    simpa only [H, q] using heathBrownHChoice_cast_le_rpow hA hlambda
  have hqLower : (N : ℝ) / 2 ≤ q := hNHalf.trans hHq
  have hAroot : 0 ≤ A ^ (1 / (k : ℝ)) := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hqLower hAroot
  rw [heathBrown_source_scale_separated
    (by omega : 1 ≤ k) hA hlambda] at hscaled
  calc
    A ^ (1 / (k : ℝ)) / 2 * (N : ℝ) =
        A ^ (1 / (k : ℝ)) * ((N : ℝ) / 2) := by ring
    _ ≤ lambda ^ (-(1 / (k : ℝ))) := hscaled

theorem heathBrown_third_lower_of_H_gt_N_sub_two :
    (A ^ (1 / (k : ℝ)) / 2) ^
        (2 * heathBrownCriticalReciprocal k) * (N : ℝ) ≤
      heathBrownThirdTerm N k lambda := by
  let r := heathBrownCriticalReciprocal k
  let c := A ^ (1 / (k : ℝ)) / 2
  pm_2811
  have hr : 0 < r := heathBrownCriticalReciprocal_pos (by omega : 2 ≤ k)
  have hq : 0 ≤ 1 - 2 * r := by
    linarith [heathBrownCriticalReciprocal_le_half (by omega : 2 ≤ k)]
  pm_2780
  pm_82 hc0 c
  have hL : c * (N : ℝ) ≤ L := by
    simpa only [c, L] using
      heathBrown_lambda_scale_lower_of_H_gt_N_sub_two hN hk hA hlambda hHN
  have hpower : (c * (N : ℝ)) ^ (2 * r) ≤ L ^ (2 * r) :=
    Real.rpow_le_rpow (mul_nonneg hc0 hNpos.le) hL (by positivity)
  pm_2842
  unfold heathBrownThirdTerm
  dsimp only
  change c ^ (2 * r) * (N : ℝ) ≤
    (N : ℝ) ^ (1 - 2 * r) *
      lambda ^ (-2 * r / (k : ℝ))
  calc
    c ^ (2 * r) * (N : ℝ) =
        (N : ℝ) ^ (1 - 2 * r) *
          (c * (N : ℝ)) ^ (2 * r) := by
      rw [Real.mul_rpow hc0 hNpos.le]
      calc
        c ^ (2 * r) * (N : ℝ) =
            c ^ (2 * r) *
              ((N : ℝ) ^ (1 - 2 * r) * (N : ℝ) ^ (2 * r)) := by
          rw [← Real.rpow_add hNpos]
          pm_2781
        _ = (N : ℝ) ^ (1 - 2 * r) *
            (c ^ (2 * r) * (N : ℝ) ^ (2 * r)) := by ring
    _ ≤ (N : ℝ) ^ (1 - 2 * r) * L ^ (2 * r) := by gcongr
    _ = (N : ℝ) ^ (1 - 2 * r) *
        lambda ^ (-2 * r / (k : ℝ)) := by rw [hlambdaPower]
end



end GafniTao
