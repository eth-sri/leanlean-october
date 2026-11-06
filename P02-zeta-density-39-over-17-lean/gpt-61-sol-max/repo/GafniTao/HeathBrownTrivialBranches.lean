module
import Mathlib
public import GafniTao.HeathBrownBadScale

@[expose] public section

/-!
# Trivial exponential-sum branches in Heath-Brown Theorem 1

Every failure of a technical Lemma 1 hypothesis forces one of the displayed
Theorem 1 monomials to dominate the trivial bound.  This file packages those
comparisons with literal positive constants.
-/

namespace GafniTao



theorem heathBrown_lambda_component_le_factor
    {k : ℕ} (hk : 2 ≤ k) (N : ℝ) {lambda : ℝ}
    (hN : 0 ≤ N) (hlambda : 0 < lambda) :
    lambda ^ heathBrownCriticalReciprocal k ≤
      heathBrownKthDerivativeFactor k N lambda := by
  rw [heathBrownKthDerivativeFactor_eq_critical hk N lambda]
  dsimp only
  have hsecond : 0 ≤ N ^ (-heathBrownCriticalReciprocal k) :=
    Real.rpow_nonneg hN _
  have hthird : 0 ≤ N ^ (-2 * heathBrownCriticalReciprocal k) *
      lambda ^ (-2 * heathBrownCriticalReciprocal k / (k : ℝ)) := by
    exact mul_nonneg (Real.rpow_nonneg hN _)
      (Real.rpow_nonneg hlambda.le _)
  linarith

section
variable {N k : ℕ} (hN : 1 ≤ N) (hk : 3 ≤ k)
include N k hN hk

theorem norm_heathBrownExponentialSum_le_of_lambda_lower
     (f : ℝ → ℝ)
    {lambda epsilon b : ℝ} (hlambda : 0 < lambda) (hepsilon : 0 < epsilon)
    (hb : 0 < b) (hblambda : b ≤ lambda) :
    ‖heathBrownExponentialSum N f‖ ≤
      (b ^ heathBrownCriticalReciprocal k)⁻¹ *
        (N : ℝ) ^ (1 + epsilon) *
          heathBrownKthDerivativeFactor k N lambda := by
  let r := heathBrownCriticalReciprocal k
  have hr0 : 0 ≤ r :=
    (heathBrownCriticalReciprocal_pos (by omega : 2 ≤ k)).le
  have hbpow :=
    Real.rpow_le_rpow hb.le hblambda hr0
  have hbpowPos : 0 < b ^ r := Real.rpow_pos_of_pos hb _
  have hcomponent := heathBrown_lambda_component_le_factor
    (by omega : 2 ≤ k) (N : ℝ) (by positivity) hlambda
  have hNReal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpow : (N : ℝ) ≤ (N : ℝ) ^ (1 + epsilon) := by
    calc
      (N : ℝ) = (N : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ ≤ (N : ℝ) ^ (1 + epsilon) :=
        Real.rpow_le_rpow_of_exponent_le hNReal (by linarith)
  have htarget : (N : ℝ) * b ^ r ≤
      (N : ℝ) ^ (1 + epsilon) *
        heathBrownKthDerivativeFactor k N lambda :=
    mul_le_mul hNpow (hbpow.trans hcomponent) (by positivity) (by positivity)
  have htrivial := norm_heathBrownExponentialSum_le N f
  calc
    ‖heathBrownExponentialSum N f‖ ≤ (N : ℝ) := by exact_mod_cast htrivial
    _ = (b ^ r)⁻¹ * ((N : ℝ) * b ^ r) := by grind
    _ ≤ (b ^ r)⁻¹ *
        ((N : ℝ) ^ (1 + epsilon) *
          heathBrownKthDerivativeFactor k N lambda) := by gcongr
    _ = _ := by ring

theorem norm_heathBrownExponentialSum_le_of_third_lower
     (f : ℝ → ℝ)
    {lambda epsilon c : ℝ} (hlambda : 0 < lambda) (hepsilon : 0 < epsilon)
    (hc : 0 < c) (hthird : c * (N : ℝ) ≤
      heathBrownThirdTerm N k lambda) :
    ‖heathBrownExponentialSum N f‖ ≤
      c⁻¹ * (N : ℝ) ^ (1 + epsilon) *
        heathBrownKthDerivativeFactor k N lambda := by
  have hthirdThree := heathBrownThirdTerm_le_threeTerm (k := k) hN hlambda
  have hNone : (1 : ℝ) ≤ (N : ℝ) ^ epsilon :=
    Real.one_le_rpow (by exact_mod_cast hN) hepsilon.le
  have hthree0 := (heathBrownThreeTerm_pos (k := k) hN hlambda).le
  have hscaled : c * (N : ℝ) ≤
      (N : ℝ) ^ epsilon * heathBrownThreeTerm N k lambda := by nlinarith
  rw [heathBrownThreeTerm_scaled_identity hN (by omega : 2 ≤ k)
    lambda epsilon] at hscaled
  have htrivial := norm_heathBrownExponentialSum_le N f
  calc
    ‖heathBrownExponentialSum N f‖ ≤ (N : ℝ) := by exact_mod_cast htrivial
    _ = c⁻¹ * (c * (N : ℝ)) := by grind
    _ ≤ c⁻¹ *
        ((N : ℝ) ^ (1 + epsilon) *
          heathBrownKthDerivativeFactor k N lambda) := by gcongr
    _ = _ := by ring

theorem one_le_heathBrown_scaled_factor
    
    {lambda epsilon : ℝ} (hlambda : 0 < lambda) (hepsilon : 0 < epsilon) :
    1 ≤ (N : ℝ) ^ (1 + epsilon) *
      heathBrownKthDerivativeFactor k N lambda := by
  let r := heathBrownCriticalReciprocal k
  have hr : 0 < r := heathBrownCriticalReciprocal_pos (by omega : 2 ≤ k)
  have hrHalf : r ≤ 1 / 2 :=
    heathBrownCriticalReciprocal_le_half (by omega : 2 ≤ k)
  have hNReal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  rw [← heathBrownThreeTerm_scaled_identity hN (by omega : 2 ≤ k)
    lambda epsilon]
  by_cases hlambdaOne : lambda ≤ 1
  · have hNq : 1 ≤ (N : ℝ) ^ (1 - 2 * r) :=
      Real.one_le_rpow hNReal (by linarith)
    have hlambdaNeg : 1 ≤ lambda ^ (-2 * r / (k : ℝ)) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hlambda hlambdaOne (by field_simp <;> nlinarith)
    have hthirdOne : 1 ≤ heathBrownThirdTerm N k lambda := by
      unfold heathBrownThirdTerm
      bound
    have hthirdThree := heathBrownThirdTerm_le_threeTerm (k := k) hN hlambda
    have hNpowOne : 1 ≤ (N : ℝ) ^ epsilon :=
      Real.one_le_rpow hNReal hepsilon.le
    have hthree0 := (heathBrownThreeTerm_pos (k := k) hN hlambda).le
    nlinarith
  · have hlambdaLower : 1 ≤ lambda := le_of_not_ge hlambdaOne
    have hlambdaPow : 1 ≤ lambda ^ r :=
      Real.one_le_rpow hlambdaLower hr.le
    have hcomponent : lambda ^ r ≤ heathBrownThreeTerm N k lambda := by
      unfold heathBrownThreeTerm
      dsimp only
      have hNfirst : 1 ≤ (N : ℝ) ^ (1 - r) :=
        Real.one_le_rpow hNReal (by linarith)
      have hmiddle : lambda ^ r ≤ (N : ℝ) * lambda ^ r := by
        nlinarith [Real.rpow_nonneg hlambda.le r]
      have hlast : 0 ≤ (N : ℝ) ^ (1 - 2 * r) *
          lambda ^ (-2 * r / (k : ℝ)) := by positivity
      linarith
    have hNpowOne : 1 ≤ (N : ℝ) ^ epsilon :=
      Real.one_le_rpow hNReal hepsilon.le
    have hthree0 := (heathBrownThreeTerm_pos (k := k) hN hlambda).le
    nlinarith
end


theorem norm_heathBrownExponentialSum_le_small_N_factor
    {N k : ℕ} (hN : 1 ≤ N) (hNsmall : N < 3) (hk : 3 ≤ k)
    (f : ℝ → ℝ) {lambda epsilon : ℝ}
    (hlambda : 0 < lambda) (hepsilon : 0 < epsilon) :
    ‖heathBrownExponentialSum N f‖ ≤
      2 * (N : ℝ) ^ (1 + epsilon) *
        heathBrownKthDerivativeFactor k N lambda := by
  have htrivial := norm_heathBrownExponentialSum_le N f
  have hNtwo : (N : ℝ) ≤ 2 := by exact_mod_cast (show N ≤ 2 by omega)
  have hfactorOne := one_le_heathBrown_scaled_factor hN hk hlambda hepsilon
  calc
    ‖heathBrownExponentialSum N f‖ ≤ (N : ℝ) := by exact_mod_cast htrivial
    _ ≤ 2 := hNtwo
    _ ≤ 2 * ((N : ℝ) ^ (1 + epsilon) *
        heathBrownKthDerivativeFactor k N lambda) := by nlinarith
    _ = _ := by ring





