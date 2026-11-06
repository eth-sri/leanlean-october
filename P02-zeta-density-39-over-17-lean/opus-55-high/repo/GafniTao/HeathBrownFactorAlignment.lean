module
public import GafniTao.HeathBrownFloorRemainder
import WeylPort.Analytic.RealLaplace

public section

/-!
# Alignment with the published Heath-Brown Theorem 1 factor

This file proves both source algebra steps after Lemma 1: the three critical
monomials are exactly `N` times the displayed theorem factor, and the extra
`lambda^(-1/k)` term is dominated by the third critical monomial whenever
that monomial does not already make the trivial bound sufficient.
-/

namespace GafniTao


theorem heathBrownKthDerivativeFactor_eq_critical
    {k : ℕ} (hk : 2 ≤ k) (N lambda : ℝ) :
    heathBrownKthDerivativeFactor k N lambda =
      let r := heathBrownCriticalReciprocal k
      lambda ^ r + N ^ (-r) +
        N ^ (-2 * r) * lambda ^ (-2 * r / (k : ℝ)) := by
  dsimp only
  unfold heathBrownKthDerivativeFactor heathBrownCriticalReciprocal
  pm_2792
  have hk0 : (k : ℝ) ≠ 0 := by linarith
  pm_5931 hkm10 k
  congr 1
  grind
  grind

theorem heathBrownThreeTerm_scaled_identity
    {N k : ℕ} (hN : 1 ≤ N) (hk : 2 ≤ k)
    (lambda epsilon : ℝ) :
    (N : ℝ) ^ epsilon * heathBrownThreeTerm N k lambda =
      (N : ℝ) ^ (1 + epsilon) *
        heathBrownKthDerivativeFactor k N lambda := by
  let r := heathBrownCriticalReciprocal k
  pm_6810 hNpos N
  have hfirst :
      (N : ℝ) ^ epsilon * (N : ℝ) ^ (1 - r) =
        (N : ℝ) ^ (1 + epsilon) * (N : ℝ) ^ (-r) := by
    pm_344 hNpos
    ring
  have hmiddle :
      (N : ℝ) ^ epsilon * ((N : ℝ) * lambda ^ r) =
        (N : ℝ) ^ (1 + epsilon) * lambda ^ r := by
    calc
      (N : ℝ) ^ epsilon * ((N : ℝ) * lambda ^ r) =
          ((N : ℝ) ^ epsilon * (N : ℝ)) * lambda ^ r := by ring
      _ = (N : ℝ) ^ (epsilon + 1) * lambda ^ r := by
        rw [Real.rpow_add_one hNpos.ne']
      _ = (N : ℝ) ^ (1 + epsilon) * lambda ^ r := by grind
  have hlast :
      (N : ℝ) ^ epsilon *
          ((N : ℝ) ^ (1 - 2 * r) *
            lambda ^ (-2 * r / (k : ℝ))) =
        (N : ℝ) ^ (1 + epsilon) *
          ((N : ℝ) ^ (-2 * r) *
            lambda ^ (-2 * r / (k : ℝ))) := by
    have hpow :
        (N : ℝ) ^ epsilon * (N : ℝ) ^ (1 - 2 * r) =
          (N : ℝ) ^ (1 + epsilon) * (N : ℝ) ^ (-2 * r) := by
      pm_344 hNpos
      ring
    grind
  rw [heathBrownKthDerivativeFactor_eq_critical hk N lambda]
  unfold heathBrownThreeTerm
  dsimp only
  rw [mul_add, mul_add, mul_add, mul_add]
  rw [hfirst, hmiddle, hlast]
  ring

theorem heathBrown_lambda_power_identity
    {k : ℕ} (hk : 2 ≤ k) {lambda : ℝ} (hlambda : 0 < lambda) :
    let r := heathBrownCriticalReciprocal k
    (lambda ^ (-(1 / (k : ℝ)))) ^ (2 * r) =
      lambda ^ (-2 * r / (k : ℝ)) := by
  dsimp only
  let r := heathBrownCriticalReciprocal k
  pm_392 hk0 k
  rw [← Real.rpow_mul hlambda.le]
  congr 1
  field_simp

/-- Source final case split: below the trivial range, the extra
`lambda^(-1/k)` term is bounded by the third displayed monomial. -/
theorem heathBrown_lambda_term_le_third_of_third_le_N
    {N k : ℕ} (hN : 1 ≤ N) (hk : 3 ≤ k)
    {lambda : ℝ} (hlambda : 0 < lambda)
    (hthird :
      (N : ℝ) ^ (1 - 2 * heathBrownCriticalReciprocal k) *
          lambda ^ (-2 * heathBrownCriticalReciprocal k / (k : ℝ)) ≤
        N) :
    lambda ^ (-(1 / (k : ℝ))) ≤
      (N : ℝ) ^ (1 - 2 * heathBrownCriticalReciprocal k) *
        lambda ^ (-2 * heathBrownCriticalReciprocal k / (k : ℝ)) := by
  let r := heathBrownCriticalReciprocal k
  pm_2811
  pm_2843
  pm_8549 hq
  pm_2780
  pm_116 hLpos L
  pm_2842
  have hNsplit :
      (N : ℝ) = (N : ℝ) ^ (1 - 2 * r) *
        (N : ℝ) ^ (2 * r) := by
    rw [← Real.rpow_add hNpos]
    pm_2781
  have hpower : L ^ (2 * r) ≤ (N : ℝ) ^ (2 * r) := by
    have hthird' : (N : ℝ) ^ (1 - 2 * r) * L ^ (2 * r) ≤
        (N : ℝ) := by
      rw [hlambdaPower]
      simpa only [r] using hthird
    rw [hNsplit] at hthird'
    have hfactorPos : 0 < (N : ℝ) ^ (1 - 2 * r) :=
      Real.rpow_pos_of_pos hNpos _
    nlinarith
  have hLN : L ≤ (N : ℝ) :=
    (Real.rpow_le_rpow_iff hLpos.le hNpos.le (by positivity : 0 < 2 * r)).mp hpower
  have hbasePower : L ^ (1 - 2 * r) ≤
      (N : ℝ) ^ (1 - 2 * r) :=
    Real.rpow_le_rpow hLpos.le hLN hq
  calc
    lambda ^ (-(1 / (k : ℝ))) = L := rfl
    _ = L ^ (1 - 2 * r) * L ^ (2 * r) := by
      rw [← Real.rpow_add hLpos]
      pm_2781
    _ ≤ (N : ℝ) ^ (1 - 2 * r) * L ^ (2 * r) := by gcongr
    _ = (N : ℝ) ^ (1 - 2 * r) *
        lambda ^ (-2 * r / (k : ℝ)) := by rw [hlambdaPower]
    _ = _ := by rfl



end GafniTao
