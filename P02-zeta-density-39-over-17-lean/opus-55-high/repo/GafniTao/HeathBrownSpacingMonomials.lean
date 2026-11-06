module
public import GafniTao.HeathBrownLogAbsorption
import WeylPort.Analytic.RealLaplace

@[expose] public section

/-!
# The three spacing monomials in Heath-Brown's Lemma 1

Lemma 2 supplies `N + lambda*N^2 + lambda^(-2/k)`.  At the critical
exponent `r = 1/(k(k-1))`, multiplication by the Weyl-moment factor
`N^(1-2r)` gives exactly the three terms used in the source proof.
-/

namespace GafniTao

noncomputable section

noncomputable def heathBrownSpacingBase
    (N k : ℕ) (lambda : ℝ) : ℝ :=
  (N : ℝ) + lambda * (N : ℝ) ^ 2 +
    lambda ^ (-(2 / (k : ℝ)))

noncomputable def heathBrownThreeTerm
    (N k : ℕ) (lambda : ℝ) : ℝ :=
  let r := heathBrownCriticalReciprocal k
  (N : ℝ) ^ (1 - r) +
    (N : ℝ) * lambda ^ r +
    (N : ℝ) ^ (1 - 2 * r) *
      lambda ^ (-2 * r / (k : ℝ))

theorem heathBrown_three_sum_rpow_le
    {x y z r : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (hr : 0 ≤ r) :
    (x + y + z) ^ r ≤
      (3 : ℝ) ^ r * (x ^ r + y ^ r + z ^ r) := by
  let m := max x (max y z)
  have hxm : x ≤ m := le_max_left _ _
  have hym : y ≤ m := (le_max_left y z).trans (le_max_right x (max y z))
  have hzm : z ≤ m := (le_max_right y z).trans (le_max_right x (max y z))
  have hm0 : 0 ≤ m := hx.trans hxm
  have hsum : x + y + z ≤ 3 * m := by linarith
  have hpow := Real.rpow_le_rpow (by positivity) hsum hr
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) hm0] at hpow
  have hmPower : m ^ r = max (x ^ r) (max (y ^ r) (z ^ r)) := by
    dsimp only [m]
    rw [Real.rpow_max hx (by positivity) hr, Real.rpow_max hy hz hr]
  rw [hmPower] at hpow
  have hmaxSum : max (x ^ r) (max (y ^ r) (z ^ r)) ≤
      x ^ r + y ^ r + z ^ r := by
    pm_1446 hxPower x r hx
    pm_1446 hyPower y r hy
    pm_1446 hzPower z r hz
    apply max_le
    · linarith
    grind
  exact hpow.trans
    (mul_le_mul_of_nonneg_left hmaxSum (by positivity))

theorem heathBrownSpacingBase_rpow_le
    {N k : ℕ} {lambda : ℝ}
    (hlambda : 0 < lambda) {r : ℝ} (hr : 0 ≤ r) :
    (heathBrownSpacingBase N k lambda) ^ r ≤
      (3 : ℝ) ^ r *
        ((N : ℝ) ^ r +
          (lambda * (N : ℝ) ^ 2) ^ r +
          (lambda ^ (-(2 / (k : ℝ)))) ^ r) := by
  unfold heathBrownSpacingBase
  exact heathBrown_three_sum_rpow_le
    (by positivity) (by positivity) (by positivity) hr

section
variable {N k : ℕ} (hN : 1 ≤ N)
include N k hN
theorem heathBrown_spacing_monomial_identity (hk : 2 ≤ k)
    {lambda : ℝ} (hlambda : 0 < lambda) :
    let r := heathBrownCriticalReciprocal k
    (N : ℝ) ^ (1 - 2 * r) *
        ((N : ℝ) ^ r +
          (lambda * (N : ℝ) ^ 2) ^ r +
          (lambda ^ (-(2 / (k : ℝ)))) ^ r) =
      heathBrownThreeTerm N k lambda := by
  dsimp only
  let r := heathBrownCriticalReciprocal k
  pm_2780
  have hlambdaNonneg : 0 ≤ lambda := hlambda.le
  have hNnonneg : (0 : ℝ) ≤ N := hNpos.le
  pm_392 hkr k
  rw [mul_add, mul_add]
  have hfirst :
      (N : ℝ) ^ (1 - 2 * r) * (N : ℝ) ^ r =
        (N : ℝ) ^ (1 - r) := by
    rw [← Real.rpow_add hNpos]
    congr 1
    ring
  have hmiddlePower :
      (lambda * (N : ℝ) ^ 2) ^ r =
        lambda ^ r * (N : ℝ) ^ (2 * r) := by
    rw [Real.mul_rpow hlambdaNonneg (by positivity)]
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hNnonneg]
    norm_num
  have hmiddle :
      (N : ℝ) ^ (1 - 2 * r) *
          (lambda * (N : ℝ) ^ 2) ^ r =
        (N : ℝ) * lambda ^ r := by
    rw [hmiddlePower]
    calc
      (N : ℝ) ^ (1 - 2 * r) *
          (lambda ^ r * (N : ℝ) ^ (2 * r)) =
          lambda ^ r *
            ((N : ℝ) ^ (1 - 2 * r) * (N : ℝ) ^ (2 * r)) := by ring
      _ = lambda ^ r * (N : ℝ) ^ (1 - 2 * r + 2 * r) := by
        rw [Real.rpow_add hNpos]
      _ = (N : ℝ) * lambda ^ r := by
        pm_2781
        ring
  have hlastPower :
      (lambda ^ (-(2 / (k : ℝ)))) ^ r =
        lambda ^ (-2 * r / (k : ℝ)) := by
    rw [← Real.rpow_mul hlambdaNonneg]
    congr 1
    field_simp
  have hlast :
      (N : ℝ) ^ (1 - 2 * r) *
          (lambda ^ (-(2 / (k : ℝ)))) ^ r =
        (N : ℝ) ^ (1 - 2 * r) *
          lambda ^ (-2 * r / (k : ℝ)) := by
    rw [hlastPower]
  unfold heathBrownThreeTerm
  dsimp only
  grind

theorem heathBrownThreeTerm_pos
    {lambda : ℝ} (hlambda : 0 < lambda) :
    0 < heathBrownThreeTerm N k lambda := by
  unfold heathBrownThreeTerm
  positivity
end


end

end GafniTao
