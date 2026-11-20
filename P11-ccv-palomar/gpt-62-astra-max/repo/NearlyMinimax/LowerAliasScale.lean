module

public import NearlyMinimax.LowerActivityHierarchy
public import NearlyMinimax.CardinalGlobalBandL2

@[expose] public section

/-! Fixed-constant scale reduction for actual active fine interpolation bands.
Only the alias factorial tail receives exp(L*M); the local activity exponent
is unaffected. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000

section
variable (d R : ℕ) (θ c0 K : ℝ)

def cardinalBandDimensionConstant : ℝ :=
  (100 * d)^2 * 16 * spatialScaleIntegralConstant d

theorem cardinalBandDimensionConstant_nonneg :
    0 ≤ cardinalBandDimensionConstant d := by
  unfold cardinalBandDimensionConstant spatialScaleIntegralConstant
  positivity

def lowerAliasSpatialA : ℝ :=
  R^2 * 2^d * (1+cardinalBandDimensionConstant d)^R

def lowerAliasSpatialL : ℝ :=
  c0*K*(d-4) + R

theorem lowerAliasSpatialA_nonneg : 0 ≤ lowerAliasSpatialA d R := by
  unfold lowerAliasSpatialA
  have := cardinalBandDimensionConstant_nonneg d
  positivity

theorem lowerAliasSpatialL_nonneg {d R : ℕ} (hd : 4 ≤ d) {c0 K : ℝ}
    (hc0 : 0 ≤ c0) (_hK : 0 ≤ K) : 0 ≤ lowerAliasSpatialL d R c0 K := by
  unfold lowerAliasSpatialL
  have hdR : (4 : ℝ) ≤ d := by exact_mod_cast hd
  positivity

/-- Exact scalar reduction for any bounded-order band with the source cutoff. -/
theorem cardinalBandSquareBudget_cutoff_le {d r R : ℕ} {M D K c0 N : ℝ}
    (hd : 4 ≤ d) (hr : r ≤ R) (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hK : 0 ≤ K) (hc0 : 0 ≤ c0) (hDK : D ≤ K*M) (hN : 0 < N)
    (hell : 1 ≤ N*Real.exp (-c0*D))
    (hH : Real.log (1+Real.log N) ≤ M) :
    let expScale := Real.exp (-c0*D)
    r^2 * 2^d * cardinalBandSquareBudget d r (N*expScale) ≤
      lowerAliasSpatialA d R * N^(4-(d : ℝ)) * Real.exp (lowerAliasSpatialL d R c0 K * M) := by
  intro expScale
  have hC := cardinalBandDimensionConstant_nonneg d
  have hdR : (4 : ℝ) ≤ d := by exact_mod_cast hd
  have he1 : expScale ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hellN : N*expScale ≤ N := by nlinarith
  have hHp : 0 < 1+Real.log N := by linarith [Real.log_nonneg (hell.trans hellN)]
  have hlog  :=
    add_le_add_right (Real.log_le_log (by positivity) hellN) 1
  have hlog0 : 0 ≤ 1+Real.log (N*expScale) := by linarith [Real.log_nonneg hell]
  have hHexp : 1+Real.log N ≤ Real.exp M := by
    simpa only [Real.exp_log hHp] using Real.exp_le_exp.mpr hH
  have hlogpower : (1+Real.log (N*expScale))^(r-2) ≤ Real.exp (R*M) := by
    calc
      _ ≤ _ := by bound
      _ ≤ _ := pow_le_pow_right₀ (Real.one_le_exp_iff.mpr hM) (by omega)
      _ = _ := (Real.exp_nat_mul M R).symm
  have hCpower : (cardinalBandDimensionConstant d)^(r-1) ≤ (1+cardinalBandDimensionConstant d)^R := (pow_le_pow_left₀ hC (by linarith) (r-1)).trans
      (pow_le_pow_right₀ (by linarith) (by omega))
  have hr2 : r^2 ≤ (R : ℝ)^2 := by exact_mod_cast Nat.pow_le_pow_left hr 2
  have hscale : (N*expScale)^(4-(d : ℝ)) ≤
      N^(4-(d : ℝ)) * Real.exp ((c0*K*(d-4))*M) := by
    rw [Real.mul_rpow hN.le (Real.exp_pos _).le, ← Real.exp_mul]
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hN.le _)
    apply Real.exp_le_exp.mpr
    have hp := mul_le_mul_of_nonneg_left hDK (show 0 ≤ c0*(d-4) by positivity)
    nlinarith
  have hbound := mul_le_mul (mul_le_mul (mul_le_mul hr2 (le_refl (2^d)) (by positivity) (sq_nonneg _))
      hCpower (by positivity) (by positivity))
    (mul_le_mul hscale hlogpower (by positivity) (by positivity)) (by positivity) (by positivity)
  calc
    _ = _ := by
      unfold cardinalBandSquareBudget cardinalBandDimensionConstant
      ring
    _ ≤ _ := hbound
    _ = _ := by
      unfold lowerAliasSpatialA lowerAliasSpatialL cardinalBandDimensionConstant
      rw [show Real.exp ((c0*K*(d-4)+R)*M) =
        Real.exp ((c0*K*(d-4))*M) * Real.exp (R*M) by rw [← Real.exp_add]; congr 1; ring]
      ring

def lowerAliasSpatialFixedL : ℝ :=
  lowerAliasSpatialL d (lowerAliasFineTargetBound d θ c0) c0 ((d+8)/4+1)

end

theorem lowerSaddleD_le_fixed_linear {d m x : ℝ} (hd : 0 < d)
    (hM : 1 ≤ (lowerSaddleM m x : ℝ)) :
    (lowerSaddleD d m x) ≤ ((d+8)/4+1) * lowerSaddleM m x := by
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ (d+8)/4*(lowerSaddleM m x) by positivity)
  change (lowerSaddleD d m x) < (d+8)/4*(lowerSaddleM m x)+1 at hceil
  nlinarith

theorem lowerAliasSpatialFixedL_nonneg {d : ℕ} (hd : 4 ≤ d) (θ : ℝ)
    {c0 : ℝ} (hc0 : 0 ≤ c0) : 0 ≤ lowerAliasSpatialFixedL d θ c0 :=
  lowerAliasSpatialL_nonneg hd hc0 (by positivity)

end NearlyMinimax
