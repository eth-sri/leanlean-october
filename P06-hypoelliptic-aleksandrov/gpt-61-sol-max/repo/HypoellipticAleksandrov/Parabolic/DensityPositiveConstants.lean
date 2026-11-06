module

public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Grind



/-!
# Scalar constants for positive parabolic density descent

This module records the explicit real parameters used in the finite density
descent of Krylov--Safonov Lemma 3.3.  It is deliberately independent of the
parabolic geometry, measure argument, and analytic density-to-point result.
-/

@[expose] public section

namespace HypoellipticAleksandrov.Parabolic

noncomputable section

/-- The explicit slack in the positive-density descent. -/
def positiveDensityEta (a : ℝ) : ℝ :=
  min (1 / 2) ((a ^ (-(1 / 2 : ℝ)) - 1) / 2)

/-- The terminal contraction parameter in Lemma 3.3. -/
def positiveDensityZeta (d : ℕ) (a : ℝ) : ℝ :=
  a ^ (1 / (2 * ((d : ℝ) + 2)))

/-- The normalized aggregate coefficient controlling one density step. -/
def positiveDensityDescentRatio (a eta : ℝ) : ℝ :=
  (1 + eta) * Real.sqrt a

/-- A canonical point strictly between an admissible ratio and one. -/
def positiveDensityQ (L : ℝ) : ℝ :=
  (1 + L) / 2

/-- The finite density sequence for the explicit descent. -/
def positiveDensityBeta (q a : ℝ) (n : ℕ) : ℝ :=
  q ^ n * a ^ 2

private theorem rpow_neg_half_eq_sqrt_inv {a : ℝ} (ha0 : 0 < a) :
    a ^ (-(1 / 2 : ℝ)) = (Real.sqrt a)⁻¹ := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg ha0.le]

private theorem zeta_exponent_mul_dim_add_two (d : ℕ) :
    (1 / (2 * ((d : ℝ) + 2))) * ((d + 2 : ℕ) : ℝ) = 1 / 2 := by
  grind

section
variable {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)

include ha0 ha1
/-- The chosen slack is positive whenever the initial density lies in `(0, 1)`. -/
theorem positiveDensityEta_pos  : 0 < positiveDensityEta a := by
  rw [positiveDensityEta]
  apply lt_min
  · norm_num
  · have hpow : 1 < a ^ (-(1 / 2 : ℝ)) :=
      Real.one_lt_rpow_of_pos_of_lt_one_of_neg ha0 ha1 (by norm_num)
    linarith

/-- The chosen slack is strictly less than one. -/
theorem positiveDensityEta_lt_one  : positiveDensityEta a < 1 := by
  have heta0  := positiveDensityEta_pos ha0 ha1
  have hetaHalf : positiveDensityEta a ≤ 1 / 2 := by
    rw [positiveDensityEta]
    exact min_le_left _ _
  calc
    positiveDensityEta a < positiveDensityEta a + positiveDensityEta a := by
      linarith
    _ ≤ 1 := by linarith

/-- The explicit slack makes the source descent ratio strictly subunit. -/
theorem one_add_positiveDensityEta_mul_sqrt_lt_one  :
    (1 + positiveDensityEta a) * Real.sqrt a < 1 := by
  let sharedTerm_83323e403a := ((((Real.sqrt a)⁻¹ - 1) / 2))
  have hs0  := Real.sqrt_pos.2 ha0
  have hs1 : Real.sqrt a < 1 := by
    nlinarith [Real.sq_sqrt ha0.le]
  have heta : positiveDensityEta a ≤ (Real.sqrt a)⁻¹ / 2 - 1 / 2 := by
    rw [positiveDensityEta, rpow_neg_half_eq_sqrt_inv ha0]
    calc
      min (1 / 2 : ℝ) sharedTerm_83323e403a ≤
          sharedTerm_83323e403a := min_le_right _ _
      _ = (Real.sqrt a)⁻¹ / 2 - 1 / 2 := by ring
  calc
    (1 + positiveDensityEta a) * Real.sqrt a ≤
        (1 + ((Real.sqrt a)⁻¹ / 2 - 1 / 2)) * Real.sqrt a :=
      mul_le_mul_of_nonneg_right (by linarith) hs0.le
    _ = (1 + Real.sqrt a) / 2 := by
      field_simp [hs0.ne']
      ring
    _ < 1 := by linarith
end


variable (d : ℕ)

section
variable {a : ℝ} (ha0 : 0 < a)

include ha0
/-- The terminal contraction parameter is positive in every dimension. -/
theorem positiveDensityZeta_pos   : 0 < positiveDensityZeta d a := by
  rw [positiveDensityZeta]
  exact Real.rpow_pos_of_pos ha0 _

/-- The terminal contraction parameter is strictly subunit when `a < 1`. -/
theorem positiveDensityZeta_lt_one   (ha1 : a < 1) : positiveDensityZeta d a < 1 := by
  rw [positiveDensityZeta]
  apply Real.rpow_lt_one ha0.le ha1
  positivity

/-- The natural power of the terminal contraction is exactly `sqrt a`. -/
theorem positiveDensityZeta_pow_dim_add_two   :
    positiveDensityZeta d a ^ (d + 2) = Real.sqrt a := by
  let sharedTerm_a4a94df6cb := ((1 / (2 * ((d : ℝ) + 2))))
  rw [positiveDensityZeta]
  calc
    (a ^ sharedTerm_a4a94df6cb) ^ (d + 2) =
        a ^ ((sharedTerm_a4a94df6cb) * ((d + 2 : ℕ) : ℝ)) :=
      (Real.rpow_mul_natCast ha0.le _ _).symm
    _ = a ^ (1 / 2 : ℝ) := by rw [zeta_exponent_mul_dim_add_two]
    _ = Real.sqrt a := (Real.sqrt_eq_rpow a).symm

/-- The inverse integer power of the contraction is exactly `(sqrt a)⁻¹`. -/
theorem positiveDensityZeta_zpow_neg_dim_add_two   :
    positiveDensityZeta d a ^ (-((d : ℤ) + 2)) = (Real.sqrt a)⁻¹ := by
  have hindex : -((d : ℤ) + 2) = -((d + 2 : ℕ) : ℤ) := by
    norm_num [Nat.cast_add]
  rw [hindex, zpow_neg, zpow_natCast, positiveDensityZeta_pow_dim_add_two d ha0]
end


/-- The source aggregate factor reduces to the normalized descent ratio. -/
theorem positiveDensityAggregateFactor_eq  {a eta : ℝ}
    (ha0 : 0 < a) :
    a * (1 + eta) * positiveDensityZeta d a ^ (-((d : ℤ) + 2)) =
      positiveDensityDescentRatio a eta := by
  rw [positiveDensityZeta_zpow_neg_dim_add_two d ha0, positiveDensityDescentRatio]

  calc
    a * (1 + eta) * (Real.sqrt a)⁻¹ =
        Real.sqrt a ^ 2 * (1 + eta) * (Real.sqrt a)⁻¹ := by
      rw [Real.sq_sqrt ha0.le]
    _ = (1 + eta) * Real.sqrt a := by field_simp [(Real.sqrt_pos.2 ha0).ne']

/-- A positive slack gives a positive normalized descent ratio. -/
theorem positiveDensityDescentRatio_pos {a eta : ℝ}
    (ha0 : 0 < a) (heta0 : 0 < eta) :
    0 < positiveDensityDescentRatio a eta := by
  rw [positiveDensityDescentRatio]
  positivity

section
variable {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)

include ha0 ha1
/-- The canonical eta choice gives a positive normalized descent ratio. -/
theorem positiveDensityCanonicalRatio_pos  :
    0 < positiveDensityDescentRatio a (positiveDensityEta a) :=
  positiveDensityDescentRatio_pos ha0 (positiveDensityEta_pos ha0 ha1)

/-- The canonical eta choice gives a strictly subunit descent ratio. -/
theorem positiveDensityCanonicalRatio_lt_one  :
    positiveDensityDescentRatio a (positiveDensityEta a) < 1 := by
  rw [positiveDensityDescentRatio]
  exact one_add_positiveDensityEta_mul_sqrt_lt_one ha0 ha1
end


/-- The midpoint ratio lies strictly between a positive subunit ratio and one. -/
theorem positiveDensityQ_bounds {L : ℝ}
    (hL0 : 0 < L) (hL1 : L < 1) :
    0 < L ∧ L < positiveDensityQ L ∧ positiveDensityQ L < 1 := by
  rw [positiveDensityQ]
  constructor
  · exact hL0
  constructor <;> linarith

/-- Each successor in the finite density sequence is strictly smaller. -/
theorem positiveDensityBeta_succ_lt {q a : ℝ} (n : ℕ)
    (hq0 : 0 < q) (hq1 : q < 1) (ha0 : 0 < a) :
    positiveDensityBeta q a (n + 1) < positiveDensityBeta q a n := by

  rw [positiveDensityBeta, pow_succ]
  calc
    q ^ n * q * a ^ 2 = q * (q ^ n * a ^ 2) := by ring
    _ < 1 * (q ^ n * a ^ 2) := mul_lt_mul_of_pos_right hq1 (by positivity)
    _ = q ^ n * a ^ 2 := by ring

variable {L q a : ℝ} (n : ℕ)

/-- Multiplication by an admissible ratio moves one density term below its successor. -/
theorem positiveDensityBeta_step_mul
    (hLq : L < q) (hq0 : 0 < q) (ha0 : 0 < a) :
    L * positiveDensityBeta q a n < positiveDensityBeta q a (n + 1) := by

  rw [positiveDensityBeta, pow_succ]
  calc
    L * (q ^ n * a ^ 2) < q * (q ^ n * a ^ 2) :=
      mul_lt_mul_of_pos_right hLq (by positivity)
    _ = q ^ n * q * a ^ 2 := by ring

/-- Division by a positive admissible ratio moves a density term below its successor. -/
theorem positiveDensityBeta_step_div
    (hL0 : 0 < L) (hLq : L < q) (hq0 : 0 < q) (ha0 : 0 < a) :
    positiveDensityBeta q a n < positiveDensityBeta q a (n + 1) / L := by
  rw [lt_div_iff₀ hL0]
  rw [mul_comm]
  exact positiveDensityBeta_step_mul n hLq hq0 ha0

/-- The finite density sequence eventually falls below every positive target. -/
theorem exists_positiveDensityBeta_lt {q a beta : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) (ha0 : 0 < a) (hbeta0 : 0 < beta) :
    ∃ N : ℕ, positiveDensityBeta q a N < beta := by
  have ha2  := sq_pos_of_pos ha0
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (div_pos hbeta0 ha2) hq1
  refine ⟨N + 1, (positiveDensityBeta_succ_lt N hq0 hq1 ha0).trans ?_⟩
  rw [positiveDensityBeta]
  exact (lt_div_iff₀ ha2).mp hN

end

end HypoellipticAleksandrov.Parabolic
