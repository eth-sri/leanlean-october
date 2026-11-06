module

public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# Scalar constants for positive parabolic density descent

This module records the explicit real parameters used in the finite density
descent of Krylov--Safonov Lemma 3.3.  It is deliberately independent of the
parabolic geometry, measure argument, and analytic density-to-point result.
-/

@[expose] public section

namespace HypoellipticAleksandrov.Parabolic

noncomputable section

/- The explicit slack in the positive-density descent. -/
def positiveDensityEta (a : ℝ) : ℝ :=
  min (1 / 2) ((a ^ (-(1 / 2 : ℝ)) - 1) / 2)

/- The terminal contraction parameter in Lemma 3.3. -/
def positiveDensityZeta (d : ℕ) (a : ℝ) : ℝ :=
  a ^ (1 / (2 * ((d : ℝ) + 2)))

/- The normalized aggregate coefficient controlling one density step. -/
def positiveDensityDescentRatio (a eta : ℝ) : ℝ :=
  (1 + eta) * Real.sqrt a

/- A canonical point strictly between an admissible ratio and one. -/
def positiveDensityQ (L : ℝ) : ℝ :=
  (1 + L) / 2

/- The finite density sequence for the explicit descent. -/
def positiveDensityBeta (q a : ℝ) (n : ℕ) : ℝ :=
  q ^ n * a ^ 2

private theorem zeta_exponent_mul_dim_add_two (d : ℕ) :
    (1 / (2 * ((d : ℝ) + 2))) * ((d + 2 : ℕ) : ℝ) = 1 / 2 := by
  have hdim : 0 < (d : ℝ) + 2 := by positivity
  rw [Nat.cast_add, Nat.cast_ofNat]
  field_simp

/- The chosen slack is positive whenever the initial density lies in `(0, 1)`. -/
theorem positiveDensityEta_pos {a }
    (ha0 : 0 < a) (ha1 : a < 1) : 0 < positiveDensityEta a := by
  rw [positiveDensityEta]
  apply lt_min
  · norm_num
  · have hpow : 1 < a ^ (-(1 / 2 : ℝ)) :=
      Real.one_lt_rpow_of_pos_of_lt_one_of_neg ha0 ha1 (by norm_num)
    linarith

/- The chosen slack is strictly less than one. -/
theorem positiveDensityAggregateFactor_eq (d : ℕ) {a eta }
    (ha0 : 0 < a) :
    a * (1 + eta) * positiveDensityZeta d a ^ (-((d : ℤ) + 2)) =
      positiveDensityDescentRatio a eta := by
  have _h_inl_20 : positiveDensityZeta d a ^ (-((d : ℤ) + 2)) = (Real.sqrt a)⁻¹ := by
      have hindex : -((d : ℤ) + 2) = -((d + 2 : ℕ) : ℤ) := by
        norm_num [Nat.cast_add]
      have _h_inl_21 : positiveDensityZeta d a ^ (d + 2) = Real.sqrt a := by
          rw [positiveDensityZeta]
          calc
            (a ^ (1 / (2 * ((d : ℝ) + 2)))) ^ (d + 2) =
                a ^ ((1 / (2 * ((d : ℝ) + 2))) * ((d + 2 : ℕ) : ℝ)) :=
              (Real.rpow_mul_natCast ha0.le _ _).symm
            _ = a ^ (1 / 2 : ℝ) := by rw [zeta_exponent_mul_dim_add_two]
            _ = Real.sqrt a := (Real.sqrt_eq_rpow a).symm

        /- The inverse integer power of the contraction is exactly `(sqrt a)⁻¹`. -/
      rw [hindex, zpow_neg, zpow_natCast, _h_inl_21]

    /- The source aggregate factor reduces to the normalized descent ratio. -/
  rw [_h_inl_20, positiveDensityDescentRatio]
  have hs0 := Real.sqrt_pos.2 ha0
  calc
    a * (1 + eta) * (Real.sqrt a)⁻¹ =
        Real.sqrt a ^ 2 * (1 + eta) * (Real.sqrt a)⁻¹ := by
      rw [Real.sq_sqrt ha0.le]
    _ = (1 + eta) * Real.sqrt a := by field_simp [hs0.ne']

/- A positive slack gives a positive normalized descent ratio. -/
theorem positiveDensityDescentRatio_pos {a eta }
    (ha0 : 0 < a) (heta0 : 0 < eta) :
    0 < positiveDensityDescentRatio a eta := by
  rw [positiveDensityDescentRatio]
  positivity

/- The canonical eta choice gives a positive normalized descent ratio. -/
theorem positiveDensityCanonicalRatio_pos {a }
    (ha0 : 0 < a) (ha1 : a < 1) :
    0 < positiveDensityDescentRatio a (positiveDensityEta a) :=
  positiveDensityDescentRatio_pos ha0 (positiveDensityEta_pos ha0 ha1)

/- The canonical eta choice gives a strictly subunit descent ratio. -/
end

end HypoellipticAleksandrov.Parabolic
