module

public import PottsDiscontinuity.Bethe.DiscreteCore
public import PottsDiscontinuity.Bethe.Prop21Rho
public import PottsDiscontinuity.Bethe.Theorem23Kernel

/-! # The smooth counting function in the proof of Lemma 2.4 -/

@[expose] public noncomputable section

open Set
open scoped BigOperators

namespace PottsDiscontinuity.Bethe

section
variable (Δ : ℝ) (N n : ℕ) (p : Fin n → ℝ) (x : ℝ)
/-- The function `f_p` of (2.8). -/
def betheCountingFunction  : ℝ :=
  (x + (∑ j : Fin n, theta Δ x (p j)) / (N : ℝ)) / (2 * Real.pi)

/-- The explicit derivative of the counting function. -/
def betheCountingDerivative  : ℝ :=
  (1 + (∑ j : Fin n, d1Theta Δ x (p j)) / (N : ℝ)) / (2 * Real.pi)
end

section
variable {Δ : ℝ} (hΔ : Δ < -1)
include hΔ
theorem hasDerivAt_betheCountingFunction (N n : ℕ) (p : Fin n → ℝ) (x : ℝ) :
    HasDerivAt (betheCountingFunction Δ N n p) (betheCountingDerivative Δ N n p x) x := by
  have hsum : HasDerivAt (fun t => ∑ j : Fin n, theta Δ t (p j))
      (∑ j : Fin n, d1Theta Δ x (p j)) x :=
    HasDerivAt.fun_sum (fun j _ => (analyticAt_theta_left hΔ x (p j)).differentiableAt.hasDerivAt)
  exact ((hasDerivAt_id x).add (hsum.div_const (N : ℝ))).div_const (2 * Real.pi)

theorem continuous_d1Theta_left (y : ℝ) :
    Continuous (fun x => d1Theta Δ x y) := by
  apply continuous_iff_continuousAt.2
  intro x
  have ha : AnalyticAt ℝ (fun t => thetaFirstInv (1 / Δ) t y) x :=
    AnalyticAt.comp (f := fun t : ℝ => ((1 / Δ, t, y) : ℝ × ℝ × ℝ))
     
      (analyticAt_thetaFirstInv (abs_inverse_parameter_lt_one hΔ) x y) (by fun_prop)
  have heq :=
    funext fun t => (d1Theta_eq_thetaFirstInv hΔ t y).symm
  simp_all
  fun_prop

theorem continuous_betheCountingDerivative (N n : ℕ) (p : Fin n → ℝ) : Continuous (betheCountingDerivative Δ N n p) :=
  (continuous_const.add
    ((continuous_finsetSum _ (fun j _ => continuous_d1Theta_left hΔ (p j))).div_const _)).div_const _

theorem densityNorm_bddAbove_of_continuous {f : ℝ → ℝ} (hf : Continuous f) :
    BddAbove (range fun α : Icc (-Real.pi) Real.pi =>
      |Xi (lamOf Δ) α * f (kMap (lamOf Δ) α)|) := by
  have hc : Continuous (fun α : Icc (-Real.pi) Real.pi =>
      |Xi (lamOf Δ) α * f (kMap (lamOf Δ) α)|) :=
    (((continuous_Xi (lamOf_pos hΔ)).comp continuous_subtype_val).mul
      (hf.comp ((continuous_kMap (lamOf_pos hΔ)).comp continuous_subtype_val))).abs
  exact (isCompact_range hc).bddAbove

theorem countingError_bddAbove (N n : ℕ) (p : Fin n → ℝ) :
    BddAbove (range fun α : Icc (-Real.pi) Real.pi =>
      |Xi (lamOf Δ) α *
        (betheCountingDerivative Δ N n p (kMap (lamOf Δ) α) - rho Δ (kMap (lamOf Δ) α))|) :=
  densityNorm_bddAbove_of_continuous hΔ
    ((continuous_betheCountingDerivative hΔ N n p).sub (continuous_rho hΔ))
end

section
variable {Δ : ℝ} {N n : ℕ} (hN : 0 < N) (p : Fin n → ℝ)
include hN
theorem betheCountingFunction_root_value (hBE : DiscreteBetheEquation Δ N n p) (j : Fin n) :
    betheCountingFunction Δ N n p (p j) = discreteBetheIndex n j / (N : ℝ) := by
  have h := hBE j
  unfold betheCountingFunction
  field_simp
  linarith

theorem betheCountingFunction_period (x : ℝ) :
    betheCountingFunction Δ N n p (x + 2 * Real.pi) =
      betheCountingFunction Δ N n p x + ((N : ℝ) - (n : ℝ)) / (N : ℝ) := by
  unfold betheCountingFunction
  simp_rw [theta_add_two_pi_left]
  simp
  field_simp
  ring
end

end PottsDiscontinuity.Bethe
