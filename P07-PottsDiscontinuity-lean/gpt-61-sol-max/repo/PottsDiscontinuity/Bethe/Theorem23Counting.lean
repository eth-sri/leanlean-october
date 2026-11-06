module
public import Mathlib

public import PottsDiscontinuity.Bethe.DiscreteCore
public import PottsDiscontinuity.Bethe.Prop21Rho
public import PottsDiscontinuity.Bethe.Theorem23Kernel

/-! # The smooth counting function in the proof of Lemma 2.4 -/

@[expose] public section

open Set


namespace PottsDiscontinuity.Bethe

/-- The function `f_p` of (2.8). -/
noncomputable def betheCountingFunction (Δ : ℝ) (N n : ℕ) (p : Fin n → ℝ) (x : ℝ) : ℝ :=
  (x + (∑ j : Fin n, theta Δ x (p j)) / (N : ℝ)) / (2 * Real.pi)

/-- The explicit derivative of the counting function. -/
noncomputable def betheCountingDerivative (Δ : ℝ) (N n : ℕ) (p : Fin n → ℝ) (x : ℝ) : ℝ :=
  (1 + (∑ j : Fin n, d1Theta Δ x (p j)) / (N : ℝ)) / (2 * Real.pi)

section

variable {Δ : ℝ} (hΔ : Δ < -1)
include hΔ

theorem hasDerivAt_betheCountingFunction 
    (N n : ℕ) (p : Fin n → ℝ) (x : ℝ) :
    HasDerivAt (betheCountingFunction Δ N n p) (betheCountingDerivative Δ N n p x) x := have hsum :=
                                                                                          HasDerivAt.fun_sum fun j x_1 =>
                                                                                            DifferentiableAt.hasDerivAt (AnalyticAt.differentiableAt (analyticAt_theta_left hΔ x (p j)));
                                                                                        HasDerivAt.div_const (HasDerivAt.add (hasDerivAt_id x) (HasDerivAt.div_const hsum ↑N)) (2 * Real.pi)

theorem continuous_d1Theta_left  (y : ℝ) :
    Continuous  fun x => d1Theta Δ x y  := by
  apply continuous_iff_continuousAt.2
  intro x
  
  have ha : AnalyticAt ℝ (fun t => thetaFirstInv (1 / Δ) t y) x :=
    AnalyticAt.comp (f := fun t  =>  (1 / Δ, t, y) )
      (g := fun z  => thetaFirstInv z.1 z.2.1 z.2.2)
      (analyticAt_thetaFirstInv (abs_inverse_parameter_lt_one hΔ) x y) (analyticAt_const.prod (analyticAt_id.prod analyticAt_const))
  
  rw [ funext fun t => (d1Theta_eq_thetaFirstInv hΔ t y).symm ] at ha
  exact ha.continuousAt

theorem continuous_betheCountingDerivative 
    (N n : ℕ) (p : Fin n → ℝ) : Continuous (betheCountingDerivative Δ N n p) := (continuous_const.add
                                                                            ((continuous_finsetSum _  fun j _ => continuous_d1Theta_left hΔ (p j) ).div_const _)).div_const _

theorem densityNorm_bddAbove_of_continuous 
    {f : ℝ → ℝ} (hf : Continuous f) :
    BddAbove (range fun α : Icc (-Real.pi) Real.pi =>
      |Xi (lamOf Δ) α * f (kMap (lamOf Δ) α)|) := have hc :=
                                                    Continuous.abs
                                                      (Continuous.mul (Continuous.comp (continuous_Xi (lamOf_pos hΔ)) continuous_subtype_val)
                                                        (Continuous.comp hf (Continuous.comp (continuous_kMap (lamOf_pos hΔ)) continuous_subtype_val)));
                                                  IsCompact.bddAbove (isCompact_range hc)

theorem countingError_bddAbove 
    (N n : ℕ) (p : Fin n → ℝ) :
    BddAbove (range fun α : Icc (-Real.pi) Real.pi =>
      |Xi (lamOf Δ) α *
        (betheCountingDerivative Δ N n p (kMap (lamOf Δ) α) - rho Δ (kMap (lamOf Δ) α))|) :=
  densityNorm_bddAbove_of_continuous hΔ
    ((continuous_betheCountingDerivative hΔ N n p).sub (continuous_rho hΔ))

end

section

variable {Δ : ℝ} {N n : ℕ} (hN : 0 < N) (p : Fin n → ℝ)
include hN

theorem betheCountingFunction_root_value  (hBE : DiscreteBetheEquation Δ N n p) (j : Fin n) :
    betheCountingFunction Δ N n p (p j) = discreteBetheIndex n j / (N : ℝ) := by
  
  have h := hBE j
  unfold betheCountingFunction
  field_simp 
  linarith

theorem betheCountingFunction_period  (x : ℝ) :
    betheCountingFunction Δ N n p (x + 2 * Real.pi) =
      betheCountingFunction Δ N n p x + ((N : ℝ) - (n : ℝ)) / (N : ℝ) := by
  
  unfold betheCountingFunction
  simp_rw [theta_add_two_pi_left]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  field_simp 
  ring

end

end PottsDiscontinuity.Bethe
