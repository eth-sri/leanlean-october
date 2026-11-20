module

public import PottsDiscontinuity.Bethe.DiscreteCore
public import PottsDiscontinuity.Bethe.AsymptoticDefs
public import PottsDiscontinuity.Bethe.Prop21Rho
public import PottsDiscontinuity.Bethe.Theorem23Kernel

/-! # The smooth counting function in the proof of Lemma 2.4 -/

@[expose] public section

open Set
open scoped BigOperators

namespace PottsDiscontinuity.Bethe

section

variable (Δ : ℝ) (N n : ℕ) (p : Fin n → ℝ) (x : ℝ)

/-- The function `f_p` of (2.8). -/
noncomputable def betheCountingFunction : ℝ :=
  (x + (∑ j : Fin n, theta Δ x (p j)) / (N : ℝ)) / (2 * Real.pi)

/-- The explicit derivative of the counting function. -/
noncomputable def betheCountingDerivative : ℝ :=
  (1 + (∑ j : Fin n, d1Theta Δ x (p j)) / (N : ℝ)) / (2 * Real.pi)

end

theorem hasDerivAt_betheCountingFunction {Δ : ℝ} (hΔ : Δ < -1)
    (N n : ℕ) (p : Fin n → ℝ) (x : ℝ) :
    HasDerivAt (betheCountingFunction Δ N n p) (betheCountingDerivative Δ N n p x) x := by
  have hsum : HasDerivAt (fun t => ∑ j : Fin n, theta Δ t (p j))
      (∑ j : Fin n, d1Theta Δ x (p j)) x := HasDerivAt.fun_sum (fun j _ => (analyticAt_theta_left hΔ x (p j)).differentiableAt.hasDerivAt)
  exact ((hasDerivAt_id x).add (hsum.div_const (N : ℝ))).div_const (2 * Real.pi)

theorem continuous_d1Theta_left {Δ : ℝ} (hΔ : Δ < -1) (y : ℝ) :
    Continuous (fun x => d1Theta Δ x y) := by
  exact (continuous_d1Theta_pair hΔ).comp (continuous_id.prodMk continuous_const)

theorem continuous_betheCountingDerivative {Δ : ℝ} (hΔ : Δ < -1)
    (N n : ℕ) (p : Fin n → ℝ) : Continuous (betheCountingDerivative Δ N n p) := by
  exact (continuous_const.add
    ((continuous_finsetSum _ (fun j _ => continuous_d1Theta_left hΔ (p j))).div_const _)).div_const _

theorem densityNorm_bddAbove_of_continuous {Δ : ℝ} (hΔ : Δ < -1)
    {f : ℝ → ℝ} (hf : Continuous f) :
    BddAbove (densityValues Δ f) := by
  have hc : Continuous (fun α : Icc (-Real.pi) Real.pi =>
      |Xi (lamOf Δ) α * f (kMap (lamOf Δ) α)|) :=
    (((continuous_Xi (lamOf_pos hΔ)).comp continuous_subtype_val).mul
      (hf.comp ((continuous_kMap (lamOf_pos hΔ)).comp continuous_subtype_val))).abs
  exact (isCompact_range hc).bddAbove

theorem countingError_bddAbove {Δ : ℝ} (hΔ : Δ < -1)
    (N n : ℕ) (p : Fin n → ℝ) :
    BddAbove (densityValues Δ (fun x => betheCountingDerivative Δ N n p x - rho Δ x)) :=
  densityNorm_bddAbove_of_continuous hΔ
    ((continuous_betheCountingDerivative hΔ N n p).sub (continuous_rho hΔ))

theorem betheCountingFunction_root_value {Δ : ℝ} {N n : ℕ} (hN : 0 < N)
    (p : Fin n → ℝ) (hBE : DiscreteBetheEquation Δ N n p) (j : Fin n) :
    betheCountingFunction Δ N n p (p j) = discreteBetheIndex n j / (N : ℝ) := by
  have hNc : (N : ℝ) ≠ 0 := by positivity
  have h := hBE j
  unfold betheCountingFunction
  field_simp [hNc]
  linarith

theorem betheCountingFunction_period {Δ : ℝ} {N n : ℕ} (hN : 0 < N)
    (p : Fin n → ℝ) (x : ℝ) :
    betheCountingFunction Δ N n p (x + 2 * Real.pi) =
      betheCountingFunction Δ N n p x + ((N : ℝ) - (n : ℝ)) / (N : ℝ) := by
  have hNc : (N : ℝ) ≠ 0 := by positivity
  unfold betheCountingFunction
  simp_rw [theta_add_two_pi_left]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp [hNc]
  ring

end PottsDiscontinuity.Bethe
