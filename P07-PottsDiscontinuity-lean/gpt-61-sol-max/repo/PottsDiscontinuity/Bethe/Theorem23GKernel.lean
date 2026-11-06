module
public import Mathlib

public import PottsDiscontinuity.Bethe.Theorem23Kernel
public import PottsDiscontinuity.Bethe.DiscreteJacobian

/-! # Uniform bounds for the kernel in the Jacobian row sums -/

@[expose] public section

open Set

namespace PottsDiscontinuity.Bethe

/-- Antisymmetry exchanges the two partial derivatives. -/
theorem thetaPartialSecond_eq_neg_d1Theta {Δ : ℝ} (hΔ : Δ < -1) (x y : ℝ) :
    thetaPartialSecond Δ x y = -d1Theta Δ y x := by
  have heq  :=
    funext fun t => theta_swap Δ t x
  unfold thetaPartialSecond d1Theta
  simp_all

/-- Bounds and a modulus of continuity for the derivative of `G`, uniform in
the entire antiferroelectric parameter range. -/
theorem exists_uniform_discreteBetheG_deriv_bounds {Δ₀ : ℝ} (hΔ₀ : Δ₀ < -1) :
    ∃ C : ℝ, 0 < C ∧ ∀ Δ ≤ Δ₀,
      (∀ x ∈ Icc (-Real.pi) Real.pi, ∀ y ∈ Icc (-Real.pi) Real.pi,
        |deriv  (discreteBetheG Δ x)  y| ≤ C) ∧
       ∀ x ∈ Icc (-Real.pi) Real.pi, ∀ y ∈ Icc (-Real.pi) Real.pi,
        ∀ z ∈ Icc (-Real.pi) Real.pi,
        |deriv  (discreteBetheG Δ x)  y -
          deriv  (discreteBetheG Δ x)  z| ≤ C * |y - z|  := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_d1Theta_bounds hΔ₀
  refine ⟨2 * C, by positivity, fun Δ hΔ => ?_⟩
  have hvalid := lt_of_le_of_lt hΔ hΔ₀
  have hneg {x : ℝ} (hx : x ∈ Icc (-Real.pi) Real.pi) :
      -x ∈ Icc (-Real.pi) Real.pi := by
                                       grind
  have heq (x y : ℝ) : deriv ((discreteBetheG Δ x)) y =
      -d1Theta Δ y x + d1Theta Δ y (-x) := by
    rw [deriv_discreteBetheG_right hvalid,
      thetaPartialSecond_eq_neg_d1Theta hvalid,
      thetaPartialSecond_eq_neg_d1Theta hvalid]
    ring
  constructor
  · intro x hx y hy
    rw [heq]
    calc
      _ ≤ |-d1Theta Δ y x| + |d1Theta Δ y (-x)| := abs_add_le _ _
      _ ≤ C + C := by
        rw [abs_neg]
        grind
      _ = _ := by ring
  · intro x hx y hy z hz
    rw [heq, heq]
    have h₁ := (hb Δ hΔ).2 y hy x hx z hz x hx
    have h₂ := (hb Δ hΔ).2 y hy (-x) (hneg hx) z hz (-x) (hneg hx)
    simp only [sub_self, abs_zero, max_eq_left (abs_nonneg (y - z))] at h₁ h₂
    calc
      _ = |-(d1Theta Δ y x - d1Theta Δ z x) +
          (d1Theta Δ y (-x) - d1Theta Δ z (-x))| := by  ring
      _ ≤ |-(d1Theta Δ y x - d1Theta Δ z x)| +
          |d1Theta Δ y (-x) - d1Theta Δ z (-x)| := abs_add_le _ _
      _ ≤ C * |y-z| + C * |y-z| := by rw [abs_neg]; exact add_le_add h₁ h₂
      _ = _ := by ring

end PottsDiscontinuity.Bethe
