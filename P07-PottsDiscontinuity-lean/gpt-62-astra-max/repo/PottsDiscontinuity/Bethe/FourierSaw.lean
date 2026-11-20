module

public import Mathlib
public import PottsDiscontinuity.Bethe.Prop21Defs

/-!
# The sawtooth series and the closed form of `Ψ`

* `integral_id_mul_sin`: `∫_{-π}^{π} β sin(mβ) dβ = -2π (-1)^m/m`;
* `sawS μ α = ∑_{m ≥ 1} 2 (-1)^m e^{-μ m} sin(mα)/m` and `xiConv_neg_id`:
  the Poisson convolution of the sawtooth `β ↦ -β` on `[-π, π]` is `sawS μ`;
* `PsiFn_eq_neg_sub_sawS`: `Ψ(α) = -α - sawS(2λ)(α)`, the series form of the Fourier
  coefficients `Ψ̂(m) = ((-1)^m/(i m))(1 - Ξ̂_{2λ}(m))` of §4 (proved by differentiating, since
  `Ψ'(α) = -Ξ_{2λ}(α - π)` by footnote 5).
-/

@[expose] public section

open Complex Real MeasureTheory Filter Topology Set intervalIntegral

namespace PottsDiscontinuity.Bethe

/-- `∫_{-π}^{π} β sin(m β) dβ = -2π (-1)^m / m`. -/
theorem integral_id_mul_sin {m : ℕ} (hm : m ≠ 0) :
    ∫ β in (-π)..π, β * Real.sin (m * β) = -(2 * π * (-1) ^ m / m) := by
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := -π) (b := π)
    (u := fun x : ℝ => x) (u' := fun _ => 1) (v := fun x : ℝ => -(Real.cos (m * x) / m))
    (v' := fun x : ℝ => Real.sin (m * x))
    (fun x _ => hasDerivAt_id x)
    (fun x _ => by
      have h1 : HasDerivAt (fun x : ℝ => m * x) m x := by
        simpa using (hasDerivAt_id x).const_mul ↑m
      have h2 := h1.cos.div_const m |>.neg
      convert h2 using 1
      field_simp)
    (by simp) (by apply Continuous.intervalIntegrable <;> fun_prop)
  have h1 := Real.cos_nat_mul_pi m
  have h2 : Real.cos (m * -π) = (-1) ^ m := by
    simp [*]
  have h3 : ∫ x in (-π)..π, 1 * -(Real.cos (m * x) / m) = 0 := by
    simp [*]
  grind

theorem integral_odd_eq_zero {f : ℝ → ℝ} (hf : ∀ x, f (-x) = -f x) :
    ∫ x in (-π)..π, f x = 0 := by
  have h := intervalIntegral.integral_comp_neg (a := -π) (b := π) f
  simp_rw [hf] at h
  grind [intervalIntegral.integral_neg]

/-- The coefficient `n ↦ 2 (-1)^{n+1} e^{-μ(n+1)} / (n+1)` series: `∑_{m≥1} 2(-1)^m e^{-μ m} sin(mα)/m`. -/
noncomputable def sawS (μ α : ℝ) : ℝ :=
  ∑' n : ℕ, 2 * (-1) ^ (n + 1) * Real.exp (-μ) ^ (n + 1) / (n + 1) *
    Real.sin ((n + 1 : ℕ) * α)

theorem cosCoeff_neg_id (m : ℕ) : cosCoeff (fun β => -β) m = 0 := by
  exact integral_odd_eq_zero (by simp)

theorem sinCoeff_neg_id (n : ℕ) :
    sinCoeff (fun β => -β) (n + 1) = 2 * π * (-1) ^ (n + 1) / (n + 1) := by
  unfold sinCoeff
  have : ∀ β : ℝ, -β * Real.sin ((n + 1 : ℕ) * β) = -(β * Real.sin ((n + 1 : ℕ) * β)) :=
    fun β => by ring
  simp_rw [this]
  rw [intervalIntegral.integral_neg, integral_id_mul_sin (by omega)]
  push_cast
  ring

variable {μ : ℝ} (hμ : 0 < μ) {Δ : ℝ} (hΔ : Δ < -1) (α : ℝ)

include hμ in
theorem hasSum_xiConv_neg_id :
    HasSum (fun n : ℕ => 2 * (-1) ^ (n + 1) * Real.exp (-μ) ^ (n + 1) / (n + 1) *
      Real.sin ((n + 1 : ℕ) * α)) (xiConv μ (fun β => -β) α) := by
  have hpi := Real.pi_pos
  have h := hasSum_xiConv hμ ((continuous_neg).intervalIntegrable _ _) α
  grind [cosCoeff_neg_id, sinCoeff_neg_id, mul_zero, zero_add, sub_zero]

include hμ in
theorem xiConv_neg_id : xiConv μ (fun β => -β) α = sawS μ α :=
  (hasSum_xiConv_neg_id hμ α).tsum_eq.symm

theorem Xi_sub_pi_eq_add_pi (μ α : ℝ) : Xi μ (α - π) = Xi μ (α + π) := by
  unfold Xi
  simp

include hΔ in
theorem hasDerivAt_PsiFn :
    HasDerivAt (PsiFn Δ) (-Xi (2 * lamOf Δ) (α + π)) α := by
  have hlam := lamOf_pos hΔ
  have hcosh := cosh_lamOf hΔ
  have h1 := hasDerivAt_theta_kMap_left hlam hcosh α π
  have h2 := hasDerivAt_theta_kMap_left hlam hcosh α (-π)
  rw [kMap_pi] at h1
  rw [kMap_neg_pi] at h2
  have h3 := (h2.add h1).div_const 2
  have e : (-Xi (2 * lamOf Δ) (α - -π) + -Xi (2 * lamOf Δ) (α - π)) / 2 =
      -Xi (2 * lamOf Δ) (α + π) := by
    simp [Xi_sub_pi_eq_add_pi]
  rw [e] at h3
  exact h3

theorem PsiFn_zero : PsiFn Δ 0 = 0 := by
  simp [kMap_zero, theta, PsiFn]

include hμ in
theorem hasDerivAt_sawS :
    HasDerivAt (sawS μ) (Xi μ (α + π) - 1) α := by
  have hr1 : Real.exp (-μ) < 1 := by grind [Real.exp_lt_one_iff]
  have hu : Summable (fun n : ℕ => 2 * Real.exp (-μ) ^ (n + 1)) := by
    have := (summable_geometric_of_lt_one (Real.exp_pos _).le hr1).mul_left (2 * Real.exp (-μ))
    grind
  have hd := hasDerivAt_tsum (𝕜 := ℝ) (y₀ := 0) hu
    (g := fun n y => 2 * (-1) ^ (n + 1) * Real.exp (-μ) ^ (n + 1) / (n + 1) *
      Real.sin ((n + 1 : ℕ) * y))
    (g' := fun n y => 2 * (-1) ^ (n + 1) * Real.exp (-μ) ^ (n + 1) *
      Real.cos ((n + 1 : ℕ) * y))
    (fun n y => by
      have h1 : HasDerivAt (fun y : ℝ => (n + 1 : ℕ) * y) ((n + 1 : ℕ)) y := by
        simpa using (hasDerivAt_id y).const_mul ((n + 1 : ℝ))
      have h2 := h1.sin.const_mul (2 * (-1) ^ (n + 1) * Real.exp (-μ) ^ (n + 1) / (n + 1))
      grind)
    (fun n y => by
      have h : |2 * (-1) ^ (n + 1) * Real.exp (-μ) ^ (n + 1) *
          Real.cos ((n + 1 : ℕ) * y)| =
          2 * Real.exp (-μ) ^ (n + 1) * |Real.cos ((n + 1 : ℕ) * y)| := by
        simp
      rw [Real.norm_eq_abs, h]
      exact mul_le_of_le_one_right (by positivity) (Real.abs_cos_le_one _))
    (by simp) α
  have hsum : ∑' n : ℕ, 2 * (-1) ^ (n + 1) * Real.exp (-μ) ^ (n + 1) *
      Real.cos ((n + 1 : ℕ) * α) = Xi μ (α + π) - 1 := by
    refine HasSum.tsum_eq ?_
    convert (hasSum_Xi_cos hμ (α + π)) using 1
    funext n
    have : Real.cos ((n + 1 : ℕ) * (α + π)) =
        (-1) ^ (n + 1) * Real.cos ((n + 1 : ℕ) * α) := by
      rw [mul_add, Real.cos_add, Real.cos_nat_mul_pi, Real.sin_nat_mul_pi]
      ring
    grind
  rw [hsum] at hd
  exact hd

theorem sawS_zero (μ : ℝ) : sawS μ 0 = 0 := by
  unfold sawS
  simp

include hΔ in
/-- `Ψ(α) = -α - ∑_{m≥1} 2(-1)^m e^{-2λ m} sin(mα)/m`, i.e. `Ψ̂(m)` of §4 in closed series form. -/
theorem PsiFn_eq_neg_sub_sawS :
    PsiFn Δ α = -α - sawS (2 * lamOf Δ) α := by
  have hlam := lamOf_pos hΔ
  have hlam2 : 0 < 2 * lamOf Δ := by linarith
  have hd : ∀ x : ℝ, HasDerivAt (fun y => PsiFn Δ y + y + sawS (2 * lamOf Δ) y) 0 x := by
    intro x
    have h2 := ((hasDerivAt_PsiFn hΔ x).add (hasDerivAt_id x)).add (hasDerivAt_sawS hlam2 x)
    exact h2.congr_deriv (by ring)
  have hc := is_const_of_deriv_eq_zero
    (fun x => (hd x).differentiableAt) (fun x => (hd x).deriv) α 0
  grind [PsiFn_zero, sawS_zero, add_zero]

end PottsDiscontinuity.Bethe
