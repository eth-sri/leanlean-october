/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.BPZ.WardLimitSym

/-! # Uniform bounds for the symmetrized kernels

With a Lipschitz test function `φ` supported where `ρ = 1` (with margin `2δ`), the antisymmetrized
kernel built from any kernel `L` with `|L(w)| ≤ c|v|/|w|` is bounded by a multiple of
`ρ(x)|k(x)| ρ(y)|k(y)|`, uniformly in the cutoff: near the diagonal the combination
`φ(x)ρ(y) − φ(y)ρ(x)` is `φ(x) − φ(y)`, of size `Lip(φ)|x − y|`, which cancels the kernel
singularity. The far-region test function is bounded by a multiple of `ρ(x)|k(x)|` times the
far mass. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- A continuous compactly supported real function is uniformly continuous. -/
theorem bpz_unifCont_of_compact {f : ℂ → ℝ} (hf : Continuous f) (hc : HasCompactSupport f) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x x', ‖x - x'‖ ≤ δ → |f x - f x'| ≤ ε := by
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := Metric.uniformContinuous_iff.1 (hc.uniformContinuous_of_continuous hf)
    ε hε
  refine ⟨δ / 2, by positivity, fun x x' hxx' => ?_⟩
  have := h (show dist x x' < δ by rw [dist_eq_norm]; linarith)
  bound

namespace BPZLimitData

variable {γ q δ : ℝ} {ρ kt k₂ φ : ℂ → ℝ} {D : Set ℂ}
section
variable (hd : BPZLimitData γ q δ ρ kt k₂ φ D)
include hd

theorem phi_cont : Continuous φ := by
  obtain ⟨L, hL⟩ := hd.φ_lip
  exact hL.continuous

theorem phi_bdd : ∃ B : ℝ, 0 ≤ B ∧ ∀ x, |φ x| ≤ B := by
  obtain ⟨B, hB⟩ := hd.phi_cont.bounded_above_of_compact_support hd.φ_compact
  exact ⟨max B 0, le_max_right .., fun x => by
    simp_all⟩

end
section
variable (hd : BPZLimitData γ q δ ρ kt k₂ φ D) {B : ℝ} (hB : ∀ x, |φ x| ≤ B)
include hd hB

theorem abs_phi_le (x : ℂ) : |φ x| ≤ B * ρ x := by
  by_cases hx : φ x = 0
  · rw [hx, abs_zero]
    exact mul_nonneg ((abs_nonneg _).trans (hB x)) (hd.ρ_nonneg x)
  · rw [hd.rho_eq_one (subset_tsupport φ hx), mul_one]
    simp_all

/-- The antisymmetrized kernel is bounded by `ρ|k| ⊗ ρ|k|`, uniformly in the kernel `L`. -/
theorem abs_symKer_le {Lφ : ℝ≥0} (hLφ : LipschitzWith Lφ φ) {c : ℝ} (hc : 0 ≤ c) (v : ℂ) {k L : ℂ → ℝ}
    (hL : ∀ w, |L w| ≤ c * ‖v‖ / ‖w‖) (x y : ℂ) :
    |bpzSymKer φ ρ k L x y| ≤
      c * ‖v‖ * ((Lφ : ℝ) + B / δ) * ((ρ x * |k x|) * (ρ y * |k y|)) := by
  have hδ := hd.δ_pos
  have hB0 := (abs_nonneg _).trans (hB 0)
  have hρx := hd.ρ_nonneg x
  have hρy := hd.ρ_nonneg y
  have hP : 0 ≤ (ρ x * |k x|) * (ρ y * |k y|) := by positivity
  have hC : 0 ≤ c * ‖v‖ * (Lφ + B / δ) := by positivity
  unfold bpzSymKer
  rcases eq_or_ne x y with rfl | hxy
  · simp
    positivity
  have hxy' := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  rw [abs_div, abs_two, abs_mul, abs_mul, abs_mul]
  by_cases hnear : ‖x - y‖ < 2 * δ
  · rw [hd.near_diag hnear]
    by_cases hφe : φ x = φ y
    · rw [hφe, sub_self, abs_zero, zero_mul, zero_mul, zero_div]
      positivity
    have hρ1 : ρ x = 1 ∧ ρ y = 1 := by
      have hor : φ x ≠ 0 ∨ φ y ≠ 0 := by
        by_contra h
        push Not at h
        exact hφe (by linarith)
      rcases hor with h | h
      · have hxt := subset_tsupport φ h
        refine ⟨hd.rho_eq_one hxt, ?_⟩
        by_contra hne
        have := hd.sep x hxt y (lt_of_le_of_ne (hd.ρ_le_one y) hne)
        linarith
      · have hyt := subset_tsupport φ h
        refine ⟨?_, hd.rho_eq_one hyt⟩
        by_contra hne
        have := hd.sep y hyt x (lt_of_le_of_ne (hd.ρ_le_one x) hne)
        rw [norm_sub_rev] at this
        linarith
    rw [hρ1.1, hρ1.2]
    have hlip : |φ x - φ y| ≤ Lφ * ‖x - y‖ := by
      rw [← Real.dist_eq, ← dist_eq_norm]; exact hLφ.dist_le_mul x y
    have hLb := hL (x - y)
    calc |φ x - φ y| * (|k x| * |k y|) * |L _| / 2
        ≤ (Lφ * ‖x - y‖) * (|k x| * |k y|) * (c * ‖v‖ / ‖x - y‖) / 2 := by gcongr
      _ = c * ‖v‖ * Lφ / 2 * (|k x| * |k y|) := by field_simp
      _ ≤ c * ‖v‖ * (Lφ + B / δ) * ((1 * |k x|) * (1 * |k y|)) := by
          rw [one_mul, one_mul]
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          have : Lφ / 2 ≤ Lφ + B / δ := by
            have := Lφ.coe_nonneg; have : 0 ≤ B / δ := by positivity
            linarith
          calc c * ‖v‖ * Lφ / 2 = c * ‖v‖ * (Lφ / 2) := by ring
            _ ≤ c * ‖v‖ * (Lφ + B / δ) := by bound
  · push Not at hnear
    have h1 : |φ x * ρ y - φ y * ρ x| ≤ 2 * B * (ρ x * ρ y) := by
      have ha := hd.abs_phi_le hB x
      have hb := hd.abs_phi_le hB y
      calc |φ x * ρ y - φ y * ρ x| ≤ |φ x| * ρ y + |φ y| * ρ x := by
            refine (abs_sub ..).trans ?_
            rw [abs_mul, abs_mul, abs_of_nonneg hρy, abs_of_nonneg hρx]
        _ ≤ B * ρ x * ρ y + B * ρ y * ρ x := by
            gcongr
        _ = 2 * B * (ρ x * ρ y) := by ring
    have hLb :=
      (hL _).trans (div_le_div_of_nonneg_left (by positivity) (by positivity) hnear)
    calc |φ x * ρ y - φ y * ρ x| * (|k x| * |k y|) * |L _| / 2
        ≤ 2 * B * (ρ x * ρ y) * (|k x| * |k y|) * (c * ‖v‖ / (2 * δ)) / 2 := by gcongr
      _ = c * ‖v‖ * (B / δ) / 2 * ((ρ x * |k x|) * (ρ y * |k y|)) := by field_simp
      _ ≤ c * ‖v‖ * (Lφ + B / δ) * ((ρ x * |k x|) * (ρ y * |k y|)) := by
          apply mul_le_mul_of_nonneg_right _ hP
          have : B / δ / 2 ≤ Lφ + B / δ := by
            have := Lφ.coe_nonneg; have : 0 ≤ B / δ := by positivity
            linarith
          calc c * ‖v‖ * (B / δ) / 2 = c * ‖v‖ * (B / δ / 2) := by ring
            _ ≤ c * ‖v‖ * (Lφ + B / δ) := by bound

/-- The far-region test function is bounded by `ρ|k|` times the far mass. -/
theorem abs_mixTest_le {c : ℝ} (hc : 0 ≤ c) (v : ℂ) {k L : ℂ → ℝ} (hL : ∀ w, |L w| ≤ c * ‖v‖ / ‖w‖)
    {m : Measure ℂ} (hint : Integrable (fun y => (1 - ρ y) * k₂ y) m) (x : ℂ) :
    |bpzMixTest φ ρ k k₂ L m x| ≤
      c * ‖v‖ / (2 * δ) * B * (ρ x * |k x|) * ∫ y, (1 - ρ y) * k₂ y ∂m := by
  have hδ := hd.δ_pos
  have hB0 := (abs_nonneg _).trans (hB 0)
  rw [← Real.norm_eq_abs, ← integral_const_mul]
  refine norm_integral_le_of_norm_le (hint.const_mul _) (Eventually.of_forall fun y => ?_)
  have hw : 0 ≤ (1 - ρ y) * k₂ y := mul_nonneg (by linarith [hd.ρ_le_one y]) (hd.k₂_nonneg y)
  rw [Real.norm_eq_abs, abs_mul _, abs_of_nonneg hw]
  have hR0 : 0 ≤ c * ‖v‖ / (2 * δ) * B * (ρ x * |k x|) * ((1 - ρ y) * k₂ y) := by
    have := hd.ρ_nonneg x
    positivity
  by_cases hφx : φ x = 0
  · simp_all
  by_cases hρy : ρ y = 1
  · simp_all
  have hxt := subset_tsupport φ hφx
  have hsep := hd.sep x hxt y (lt_of_le_of_ne (hd.ρ_le_one y) hρy)
  have hLb :=
    (hL _).trans (div_le_div_of_nonneg_left (by positivity) (by positivity) hsep)
  have hφ' : |φ x| ≤ B * ρ x := hd.abs_phi_le hB x
  have hBρ : 0 ≤ B * ρ x * |k x| := mul_nonneg (mul_nonneg hB0 (hd.ρ_nonneg x)) (abs_nonneg _)
  rw [abs_mul, abs_mul]
  calc (1 - ρ y) * k₂ y * (|φ x| * |k x| * |L _|)
      ≤ (1 - ρ y) * k₂ y * (B * ρ x * |k x| * (c * ‖v‖ / (2 * δ))) := by gcongr
    _ = c * ‖v‖ / (2 * δ) * B * (ρ x * |k x|) * ((1 - ρ y) * k₂ y) := by ring

end

end BPZLimitData

end DOZZ.Proofs
