/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ODE.ParameterSeriesFamily
public import DOZZ.Hypergeom.ODE.ParameterSeriesUniformFDeriv
public import DOZZ.Hypergeom.ODE.SeriesSpatialDerivative

/-! Parameter regularity of spatial derivatives on the ordinary-series disk. -/

@[expose] public section

open Filter
open scoped Topology

namespace DOZZ.Proofs


/-- The spatial derivative of any characterized family is the shifted-series value on the unit
disk. This uses only its ordinary-series characterization and is independent of the chosen
global continuation. -/
theorem IsGaussHypergeometricFamily.hasDerivAt_unitDisk
    {H}
    (hH : IsGaussHypergeometricFamily H) a b c z
    (hc : ∀ n : ℕ, c ≠ -(n : ℂ)) (hz : ‖z‖ < 1) :
    HasDerivAt (H a b c)
      (a * b / c * H (a + 1) (b + 1) (c + 1) z) z := by
  have hseries := ordinaryHypergeometric_hasDerivAt_unitDisk a b c z hc hz
  rw [← (show H (a + 1) (b + 1) (c + 1) z = ordinaryHypergeometric (a + 1) (b + 1) (c + 1) z by exact (hH (a + 1) (b + 1) (c + 1) (by intro n heq; apply hc (n + 1); push_cast at heq ⊢; linear_combination heq)).2 z hz)] at hseries
  exact hseries.congr_of_eventuallyEq (by filter_upwards [Metric.isOpen_ball.mem_nhds (show z ∈ Metric.ball (0 : ℂ) 1 by simpa [Metric.mem_ball, dist_zero_right] using hz)] with w hw; exact (hH a b c hc).2 w (by simpa [Metric.mem_ball, dist_zero_right] using hw))

/-- At each admissible parameter tuple, the spatial derivative at a fixed unit-disk point varies
holomorphically with all three parameters. This supplies the derivative entries in the midpoint
Cramer formulas for the connection matrix. -/
theorem IsGaussHypergeometricFamily.differentiableAt_params_deriv_unitDisk
    {H}
    (hH : IsGaussHypergeometricFamily H) {p}
    (hp : p ∈ gaussParameterPoleFreeDomain) {z} (hz : ‖z‖ < 1) :
    DifferentiableAt ℂ (fun q : ℂ × ℂ × ℂ =>
      deriv (fun w => H q.1 q.2.1 q.2.2 w) z) p := by
  have gaussParameterPoleFreeDomain_shift_add_one : (p.1 + 1, p.2.1 + 1, p.2.2 + 1) ∈ gaussParameterPoleFreeDomain := by
    intro n hn
    apply hp (n + 1)
    push_cast at hn ⊢
    linear_combination hn
  let shift : ℂ × ℂ × ℂ → ℂ × ℂ × ℂ := fun q => q + ((1 : ℂ), 1, 1)
  have hpShift := gaussParameterPoleFreeDomain_shift_add_one
  have : p.2.2 ≠ 0 := by
    intro hzero
    exact hp 0 (by simpa using hzero)
  exact ((show DifferentiableAt ℂ (fun q : ℂ × ℂ × ℂ => q.1 * q.2.1 / q.2.2) p by fun_prop (disch := assumption)).mul (by change DifferentiableAt ℂ ((fun q : ℂ × ℂ × ℂ => H q.1 q.2.1 q.2.2 z) ∘ shift) p; exact (((IsGaussHypergeometricFamily.differentiableOn_params_unitDisk hH hz) (shift p) hpShift).differentiableAt (gaussParameterPoleFreeDomain_isOpen.mem_nhds hpShift)).comp p (by fun_prop))).congr_of_eventuallyEq (by filter_upwards [gaussParameterPoleFreeDomain_isOpen.mem_nhds hp] with q hq; exact (IsGaussHypergeometricFamily.hasDerivAt_unitDisk hH q.1 q.2.1 q.2.2 z hq hz).deriv)

end DOZZ.Proofs
