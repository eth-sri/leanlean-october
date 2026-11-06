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

private theorem gaussParameterPoleFreeDomain_shift_add_one
    {p : ℂ × ℂ × ℂ} (hp : p ∈ gaussParameterPoleFreeDomain) :
    (p.1 + 1, p.2.1 + 1, p.2.2 + 1) ∈ gaussParameterPoleFreeDomain := by
  intro n hn
  apply hp (n + 1)
  grind
section
variable {H : ℂ → ℂ → ℂ → ℂ → ℂ}
section
variable (hH : IsGaussHypergeometricFamily H)
include hH

/-- The spatial derivative of any characterized family is the shifted-series value on the unit
disk. This uses only its ordinary-series characterization and is independent of the chosen
global continuation. -/
theorem IsGaussHypergeometricFamily.hasDerivAt_unitDisk
    (a b c z : ℂ)
    (hc : ∀ n : ℕ, c ≠ -(n : ℂ)) (hz : ‖z‖ < 1) :
    HasDerivAt (H a b c)
      (a * b / c * H (a + 1) (b + 1) (c + 1) z) z := by
  have hseries := ordinaryHypergeometric_hasDerivAt_unitDisk a b c z hc hz
  have hzball : z ∈ Metric.ball 0 1 := by
    simp_all
  have hnear : (H a b c) =ᶠ[𝓝 z] ordinaryHypergeometric a b c := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hzball] with w hw
    have hwnorm : ‖w‖ < 1 := by
      simp_all
    exact (hH a b c hc).2 w hwnorm
  have hseriesShift : H (a + 1) (b + 1) (c + 1) z =
      ordinaryHypergeometric (a + 1) (b + 1) (c + 1) z := by
    have hcShift : ∀ n : ℕ, c + 1 ≠ -n := by
      intro n heq
      apply hc (n + 1)
      grind
    exact (hH _ _ _ hcShift).2 z hz
  rw [← hseriesShift] at hseries
  exact hseries.congr_of_eventuallyEq hnear

/-- At each admissible parameter tuple, the spatial derivative at a fixed unit-disk point varies
holomorphically with all three parameters. This supplies the derivative entries in the midpoint
Cramer formulas for the connection matrix. -/
theorem IsGaussHypergeometricFamily.differentiableAt_params_deriv_unitDisk
    {p : ℂ × ℂ × ℂ}
    (hp : p ∈ gaussParameterPoleFreeDomain) {z : ℂ} (hz : ‖z‖ < 1) :
    DifferentiableAt ℂ (fun q : ℂ × ℂ × ℂ =>
      deriv (fun w => H q.1 q.2.1 q.2.2 w) z) p := by
  let shift : ℂ × ℂ × ℂ → ℂ × ℂ × ℂ := fun q => q + (1, 1, 1)
  have hpShift : shift p ∈ gaussParameterPoleFreeDomain := gaussParameterPoleFreeDomain_shift_add_one hp
  have hshiftOn :=
    IsGaussHypergeometricFamily.differentiableOn_params_unitDisk hH hz
  have hshiftAt :=
    (hshiftOn (shift p) hpShift).differentiableAt
      (gaussParameterPoleFreeDomain_isOpen.mem_nhds hpShift)
  have hshiftMap : DifferentiableAt ℂ shift p := by
    fun_prop
  have hshiftComp : DifferentiableAt ℂ
      (fun q => H (q.1 + 1) (q.2.1 + 1) (q.2.2 + 1) z) p := by
    fun_prop
  have hpC : p.2.2 ≠ 0 := by
    intro hzero
    exact hp 0 (by simp_all)
  have hfactor : DifferentiableAt ℂ
      (fun q => q.1 * q.2.1 / q.2.2) p := by
    fun_prop
  have hright :=
    hfactor.mul hshiftComp
  have hlocal : (fun q =>
      deriv (H q.1 q.2.1 q.2.2) z) =ᶠ[𝓝 p]
      (fun q =>
        q.1 * q.2.1 / q.2.2 * H (q.1 + 1) (q.2.1 + 1) (q.2.2 + 1) z) := by
    filter_upwards [gaussParameterPoleFreeDomain_isOpen.mem_nhds hp] with q hq
    exact (IsGaussHypergeometricFamily.hasDerivAt_unitDisk hH
      q.1 q.2.1 q.2.2 z hq hz).deriv
  exact hright.congr_of_eventuallyEq hlocal

end

end

end DOZZ.Proofs
