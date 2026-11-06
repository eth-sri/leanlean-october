/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ClassificationWirtingerC2
public import DOZZ.Hypergeom.ODE.GaussSystem

/-! Reflection of the real Gauss PDE under `z ↦ 1-z`. -/

@[expose] public section

open Filter
open scoped Topology

namespace DOZZ.Proofs

private theorem hasFDerivAt_reflection (z : ℂ) :
    HasFDerivAt (𝕜 := ℝ) (fun w : ℂ => 1 - w)
      (-ContinuousLinearMap.id ℝ ℂ) z := by
  fun_prop

/-- Pulling a real differentiable map back by `z ↦ 1-z` negates its `∂z` derivative. -/
theorem wirtingerZ_reflection {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℝ f (1 - z)) :
    wirtingerZ (fun w => f (1 - w)) z = -wirtingerZ f (1 - z) := by
  have hmap := hasFDerivAt_reflection z
  have hfd : fderiv ℝ (fun w => f (1 - w)) z =
      (fderiv ℝ f (1 - z)).comp (-ContinuousLinearMap.id ℝ ℂ) := by
    simpa only [Function.comp_def, hmap.fderiv] using (hf.hasFDerivAt.comp z hmap).fderiv
  rw [wirtingerZ, wirtingerZ, hfd]
  simp
  ring

private theorem gaussRegularPlane_reflection (z : ℂ)
    (hz : z ∈ gaussRegularPlane) : 1 - z ∈ gaussRegularPlane := by
  change z ≠ 0 ∧ z ≠ 1 at hz
  change 1 - z ≠ 0 ∧ 1 - z ≠ 1
  grind

/-- The second `∂z` derivative is invariant under reflection on an open domain stable
under `z ↦ 1-z`. -/
theorem wirtingerZ_second_reflection
    {U : Set ℂ} (hU : IsOpen U)
    (hreflect : ∀ w ∈ U, 1 - w ∈ U)
    {f : ℂ → ℂ} (hf : ContDiffOn ℝ 2 f U)
    {z : ℂ} (hz : z ∈ U) (hz' : 1 - z ∈ U) :
    wirtingerZ (fun w => wirtingerZ (fun v => f (1 - v)) w) z =
      wirtingerZ (fun w => wirtingerZ f w) (1 - z) := by
  have hAt :=
    hf _ hz' |>.contDiffAt (hU.mem_nhds hz')
  have hmap : ContDiffAt ℝ 2 (fun w => 1 - w) z := by fun_prop
  have hleft :=
    differentiableAt_wirtingerZ_of_contDiffAt_two (hAt.comp z hmap)
  have hG :=
    differentiableAt_wirtingerZ_of_contDiffAt_two hAt
  have hmapDiff : DifferentiableAt ℝ (fun w => (1 : ℂ) - w) z :=
    by fun_prop
  have hGcomp :=
    hG.comp z hmapDiff
  have heq : (fun w => wirtingerZ (fun v => f (1 - v)) w) =ᶠ[𝓝 z]
      (fun w => -wirtingerZ f (1 - w)) := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact wirtingerZ_reflection
      (((hf _ (hreflect w hw)).contDiffAt
        (hU.mem_nhds (hreflect w hw))).differentiableAt (by norm_num))
  have hfirst := wirtingerZ_congr_of_eventuallyEq hleft hGcomp.neg heq
  have hminus := wirtingerZ_reflection hG
  have hsub := wirtingerZ_sub (differentiableAt_const 0) hGcomp
  have hzero : wirtingerZ (fun _ => 0) z = 0 := by simp [wirtingerZ]
  continuity

/-- Reflection preserves the real-solution condition `IsRealGaussSolution` after
changing `c` to `1 + a + b - c`. -/
theorem realGaussSolution_reflection
    (a b c : ℝ) (T : ℂ → ℝ) (hT : IsRealGaussSolution a b c T) :
    IsRealGaussSolution a b (1 + a + b - c) (fun z => T (1 - z)) := by
  let F : ℂ → ℂ := fun z => (T z)
  let U : ℂ → ℂ := fun z => ((T (1 - z)))
  have hregMap : ∀ z ∈ gaussRegularPlane, 1 - z ∈ gaussRegularPlane :=
    fun z hz => gaussRegularPlane_reflection z hz
  have hF : ContDiffOn ℝ 2 F gaussRegularPlane := by
    intro z hz
    exact Complex.ofRealCLM.contDiff.contDiffAt.comp z
      ((hT.1 z hz).contDiffAt (gaussRegularPlane_isOpen.mem_nhds hz)) |>.contDiffWithinAt
  have hUreg := hregMap
  have hTref : ContDiffOn ℝ 2 (fun z => T (1 - z)) gaussRegularPlane := by
    intro z hz
    have hAt := (hT.1 _ (hUreg z hz)).contDiffAt
      (gaussRegularPlane_isOpen.mem_nhds (hUreg z hz))
    have hmap : ContDiffAt ℝ 2 (fun w => 1 - w) z := by fun_prop
    exact (hAt.comp z hmap).contDiffWithinAt
  refine ⟨hTref, ?_⟩
  intro z hz
  have hz' := hUreg z hz
  have hsecond := wirtingerZ_second_reflection gaussRegularPlane_isOpen
    hregMap hF hz hz'
  have hfirst := wirtingerZ_reflection
    (((hF _ hz').contDiffAt
      (gaussRegularPlane_isOpen.mem_nhds hz')).differentiableAt (by norm_num))
  have hfirst' : wirtingerZ F (1 - z) = -wirtingerZ U z := by
    aesop
  have hPDE := hT.2 _ hz'
  have hden : (1 - z) * (1 - (1 - z)) = z * (1 - z) := by ring
  have hcoef : c - (1 - z) * (a + b + 1) =
      -(((1 + a + b - c)) - z * (a + b + 1)) := by
    ring
  have hcoeffmul :
      (c - (1 - z) * (a + b + 1)) /
          (z * (1 - z)) * (-wirtingerZ U z) =
        (((1 + a + b - c)) - z * (a + b + 1)) /
          (z * (1 - z)) * wirtingerZ U z := by
    ring
  rw [← hsecond, hfirst', hden, hcoeffmul] at hPDE
  simpa [F, U] using hPDE

end DOZZ.Proofs
