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
  have hcomp := hf.hasFDerivAt.comp z hmap
  have hfd : fderiv ℝ (fun w => f (1 - w)) z =
      (fderiv ℝ f (1 - z)).comp (-ContinuousLinearMap.id ℝ ℂ) := by
    simpa only [Function.comp_def, hmap.fderiv] using hcomp.fderiv
  simp only [wirtingerZ, hfd]
  simp
  ring

private theorem gaussRegularPlane_reflection (z : ℂ)
    (hz : z ∈ gaussRegularPlane) : 1 - z ∈ gaussRegularPlane := by
  constructor
  · intro h
    apply hz.2
    exact Eq.symm (sub_eq_zero.mp h)
  · intro h
    apply hz.1
    simp_all

/-- The second `∂z` derivative is invariant under reflection on an open domain stable
under `z ↦ 1-z`. -/
theorem wirtingerZ_second_reflection
    {U : Set ℂ} (hU : IsOpen U)
    (hreflect : ∀ w ∈ U, 1 - w ∈ U)
    {f : ℂ → ℂ} (hf : ContDiffOn ℝ 2 f U)
    {z : ℂ} (hz : z ∈ U) (hz' : 1 - z ∈ U) :
    wirtingerZ (fun w => wirtingerZ (fun v => f (1 - v)) w) z =
      wirtingerZ (fun w => wirtingerZ f w) (1 - z) := by
  have hAt := hf (1 - z) hz' |>.contDiffAt (hU.mem_nhds hz')
  have hG := differentiableAt_wirtingerZ_of_contDiffAt_two hAt
  have hGcomp  :=
      hG.comp z ((differentiableAt_const 1).sub differentiableAt_id)
  have heq : (fun w => wirtingerZ (fun v => f (1 - v)) w) =ᶠ[𝓝 z]
      (fun w => -wirtingerZ f (1 - w)) := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact wirtingerZ_reflection
      (((hf (1 - w) (hreflect w hw)).contDiffAt
        (hU.mem_nhds (hreflect w hw))).differentiableAt (by norm_num))
  have hminus := wirtingerZ_reflection hG
  have hsub := wirtingerZ_sub (differentiableAt_const (0 : ℂ)) hGcomp
  have hzero : wirtingerZ (fun _ : ℂ => (0 : ℂ)) z = 0 := by simp [wirtingerZ]
  refine (wirtingerZ_congr_of_eventuallyEq (differentiableAt_wirtingerZ_of_contDiffAt_two (hAt.comp z (by fun_prop))) hGcomp.neg heq).trans ?_
  calc
    _ = wirtingerZ (fun w => 0 - wirtingerZ f (1 - w)) z := by
      congr 1
      funext w
      simp
    _ = wirtingerZ (fun w => 0) z -
        wirtingerZ (fun w => wirtingerZ f (1 - w)) z := hsub
    _ = _ := by
      simp [*]

/-- Reflection preserves the real-solution condition `IsRealGaussSolution` after
changing `c` to `1 + a + b - c`. -/
theorem realGaussSolution_reflection
    (a b c : ℝ) (T : ℂ → ℝ) (hT : IsRealGaussSolution a b c T) :
    IsRealGaussSolution a b (1 + a + b - c) (fun z => T (1 - z)) := by
  let F := fun z => (T z : ℂ)
  let U := fun z => ((T (1 - z) : ℝ) : ℂ)
  have hregMap := gaussRegularPlane_reflection
  have hF : ContDiffOn ℝ 2 F gaussRegularPlane := by
    intro z hz
    change ContDiffWithinAt ℝ 2 (Complex.ofRealCLM ∘ T) gaussRegularPlane z
    exact Complex.ofRealCLM.contDiff.contDiffAt.comp z
      ((hT.1 z hz).contDiffAt (gaussRegularPlane_isOpen.mem_nhds hz)) |>.contDiffWithinAt
  have hUreg := hregMap
  refine ⟨(by
    intro z hz
    refine (((hT.1 (1 - z) (hUreg z hz)).contDiffAt
      (gaussRegularPlane_isOpen.mem_nhds (hUreg z hz))).comp z ?_).contDiffWithinAt
    fun_prop), ?_⟩
  intro z hz
  have hz' := hUreg z hz
  have hfirst := wirtingerZ_reflection
    (((hF (1 - z) hz').contDiffAt
      (gaussRegularPlane_isOpen.mem_nhds hz')).differentiableAt (by norm_num))
  have hfirst' : wirtingerZ F (1 - z) = -wirtingerZ U z := by
    dsimp [F, U] at hfirst ⊢
    linear_combination hfirst
  have hPDE := hT.2 (1 - z) hz'
  have hden : (1 - z) * (1 - (1 - z)) = z * (1 - z) := by ring
  have hcoef : c - (1 - z) * (a + b + 1) =
      -(((1 + a + b - c : ℝ) : ℂ) - z * (a + b + 1)) := by
    push_cast
    ring
  have hcoeffmul :
      ((c : ℂ) - (1 - z) * ((a : ℂ) + b + 1)) /
          (z * (1 - z)) * (-wirtingerZ U z) =
        (((1 + a + b - c : ℝ) : ℂ) - z * ((a : ℂ) + b + 1)) /
          (z * (1 - z)) * wirtingerZ U z := by
    rw [hcoef]
    ring
  rw [← (wirtingerZ_second_reflection gaussRegularPlane_isOpen
    hregMap hF hz hz'), hfirst'] at hPDE
  rw [hden] at hPDE
  rw [hcoeffmul] at hPDE
  simp_all [F, U]

end DOZZ.Proofs
