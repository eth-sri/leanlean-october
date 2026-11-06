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


/-- Pulling a real differentiable map back by `z ↦ 1-z` negates its `∂z` derivative. -/
theorem wirtingerZ_reflection {f : ℂ → ℂ} {z}
    (hf : DifferentiableAt ℝ f (1 - z)) :
    wirtingerZ (fun w => f (1 - w)) z = -wirtingerZ f (1 - z) := by
  have hasFDerivAt_reflection : HasFDerivAt (𝕜 := ℝ) (fun w : ℂ => 1 - w) (-ContinuousLinearMap.id ℝ ℂ) z := by
    convert ((show HasDerivAt (fun w => 1 - w) (-1) z by simpa using (hasDerivAt_id z).const_sub (1 : ℂ)).hasFDerivAt.restrictScalars ℝ) using 1
    ext w
    simp
  have hmap := hasFDerivAt_reflection
  rw [wirtingerZ, wirtingerZ, (show fderiv ℝ (fun w => f (1 - w)) z = (fderiv ℝ f (1 - z)).comp (-ContinuousLinearMap.id ℝ ℂ) by simpa only [Function.comp_def, hmap.fderiv] using (hf.hasFDerivAt.comp z hmap).fderiv)]
  simp only [ContinuousLinearMap.comp_apply, neg_apply, ContinuousLinearMap.id_apply,
    map_neg]
  ring



/-- Reflection preserves the real-solution condition `IsRealGaussSolution` after
changing `c` to `1 + a + b - c`. -/
theorem realGaussSolution_reflection
    a b c T (hT : IsRealGaussSolution a b c T) :
    IsRealGaussSolution a b (1 + a + b - c) (fun z => T (1 - z)) := by
  have wirtingerZ_second_reflection {U} (hU : IsOpen U) (hreflect : ∀ w ∈ U, 1 - w ∈ U) {f : ℂ → ℂ} (hf : ContDiffOn ℝ 2 f U) {z} (hz : z ∈ U) (hz' : 1 - z ∈ U) : wirtingerZ (fun w => wirtingerZ (fun v => f (1 - v)) w) z = wirtingerZ (fun w => wirtingerZ f w) (1 - z) := by
    have hAt := hf (1 - z) hz' |>.contDiffAt (hU.mem_nhds hz')
    have hG := differentiableAt_wirtingerZ_of_contDiffAt_two hAt
    have hGcomp := hG.comp z ((differentiableAt_const (1 : ℂ)).sub differentiableAt_id)
    have hcalc : wirtingerZ (fun w => -wirtingerZ f (1 - w)) z =
        wirtingerZ (fun w => wirtingerZ f w) (1 - z) := by
      calc
        _ = wirtingerZ (fun w => (0 : ℂ) - wirtingerZ f (1 - w)) z := by
          congr 1
          funext w
          simp
        _ = wirtingerZ (fun w => (0 : ℂ)) z -
            wirtingerZ (fun w => wirtingerZ f (1 - w)) z := (wirtingerZ_sub (differentiableAt_const (0 : ℂ)) hGcomp)
        _ = wirtingerZ (fun w => wirtingerZ f w) (1 - z) := by
          rw [(show wirtingerZ (fun _ : ℂ => (0 : ℂ)) z = 0 by simp [wirtingerZ]), (wirtingerZ_reflection hG)]
          ring
    exact (wirtingerZ_congr_of_eventuallyEq (differentiableAt_wirtingerZ_of_contDiffAt_two (hAt.comp z (by fun_prop))) hGcomp.neg (by filter_upwards [hU.mem_nhds hz] with w hw; exact wirtingerZ_reflection (((hf (1 - w) (hreflect w hw)).contDiffAt (hU.mem_nhds (hreflect w hw))).differentiableAt (by norm_num)))).trans hcalc
  have gaussRegularPlane_reflection z (hz : z ∈ gaussRegularPlane) : 1 - z ∈ gaussRegularPlane := by
    change z ≠ 0 ∧ z ≠ 1 at hz
    change 1 - z ≠ 0 ∧ 1 - z ≠ 1
    constructor
    · intro h
      apply hz.2
      exact (sub_eq_zero.mp h).symm
    · intro h
      apply hz.1
      simpa using congrArg (fun w : ℂ => (1 : ℂ) - w) h
  let F : ℂ → ℂ := fun z => (T z : ℂ)
  let U : ℂ → ℂ := fun z => ((T (1 - z) : ℝ) : ℂ)
  have hregMap : ∀ z ∈ gaussRegularPlane, 1 - z ∈ gaussRegularPlane :=
    fun z hz => gaussRegularPlane_reflection z hz
  have hF : ContDiffOn ℝ 2 F gaussRegularPlane := by
    intro z hz
    change ContDiffWithinAt ℝ 2 (Complex.ofRealCLM ∘ T) gaussRegularPlane z
    exact Complex.ofRealCLM.contDiff.contDiffAt.comp z
      ((hT.1 z hz).contDiffAt (gaussRegularPlane_isOpen.mem_nhds hz)) |>.contDiffWithinAt
  have hUreg := hregMap
  refine ⟨(by intro z hz; change ContDiffWithinAt ℝ 2 (fun w => T (1 - w)) gaussRegularPlane z; exact (((hT.1 (1 - z) (hUreg z hz)).contDiffAt (gaussRegularPlane_isOpen.mem_nhds (hUreg z hz))).comp z (by fun_prop)).contDiffWithinAt), ?_⟩
  intro z hz
  have hz' := hUreg z hz
  have hfirst := wirtingerZ_reflection
    (((hF (1 - z) hz').contDiffAt
      (gaussRegularPlane_isOpen.mem_nhds hz')).differentiableAt (by norm_num))
  have hPDE := hT.2 (1 - z) hz'
  rw [← (wirtingerZ_second_reflection gaussRegularPlane_isOpen hregMap hF hz hz'), (show wirtingerZ F (1 - z) = -wirtingerZ U z by dsimp [F, U] at hfirst ⊢; linear_combination hfirst)] at hPDE
  rw [(show (1 - z) * (1 - (1 - z)) = z * (1 - z) by ring)] at hPDE
  rw [(show ((c : ℂ) - (1 - z) * ((a : ℂ) + b + 1)) / (z * (1 - z)) * (-wirtingerZ U z) = (((1 + a + b - c : ℝ) : ℂ) - z * ((a : ℂ) + b + 1)) / (z * (1 - z)) * wirtingerZ U z by rw [(show (c : ℂ) - (1 - z) * ((a : ℂ) + b + 1) = -(((1 + a + b - c : ℝ) : ℂ) - z * ((a : ℂ) + b + 1)) by push_cast; ring)]; ring)] at hPDE
  simpa [F, U] using hPDE

end DOZZ.Proofs
