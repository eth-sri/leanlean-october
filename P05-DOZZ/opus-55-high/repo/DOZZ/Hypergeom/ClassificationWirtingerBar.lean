/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ClassificationWirtinger

/-! The conjugate Wirtinger operator and its product rule. -/

@[expose] public section

namespace DOZZ.Proofs

open Filter
open scoped Topology

/-- The conjugate Wirtinger derivative, defined by conjugating the `∂z` operator. -/
noncomputable def wirtingerBar (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  star (wirtingerZ (fun w => star (f w)) z)
section
variable {f g : ℂ → ℂ} {z : ℂ}
section
variable (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z)
include hf hg

/-- The conjugate Wirtinger derivative obeys the product rule for real-differentiable maps. -/
theorem wirtingerBar_mul :
    wirtingerBar (fun w => f w * g w) z =
      f z * wirtingerBar g z + g z * wirtingerBar f z := by
  have hfstar : DifferentiableAt ℝ (fun w => star (f w)) z := by
    have hclm :=
      Complex.differentiable_conj.differentiableAt (x := f z)
    exact hclm.comp z hf
  have hgstar : DifferentiableAt ℝ (fun w => star (g w)) z := by
    have hclm :=
      Complex.differentiable_conj.differentiableAt (x := g z)
    exact hclm.comp z hg
  have hmul := wirtingerZ_mul hfstar hgstar
  have hfun : (fun w => star (f w * g w)) =
      (fun w => star (f w) * star (g w)) := by
    simp
  unfold wirtingerBar
  simp_all

/-- The conjugate Wirtinger derivative is additive on real-differentiable maps. -/
theorem wirtingerBar_add :
    wirtingerBar (fun w => f w + g w) z = wirtingerBar f z + wirtingerBar g z := by
  have hfstar : DifferentiableAt ℝ (fun w => star (f w)) z := by
    have hclm :=
      Complex.differentiable_conj.differentiableAt (x := f z)
    exact hclm.comp z hf
  have hgstar : DifferentiableAt ℝ (fun w => star (g w)) z := by
    have hclm :=
      Complex.differentiable_conj.differentiableAt (x := g z)
    exact hclm.comp z hg
  have hfun : (fun w => star (f w + g w)) =
      (fun w => star (f w) + star (g w)) := by
    simp
  unfold wirtingerBar
  rw [hfun, wirtingerZ_add hfstar hgstar]
  simp

/-- The conjugate Wirtinger derivative is unchanged by local equality of differentiable maps. -/
theorem wirtingerBar_congr_of_eventuallyEq (hfg : f =ᶠ[𝓝 z] g) : wirtingerBar f z = wirtingerBar g z := by
  have hfstar : DifferentiableAt ℝ (fun w => star (f w)) z := by
    have hclm :=
      Complex.differentiable_conj.differentiableAt (x := f z)
    exact hclm.comp z hf
  have hgstar : DifferentiableAt ℝ (fun w => star (g w)) z := by
    have hclm :=
      Complex.differentiable_conj.differentiableAt (x := g z)
    exact hclm.comp z hg
  have hstar : (fun w => star (f w)) =ᶠ[𝓝 z] (fun w => star (g w)) := by
    filter_upwards [hfg] with w hw
    simp_all
  have h := wirtingerZ_congr_of_eventuallyEq hfstar hgstar hstar
  unfold wirtingerBar
  simp_all

end

end

/-- The conjugate Wirtinger derivative annihilates a holomorphic function. -/
theorem wirtingerBar_eq_zero_of_differentiableAt {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℂ f z) : wirtingerBar f z = 0 := by
  have hzero := wirtingerZ_star_eq_zero_of_differentiableAt hf
  unfold wirtingerBar
  simp_all

/-- If the conjugate of a real-differentiable map is holomorphic, its conjugate Wirtinger
derivative is the conjugate of the ordinary derivative of that holomorphic map. -/
theorem wirtingerBar_eq_star_deriv_of_star_differentiableAt
    {f h : ℂ → ℂ} {z : ℂ}
    (hh : DifferentiableAt ℂ h z)
    (hfun : (fun w => star (f w)) = h) :
    wirtingerBar f z = star (deriv h z) := by
  unfold wirtingerBar
  rw [hfun, wirtingerZ_eq_deriv_of_differentiableAt hh]

/-- For a function equal to its conjugate pointwise, two conjugate Wirtinger derivatives are the
conjugate of two `∂z` derivatives. -/
  theorem wirtingerBar_wirtingerBar_eq_star_wirtingerZ_wirtingerZ
    {f : ℂ → ℂ} {z : ℂ}
    (hself : (fun w => star (f w)) = f) :
    wirtingerBar (fun w => wirtingerBar f w) z =
      star (wirtingerZ (fun w => wirtingerZ f w) z) := by
  unfold wirtingerBar
  have hinner : (fun w => star (wirtingerBar f w)) = wirtingerZ f := by
    funext w
    simp only [wirtingerBar, star_star]
    rw [hself]
  change star (wirtingerZ (fun w => star (wirtingerBar f w)) z) = _
  rw [hinner]

end DOZZ.Proofs
