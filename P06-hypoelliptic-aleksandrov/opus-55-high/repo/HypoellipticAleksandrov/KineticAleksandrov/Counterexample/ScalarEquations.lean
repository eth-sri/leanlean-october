module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarReduction
import Mathlib.Tactic

/-!
# The equations for both scalar pieces

Unconditional consequences of the proved M and transformed U equations.
-/

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open Set
open scoped ContDiff

/-- The cubic substitution is smooth on the whole real line. -/
theorem contDiff_scalarCubic (a : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (scalarCubic a) := by
  unfold scalarCubic
  fun_prop

variable (gamma : ScalarGamma) (Lam s : ℝ)

/-- The positive piece satisfies the source equation with diffusivity Lam. -/
theorem Fplus_ode  (hLam : 0 < Lam) (hs : 0 < s) :
    Lam * deriv (deriv (Fplus gamma Lam)) s -
      s ^ 2 / 3 * deriv (Fplus gamma Lam) s + gamma.1 * s * Fplus gamma Lam s = 0 := by
  have hz : 0 < scalarCubic Lam s :=
    div_pos (pow_pos hs 3) (mul_pos (by norm_num) hLam)
  have hc : ContDiffAt ℝ 2 _ _ :=
    ((Kummer.contDiffOn_UNr gamma.negative).contDiffAt (isOpen_Ioi.mem_nhds hz)).of_le
      (by norm_num)
  exact scalarCubic_ode _ gamma.1 Lam s hLam.ne' hc
    (by simpa only [ScalarGamma.negative, neg_mul, sub_neg_eq_add] using
      Kummer.UNr_ode gamma.negative _ hz)

/-- Constant linear combinations preserve the scalar ODE. -/
theorem scalar_ode_linear_combination (f g : ℝ → ℝ) (gamma a c d s : ℝ)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hfo : a * deriv (deriv f) s - s ^ 2 / 3 * deriv f s + gamma * s * f s = 0)
    (hgo : a * deriv (deriv g) s - s ^ 2 / 3 * deriv g s + gamma * s * g s = 0) :
    a * deriv (deriv (fun t => c * f t + d * g t)) s -
      s ^ 2 / 3 * deriv (fun t => c * f t + d * g t) s +
        gamma * s * (c * f s + d * g s) = 0 := by
  have hfirst (t : ℝ) : HasDerivAt (fun w => c * f w + d * g w)
      (c * deriv f t + d * deriv g t) t := by
    simpa only [Pi.add_def] using
      ((hf.differentiable (by norm_num) t).hasDerivAt.const_mul c).add
        ((hg.differentiable (by norm_num) t).hasDerivAt.const_mul d)
  have he : deriv _ =
      fun t => c * deriv f t + d * deriv g t := funext (fun t => (hfirst t).deriv)
  have hsecond : HasDerivAt (fun t => c * deriv f t + d * deriv g t)
      (c * deriv (deriv f) s + d * deriv (deriv g) s) s := by
    simpa only [Pi.add_def] using
      ((hf.differentiable_deriv_two s).hasDerivAt.const_mul c).add
        ((hg.differentiable_deriv_two s).hasDerivAt.const_mul d)
  rw [he, hsecond.deriv]
  grind

/-- The negative piece is smooth, including at zero. -/
theorem contDiff_Fminus  (Lam : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (Fminus gamma Lam) := by
  have hm (a : ℝ) (b : Kummer.Pos) : ContDiff ℝ (⊤ : ℕ∞) _ :=
    (Kummer.analyticOnNhd_M a b).contDiff
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => s ^ 3 / 9) := by fun_prop
  exact (contDiff_const.mul ((hm _ _).comp hc)).add
    (((contDiff_const.mul contDiff_id).div_const _).mul ((hm _ _).comp hc))

/-- The signed negative-s piece satisfies the source equation with diffusivity one. -/
theorem Fminus_ode  :
    deriv (deriv (Fminus gamma Lam)) s - s ^ 2 / 3 * deriv (Fminus gamma Lam) s +
      gamma.1 * s * Fminus gamma Lam s = 0 := by
  let f  := fun t => Kummer.M (-gamma.1) Kummer.b23 (scalarCubic 1 t)
  let g  := fun t => t *
    Kummer.M (1 / 3 - gamma.1) Kummer.b43 (scalarCubic 1 t)
  have hm (a : ℝ) (b : Kummer.Pos) : ContDiff ℝ 2 _ :=
    (Kummer.analyticOnNhd_M a b).contDiff
  have hc : ContDiff ℝ 2 _ := (contDiff_scalarCubic 1).of_le (by norm_num)
  have hf : ContDiff ℝ 2 f := (hm _ _).comp hc
  have hg : ContDiff ℝ 2 g := contDiff_id.mul ((hm _ _).comp hc)
  have hfo := scalarCubic_ode (Kummer.M _ Kummer.b23) gamma.1 1 s
    one_ne_zero (hm _ _).contDiffAt
    (by simpa only [Kummer.b23, neg_mul, sub_neg_eq_add] using
      Kummer.M_ode (-gamma.1) Kummer.b23 _)
  have hgo := scalarCubic_second_ode (Kummer.M _ Kummer.b43)
    gamma.1 1 s one_ne_zero (hm _ _)
    (by simpa only [Kummer.b43] using
      Kummer.M_ode _ Kummer.b43 _)
  have he : Fminus gamma Lam = fun t => gammaA gamma.1 * f t +
      (gammaB gamma.1 / Real.rpow (9 * Lam) (1 / 3)) * g t := by
    funext t
    dsimp only [Fminus, f, g, scalarCubic]
    ring
  rw [he]
  simpa only [one_mul] using scalar_ode_linear_combination f g gamma.1 1
    _ _ s hf hg hfo hgo

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
