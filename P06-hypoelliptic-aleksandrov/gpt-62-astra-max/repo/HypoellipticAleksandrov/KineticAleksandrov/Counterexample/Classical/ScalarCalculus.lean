module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Classical.Angle

/-! # Kinetic similarity calculus on a position half-plane -/

@[expose] public noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Angular
open Set Real
open scoped Topology ContDiff

/-- Anisotropic radius of a positive position coordinate. -/
def scale (x : ℝ) := x ^ (1/3 : ℝ)

theorem scale_pos {x : ℝ} (hx : 0 < x) : 0 < scale x := rpow_pos_of_pos hx _

theorem cube_scale {x : ℝ} (hx : 0 < x) : scale x ^ 3 = x := by
  rw [scale, ← rpow_natCast, ← rpow_mul hx.le]; norm_num

private theorem hasDerivAt_scale {x : ℝ} (hx : 0 < x) :
    HasDerivAt scale (1 / (3 * scale x ^ 2)) x := by
  convert hasDerivAt_rpow_const (p := 1/3) (Or.inl hx.ne') using 1
  · rfl
  rw [rpow_sub hx, rpow_one]
  change 1 / (3 * scale x ^ 2) = 1/3 * (scale x / x)
  have hp := scale_pos hx
  field_simp
  linarith [cube_scale hx]

/-- Homogeneous lift on `x > 0`. -/
def chart (α : ℝ) (f : ℝ → ℝ) (x v : ℝ) := scale x ^ α * f (v / scale x)

private theorem chart_drv (α x v : ℝ) {f : ℝ → ℝ} (hf : Differentiable ℝ f) :
    HasDerivAt (chart α f x) ((scale x^α / scale x) * deriv f (v/scale x)) v := by
  convert ((hf _).hasDerivAt.comp v ((hasDerivAt_id v).div_const (scale x))).const_mul (scale x^α) using 1
  · rfl
  · dsimp; ring

theorem chart_deriv2 {α x : ℝ} {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (v : ℝ) :
    deriv (deriv (chart α f x)) v = (scale x^α / scale x^2) * deriv (deriv f) (v / scale x) := by
  rw [show deriv (chart α f x) = _ from funext (fun z => (chart_drv α x z (hf.differentiable (by simp))).deriv)]
  have hd := (((contDiff_infty_iff_deriv.mp hf).2.differentiable (by simp) _).hasDerivAt.comp v
    ((hasDerivAt_id v).div_const (scale x))).const_mul (scale x^α / scale x)
  convert hd.deriv using 1
  · rfl
  · dsimp; ring

theorem chart_transport {α x : ℝ} (v : ℝ) {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hx : 0 < x) :
    v * deriv (fun y => chart α f y v) x = (scale x^α / scale x^2) * drift α f (v/scale x) := by
  have hp := scale_pos hx
  have hr := hasDerivAt_scale hx
  have hq := (hasDerivAt_const x v).div hr hp.ne'
  have hd := (hr.rpow_const (p := α) (Or.inl hp.ne')).mul
    (((hf.differentiable (by simp) _).hasDerivAt).comp x hq)
  rw [show deriv (fun y => chart α f y v) x = _ from hd.deriv, rpow_sub hp, rpow_one, drift]
  dsimp
  field_simp; ring

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Angular
