module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ClockJacobian
public import Mathlib.Analysis.Calculus.Deriv.Abs
public import Mathlib.Analysis.Calculus.Deriv.Inv

/-! # Literal clock coefficients and their local calculus

The coefficient formulas are asserted on `|y| < 1`; no global ellipticity is
claimed for the raw total division formulas outside that source region.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous

section
variable {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam) (c : Clock)
    (A : SmoothAutonomous lam Lam) (a : ℝ → ℝ → ℝ) (e : Point) (s y : ℝ)

include c a e s y in
/-- The normalized autonomous diffusion, independent of the old time coordinate `z`. -/
def Clock.diffusion : ℝ :=
  |c.vbar| * a (e.position 0 + c.vbar * c.r ^ 2 * s) (c.vbar + c.r * y) /
    |c.vbar + c.r * y|

include c in
/-- The normalized transport drift from `e:clock-coefficients`. -/
def Clock.drift (y : ℝ) : ℝ := |c.vbar| * y / |c.vbar + c.r * y|

/-- Uniform denominator bounds in the entire cutoff region. -/
theorem Clock.normalized_abs_bounds {y : ℝ} (hy : |y| < 1) :
    |c.vbar| / 3 ≤ |c.vbar + c.r * y| ∧
      |c.vbar + c.r * y| ≤ 5 * |c.vbar| / 3 := by
  have hmul : |c.r * y| ≤ c.r := by
    rw [abs_mul, abs_of_pos c.positive]
    exact mul_le_of_le_one_right c.positive.le hy.le
  have hl := abs_sub_abs_le_abs_sub c.vbar (c.vbar + c.r * y)
  have heq : |c.vbar - (c.vbar + c.r * y)| = |c.r * y| := by
    simp
  rw [heq] at hl
  constructor <;> linarith only [hmul, (abs_add_le c.vbar (c.r * y)), hl, c.radius]

/-- The denominator cannot vanish on the cutoff region. -/
theorem Clock.normalized_ne_zero {y : ℝ} (hy : |y| < 1) :
    c.vbar + c.r * y ≠ 0 := by
  apply abs_pos.mp
  linarith only [((c.normalized_abs_bounds hy).1), (abs_pos.mpr c.nonzero)]

/-- Smoothness of the raw diffusion on the source cutoff region. -/
theorem Clock.diffusion_contDiffAt (q : ℝ × ℝ)
    (hq : c.vbar + c.r * q.2 ≠ 0) :
    ContDiffAt ℝ (⊤ : ℕ∞) (Function.uncurry (c.diffusion A.a e)) q := by
  have hs : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ =>
      (e.position 0 + c.vbar * c.r ^ 2 * q.1, c.vbar + c.r * q.2)) :=
    (contDiff_const.add (contDiff_const.mul contDiff_fst)).prodMk
      (contDiff_const.add (contDiff_const.mul contDiff_snd))
  exact (contDiffAt_const.mul (A.smooth.comp hs).contDiffAt).div
    ((contDiffAt_const.add (contDiffAt_const.mul contDiffAt_snd)).abs hq)
    (abs_ne_zero.mpr hq)

include hlam hLam in
/-- The normalized diffusion obeys the source bounds on `|y| < 1`. -/
theorem Clock.diffusion_bounds (hy : |y| < 1) :
    3 * lam / 5 ≤ c.diffusion A.a e s y ∧ c.diffusion A.a e s y ≤ 3 * Lam := by
  have hv := abs_pos.mpr c.nonzero
  have hd := abs_pos.mpr (c.normalized_ne_zero hy)
  have hb := c.normalized_abs_bounds hy
  have ha := A.bounds (e.position 0 + c.vbar * c.r ^ 2 * s) (c.vbar + c.r * y)
  change 3 * lam / 5 ≤ _ / _ ∧ _ / _ ≤ 3 * Lam
  constructor
  · rw [le_div_iff₀ hd]
    nlinarith only [(mul_le_mul_of_nonneg_left hb.2 hlam.le), (mul_le_mul_of_nonneg_left ha.1 hv.le)]
  · rw [div_le_iff₀ hd]
    have h1 := mul_le_mul_of_nonneg_left hb.1 (hlam.trans_le hLam).le
    nlinarith

end

variable (c : Clock) {y : ℝ} (hy : |y| < 1)
include hy

/-- The centre and cutoff-region velocity have the same strict sign. -/
theorem Clock.normalized_sign :
    (0 < c.vbar → 0 < c.vbar + c.r * y) ∧
      (c.vbar < 0 → c.vbar + c.r * y < 0) := by
  have hmul : |c.r * y| ≤ c.r := by
    rw [abs_mul, abs_of_pos c.positive]
    exact mul_le_of_le_one_right c.positive.le hy.le
  have hh := abs_le.mp hmul
  constructor
  · intro hv
    have hr := c.radius
    rw [abs_of_pos hv] at hr
    linarith only [hh.1, hr, hv]
  · intro hv
    have hr := c.radius
    rw [abs_of_neg hv] at hr
    linarith only [hh.2, hr, hv]

/-- The exact derivative formula of the clock drift on the cutoff region. -/
theorem Clock.hasDerivAt_drift :
    HasDerivAt c.drift (c.vbar ^ 2 / (c.vbar + c.r * y) ^ 2) y := by
  have hne := c.normalized_ne_zero hy
  have hs := c.normalized_sign hy
  have ha : HasDerivAt (fun t : ℝ => c.vbar + c.r * t) c.r y := by
    simpa only [mul_one, id_eq] using! ((hasDerivAt_id y).const_mul c.r).const_add c.vbar
  have hn : HasDerivAt (fun t : ℝ => |c.vbar| * t) |c.vbar| y := by
    simpa only [mul_one, id_eq] using! (hasDerivAt_id y).const_mul |c.vbar|
  rcases lt_or_gt_of_ne c.nonzero with hv | hv
  · have hden := (hasDerivAt_abs_neg (hs.2 hv)).comp y ha
    convert! (hn.div hden (abs_ne_zero.mpr hne)) using 1
    simp only [Function.comp_apply]
    rw [abs_of_neg hv, abs_of_neg (hs.2 hv)]
    field_simp
    ring
  · have hden := (hasDerivAt_abs_pos (hs.1 hv)).comp y ha
    convert! (hn.div hden (abs_ne_zero.mpr hne)) using 1
    simp only [Function.comp_apply]
    rw [abs_of_pos hv, abs_of_pos (hs.1 hv)]
    field_simp
    ring

/-- The universal derivative bounds used in case (I). -/
theorem Clock.drift_deriv_bounds :
    (9 / 25 : ℝ) ≤ deriv c.drift y ∧ deriv c.drift y ≤ 9 := by
  rw [(c.hasDerivAt_drift hy).deriv]
  have hb := c.normalized_abs_bounds hy
  have hp := sq_pos_of_ne_zero (c.normalized_ne_zero hy)
  have h1 :=
    pow_le_pow_left₀ (abs_pos.mpr (c.normalized_ne_zero hy)).le hb.2 2
  have h2 :=
    pow_le_pow_left₀ (by positivity) hb.1 2
  simp only [div_pow, mul_pow, sq_abs] at h1 h2
  constructor
  · rw [le_div_iff₀ hp]
    nlinarith only [h1]
  · rw [div_le_iff₀ hp]
    nlinarith only [h2]

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
