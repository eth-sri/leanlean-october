module
/- McColm source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0. -/
public import WeylPort.AFE.NonstationaryPhase
import WeylPort.Analytic.RealLaplace

@[expose] public section

-- Lean 4.34 elaborator compatibility.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-! # The sharp first-derivative integral test in source Lemma 4

The existing foundation theorem supplies the decreasing-quotient case. Scaling
and reflection give the source normalization and both monotonicity directions.
-/

namespace DhimanKadiriQuesadaHerrera2026

open MeasureTheory

section
variable {a b : ℝ} (hab : a < b)
include a b hab
/-- A continuous explicitly supplied derivative gives C¹ on a nondegenerate interval. -/
theorem contDiffOn_one_of_continuous_derivative
    {f f' : ℝ → ℝ} (hd : ∀ x ∈ Set.Icc a b, HasDerivAt f (f' x) x)
    (hc : ContinuousOn f' (Set.Icc a b)) : ContDiffOn ℝ 1 f (Set.Icc a b) := by
  apply (contDiffOn_one_iff_derivWithin (uniqueDiffOn_Icc hab)).mpr
  constructor
  · exact fun x hx => (hd x hx).differentiableAt.differentiableWithinAt
  · apply hc.congr
    intro x hx
    exact (hd x hx).hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc hab x hx)

/-- Source exponential normalization and constant 2 for a decreasing absolute quotient. -/
theorem first_derivative_test_antitone
    {f f' g : ℝ → ℝ} (hd : ∀ x ∈ Set.Icc a b, HasDerivAt f (f' x) x)
    (hc : ContinuousOn f' (Set.Icc a b)) (hg : ContinuousOn g (Set.Icc a b))
    (hn : ∀ x ∈ Set.Icc a b, f' x ≠ 0)
    (hm : AntitoneOn (fun x => |g x / f' x|) (Set.Icc a b)) :
    ‖∫ x in a..b, (g x : ℂ) * Complex.exp (Complex.I * (f x : ℂ))‖ ≤
      2 * |g a / f' a| := by
  let φ : ℝ → ℝ := fun x => f x / (2 * Real.pi)
  have hdφ (x : ℝ) (hx : x ∈ Set.Icc a b) : deriv φ x = f' x / (2 * Real.pi) :=
    ((hd x hx).div_const (2 * Real.pi)).deriv
  have hq (x : ℝ) (hx : x ∈ Set.Icc a b) :
      g x / deriv φ x = (2 * Real.pi) * (g x / f' x) := by
    rw [hdφ x hx, div_div_eq_mul_div]
    ring
  have hqa (x : ℝ) (hx : x ∈ Set.Icc a b) :
      |g x / deriv φ x| = (2 * Real.pi) * |g x / f' x| := by
    rw [hq x hx, abs_mul, abs_of_pos Real.two_pi_pos]
  have hφ := (contDiffOn_one_of_continuous_derivative hab hd hc).div_const (2 * Real.pi)
  have h := nonstationary_interval_bound hab φ g hφ
    (fun x hx => by rw [hdφ x hx]; exact div_ne_zero (hn x hx) Real.two_pi_pos.ne')
    (((hg.div hc hn).const_mul (2 * Real.pi)).congr (fun x hx => hq x hx))
    (by
      intro x hx y hy hxy
      dsimp only
      rw [hqa x hx, hqa y hy]
      exact mul_le_mul_of_nonneg_left (hm hx hy hxy) Real.two_pi_pos.le)
  rw [hqa a (Set.left_mem_Icc.mpr hab.le)] at h
  have he (x : ℝ) : 2 * (Real.pi : ℂ) * Complex.I * (φ x : ℂ) = Complex.I * (f x : ℂ) := by
    dsimp [φ]
    push_cast
    field_simp
  simp_rw [he] at h
  convert h using 1
  field_simp

/-- Reflection gives the sharp endpoint bound for an increasing absolute quotient. -/
theorem first_derivative_test_monotone
    {f f' g : ℝ → ℝ} (hd : ∀ x ∈ Set.Icc a b, HasDerivAt f (f' x) x)
    (hc : ContinuousOn f' (Set.Icc a b)) (hg : ContinuousOn g (Set.Icc a b))
    (hn : ∀ x ∈ Set.Icc a b, f' x ≠ 0)
    (hm : MonotoneOn (fun x => |g x / f' x|) (Set.Icc a b)) :
    ‖∫ x in a..b, (g x : ℂ) * Complex.exp (Complex.I * (f x : ℂ))‖ ≤
      2 * |g b / f' b| := by
  have hmap : Set.MapsTo (fun x : ℝ => -x) (Set.Icc (-b) (-a)) (Set.Icc a b) := by
    pm_8035
  have hdr (x : ℝ) (hx : x ∈ Set.Icc (-b) (-a)) :
      HasDerivAt (fun u => f (-u)) (-f' (-x)) x := by
    simpa only [mul_neg_one, Function.comp_def] using (hd (-x) (hmap hx)).comp x (hasDerivAt_neg x)
  have h := first_derivative_test_antitone (show -b < -a by linarith) hdr
    ((hc.comp continuous_neg.continuousOn hmap).neg)
    (hg.comp continuous_neg.continuousOn hmap)
    (fun x hx => neg_ne_zero.mpr (hn (-x) (hmap hx)))
    (by
      intro x hx y hy hxy
      simp only [div_neg, abs_neg]
      exact hm (hmap hy) (hmap hx) (neg_le_neg hxy))
  pm_298 Function.comp_apply neg_neg div_neg abs_neg h
  rw [intervalIntegral.integral_comp_neg (fun x =>
    (g x : ℂ) * Complex.exp (Complex.I * (f x : ℂ))), neg_neg, neg_neg] at h
  exact h
end

/-- Lemma 4 for either monotonicity direction, with the maximum realized at an endpoint.
The proof also permits vanishing weights, a stronger conclusion than the printed nonzero condition. -/
theorem first_derivative_test {a b : ℝ} (hab : a ≤ b)
    {f f' g : ℝ → ℝ} (hd : ∀ x ∈ Set.Icc a b, HasDerivAt f (f' x) x)
    (hc : ContinuousOn f' (Set.Icc a b)) (hg : ContinuousOn g (Set.Icc a b))
    (hn : ∀ x ∈ Set.Icc a b, f' x ≠ 0)
    (hm : MonotoneOn (fun x => |g x / f' x|) (Set.Icc a b) ∨
      AntitoneOn (fun x => |g x / f' x|) (Set.Icc a b)) :
    ‖∫ x in a..b, (g x : ℂ) * Complex.exp (Complex.I * (f x : ℂ))‖ ≤
      2 * max |g a / f' a| |g b / f' b| := by
  rcases hab.eq_or_lt with rfl | hab
  · simp
  rcases hm with hm | hm
  pm_6575 first_derivative_test_monotone le_max_right
  pm_6575 first_derivative_test_antitone le_max_left

end DhimanKadiriQuesadaHerrera2026
