module
public import Mathlib.Tactic

@[expose] public section
namespace DensityStrip

/-- Certify an affine inequality throughout a length window by checking
its endpoints. The last identity only tests affineness; it is a ring goal. -/
theorem affine_window {a b : ℝ} {f g : ℝ → ℝ} (ha : f a ≤ g a) (hb : f b ≤ g b)
    (h : ∀ x, (g x-f x)*(b-a)=(b-x)*(g a-f a)+(x-a)*(g b-f b)) :
    ∀ x, a ≤ x → x ≤ b → f x ≤ g x := by
  intro x hax hxb
  rcases lt_or_eq_of_le (hax.trans hxb) with hab|hab
  · have hh : 0 ≤ (g x-f x)*(b-a) := (h x).symm ▸ add_nonneg
      (mul_nonneg (sub_nonneg.mpr hxb) (sub_nonneg.mpr ha)) (mul_nonneg (sub_nonneg.mpr hax) (sub_nonneg.mpr hb))
    exact sub_nonneg.mp (nonneg_of_mul_nonneg_left hh (sub_pos.mpr hab))
  · simpa only [le_antisymm (hxb.trans_eq hab.symm) hax] using ha

/-- Positivity certificates in the Bernstein basis on a closed interval.
Every basis product is nonnegative, so `linarith` can combine them after
clearing denominators. -/
theorem sq_span {a x : ℝ} (_ : a ≤ x) : 0 ≤ (x-a)^2 := sq_nonneg _

macro "quadratic_on " hl:term ", " hr:term : tactic => `(tactic|
  nlinarith only [$hl,$hr,sq_span $hl, mul_nonneg (sub_nonneg.mpr $hl) (sub_nonneg.mpr $hr),
    sq_span $hr])

end DensityStrip
