module

public import NearlyMinimax.SaddleAsymptotics

@[expose] public section

open Filter
open scoped Topology
namespace NearlyMinimax

variable {X : Type*} {l : Filter X} {f g M N : X → ℝ} {a b : ℝ}

theorem tendsto_ratio_comp (h₁ : Tendsto (fun x => f x / M x) l (𝓝 a))
    (h₂ : Tendsto (fun x => M x / N x) l (𝓝 b)) (hM : ∀ᶠ x in l, M x ≠ 0) :
    Tendsto (fun x => f x / N x) l (𝓝 (a * b)) := by
  refine (h₁.mul h₂).congr' (hM.mono fun x hx => ?_)
  field_simp

theorem tendsto_ratio_div {f g M : X → ℝ} {a b : ℝ}
    (hf : Tendsto (fun x => f x / M x) l (𝓝 a))
    (hg : Tendsto (fun x => g x / M x) l (𝓝 b)) (hb : b ≠ 0)
    (hM : ∀ᶠ x in l, M x ≠ 0) : Tendsto (fun x => f x / g x) l (𝓝 (a / b)) :=
  (hf.div hg hb).congr' (hM.mono fun _ hx => div_div_div_cancel_right₀ hx _ _)

/-- A negative rescaled logarithmic upper bound forces a nonnegative profile to vanish. -/
theorem tendsto_zero_of_scaled_log_bound {a : ℝ} (hM : Tendsto M l atTop)
    (hg : Tendsto g l (𝓝 a)) (ha : a < 0) (hf : ∀ᶠ x in l, 0 ≤ f x)
    (h : ∀ᶠ x in l, Real.log (f x) ≤ g x * M x) : Tendsto f l (𝓝 0) :=
  squeeze_zero' hf (h.mono fun _ => Real.le_exp_of_log_le)
    (Real.tendsto_exp_atBot.comp (hg.neg_mul_atTop ha hM))

section
variable (hM : Tendsto M l atTop)
    (hf : Tendsto (fun x => f x / M x) l (𝓝 a))
include hM hf

theorem tendsto_atTop_of_div_positive (ha : 0 < a) : Tendsto f l atTop :=
  (hM.atTop_mul_pos ha hf).congr' <|
    (hM.eventually (eventually_gt_atTop 0)).mono fun x hx => mul_div_cancel₀ _ hx.ne'

theorem tendsto_atBot_of_div_negative (ha : a < 0) : Tendsto f l atBot :=
  (hM.atTop_mul_neg ha hf).congr' <|
    (hM.eventually (eventually_gt_atTop 0)).mono fun x hx => mul_div_cancel₀ _ hx.ne'

end

/-- A positive profile and its asymptotic logarithmic rate relative to `M`. -/
structure LogSlope (l : Filter X) (M f : X → ℝ) (a : ℝ) : Prop where
  pos : ∀ᶠ x in l, 0 < f x
  limit : Tendsto (fun x => Real.log (f x) / M x) l (𝓝 a)

namespace LogSlope

section
variable (hf : LogSlope l M f a)
include hf

protected theorem congr (h : f =ᶠ[l] g) : LogSlope l M g a :=
  ⟨h.mp (hf.pos.mono fun _ hp he => he ▸ hp), hf.limit.congr' (h.mono fun _ he => by rw [he])⟩

protected theorem mul (hg : LogSlope l M g b) :
    LogSlope l M (fun x => f x * g x) (a + b) := by
  refine ⟨hf.pos.mp (hg.pos.mono fun _ hy hx => mul_pos hx hy), (hf.limit.add hg.limit).congr' ?_⟩
  filter_upwards [hf.pos, hg.pos] with x hx hy
  rw [Real.log_mul hx.ne' hy.ne', add_div]

protected theorem div (hg : LogSlope l M g b) :
    LogSlope l M (fun x => f x / g x) (a - b) := by
  refine ⟨hf.pos.mp (hg.pos.mono fun _ hy hx => div_pos hx hy), (hf.limit.sub hg.limit).congr' ?_⟩
  filter_upwards [hf.pos, hg.pos] with x hx hy
  rw [Real.log_div hx.ne' hy.ne', sub_div]

protected theorem rpow (r : ℝ) :
    LogSlope l M (fun x => f x ^ r) (r * a) := by
  refine ⟨hf.pos.mono (fun _ hx => Real.rpow_pos_of_pos hx _), (hf.limit.const_mul r).congr' ?_⟩
  filter_upwards [hf.pos] with x hx
  rw [Real.log_rpow hx, mul_div_assoc]

protected theorem pow (r : ℕ) :
    LogSlope l M (fun x => f x ^ r) (r * a) := by
  simpa only [Real.rpow_natCast] using hf.rpow r

end

protected theorem exp (hf : Tendsto (fun x => f x / M x) l (𝓝 a)) :
    LogSlope l M (Real.exp ∘ f) a := ⟨Eventually.of_forall fun _ => Real.exp_pos _, by simpa using hf⟩

section
variable (hM : Tendsto M l atTop)
include hM

protected theorem const (ha : 0 < a) :
    LogSlope l M (fun _ => a) 0 :=
  ⟨Eventually.of_forall fun _ => ha, by
    simpa only [div_eq_mul_inv, Pi.inv_apply, mul_zero] using hM.inv_tendsto_atTop.const_mul (Real.log a)⟩

protected theorem self : LogSlope l M M 0 := by
  refine ⟨hM.eventually (eventually_gt_atTop 0), ?_⟩
  simpa [Function.comp_def] using Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hM

/-- Multiplication by a polynomial-scale profile does not alter the exponential rate. -/
protected theorem of_poly (p : ℕ) (ha : 0 < a)
    (hf : Tendsto (fun x => f x / (M x)^p) l (𝓝 a)) : LogSlope l M f 0 := by
  have hp := hM.eventually (eventually_gt_atTop 0)
  have hpos : ∀ᶠ x in l, 0 < f x := by
    filter_upwards [hp, hf.eventually (lt_mem_nhds ha)] with x hx hfx
    exact (div_pos_iff_of_pos_right (pow_pos hx _)).mp hfx
  refine ⟨hpos, ?_⟩
  have hh := ((Real.continuousAt_log ha.ne').tendsto.comp hf).mul hM.inv_tendsto_atTop
  have hg := hh.add ((LogSlope.self hM).limit.const_mul (p : ℝ))
  simp only [mul_zero, add_zero] at hg
  refine hg.congr' ?_
  filter_upwards [hpos, hp] with x hx hMx
  simp only [Function.comp_apply, Pi.inv_apply]
  rw [Real.log_div hx.ne' (pow_pos hMx p).ne', Real.log_pow]
  simp only [div_eq_mul_inv]
  ring

end

section
variable (hf : LogSlope l M f a) (hM : Tendsto M l atTop)
include hf hM

protected theorem tends_zero (ha : a < 0) :
    Tendsto f l (𝓝 0) :=
  (Real.tendsto_exp_atBot.comp (tendsto_atBot_of_div_negative hM hf.limit ha)).congr'
    (hf.pos.mono fun _ => Real.exp_log)

protected theorem tends_top (ha : 0 < a) :
    Tendsto f l atTop :=
  (Real.tendsto_exp_atTop.comp (tendsto_atTop_of_div_positive hM hf.limit ha)).congr'
    (hf.pos.mono fun _ => Real.exp_log)

end

end LogSlope
end NearlyMinimax
