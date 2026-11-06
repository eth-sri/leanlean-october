module

public import PottsDiscontinuity.Bethe.RatioProducts

/-! # The central simple pole of the spectral factor

The regular part is given by an explicit sinc formula. No singular value
is assigned by a default branch. Its value at zero is exactly c².
-/

public section

open Set Filter Complex
open scoped Topology

namespace PottsDiscontinuity.Bethe

open BetheAnsatz

/-- The regular numerator/sinc profile obtained by removing the central pole. -/
noncomputable def ratioRegularPart (c x : ℝ) : ℝ :=
  ‖1 - (c : ℂ) ^ 2 - z x‖ / |Real.sinc (x / 2)|

section
variable (c : ℝ)
theorem ratio_regularPart_zero  : ratioRegularPart c 0 = c ^ 2 := by
  simp [ratioRegularPart]

theorem ratio_continuousAt_regularPart_zero  : ContinuousAt (ratioRegularPart c) 0 := by
  unfold ratioRegularPart z
  fun_prop (disch := simp)
end

theorem ratio_norm_denominator (x : ℝ) : ‖1 - z x‖ = |x| * |Real.sinc (x / 2)| := by
  by_cases hx : x = 0
  · simp_all
  calc
    ‖1 - z x‖ = ‖z x - 1‖ := norm_sub_rev _ _
    _ = ‖2 * Real.sin (x / 2)‖ := Complex.norm_exp_I_mul_ofReal_sub_one x
    _ = |x| * |Real.sinc (x / 2)| := by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
        Real.sinc_of_ne_zero (by positivity), abs_div, abs_div,
        abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      field_simp

/-- The regular part equals `|x| |M|` throughout the punctured fundamental interval. -/
theorem ratio_regularPart_eq_mul_norm {c x : ℝ}
    (hx : x ∈ Ioo (-Real.pi) Real.pi) (hx0 : x ≠ 0) :
    ratioRegularPart c x = |x| * ‖M c (z x)‖ := by
  have hzx := z_ne_one hx hx0
  have hM : M c (z x) = (1 - (c : ℂ) ^ 2 - z x) / (1 - z x) := by
    unfold M
    grind
  rw [hM, norm_div, ratio_norm_denominator]
  unfold ratioRegularPart
  field_simp

section
variable {ι : Type*} {l : Filter ι}
theorem ratio_norm_div_size_tendsto {c a : ℝ}
    (ha : 0 < a) (N : ι → ℝ) (hN : ∀ i, N i ≠ 0)
    (x : ι → ℝ) (hx : ∀ i, x i ∈ Ioo (-Real.pi) Real.pi) (hxpos : ∀ i, 0 < x i)
    (hxlim : Tendsto x l (𝓝 0)) (hscale : Tendsto (fun i => N i * x i) l (𝓝 a)) :
    Tendsto (fun i => ‖M c (z (x i))‖ / N i) l (𝓝 (c ^ 2 / a)) := by
  have hr := (ratio_continuousAt_regularPart_zero c).tendsto.comp hxlim
  rw [ratio_regularPart_zero] at hr
  have ht := hr.div hscale ha.ne'
  apply ht.congr
  intro i
  dsimp
  rw [ratio_regularPart_eq_mul_norm (hx i) (hxpos i).ne', abs_of_pos (hxpos i)]
  field_simp [(hxpos i).ne', hN i]

/-- In particular, this is the source term (3) after the central root scaling. -/
theorem ratio_scaled_inverse_norm_tendsto {c a : ℝ}
    (hc : 2 < c) (N : ι → ℝ) (x : ι → ℝ)
    (hx : ∀ i, x i ∈ Ioo (-Real.pi) Real.pi) (hxpos : ∀ i, 0 < x i)
    (hxlim : Tendsto x l (𝓝 0)) (hscale : Tendsto (fun i => N i * x i) l (𝓝 a)) :
    Tendsto (fun i => N i * ‖M c (z (x i))‖⁻¹) l (𝓝 (a / c ^ 2)) := by
  have hr := (ratio_continuousAt_regularPart_zero c).tendsto.comp hxlim
  rw [ratio_regularPart_zero] at hr
  have ht := hscale.div hr (pow_ne_zero 2 (by linarith))
  apply ht.congr
  intro i
  dsimp
  rw [ratio_regularPart_eq_mul_norm (hx i) (hxpos i).ne', abs_of_pos (hxpos i)]
  field_simp [(hxpos i).ne', norm_ne_zero_iff.mpr (ratio_M_ne_zero hc (x i))]

/-- The fixed-rank midpoint factor; half-integer root scales give the
Wallis factor `1-1/(4(k+1)²)` after substitution. -/
theorem ratio_midpoint_factor_tendsto {c a b : ℝ}
    (hc : 2 < c) (ha : 0 < a) (hb : 0 < b) (N : ι → ℝ) (hN : ∀ i, N i ≠ 0)
    (x y : ι → ℝ) (hx : ∀ i, x i ∈ Ioo (-Real.pi) Real.pi)
    (hy : ∀ i, y i ∈ Ioo (-Real.pi) Real.pi) (hxpos : ∀ i, 0 < x i) (hypos : ∀ i, 0 < y i)
    (hxlim : Tendsto x l (𝓝 0)) (hylim : Tendsto y l (𝓝 0))
    (hscaleX : Tendsto (fun i => N i * x i) l (𝓝 a))
    (hscaleY : Tendsto (fun i => N i * y i) l (𝓝 b)) :
    Tendsto (fun i => ‖M c (z ((x i + y i) / 2))‖ ^ 2 /
      (‖M c (z (x i))‖ * ‖M c (z (y i))‖)) l (𝓝 (4 * a * b / (a + b) ^ 2)) := by
  let zmid := fun i => (x i + y i) / 2
  have hmid (i : ι) : zmid i ∈ Ioo (-Real.pi) Real.pi := by
    grind
  have hmidscale : Tendsto (fun i => N i * zmid i) l (𝓝 ((a + b) / 2)) := by
    have ht := (hscaleX.add hscaleY).div_const 2
    grind
  have hX := ratio_norm_div_size_tendsto (c := c) ha N hN x hx hxpos hxlim hscaleX
  have hZ := ratio_norm_div_size_tendsto (c := c) (div_pos (add_pos ha hb) (by norm_num))
    N hN zmid hmid (by grind) (by simpa [zmid] using (hxlim.add hylim).div_const 2) hmidscale
  have ht := (hZ.pow 2).div (hX.mul (ratio_norm_div_size_tendsto hb N hN y hy hypos hylim hscaleY)) (by positivity)
  have hvalue : (c ^ 2 / ((a + b) / 2)) ^ 2 / (c ^ 2 / a * (c ^ 2 / b)) =
      4 * a * b / (a + b) ^ 2 := by
    field_simp
    ring
  simp_all
  apply ht.congr
  intro i
  change (‖M c (z (zmid i))‖ / N i) ^ 2 /
    ((‖M c (z (x i))‖ / N i) * (‖M c (z (y i))‖ / N i)) = _
  dsimp only [zmid]
  field_simp [hN i, norm_ne_zero_iff.mpr (ratio_M_ne_zero hc (x i)),
    norm_ne_zero_iff.mpr (ratio_M_ne_zero hc (y i))]
end

end PottsDiscontinuity.Bethe
