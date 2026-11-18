module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.EulerSineProd
public import PottsDiscontinuity.Analysis.Section4Series
public import PottsDiscontinuity.Bethe.Asymptotic29
public import PottsDiscontinuity.Bethe.AsymptoticQuadrature
public import PottsDiscontinuity.Bethe.RatioProducts

/-! # Eigenvalue ratio limits for even and odd deficits (`N ∈ 4ℕ`) -/

@[expose] public section

open Set Filter MeasureTheory Finset Asymptotics Complex
open scoped Topology BigOperators

namespace PottsDiscontinuity.Bethe

open BetheAnsatz

/-! ### 1. Logarithmic spectral profile, derivatives, and pole/Wallis helpers -/

private noncomputable def ratioEll (c x : ℝ) : ℝ := Real.log ‖M c (z x)‖

private noncomputable def ratioNumerator (c x : ℝ) : ℝ :=
  (c ^ 2 - 2) ^ 2 + 2 * (c ^ 2 - 1) * (1 + Real.cos x)

private noncomputable def ratioEllPrime (c x : ℝ) : ℝ :=
  -(c ^ 2 - 1) * Real.sin x / ratioNumerator c x - Real.sin x / (2 * (1 - Real.cos x))

private noncomputable def ratioEllSecond (c x : ℝ) : ℝ :=
  1 / (2 * (1 - Real.cos x)) - (c ^ 2 - 1) * Real.cos x / ratioNumerator c x -
    2 * (c ^ 2 - 1) ^ 2 * Real.sin x ^ 2 / ratioNumerator c x ^ 2

private theorem ratio_ell_neg (c x : ℝ) : ratioEll c (-x) = ratioEll c x := by
  unfold ratioEll; rw [ratio_M_neg, Complex.norm_conj]

private theorem ratio_ell_zero (c : ℝ) : ratioEll c 0 = 0 := by
  simp [ratioEll, BetheAnsatz.M]

private theorem ratio_exp_ell {c : ℝ} (hc : 2 < c) (x : ℝ) :
    Real.exp (ratioEll c x) = ‖M c (z x)‖ :=
  Real.exp_log (norm_pos_iff.mpr (ratio_M_ne_zero hc x))

private theorem ratio_exp_sum_ell {ι : Type*} [Fintype ι] {c : ℝ} (hc : 2 < c) (u : ι → ℝ) :
    Real.exp (∑ j, ratioEll c (u j)) = ∏ j, ‖M c (z (u j))‖ := by
  rw [Real.exp_sum]; exact prod_congr rfl fun _ _ => ratio_exp_ell hc _

private theorem ratio_numerator_pos {c : ℝ} (hc : 2 < c) (x : ℝ) : 0 < ratioNumerator c x := by
  have hc2 : 4 < c ^ 2 := by nlinarith
  exact add_pos_of_pos_of_nonneg (sq_pos_of_pos (by linarith))
    (mul_nonneg (by linarith) (by linarith [Real.neg_one_le_cos x]))

private theorem ratio_one_sub_cos_lower {x : ℝ} (hx : x ∈ Icc (-Real.pi) Real.pi) :
    2 * x ^ 2 / Real.pi ^ 2 ≤ 1 - Real.cos x := by
  have hxhalf : |x / 2| ≤ Real.pi / 2 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith [abs_le.mpr ⟨by linarith [hx.1], hx.2⟩]
  have hsq := (sq_le_sq₀ (by positivity) (abs_nonneg _)).mpr (Real.mul_abs_le_abs_sin hxhalf)
  rw [show |x / 2| = |x| / 2 by rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)],
    mul_pow, div_pow, sq_abs] at hsq
  have hsin := Real.sin_sq_eq_half_sub (x / 2)
  rw [show 2 * (x / 2) = x by ring] at hsin
  have hpi : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
  field_simp at hsq; rw [sq_abs, hsin] at hsq
  exact (div_le_iff₀ hpi).mpr (by nlinarith only [hsq])

private theorem ratio_one_sub_cos_pos {x : ℝ} (hx : x ∈ Icc (-Real.pi) Real.pi) (hx0 : x ≠ 0) :
    0 < 1 - Real.cos x :=
  lt_of_lt_of_le (by positivity : 0 < 2 * x ^ 2 / Real.pi ^ 2) (ratio_one_sub_cos_lower hx)

private theorem ratio_hasDerivAt_numerator (c x : ℝ) :
    HasDerivAt (ratioNumerator c) (-2 * (c ^ 2 - 1) * Real.sin x) x := by
  convert (((Real.hasDerivAt_cos x).const_add 1).const_mul (2 * (c ^ 2 - 1))).const_add ((c ^ 2 - 2) ^ 2) using 1
  · funext y; unfold ratioNumerator; ring
  · ring

private theorem ratio_hasDerivAt_two_one_sub_cos (x : ℝ) :
    HasDerivAt (fun y => 2 * (1 - Real.cos y)) (2 * Real.sin x) x := by
  convert ((Real.hasDerivAt_cos x).const_sub 1).const_mul 2 using 1; ring

private theorem ratio_hasDerivAt_ell {c x : ℝ} (hc : 2 < c)
    (hx : x ∈ Ioo (-Real.pi) Real.pi) (hx0 : x ≠ 0) :
    HasDerivAt (ratioEll c) (ratioEllPrime c x) x := by
  have hn := ratio_numerator_pos hc x
  have hd := ratio_one_sub_cos_pos (Ioo_subset_Icc_self hx) hx0
  have heq : ∀ y ∈ Ioo (-Real.pi) Real.pi, y ≠ 0 →
      ratioEll c y = (1 / 2 : ℝ) * Real.log (ratioNumerator c y) - (1 / 2 : ℝ) * Real.log (2 * (1 - Real.cos y)) := by
    intro y hy hy0
    have hny := ratio_numerator_pos hc y
    have hdy := ratio_one_sub_cos_pos (Ioo_subset_Icc_self hy) hy0
    have hzy := z_ne_one hy hy0
    have hM : M c (z y) = (1 - (c : ℂ) ^ 2 - z y) / (1 - z y) := by
      have : 1 - z y ≠ 0 := sub_ne_zero.mpr (Ne.symm hzy); unfold M; field_simp; ring
    have hsq : Complex.normSq (M c (z y)) = ratioNumerator c y / (2 * (1 - Real.cos y)) := by
      rw [hM, Complex.normSq_div, show z y = (Real.cos y : ℂ) + (Real.sin y : ℂ) * I from exp_I_mul_ofReal y]
      simp only [Complex.normSq_apply, sub_re, sub_im, add_re, add_im, mul_re, mul_im,
        one_re, one_im, ofReal_re, ofReal_im, pow_two, I_re, I_im, mul_zero, zero_mul,
        mul_one, zero_add, add_zero, sub_zero, zero_sub]
      unfold ratioNumerator; congr 1 <;> nlinarith only [Real.sin_sq_add_cos_sq y]
    rw [Complex.normSq_eq_norm_sq] at hsq
    have hl := congrArg Real.log hsq
    rw [Real.log_pow, Real.log_div hny.ne' (mul_pos (by norm_num) hdy).ne'] at hl
    norm_num at hl; unfold ratioEll; linarith only [hl]
  have h := (((ratio_hasDerivAt_numerator c x).log hn.ne').const_mul (1 / 2 : ℝ)).sub
    (((ratio_hasDerivAt_two_one_sub_cos x).log (mul_pos (by norm_num) hd).ne').const_mul (1 / 2 : ℝ))
  refine (h.congr_deriv (by unfold ratioEllPrime; ring)).congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hx.1 hx.2, eventually_ne_nhds hx0] with y hy hy0 using heq y hy hy0

private theorem ratio_ellPrime_weighted_bound {c : ℝ} (hc : 2 < c) {x : ℝ} (hx : x ∈ Icc (-Real.pi) Real.pi) :
    |x * ratioEllPrime c x| ≤ Real.pi * (c ^ 2 - 1) / (c ^ 2 - 2) ^ 2 + Real.pi ^ 2 / 4 := by
  have hc2 : 4 < c ^ 2 := by nlinarith
  have ha0 : 0 < (c ^ 2 - 2) ^ 2 := sq_pos_of_pos (by linarith)
  have ha := ratio_numerator_pos hc x
  have halower : (c ^ 2 - 2) ^ 2 ≤ ratioNumerator c x := by
    unfold ratioNumerator; linarith [mul_nonneg (by linarith : 0 ≤ 2 * (c ^ 2 - 1)) (by linarith [Real.neg_one_le_cos x] : 0 ≤ 1 + Real.cos x)]
  have hxabs : |x| ≤ Real.pi := abs_le.mpr ⟨by linarith [hx.1], hx.2⟩
  by_cases hx0 : x = 0
  · subst x; simp only [zero_mul, abs_zero]
    exact add_nonneg (div_nonneg (mul_nonneg Real.pi_pos.le (by linarith)) ha0.le) (by positivity)
  have hd := ratio_one_sub_cos_pos hx hx0
  have hfirst : |-(c ^ 2 - 1) * Real.sin x / ratioNumerator c x| ≤ (c ^ 2 - 1) / (c ^ 2 - 2) ^ 2 := by
    rw [abs_div, abs_mul, abs_neg, abs_of_pos ha, abs_of_pos (by linarith : 0 < c ^ 2 - 1)]
    exact (div_le_div_of_nonneg_right (by nlinarith only [Real.abs_sin_le_one x, hc2]) ha.le).trans
      (div_le_div_of_nonneg_left (by linarith) ha0 halower)
  have hfirstx : |x * (-(c ^ 2 - 1) * Real.sin x / ratioNumerator c x)| ≤ Real.pi * (c ^ 2 - 1) / (c ^ 2 - 2) ^ 2 := by
    rw [abs_mul]; exact (mul_le_mul hxabs hfirst (abs_nonneg _) Real.pi_pos.le).trans_eq (by ring)
  have hsecondx : |x * (Real.sin x / (2 * (1 - Real.cos x)))| ≤ Real.pi ^ 2 / 4 := by
    rw [← mul_div_assoc, abs_div, abs_mul, abs_of_pos (mul_pos (by norm_num) hd)]
    refine (div_le_iff₀ (mul_pos (by norm_num) hd)).mpr ?_
    have hsin : |x| * |Real.sin x| ≤ x ^ 2 := by
      simpa only [← pow_two, sq_abs] using mul_le_mul_of_nonneg_left (Real.abs_sin_le_abs (x := x)) (abs_nonneg x)
    exact hsin.trans (by nlinarith only [(div_le_iff₀ (sq_pos_of_pos Real.pi_pos)).mp (ratio_one_sub_cos_lower hx)])
  unfold ratioEllPrime; rw [mul_sub]
  exact (abs_sub _ _).trans (add_le_add hfirstx hsecondx)

private theorem ratio_continuousAt_ellPrime {c x : ℝ} (hc : 2 < c)
    (hx : x ∈ Icc (-Real.pi) Real.pi) (hx0 : x ≠ 0) :
    ContinuousAt (ratioEllPrime c) x := by
  have hn : (c ^ 2 - 2) ^ 2 + 2 * (c ^ 2 - 1) * (1 + Real.cos x) ≠ 0 := (ratio_numerator_pos hc x).ne'
  have hd : 2 * (1 - Real.cos x) ≠ 0 := mul_ne_zero two_ne_zero (ratio_one_sub_cos_pos hx hx0).ne'
  unfold ratioEllPrime ratioNumerator; fun_prop (disch := assumption)

private theorem ratio_hasDerivAt_ellPrime {c x : ℝ} (hc : 2 < c)
    (hx : x ∈ Icc (-Real.pi) Real.pi) (hx0 : x ≠ 0) :
    HasDerivAt (ratioEllPrime c) (ratioEllSecond c x) x := by
  have hn := ratio_numerator_pos hc x
  have hd := ratio_one_sub_cos_pos hx hx0
  have hfirst := ((Real.hasDerivAt_sin x).const_mul (-(c ^ 2 - 1))).div (ratio_hasDerivAt_numerator c x) hn.ne'
  have hlast := (Real.hasDerivAt_sin x).div (ratio_hasDerivAt_two_one_sub_cos x) (mul_pos (by norm_num) hd).ne'
  have hfv : ((-(c ^ 2 - 1) * Real.cos x) * ratioNumerator c x -
      (-(c ^ 2 - 1) * Real.sin x) * (-2 * (c ^ 2 - 1) * Real.sin x)) / ratioNumerator c x ^ 2 =
      -(c ^ 2 - 1) * Real.cos x / ratioNumerator c x -
        2 * (c ^ 2 - 1) ^ 2 * Real.sin x ^ 2 / ratioNumerator c x ^ 2 := by field_simp
  have hlv : (Real.cos x * (2 * (1 - Real.cos x)) - Real.sin x * (2 * Real.sin x)) /
      (2 * (1 - Real.cos x)) ^ 2 = -1 / (2 * (1 - Real.cos x)) := by
    field_simp; nlinarith only [Real.sin_sq_add_cos_sq x]
  refine (hfirst.sub hlast).congr_deriv ?_
  change _ - _ = ratioEllSecond c x; rw [hfv, hlv]; unfold ratioEllSecond; ring

private theorem ratio_midpoint_log_bound {c : ℝ} (hc : 2 < c) :
    ∃ B ≥ 0, ∀ a b : ℝ, 0 < a → a ≤ b → b < Real.pi →
      |2 * ratioEll c ((a + b) / 2) - ratioEll c a - ratioEll c b| ≤ B * ((b - a) / a) ^ 2 := by
  let R : ℝ → ℝ := fun x => -(c ^ 2 - 1) * Real.cos x / ratioNumerator c x -
    2 * (c ^ 2 - 1) ^ 2 * Real.sin x ^ 2 / ratioNumerator c x ^ 2
  have hA : Continuous (ratioNumerator c) := by unfold ratioNumerator; fun_prop
  have hR : Continuous R :=
    ((continuous_const.mul Real.continuous_cos).div hA fun x => (ratio_numerator_pos hc x).ne').sub
      ((continuous_const.mul (Real.continuous_sin.pow 2)).div (hA.pow 2) fun x => pow_ne_zero 2 (ratio_numerator_pos hc x).ne')
  obtain ⟨B₀, hB₀⟩ := (isCompact_Icc : IsCompact (Icc (-Real.pi) Real.pi)).exists_bound_of_continuousOn hR.continuousOn
  let Bw := Real.pi ^ 2 / 4 + Real.pi ^ 2 * max B₀ 0
  have hBw : 0 ≤ Bw := by dsimp [Bw]; positivity
  have hbnd (x : ℝ) (hx : x ∈ Icc (-Real.pi) Real.pi) : |x ^ 2 * ratioEllSecond c x| ≤ Bw := by
    by_cases hx0 : x = 0
    · subst x; simp only [zero_pow (by norm_num : 2 ≠ 0), zero_mul, abs_zero]; exact hBw
    have hd := ratio_one_sub_cos_pos hx hx0
    have hx2 : x ^ 2 ≤ Real.pi ^ 2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg x) Real.pi_pos.le).mpr (abs_le.mpr ⟨by linarith [hx.1], hx.2⟩)
    have hsing : |x ^ 2 * (1 / (2 * (1 - Real.cos x)))| ≤ Real.pi ^ 2 / 4 := by
      rw [mul_one_div, abs_div, abs_of_nonneg (sq_nonneg x), abs_of_pos (mul_pos (by norm_num) hd)]
      exact (div_le_iff₀ (mul_pos (by norm_num) hd)).mpr
        (by nlinarith only [(div_le_iff₀ (sq_pos_of_pos Real.pi_pos)).mp (ratio_one_sub_cos_lower hx)])
    have hreg : |x ^ 2 * R x| ≤ Real.pi ^ 2 * max B₀ 0 := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg x)]
      exact mul_le_mul hx2 ((by simpa only [Real.norm_eq_abs] using hB₀ x hx : |R x| ≤ B₀).trans (le_max_left _ _))
        (abs_nonneg _) (sq_nonneg _)
    rw [show ratioEllSecond c x = 1 / (2 * (1 - Real.cos x)) + R x by unfold ratioEllSecond R; ring, mul_add]
    exact (abs_add_le _ _).trans (add_le_add hsing hreg)
  refine ⟨Bw, hBw, fun a b ha hab hb => ?_⟩
  let L := Bw / a ^ 2
  have hL : 0 ≤ L := div_nonneg hBw (sq_nonneg a)
  have hInt {x : ℝ} (hx : x ∈ Icc a b) : x ∈ Ioo (-Real.pi) Real.pi := ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2]⟩
  have hxpos {x : ℝ} (hx : x ∈ Icc a b) : 0 < x := ha.trans_le hx.1
  have hbound (x : ℝ) (hx : x ∈ Icc a b) : |ratioEllSecond c x| ≤ L := by
    have ht := hbnd x (Ioo_subset_Icc_self (hInt hx))
    rw [abs_mul, abs_of_nonneg (sq_nonneg x)] at ht
    exact (le_div_iff₀ (sq_pos_of_pos ha)).mpr
      (by nlinarith only [ht, mul_le_mul_of_nonneg_right ((sq_le_sq₀ ha.le (hxpos hx).le).mpr hx.1) (abs_nonneg (ratioEllSecond c x))])
  let m := (a + b) / 2
  have hm : m ∈ Icc a b := ⟨by dsimp [m]; linarith, by dsimp [m]; linarith⟩
  have hLip {u v : ℝ} (hu : u ∈ Icc a b) (hv : v ∈ Icc a b) : |ratioEllPrime c v - ratioEllPrime c u| ≤ L * |v - u| := by
    simpa only [Real.norm_eq_abs] using Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun x hx => (ratio_hasDerivAt_ellPrime hc (Ioo_subset_Icc_self (hInt hx)) (hxpos hx).ne').hasDerivWithinAt)
      (fun x hx => by simpa only [Real.norm_eq_abs] using hbound x hx) (convex_Icc a b) hu hv
  let g : ℝ → ℝ := fun x => ratioEll c x - ratioEllPrime c m * x
  have hg (x : ℝ) (hx : x ∈ Icc a b) : HasDerivAt g (ratioEllPrime c x - ratioEllPrime c m) x := by
    have hid : HasDerivAt (fun t : ℝ => ratioEllPrime c m * t) (ratioEllPrime c m) x :=
      ((hasDerivAt_id x).const_mul (ratioEllPrime c m)).congr_deriv (mul_one _)
    exact (ratio_hasDerivAt_ell hc (hInt hx) (hxpos hx).ne').sub hid
  have hgBound (x : ℝ) (hx : x ∈ Icc a b) : |ratioEllPrime c x - ratioEllPrime c m| ≤ L * (b - a) :=
    (hLip hm hx).trans (mul_le_mul_of_nonneg_left (abs_le.mpr ⟨by linarith [hx.1, hm.2], by linarith [hx.2, hm.1]⟩) hL)
  have hgLip (x : ℝ) (hx : x ∈ Icc a b) : |g x - g m| ≤ L * (b - a) * |x - m| := by
    simpa only [Real.norm_eq_abs] using Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun y hy => (hg y hy).hasDerivWithinAt)
      (fun y hy => by simpa only [Real.norm_eq_abs] using hgBound y hy) (convex_Icc a b) hm hx
  have hga := hgLip a ⟨le_rfl, hab⟩; have hgb := hgLip b ⟨hab, le_rfl⟩
  rw [abs_of_nonpos (sub_nonpos.mpr hm.1), show -(a - m) = (b - a) / 2 by dsimp [m]; ring] at hga
  rw [abs_of_nonneg (sub_nonneg.mpr hm.2), show b - m = (b - a) / 2 by dsimp [m]; ring] at hgb
  have htri := abs_sub (-(g a - g m)) (g b - g m); rw [abs_neg] at htri
  have hstep : |2 * ratioEll c m - ratioEll c a - ratioEll c b| ≤ L * (b - a) ^ 2 := by
    rw [show 2 * ratioEll c m - ratioEll c a - ratioEll c b = -(g a - g m) - (g b - g m) by dsimp [g, m]; ring]
    nlinarith only [hga, hgb, htri]
  exact hstep.trans_eq (by dsimp [L]; ring)

private noncomputable def ratioRegularPart (c x : ℝ) : ℝ :=
  ‖1 - (c : ℂ) ^ 2 - z x‖ / |Real.sinc (x / 2)|

private theorem ratio_regularPart_zero (c : ℝ) : ratioRegularPart c 0 = c ^ 2 := by
  unfold ratioRegularPart; rw [z_zero, show (1 : ℂ) - (c : ℂ) ^ 2 - 1 = -((c : ℂ) ^ 2) by ring,
    norm_neg, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]; simp

private theorem ratio_continuousAt_regularPart_zero (c : ℝ) : ContinuousAt (ratioRegularPart c) 0 := by
  unfold ratioRegularPart z; fun_prop (disch := simp)

private theorem ratio_regularPart_eq_mul_norm {c x : ℝ}
    (hx : x ∈ Ioo (-Real.pi) Real.pi) (hx0 : x ≠ 0) :
    ratioRegularPart c x = |x| * ‖M c (z x)‖ := by
  have hden : 1 - z x ≠ 0 := sub_ne_zero.mpr (Ne.symm (z_ne_one hx hx0))
  have hnorm_den : ‖1 - z x‖ = |x| * |Real.sinc (x / 2)| := by
    have hhalf : x / 2 ≠ 0 := div_ne_zero hx0 (by norm_num)
    rw [norm_sub_rev, z, Complex.norm_exp_I_mul_ofReal_sub_one x, Real.norm_eq_abs, abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 2), Real.sinc_of_ne_zero hhalf, abs_div, abs_div,
      abs_of_pos (by norm_num : (0 : ℝ) < 2)]; field_simp
  have hM : M c (z x) = (1 - (c : ℂ) ^ 2 - z x) / (1 - z x) := by unfold M; field_simp; ring
  have hsinc : |Real.sinc (x / 2)| ≠ 0 := (mul_ne_zero_iff.mp (hnorm_den ▸ norm_ne_zero_iff.mpr hden)).2
  have hxabs := (abs_pos.mpr hx0).ne'
  rw [hM, norm_div, hnorm_den]; unfold ratioRegularPart; field_simp

private theorem ratio_norm_div_size_tendsto {ι : Type*} {l : Filter ι} {c a : ℝ}
    (ha : 0 < a) (N : ι → ℝ) (hN : ∀ i, N i ≠ 0)
    (x : ι → ℝ) (hx : ∀ i, x i ∈ Ioo (-Real.pi) Real.pi) (hxpos : ∀ i, 0 < x i)
    (hxlim : Tendsto x l (𝓝 0)) (hscale : Tendsto (fun i => N i * x i) l (𝓝 a)) :
    Tendsto (fun i => ‖M c (z (x i))‖ / N i) l (𝓝 (c ^ 2 / a)) := by
  have hr := (ratio_continuousAt_regularPart_zero c).tendsto.comp hxlim
  rw [ratio_regularPart_zero] at hr
  refine (hr.div hscale ha.ne').congr fun i => ?_
  dsimp only [Pi.div_apply, Function.comp_def]
  rw [ratio_regularPart_eq_mul_norm (hx i) (hxpos i).ne', abs_of_pos (hxpos i)]
  field_simp [(hxpos i).ne', hN i]

private theorem ratio_scaled_inverse_norm_tendsto {ι : Type*} {l : Filter ι} {c a : ℝ}
    (hc : 2 < c) (N : ι → ℝ) (x : ι → ℝ)
    (hx : ∀ i, x i ∈ Ioo (-Real.pi) Real.pi) (hxpos : ∀ i, 0 < x i)
    (hxlim : Tendsto x l (𝓝 0)) (hscale : Tendsto (fun i => N i * x i) l (𝓝 a)) :
    Tendsto (fun i => N i * ‖M c (z (x i))‖⁻¹) l (𝓝 (a / c ^ 2)) := by
  have hr := (ratio_continuousAt_regularPart_zero c).tendsto.comp hxlim
  rw [ratio_regularPart_zero] at hr
  refine (hscale.div hr (pow_ne_zero 2 (by linarith : c ≠ 0))).congr fun i => ?_
  dsimp only [Pi.div_apply, Function.comp_def]
  rw [ratio_regularPart_eq_mul_norm (hx i) (hxpos i).ne', abs_of_pos (hxpos i)]
  field_simp [(hxpos i).ne', norm_ne_zero_iff.mpr (ratio_M_ne_zero hc (x i))]

private noncomputable def ratioWallisFactor (k : ℕ) : ℝ := 1 - (1 / 2 : ℝ) ^ 2 / ((k : ℝ) + 1) ^ 2

private theorem ratio_wallisFactor_pos (k : ℕ) : 0 < ratioWallisFactor k := by
  have hden : (1 : ℝ) ≤ ((k : ℝ) + 1) ^ 2 := by nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  unfold ratioWallisFactor; nlinarith [div_le_self (by positivity : (0 : ℝ) ≤ (1 / 2) ^ 2) hden]

private theorem ratio_half_integer_midpoint_log_tendsto {ι : Type*} {l : Filter ι}
    {c ρ : ℝ} (hc : 2 < c) (hρ : 0 < ρ) (k : ℕ)
    (N : ι → ℝ) (hN : ∀ i, N i ≠ 0) (hNlim : Tendsto N l atTop)
    (x y : ι → ℝ) (hx : ∀ i, x i ∈ Ioo (-Real.pi) Real.pi)
    (hy : ∀ i, y i ∈ Ioo (-Real.pi) Real.pi) (hxpos : ∀ i, 0 < x i) (hypos : ∀ i, 0 < y i)
    (hscaleX : Tendsto (fun i => N i * x i) l (𝓝 (((k : ℝ) + 1 / 2) / ρ)))
    (hscaleY : Tendsto (fun i => N i * y i) l (𝓝 (((k : ℝ) + 3 / 2) / ρ))) :
    Tendsto (fun i => 2 * ratioEll c ((x i + y i) / 2) - ratioEll c (x i) - ratioEll c (y i)) l
      (𝓝 (Real.log (ratioWallisFactor k))) := by
  let a := ((k : ℝ) + 1 / 2) / ρ; let b := ((k : ℝ) + 3 / 2) / ρ
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  have hxlim : Tendsto x l (𝓝 0) := (hscaleX.div_atTop hNlim).congr fun i => by field_simp [hN i]
  have hylim : Tendsto y l (𝓝 0) := (hscaleY.div_atTop hNlim).congr fun i => by field_simp [hN i]
  let zmid : ι → ℝ := fun i => (x i + y i) / 2
  have hX := ratio_norm_div_size_tendsto (c := c) ha N hN x hx hxpos hxlim hscaleX
  have hY := ratio_norm_div_size_tendsto (c := c) hb N hN y hy hypos hylim hscaleY
  have hZ := ratio_norm_div_size_tendsto (c := c) (div_pos (add_pos ha hb) (by norm_num)) N hN zmid
    (fun i => ⟨by dsimp [zmid]; linarith [(hx i).1, (hy i).1], by dsimp [zmid]; linarith [(hx i).2, (hy i).2]⟩)
    (fun i => div_pos (add_pos (hxpos i) (hypos i)) (by norm_num))
    (by simpa [zmid] using (hxlim.add hylim).div_const 2)
    (((hscaleX.add hscaleY).div_const 2).congr fun _ => by dsimp [zmid]; ring)
  have hc0 : c ≠ 0 := by linarith
  have ht : Tendsto (fun i => ‖M c (z ((x i + y i) / 2))‖ ^ 2 / (‖M c (z (x i))‖ * ‖M c (z (y i))‖)) l
      (𝓝 (ratioWallisFactor k)) := by
    have hraw := (hZ.pow 2).div (hX.mul hY) (by positivity)
    have hval : (c ^ 2 / ((a + b) / 2)) ^ 2 / (c ^ 2 / a * (c ^ 2 / b)) = ratioWallisFactor k := by
      unfold ratioWallisFactor; dsimp [a, b]
      have hk : (k : ℝ) + 1 ≠ 0 := by positivity
      rw [show ((k : ℝ) + 1 / 2) / ρ + ((k : ℝ) + 3 / 2) / ρ = 2 * ((k : ℝ) + 1) / ρ by ring]
      field_simp [hc0, hρ.ne', hk]; ring
    rw [hval] at hraw
    refine hraw.congr fun i => ?_
    change (‖M c (z (zmid i))‖ / N i) ^ 2 / ((‖M c (z (x i))‖ / N i) * (‖M c (z (y i))‖ / N i)) = _
    dsimp only [zmid]
    field_simp [hN i, norm_ne_zero_iff.mpr (ratio_M_ne_zero hc (x i)), norm_ne_zero_iff.mpr (ratio_M_ne_zero hc (y i))]
  refine ((Real.continuousAt_log (ratio_wallisFactor_pos k).ne').tendsto.comp ht).congr fun i => ?_
  dsimp only [Function.comp_def]
  have hmx := norm_ne_zero_iff.mpr (ratio_M_ne_zero hc (x i))
  have hmy := norm_ne_zero_iff.mpr (ratio_M_ne_zero hc (y i))
  have hmm := norm_ne_zero_iff.mpr (ratio_M_ne_zero hc ((x i + y i) / 2))
  rw [Real.log_div (pow_ne_zero 2 hmm) (mul_ne_zero hmx hmy), Real.log_pow, Real.log_mul hmx hmy]
  unfold ratioEll; ring

/-! ### 2. Density limits, boundary factors, predecessor projection, and positive-rank scaling -/

private theorem ratio_densityNorm_tendsto_of_rate {ι : Type*} {l : Filter ι} {Δ K : ℝ}
    (hΔ : Δ < -1) (N : ι → ℕ) (hN : Tendsto (fun i => (N i : ℝ)) l atTop)
    (f : ι → ℝ → ℝ)
    (hb : ∀ i, BddAbove (range fun α : Icc (-Real.pi) Real.pi =>
      |Xi (lamOf Δ) α * f i (kMap (lamOf Δ) α)|))
    (hrate : ∀ᶠ i in l, densityNorm Δ hΔ (f i) (hb i) ≤ K / N i) :
    Tendsto (fun i => densityNorm Δ hΔ (f i) (hb i)) l (𝓝 0) := by
  have hKlim : Tendsto (fun i => K / (N i : ℝ)) l (𝓝 0) := tendsto_const_nhds.div_atTop hN
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  filter_upwards [hrate, hKlim.eventually (gt_mem_nhds hε)] with i hi hKi
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (densityNorm_nonneg hΔ _ (hb i))]
  exact hi.trans_lt hKi

private theorem ratio_density_eventually_bounded {ι : Type*} {l : Filter ι} {Δ : ℝ} (hΔ : Δ < -1)
    (f : ι → ℝ → ℝ)
    (hb : ∀ i, BddAbove (range fun α : Icc (-Real.pi) Real.pi =>
      |Xi (lamOf Δ) α * (f i (kMap (lamOf Δ) α) - rho Δ (kMap (lamOf Δ) α))|))
    (hlim : Tendsto (fun i => densityNorm Δ hΔ (fun x => f i x - rho Δ x) (hb i)) l (𝓝 0)) :
    ∃ M ≥ 0, ∀ᶠ i in l, ∀ x ∈ Icc (-Real.pi) Real.pi, f i x ≤ M := by
  obtain ⟨M₀, hM₀⟩ := isCompact_Icc.exists_bound_of_continuousOn (continuous_rho hΔ).continuousOn
  refine ⟨max M₀ 1 + 1, by linarith [le_max_right M₀ 1], ?_⟩
  filter_upwards [(tendsto_densityNorm_div hΔ (fun i x => f i x - rho Δ x) hb hlim).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with i hi x hx
  have herror := (abs_le.mp (abs_le_densityNorm_div hΔ (fun x => f i x - rho Δ x) (hb i) hx)).2
  have hρ : rho Δ x ≤ M₀ := (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hM₀ x hx)
  linarith [le_max_left M₀ 1]

private theorem ratio_tendsto_root_left_of_eventual_mesh {ι : Type*} {f : Filter ι}
    (n : ι → ℕ) (hn : ∀ i, 0 < n i) (p : ∀ i, Fin (n i) → ℝ)
    (hp : ∀ i, p i ∈ S_n (n i)) (d : ι → ℝ) (hd : Tendsto d f (𝓝 0))
    (hdnonneg : ∀ i, 0 ≤ d i)
    (hmesh : ∀ᶠ i in f, ∀ j : Fin (n i + 1),
      rootPartitionPoint (n i) (p i) (hn i) j.succ - rootPartitionPoint (n i) (p i) (hn i) j.castSucc ≤ d i)
    (j : ∀ i, Fin (n i)) (J : ℕ) (hrank : ∀ i, (j i).val ≤ J) :
    Tendsto (fun i => p i (j i)) f (𝓝 (-Real.pi)) := by
  have hb : Tendsto (fun i => ((J : ℝ) + 1) * d i) f (𝓝 0) := by
    simpa only [mul_zero] using hd.const_mul ((J : ℝ) + 1)
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  filter_upwards [hmesh, hb.eventually (gt_mem_nhds hε)] with i hi hbi
  rw [Real.dist_eq, sub_neg_eq_add, abs_of_nonneg (by linarith [((hp i).1 (j i)).1])]
  have hr : ((j i).val : ℝ) + 1 ≤ (J : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right (hrank i) 1
  exact (root_distance_from_boundary (hp i) (hn i) hi (j i)).1.trans_lt
    ((mul_le_mul_of_nonneg_right hr (hdnonneg i)).trans_lt hbi)

private theorem ratio_tendsto_root_left {ι : Type*} {f : Filter ι} {Δ : ℝ} (hΔ : Δ < -1)
    (r : ℕ) (N n : ι → ℕ) (p : ∀ i, Fin (n i) → ℝ)
    (hp : ∀ i, p i ∈ S_n (n i)) (hn : ∀ i, 0 < n i) (hs : ∀ i, 2 * n i ≤ N i)
    (hcount : ∀ i, N i = 2 * (n i + r))
    (hNlim : Tendsto (fun i => (N i : ℝ)) f atTop)
    (hb : ∀ i, BddAbove (range fun α : Icc (-Real.pi) Real.pi =>
      |Xi (lamOf Δ) α * (rootStepDensity (N i) (n i) (p i) (hp i) (hn i) (hs i)
        (kMap (lamOf Δ) α) - rho Δ (kMap (lamOf Δ) α))|))
    (hlim : Tendsto (fun i => densityNorm Δ hΔ
      (fun x => rootStepDensity (N i) (n i) (p i) (hp i) (hn i) (hs i) x - rho Δ x) (hb i)) f (𝓝 0))
    (j : ∀ i, Fin (n i)) (J : ℕ) (hrank : ∀ i, (j i).val ≤ J) :
    Tendsto (fun i => p i (j i)) f (𝓝 (-Real.pi)) := by
  obtain ⟨m, hm, hmesh⟩ := eventually_rootPartition_gap_le hΔ r N n p hp hn hs hcount hb hlim
  let d := fun i => 2 * (2 * r + 1 : ℝ) / (m * (N i : ℝ))
  have hd : Tendsto d f (𝓝 0) := by
    simpa only [d, div_mul_eq_div_mul_one_div, one_div, mul_zero, Function.comp_def] using
      (tendsto_inv_atTop_zero.comp hNlim).const_mul (2 * (2 * r + 1 : ℝ) / m)
  exact ratio_tendsto_root_left_of_eventual_mesh n hn p hp d hd (fun _ => by dsimp [d]; positivity) hmesh j J hrank

private theorem ratio_modulus_tendsto_endpoint {ι : Type*} {f : Filter ι} {x : ι → ℝ}
    (hx : Tendsto x f (𝓝 (-Real.pi))) (c : ℝ) :
    Tendsto (fun i => ‖M c (z (x i))‖) f (𝓝 |anisotropy c|) := by
  have hzpi : z (-Real.pi) = -1 := by
    rw [z, Complex.ofReal_neg, mul_neg, Complex.exp_neg, mul_comm I, Complex.exp_pi_mul_I]; norm_num
  have hMpi : M c (z (-Real.pi)) = (anisotropy c : ℂ) := by
    rw [hzpi]; simp only [M, sub_neg_eq_add, one_add_one_eq_two]; unfold anisotropy; push_cast; ring
  have hcont : ContinuousAt (fun y => M c (z y)) (-Real.pi) := by
    have hzc : Continuous (z : ℝ → ℂ) := by unfold z; fun_prop
    have hzne : 1 - z (-Real.pi) ≠ 0 := by rw [hzpi]; norm_num
    unfold M; exact continuousAt_const.sub (continuousAt_const.div (continuousAt_const.sub hzc.continuousAt) hzne)
  simpa only [hMpi, Complex.norm_real, Real.norm_eq_abs, Function.comp_def] using (hcont.norm.tendsto).comp hx

private noncomputable def ratioRootIndex {n : ℕ} (hn : 0 < n) (q : Fin n → ℝ) (x : ℝ) : Fin n :=
  if h : (univ.filter (fun j => q j ≤ x)).Nonempty then (univ.filter (fun j => q j ≤ x)).max' h else ⟨0, hn⟩

private theorem ratio_rootIndex_cell {n : ℕ} (hn : 0 < n) (q : Fin n → ℝ) (hq : StrictMono q) {x : ℝ}
    (hleft : q ⟨0, hn⟩ ≤ x) (hright : x < q ⟨n - 1, by omega⟩) :
    ∃ hj : (ratioRootIndex hn q x).val + 1 < n,
      q (ratioRootIndex hn q x) ≤ x ∧ x < q ⟨(ratioRootIndex hn q x).val + 1, hj⟩ := by
  classical
  obtain ⟨j, hj, hcell⟩ := exists_interior_root_cell hn q hleft hright
  have hon : ratioRootIndex hn q x = j := by
    let s := univ.filter (fun k => q k ≤ x)
    have hjmem : j ∈ s := mem_filter.mpr ⟨mem_univ _, hcell.1⟩
    have hs : s.Nonempty := ⟨j, hjmem⟩
    change (if h : s.Nonempty then s.max' h else ⟨0, hn⟩) = j
    rw [dite_eq_left hs]
    refine le_antisymm (Finset.max'_le s _ _ fun i hi => ?_) (Finset.le_max' s j hjmem)
    by_contra h
    have hle : (⟨j.val + 1, hj⟩ : Fin n) ≤ i := show j.val + 1 ≤ i.val by have := lt_of_not_ge h; omega
    linarith [hcell.2, (mem_filter.mp hi).2, hq.monotone hle]
  rw [hon]; exact ⟨hj, hcell⟩

private theorem ratio_offsetFunction_eq_predecessor {N r : ℕ} (h4 : 4 ∣ N) (hr : r ≤ N / 2)
    (hn : 0 < N / 2 - r) (p : Fin (N / 2) → ℝ) (q : Fin (N / 2 - r) → ℝ)
    (hq : q ∈ S_n (N / 2 - r)) (x : ℝ) :
    offsetFunction N r h4 hr p q hn x = offsetDisplacement N r h4 hr p q (ratioRootIndex hn q x) := by
  classical
  by_cases hleft : x < q ⟨0, hn⟩
  · have hs : univ.filter (fun j => q j ≤ x) = ∅ := Finset.eq_empty_iff_forall_notMem.mpr fun j hj => by
      linarith [(mem_filter.mp hj).2, hq.2.1.monotone (show (⟨0, hn⟩ : Fin _) ≤ j from Nat.zero_le _)]
    have hidx : ratioRootIndex hn q x = ⟨0, hn⟩ := by simp [ratioRootIndex, hs]
    rw [hidx]; simp only [offsetFunction, ite_eq_left hleft]
  by_cases hright : q ⟨N / 2 - r - 1, by omega⟩ ≤ x
  · let s := univ.filter (fun j => q j ≤ x)
    let j : Fin (N / 2 - r) := ⟨N / 2 - r - 1, by omega⟩
    have hj : j ∈ s := mem_filter.mpr ⟨mem_univ _, hright⟩
    have hs : s.Nonempty := ⟨j, hj⟩
    have hidx : ratioRootIndex hn q x = j := by
      change (if h : s.Nonempty then s.max' h else ⟨0, hn⟩) = j
      rw [dite_eq_left hs]
      exact le_antisymm (show (s.max' hs).val ≤ N / 2 - r - 1 by have := (s.max' hs).isLt; omega) (Finset.le_max' s j hj)
    rw [hidx]; simp only [offsetFunction, ite_eq_right hleft, ite_eq_left hright]; rfl
  obtain ⟨hj, hcell⟩ := ratio_rootIndex_cell hn q hq.2.1 (le_of_not_gt hleft) (lt_of_not_ge hright)
  exact offsetFunction_on_cell h4 hr hn hq.2.1 (ratioRootIndex hn q x) hj hcell

private theorem ratio_rootIndex_cast {n m : ℕ} (h : n = m) (hn : 0 < n) (hm : 0 < m)
    (q : Fin m → ℝ) (x : ℝ) :
    Fin.cast h (ratioRootIndex hn (fun j => q (Fin.cast h j)) x) = ratioRootIndex hm q x := by
  subst m; rfl

private theorem ratio_root_mesh_cast {n m : ℕ} (h : n = m) (hn : 0 < n) (hm : 0 < m)
    (q : Fin m → ℝ) {d : ℝ}
    (hmesh : ∀ j : Fin (m + 1), rootPartitionPoint m q hm j.succ - rootPartitionPoint m q hm j.castSucc ≤ d) :
    ∀ j : Fin (n + 1),
      rootPartitionPoint n (fun i => q (Fin.cast h i)) hn j.succ -
        rootPartitionPoint n (fun i => q (Fin.cast h i)) hn j.castSucc ≤ d := by
  subst m; exact hmesh

private theorem ratio_central_pair {m : ℕ} (hm : 0 < m) {p : Fin (2 * m) → ℝ} (hp : p ∈ S_n (2 * m)) :
    p ⟨m - 1, by omega⟩ = -p ⟨m, by omega⟩ := by
  have he : Fin.rev (⟨m, by omega⟩ : Fin (2 * m)) = ⟨m - 1, by omega⟩ :=
    Fin.ext (by simp only [Fin.val_rev]; omega)
  simpa only [he] using hp.2.2 ⟨m, by omega⟩

private theorem ratio_gap_tendsto_at_zero {ι : Type*} {l : Filter ι} {Δ : ℝ} (hΔ : Δ < -1)
    (N n : ι → ℕ) (q : ∀ i, Fin (n i) → ℝ) (hq : ∀ i, q i ∈ S_n (n i))
    (hn : ∀ i, 0 < n i) (hs : ∀ i, 2 * n i ≤ N i)
    (hb : ∀ i, BddAbove (range fun α : Icc (-Real.pi) Real.pi =>
      |Xi (lamOf Δ) α * (rootStepDensity (N i) (n i) (q i) (hq i) (hn i) (hs i)
        (kMap (lamOf Δ) α) - rho Δ (kMap (lamOf Δ) α))|))
    (hlim : Tendsto (fun i => densityNorm Δ hΔ
      (fun x => rootStepDensity (N i) (n i) (q i) (hq i) (hn i) (hs i) x - rho Δ x) (hb i)) l (𝓝 0))
    (j : ∀ i, Fin (n i)) (hj : ∀ i, (j i).val + 1 < n i)
    (hzero : Tendsto (fun i => q i (j i)) l (𝓝 0)) :
    Tendsto (fun i => (N i : ℝ) * (q i ⟨(j i).val + 1, hj i⟩ - q i (j i))) l (𝓝 (rho Δ 0)⁻¹) := by
  let f := fun i => rootStepDensity (N i) (n i) (q i) (hq i) (hn i) (hs i)
  have ht : Tendsto (fun i => f i (q i (j i))) l (𝓝 (rho Δ 0)) := by
    have he := tendsto_densityNorm_div hΔ (fun i y => f i y - rho Δ y) hb hlim
    have hρ := (continuous_rho hΔ).continuousAt.tendsto.comp hzero
    refine Metric.tendsto_nhds.mpr fun ε hε => ?_
    filter_upwards [he.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε / 2)),
      Metric.tendsto_nhds.mp hρ (ε / 2) (by positivity)] with i hi hρi
    have herr := abs_le_densityNorm_div hΔ (fun y => f i y - rho Δ y) (hb i)
      ⟨((hq i).1 (j i)).1.le, ((hq i).1 (j i)).2.le⟩
    rw [Real.dist_eq] at hρi ⊢; dsimp only [Function.comp_def] at hρi
    have htri := abs_add_le (f i (q i (j i)) - rho Δ (q i (j i))) (rho Δ (q i (j i)) - rho Δ 0)
    rw [sub_add_sub_cancel] at htri; linarith
  refine (ht.inv₀ (rho_pos hΔ 0).ne').congr fun i => ?_
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (hn i).ne'
  have hcast := rootStepDensity_cast hk.symm (q i) (hq i) (by omega) (hn i) (by have := hs i; omega) (hs i)
  let q' : Fin (k + 1) → ℝ := fun t => q i (Fin.cast hk.symm t)
  have hq' : q' ∈ S_n (k + 1) := mem_S_n_cast hk.symm (hq i)
  let t : Fin k := ⟨(j i).val, by have := hj i; omega⟩
  have he₀ : Fin.cast hk.symm t.castSucc = j i := Fin.ext rfl
  have he₁ : Fin.cast hk.symm t.succ = ⟨(j i).val + 1, hj i⟩ := Fin.ext rfl
  have hcell : q' t.castSucc ≤ q i (j i) ∧ q i (j i) < q' t.succ := by
    dsimp only [q']; rw [he₀, he₁]; exact ⟨le_rfl, (hq i).2.1 (show (j i).val < (j i).val + 1 by omega)⟩
  dsimp only [f]
  rw [← congrFun hcast (q i (j i)), rootStepDensity_interior hq' (by have := hs i; omega) t hcell]
  dsimp only [q']; rw [he₀, he₁, one_div, inv_inv]

private noncomputable def ratioPositiveRoot (N : ℕ) (h4 : 4 ∣ N) (p : Fin (N / 2) → ℝ)
    (j : Fin (N / 4)) : ℝ := p ⟨N / 4 + j.val, by obtain ⟨z, hz⟩ := h4; omega⟩

private theorem ratio_positiveRoot_pos {N : ℕ} (h4 : 4 ∣ N) {p : Fin (N / 2) → ℝ}
    (hp : p ∈ S_n (N / 2)) (j : Fin (N / 4)) : 0 < ratioPositiveRoot N h4 p j := by
  let idx : Fin (N / 2) := ⟨N / 4 + j.val, by obtain ⟨z, hz⟩ := h4; omega⟩
  have hi : Fin.rev idx < idx := show (Fin.rev idx).val < idx.val by
    simp only [Fin.val_rev]; dsimp only [idx]; obtain ⟨z, hz⟩ := h4; omega
  have h := hp.2.1 hi; rw [show p (Fin.rev idx) = -p idx from hp.2.2 idx] at h
  change 0 < p idx; linarith

private theorem ratio_positiveRoot_lower {N : ℕ} (h4 : 4 ∣ N) {p : Fin (N / 2) → ℝ}
    (hp : p ∈ S_n (N / 2)) (hn : 0 < N / 2) {M : ℝ}
    (hupper : ∀ x ∈ Icc (-Real.pi) Real.pi, rootStepDensity N (N / 2) p hp hn (by omega) x ≤ M)
    (j : Fin (N / 4)) :
    (j.val : ℝ) + 1 / 2 ≤ (M * N) * ratioPositiveRoot N h4 p j := by
  have hc : 2 * (N / 4) = N / 2 := by obtain ⟨z, hz⟩ := h4; omega
  have hm : 0 < N / 4 := Nat.zero_lt_of_lt j.isLt
  let p' : Fin (2 * (N / 4)) → ℝ := fun i => p (Fin.cast hc i)
  have hp' : p' ∈ S_n (2 * (N / 4)) := mem_S_n_cast hc hp
  have hs' : 2 * (2 * (N / 4)) ≤ N := by rw [hc]; omega
  have hstep (k : ℕ) (hk : k + 1 < 2 * (N / 4)) : 1 ≤ (M * N) * (p' ⟨k + 1, hk⟩ - p' ⟨k, by omega⟩) := by
    have h := root_spacing_lower_at hp' (by omega) hs'
      (fun x hx => by rw [congrFun (rootStepDensity_cast hc p hp (by omega) hn hs' (by omega)) x]; exact hupper x hx) k hk
    nlinarith only [h]
  have hcentral := hstep (N / 4 - 1) (by omega)
  rw [show (⟨N / 4 - 1 + 1, by omega⟩ : Fin (2 * (N / 4))) = ⟨N / 4, by omega⟩ from Fin.ext (by dsimp; omega),
    ratio_central_pair hm hp'] at hcentral
  have hmono : Monotone (fun i : Fin (2 * (N / 4)) => (M * N) * p' i - (i.val : ℝ)) := by
    obtain ⟨w, hw⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : 2 * (N / 4) ≠ 0)
    have hcast : ∀ a b : Fin (2 * (N / 4)), a ≤ b → (M * N) * p' a - a.val ≤ (M * N) * p' b - b.val := by
      let q : Fin (w + 1) → ℝ := fun i => (M * N) * p' (Fin.cast hw.symm i) - i.val
      have hqm : Monotone q := Fin.monotone_iff_le_succ.mpr fun i => by
        have hs := hstep i.val (by omega)
        dsimp [q]; simp only [Nat.cast_add, Nat.cast_one]
        change 1 ≤ (M * N) * (p' (Fin.cast hw.symm i.succ) - p' (Fin.cast hw.symm i.castSucc)) at hs
        linarith
      intro a b hab
      simpa [q] using hqm (show Fin.cast hw a ≤ Fin.cast hw b from hab)
    exact hcast
  have hdiff := hmono (show (⟨N / 4, by omega⟩ : Fin (2 * (N / 4))) ≤ ⟨N / 4 + j.val, by omega⟩ from Nat.le_add_right _ _)
  simp only [Nat.cast_add] at hdiff
  change _ ≤ (M * N) * p' ⟨N / 4 + j.val, by omega⟩
  nlinarith only [hcentral, hdiff]

private theorem ratio_full_positive_rank_scaling {Δ : ℝ} (hΔ : Δ < -1)
    (N : ℕ → ℕ) (h4 : ∀ i, 4 ∣ N i) (hN : ∀ i, 0 < N i)
    (p : ∀ i, Fin (N i / 2) → ℝ) (hp : ∀ i, p i ∈ S_n (N i / 2))
    (hNlim : Tendsto (fun i => (N i : ℝ)) atTop atTop)
    (hb : ∀ i, BddAbove (range fun α : Icc (-Real.pi) Real.pi =>
      |Xi (lamOf Δ) α * (rootStepDensity (N i) (N i / 2) (p i) (hp i)
        (by obtain ⟨z, hz⟩ := h4 i; have := hN i; omega) (by omega)
        (kMap (lamOf Δ) α) - rho Δ (kMap (lamOf Δ) α))|))
    (hlim : Tendsto (fun i => densityNorm Δ hΔ
      (fun x => rootStepDensity (N i) (N i / 2) (p i) (hp i)
        (by obtain ⟨z, hz⟩ := h4 i; have := hN i; omega) (by omega) x - rho Δ x) (hb i)) atTop (𝓝 0))
    (k : ℕ) (hk : ∀ i, k < N i / 4) :
    Tendsto (fun i => (N i : ℝ) * ratioPositiveRoot (N i) (h4 i) (p i) ⟨k, hk i⟩) atTop
      (𝓝 (((k : ℝ) + 1 / 2) / rho Δ 0)) := by
  let m := fun i => N i / 4
  have hm (i : ℕ) : 0 < m i := by dsimp [m]; obtain ⟨z, hz⟩ := h4 i; have := hN i; omega
  have hc (i : ℕ) : 2 * m i = N i / 2 := by dsimp [m]; obtain ⟨z, hz⟩ := h4 i; omega
  let P : ∀ i, Fin (2 * m i) → ℝ := fun i j => p i (Fin.cast (hc i) j)
  have hP (i : ℕ) : P i ∈ S_n (2 * m i) := mem_S_n_cast (hc i) (hp i)
  have hs (i : ℕ) : 2 * (2 * m i) ≤ N i := by rw [hc i]; omega
  have hρcast (i : ℕ) : rootStepDensity (N i) (2 * m i) (P i) (hP i) (by have := hm i; omega) (hs i) =
      rootStepDensity (N i) (N i / 2) (p i) (hp i) (by have := hc i; have := hm i; omega) (by omega) :=
    rootStepDensity_cast (hc i) (p i) (hp i) (by have := hm i; omega) (by have := hc i; have := hm i; omega) (hs i) (by omega)
  have hB (i : ℕ) : BddAbove (range fun α : Icc (-Real.pi) Real.pi =>
      |Xi (lamOf Δ) α * (rootStepDensity (N i) (2 * m i) (P i) (hP i)
        (by have := hm i; omega) (hs i) (kMap (lamOf Δ) α) - rho Δ (kMap (lamOf Δ) α))|) := by
    simpa only [hρcast i] using hb i
  have hL : Tendsto (fun i => densityNorm Δ hΔ
      (fun x => rootStepDensity (N i) (2 * m i) (P i) (hP i)
        (by have := hm i; omega) (hs i) x - rho Δ x) (hB i)) atTop (𝓝 0) := by
    simpa only [hρcast] using hlim
  have hnP (i : ℕ) : 0 < N i / 2 := by have := hc i; have := hm i; omega
  obtain ⟨mρ, _, hmesh⟩ := eventually_rootPartition_gap_le hΔ 0 N (fun i => N i / 2)
    p hp hnP (fun _ => by omega) (fun i => by obtain ⟨z, hz⟩ := h4 i; omega) hb hlim
  let d := fun i => (2 / mρ) / (N i : ℝ)
  have hd : Tendsto d atTop (𝓝 0) := tendsto_const_nhds.div_atTop hNlim
  have hmesh' : ∀ᶠ i in atTop, ∀ j : Fin (2 * m i + 1),
      rootPartitionPoint (2 * m i) (P i) (by have := hm i; omega) j.succ -
        rootPartitionPoint (2 * m i) (P i) (by have := hm i; omega) j.castSucc ≤ d i := by
    filter_upwards [hmesh] with i hi
    exact ratio_root_mesh_cast (hc i) (by have := hm i; omega) (hnP i) (p i)
      fun j => (hi j).trans_eq (by dsimp [d]; norm_num; ring)
  have hk' : ∀ i, k < m i := hk
  change Tendsto (fun i => (N i : ℝ) * P i ⟨m i + k, by have := hk' i; omega⟩) atTop _
  clear hk; revert hk'
  induction k with
  | zero =>
    intro hk
    have hzero : Tendsto (fun i => P i ⟨m i, by have := hm i; omega⟩) atTop (𝓝 0) := by
      have ht : Tendsto (fun i => d i / 2) atTop (𝓝 0) := by simpa using hd.div_const 2
      refine Metric.tendsto_nhds.mpr fun ε hε => ?_
      filter_upwards [hmesh', ht.eventually (gt_mem_nhds hε)] with i hi hdi
      have hpos : 0 < P i ⟨m i, by have := hm i; omega⟩ := by
        have hlt := (hP i).2.1 (show (⟨m i - 1, by have := hm i; omega⟩ : Fin (2 * m i)) < ⟨m i, by have := hm i; omega⟩ by
          change m i - 1 < m i; have := hm i; omega)
        rw [ratio_central_pair (hm i) (hP i)] at hlt; linarith
      have hle : P i ⟨m i, by have := hm i; omega⟩ ≤ d i / 2 := by
        have hg := root_interior_gap_of_mesh (P i) (by have := hm i; omega) hi (m i - 1) (by have := hm i; omega)
        rw [show (⟨m i - 1 + 1, by have := hm i; omega⟩ : Fin (2 * m i)) = ⟨m i, by have := hm i; omega⟩ from
          Fin.ext (by have := hm i; dsimp; omega), ratio_central_pair (hm i) (hP i)] at hg
        linarith
      rw [Real.dist_eq, sub_zero, abs_of_pos hpos]; exact hle.trans_lt hdi
    have hpair (i : ℕ) : P i ⟨m i - 1, by have := hm i; omega⟩ = -P i ⟨m i, by have := hm i; omega⟩ :=
      ratio_central_pair (hm i) (hP i)
    have hgap := ratio_gap_tendsto_at_zero hΔ N (fun i => 2 * m i) P hP
      (fun i => by have := hm i; omega) hs hB hL
      (fun i => ⟨m i - 1, by have := hm i; omega⟩)
      (fun i => show m i - 1 + 1 < 2 * m i by have := hm i; omega)
      (by simpa only [hpair, neg_zero] using hzero.neg)
    have hidx (i : ℕ) : (⟨m i - 1 + 1, by have := hm i; omega⟩ : Fin (2 * m i)) = ⟨m i, by have := hm i; omega⟩ :=
      Fin.ext (by have := hm i; dsimp; omega)
    simp_rw [hidx, hpair] at hgap
    have ht := hgap.div_const 2
    rw [show (rho Δ 0)⁻¹ / 2 = (((0 : ℕ) : ℝ) + 1 / 2) / rho Δ 0 by push_cast; ring] at ht
    exact ht.congr fun i => by simp only [Nat.add_zero]; ring
  | succ k ih =>
    intro hk
    have hklow (i : ℕ) : k < m i := by have := hk i; omega
    have hprev := ih hklow
    have hzero : Tendsto (fun i => P i ⟨m i + k, by have := hklow i; omega⟩) atTop (𝓝 0) :=
      (hprev.div_atTop hNlim).congr fun i => by
        have : (N i : ℝ) ≠ 0 := by exact_mod_cast (hN i).ne'
        field_simp
    have hgap := ratio_gap_tendsto_at_zero hΔ N (fun i => 2 * m i) P hP
      (fun i => by have := hm i; omega) hs hB hL
      (fun i => ⟨m i + k, by have := hklow i; omega⟩)
      (fun i => show m i + k + 1 < 2 * m i by have := hk i; omega) hzero
    have ht := hprev.add hgap
    rw [show ((k : ℝ) + 1 / 2) / rho Δ 0 + (rho Δ 0)⁻¹ = (((k + 1 : ℕ) : ℝ) + 1 / 2) / rho Δ 0 by push_cast; ring] at ht
    refine ht.congr fun i => ?_
    rw [show (⟨m i + k + 1, by have := hk i; omega⟩ : Fin (2 * m i)) = ⟨m i + (k + 1), by have := hk i; omega⟩ from Fin.ext rfl]
    ring

private noncomputable def ratioMidpointLog (c : ℝ) (N : ℕ) (h4 : 4 ∣ N)
    (p : Fin (N / 2) → ℝ) (s : ℕ) (j : Fin (N / 4 - s - 1)) : ℝ :=
  let x := ratioPositiveRoot N h4 p ⟨j.val, by have := j.isLt; omega⟩
  let y := ratioPositiveRoot N h4 p ⟨j.val + 1, by have := j.isLt; omega⟩
  2 * ratioEll c ((x + y) / 2) - ratioEll c x - ratioEll c y

private theorem ratio_source_midpoint_limit {Δ c : ℝ} (hΔ : Δ < -1) (hc : 2 < c)
    (s : ℕ) (N : ℕ → ℕ) (h4 : ∀ i, 4 ∣ N i) (hN : ∀ i, 0 < N i)
    (p : ∀ i, Fin (N i / 2) → ℝ) (hp : ∀ i, p i ∈ S_n (N i / 2))
    (hNlim : Tendsto (fun i => (N i : ℝ)) atTop atTop)
    (hb : ∀ i, BddAbove (range fun α : Icc (-Real.pi) Real.pi =>
      |Xi (lamOf Δ) α * (rootStepDensity (N i) (N i / 2) (p i) (hp i)
        (by obtain ⟨z, hz⟩ := h4 i; have := hN i; omega) (by omega)
        (kMap (lamOf Δ) α) - rho Δ (kMap (lamOf Δ) α))|))
    (hlim : Tendsto (fun i => densityNorm Δ hΔ
      (fun x => rootStepDensity (N i) (N i / 2) (p i) (hp i)
        (by obtain ⟨z, hz⟩ := h4 i; have := hN i; omega) (by omega) x - rho Δ x) (hb i)) atTop (𝓝 0)) :
    Tendsto (fun i => Real.exp (∑ j : Fin (N i / 4 - s - 1), ratioMidpointLog c (N i) (h4 i) (p i) s j))
      atTop (𝓝 (2 / Real.pi)) := by
  let t := fun i => N i / 4 - s - 1
  let v : ℕ → ℕ → ℝ := fun i k => if hk : k < t i then ratioMidpointLog c (N i) (h4 i) (p i) s ⟨k, hk⟩ else 0
  have hnP (i : ℕ) : 0 < N i / 2 := by obtain ⟨z, hz⟩ := h4 i; have := hN i; omega
  obtain ⟨mρ, hmρ, hmesh⟩ := eventually_rootPartition_gap_le hΔ 0 N (fun i => N i / 2)
    p hp hnP (fun _ => by omega) (fun i => by obtain ⟨z, hz⟩ := h4 i; omega) hb hlim
  let D := 2 / mρ
  have hD : 0 ≤ D := div_nonneg (by norm_num) hmρ.le
  obtain ⟨M, hM, hupper⟩ := ratio_density_eventually_bounded hΔ
    (fun i => rootStepDensity (N i) (N i / 2) (p i) (hp i) (hnP i) (by omega)) hb hlim
  obtain ⟨B, hB, hprofile⟩ := ratio_midpoint_log_bound hc
  let C := B * (2 * M * D) ^ 2
  have hbound : ∀ᶠ i in atTop, ∀ k, ‖v i k‖ ≤ C / ((k : ℝ) + 1) ^ 2 := by
    filter_upwards [hmesh, hupper] with i hiMesh hiUpper k
    by_cases hk : k < t i
    · let j : Fin (N i / 4) := ⟨k, by dsimp [t] at hk; omega⟩
      let j' : Fin (N i / 4) := ⟨k + 1, by dsimp [t] at hk; omega⟩
      let a := ratioPositiveRoot (N i) (h4 i) (p i) j
      let b := ratioPositiveRoot (N i) (h4 i) (p i) j'
      have ha := ratio_positiveRoot_pos (h4 i) (hp i) j
      have hab : a ≤ b := (hp i).2.1.monotone (show N i / 4 + k ≤ N i / 4 + (k + 1) by omega)
      have hgap : b - a ≤ D / N i :=
        (root_interior_gap_of_mesh (p i) (hnP i)
          (fun l => (hiMesh l).trans_eq (by dsimp [D]; norm_num; ring))
          (N i / 4 + k) (by obtain ⟨z, hz⟩ := h4 i; dsimp [t] at hk; omega))
      have hrank := ratio_positiveRoot_lower (h4 i) (hp i) (hnP i) hiUpper j
      have hNp : (0 : ℝ) < N i := Nat.cast_pos.mpr (hN i)
      have hkpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      have hrank' : (k : ℝ) + 1 ≤ 2 * (M * N i) * a := by nlinarith only [hrank, (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
      have hgap' : (b - a) * (N i : ℝ) ≤ D := (le_div_iff₀ hNp).mp hgap
      have hratio : (b - a) / a ≤ (2 * M * D) / ((k : ℝ) + 1) := (div_le_div_iff₀ ha hkpos).mpr
        (by nlinarith [mul_le_mul_of_nonneg_right hrank' (sub_nonneg.mpr hab),
          mul_le_mul_of_nonneg_left hgap' (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hM) ha.le)])
      have hsq : ((b - a) / a) ^ 2 ≤ ((2 * M * D) / ((k : ℝ) + 1)) ^ 2 :=
        (sq_le_sq₀ (div_nonneg (sub_nonneg.mpr hab) ha.le) (by positivity)).mpr hratio
      change ‖v i k‖ ≤ _; rw [show v i k = ratioMidpointLog c (N i) (h4 i) (p i) s ⟨k, hk⟩ from dite_eq_left hk, Real.norm_eq_abs]
      exact (hprofile a b ha hab ((hp i).1 _).2).trans ((mul_le_mul_of_nonneg_left hsq hB).trans_eq (by dsimp [C]; rw [div_pow, ← mul_div_assoc]))
    · rw [show v i k = 0 from dite_eq_right hk, norm_zero]
      exact div_nonneg (mul_nonneg hB (sq_nonneg _)) (sq_nonneg _)
  have hpoint (k : ℕ) : Tendsto (fun i => v i k) atTop (𝓝 (Real.log (ratioWallisFactor k))) := by
    have hlarge : ∀ᶠ i in atTop, k < t i := by
      filter_upwards [hNlim.eventually (eventually_ge_atTop (((4 * (k + s + 2) : ℕ) : ℝ)))] with i hi
      have : 4 * (k + s + 2) ≤ N i := by exact_mod_cast hi
      dsimp [t]; obtain ⟨z, hz⟩ := h4 i; omega
    obtain ⟨i₀, hi₀⟩ := eventually_atTop.mp hlarge
    let T := fun i : ℕ => i₀ + i
    have hT : Tendsto T atTop atTop := tendsto_atTop.mpr fun a => eventually_atTop.mpr ⟨a, fun b hb => by dsimp [T]; omega⟩
    have hkT (i : ℕ) : k < t (T i) := hi₀ (T i) (by dsimp [T]; omega)
    have hkX (i : ℕ) : k < N (T i) / 4 := by have := hkT i; dsimp [t] at this; omega
    have hkY (i : ℕ) : k + 1 < N (T i) / 4 := by have := hkT i; dsimp [t] at this; omega
    have hX := ratio_full_positive_rank_scaling hΔ (fun i => N (T i)) (fun i => h4 (T i))
      (fun i => hN (T i)) (fun i => p (T i)) (fun i => hp (T i)) (hNlim.comp hT)
      (fun i => hb (T i)) (hlim.comp hT) k hkX
    have hY := ratio_full_positive_rank_scaling hΔ (fun i => N (T i)) (fun i => h4 (T i))
      (fun i => hN (T i)) (fun i => p (T i)) (fun i => hp (T i)) (hNlim.comp hT)
      (fun i => hb (T i)) (hlim.comp hT) (k + 1) hkY
    have hY' : Tendsto (fun i => (N (T i) : ℝ) * ratioPositiveRoot (N (T i)) (h4 (T i)) (p (T i)) ⟨k + 1, hkY i⟩)
        atTop (𝓝 (((k : ℝ) + 3 / 2) / rho Δ 0)) := by convert hY using 2; push_cast; ring
    have ht := ratio_half_integer_midpoint_log_tendsto hc (rho_pos hΔ 0) k
      (fun i => (N (T i) : ℝ)) (fun i => by exact_mod_cast (hN (T i)).ne') (hNlim.comp hT)
      (fun i => ratioPositiveRoot (N (T i)) (h4 (T i)) (p (T i)) ⟨k, hkX i⟩)
      (fun i => ratioPositiveRoot (N (T i)) (h4 (T i)) (p (T i)) ⟨k + 1, hkY i⟩)
      (fun i => (hp (T i)).1 _) (fun i => (hp (T i)).1 _)
      (fun i => ratio_positiveRoot_pos (h4 (T i)) (hp (T i)) _)
      (fun i => ratio_positiveRoot_pos (h4 (T i)) (hp (T i)) _) hX hY'
    have hvTail : Tendsto (fun i => v (T i) k) atTop (𝓝 (Real.log (ratioWallisFactor k))) :=
      ht.congr fun i => by rw [show v (T i) k = ratioMidpointLog c (N (T i)) (h4 (T i)) (p (T i)) s ⟨k, hkT i⟩ from dite_eq_left (hkT i)]; rfl
    refine Metric.tendsto_nhds.mpr fun ε hε => ?_
    obtain ⟨j₀, hj₀⟩ := eventually_atTop.mp (Metric.tendsto_nhds.mp hvTail ε hε)
    refine eventually_atTop.mpr ⟨i₀ + j₀, fun i hi => ?_⟩
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (show i₀ ≤ i by omega)
    exact hj₀ j (by omega)
  have hdom : Summable (fun k : ℕ => C / ((k : ℝ) + 1) ^ 2) := by
    simpa only [Nat.cast_add, Nat.cast_one, mul_one_div] using
      ((summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))).mul_left C
  have hlogSummable : Summable (fun k => Real.log (ratioWallisFactor k)) :=
    Summable.of_norm_bounded hdom fun k => le_of_tendsto (hpoint k).norm (hbound.mono fun _ hi => hi k)
  have hseries := tendsto_tsum_of_dominated_convergence hdom hpoint hbound
  have hwallis : Tendsto (fun n => ∏ k ∈ range n, ratioWallisFactor k) atTop (𝓝 (2 / Real.pi)) := by
    have hw := (Real.tendsto_euler_sin_prod (1 / 2)).div_const (Real.pi * (1 / 2))
    rw [show Real.sin (Real.pi * (1 / 2)) / (Real.pi * (1 / 2)) = 2 / Real.pi by
      rw [mul_one_div, Real.sin_pi_div_two]; field_simp] at hw
    exact hw.congr fun n => by unfold ratioWallisFactor; field_simp [Real.pi_ne_zero]
  have hlogs : Tendsto (fun n => ∏ k ∈ range n, ratioWallisFactor k) atTop
      (𝓝 (Real.exp (∑' k, Real.log (ratioWallisFactor k)))) := by
    refine ((Real.continuous_exp.tendsto _).comp hlogSummable.hasSum.tendsto_sum_nat).congr fun n => ?_
    dsimp only [Function.comp_def]; rw [Real.exp_sum]
    exact prod_congr rfl fun k _ => Real.exp_log (ratio_wallisFactor_pos k)
  have ht := (Real.continuous_exp.tendsto _).comp hseries
  rw [tendsto_nhds_unique hlogs hwallis] at ht
  refine ht.congr fun i => ?_
  dsimp only [Function.comp_def]
  rw [tsum_eq_sum fun k hk => dite_eq_right (fun h => hk (mem_range.mpr h)),
    ← Fin.sum_univ_eq_sum_range]
  exact congrArg Real.exp (sum_congr rfl fun j _ => dite_eq_left j.isLt)

/-! ### 3. Bulk quadrature Helpers, Finite Factorizations, and Fourier Integral -/

private noncomputable def ratioInteriorTest {k : ℕ} (N : ℕ) (p : Fin (k + 1) → ℝ)
    (_hp : p ∈ S_n (k + 1)) (v : Fin (k + 1) → ℝ) (x : ℝ) : ℝ :=
  ∑ j : Fin k, (Ico (p j.castSucc) (p j.succ)).indicator
    (fun _ => v j.castSucc / ((N : ℝ) * (p j.succ - p j.castSucc))) x

private theorem ratio_interiorTest_eq_density {k N : ℕ} {p : Fin (k + 1) → ℝ}
    (hp : p ∈ S_n (k + 1)) (hs : 2 * (k + 1) ≤ N) (v : Fin (k + 1) → ℝ)
    (j : Fin k) {x : ℝ} (hx : p j.castSucc ≤ x ∧ x < p j.succ) :
    ratioInteriorTest N p hp v x = v j.castSucc * rootStepDensity N (k + 1) p hp (by omega) hs x := by
  have hon : ratioInteriorTest N p hp v x = v j.castSucc / ((N : ℝ) * (p j.succ - p j.castSucc)) := by
    unfold ratioInteriorTest
    rw [Finset.sum_eq_single j (fun l _ hlj => indicator_of_notMem (fun hc => by
      rcases lt_or_gt_of_ne hlj with hlt | hgt
      · linarith [hx.1, hc.2, hp.2.1.monotone (show l.succ ≤ j.castSucc from hlt)]
      · linarith [hx.2, hc.1, hp.2.1.monotone (show j.succ ≤ l.castSucc from hgt)]) _)
      (fun h => absurd (Finset.mem_univ j) h)]
    exact Set.indicator_of_mem hx (fun _ => v j.castSucc / ((N : ℝ) * (p j.succ - p j.castSucc)))
  rw [hon, rootStepDensity_interior hp hs j hx]; ring

private theorem ratio_interiorTest_outside {k N : ℕ} {p : Fin (k + 1) → ℝ}
    (hp : p ∈ S_n (k + 1)) (v : Fin (k + 1) → ℝ) {x : ℝ}
    (hx : x < p 0 ∨ p (Fin.last k) ≤ x) : ratioInteriorTest N p hp v x = 0 :=
  Finset.sum_eq_zero fun j _ => indicator_of_notMem (fun hc => by
    rcases hx with hl | hr
    · linarith [hc.1, hp.2.1.monotone (Fin.zero_le j.castSucc)]
    · linarith [hc.2, hp.2.1.monotone (Fin.le_last j.succ)]) _

private theorem ratio_scaled_root_log_bound {c x y C : ℝ} {N : ℕ}
    (hc : 2 < c) (hN : 0 < N) (hC : 0 ≤ C) (hlarge : 2 * C ≤ N)
    (hx : x ∈ Ioo (-Real.pi) Real.pi) (hy : y ∈ Ioo (-Real.pi) Real.pi)
    (hshift : |(N : ℝ) * (x - y)| ≤ C * |x|) :
    |(N : ℝ) * (ratioEll c x - ratioEll c y)| ≤
      2 * (Real.pi * (c ^ 2 - 1) / (c ^ 2 - 2) ^ 2 + Real.pi ^ 2 / 4) * C := by
  let B := Real.pi * (c ^ 2 - 1) / (c ^ 2 - 2) ^ 2 + Real.pi ^ 2 / 4
  have hB : 0 ≤ B := add_nonneg (div_nonneg (mul_nonneg Real.pi_pos.le (by nlinarith)) (sq_nonneg _)) (by positivity)
  have hNp : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  by_cases hx0 : x = 0
  · subst x; rw [abs_zero, mul_zero] at hshift
    have hxy := sub_eq_zero.mp ((mul_eq_zero.mp (abs_nonpos_iff.mp hshift)).resolve_left hNp.ne')
    rw [← hxy, sub_self, mul_zero, abs_zero]; positivity
  · have hxpos := abs_pos.mpr hx0
    have hsmall : |y - x| ≤ C * |x| / N := (le_div_iff₀ hNp).mpr (by
      rw [abs_mul, abs_of_pos hNp, abs_sub_comm x y] at hshift; linarith)
    have hclose : |y - x| ≤ |x| / 2 := hsmall.trans ((div_le_iff₀ hNp).mpr
      (by nlinarith [mul_le_mul_of_nonneg_right hlarge hxpos.le]))
    have haway {t : ℝ} (ht : t ∈ uIcc x y) : |x| / 2 ≤ |t| ∧ t ≠ 0 ∧ t ∈ Ioo (-Real.pi) Real.pi := by
      have hd : |t - x| ≤ |x| / 2 := (show |t - x| ≤ |y - x| by
        rcases le_total x y with hxy | hyx
        · rw [uIcc_of_le hxy] at ht; rw [abs_of_nonneg (by linarith [ht.1]), abs_of_nonneg (by linarith)]; linarith [ht.2]
        · rw [uIcc_of_ge hyx] at ht; rw [abs_of_nonpos (by linarith [ht.2]), abs_of_nonpos (by linarith)]; linarith [ht.1]).trans hclose
      have htri : |x| ≤ |t| + |t - x| := by have h := abs_add_le t (x - t); rwa [add_sub_cancel, abs_sub_comm x t] at h
      refine ⟨by linarith, fun hz => by rw [hz, zero_sub, abs_neg] at hd; linarith, ?_⟩
      rcases le_total x y with hxy | hyx
      · rw [uIcc_of_le hxy] at ht; exact ⟨hx.1.trans_le ht.1, ht.2.trans_lt hy.2⟩
      · rw [uIcc_of_ge hyx] at ht; exact ⟨hy.1.trans_le ht.1, ht.2.trans_lt hx.2⟩
    have hm := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := ratioEll c) (f' := ratioEllPrime c)
      (C := 2 * B / |x|)
      (fun t ht => (ratio_hasDerivAt_ell hc (haway ht).2.2 (haway ht).2.1).hasDerivWithinAt)
      (fun t ht => by
        rw [Real.norm_eq_abs, le_div_iff₀ hxpos]
        have hb := ratio_ellPrime_weighted_bound hc (Ioo_subset_Icc_self (haway ht).2.2)
        rw [abs_mul] at hb; dsimp only [B]
        nlinarith [mul_le_mul_of_nonneg_right (haway ht).1 (abs_nonneg (ratioEllPrime c t)), hb])
      (convex_uIcc x y) left_mem_uIcc right_mem_uIcc
    simp only [Real.norm_eq_abs] at hm
    have hb : |ratioEll c y - ratioEll c x| ≤ (2 * B * C) / N :=
      hm.trans ((mul_le_mul_of_nonneg_left hsmall (by positivity)).trans_eq (by field_simp))
    rw [abs_mul, abs_of_pos hNp, abs_sub_comm, mul_comm]
    exact (le_div_iff₀ hNp).mp hb

private theorem ratio_even_quotient_split {m n s : ℕ} (hcount : s + n + s = m)
    {p : Fin m → ℝ} {q : Fin n → ℝ} {c : ℝ} (hc : 2 < c)
    (hp : p ∈ S_n m) (hq : q ∈ S_n n) :
    eigenvalueRegular c q / eigenvalueRegular c p =
      (((∏ j : Fin n, ‖M c (z (q j))‖ / ‖M c (z (p ⟨j.val + s, by omega⟩))‖) *
        ((∏ j : Fin s, ‖M c (z (p ⟨j.val, by omega⟩))‖) ^ 2)⁻¹ : ℝ) : ℂ) := by
  have hquot : eigenvalueRegular c q / eigenvalueRegular c p =
      (((∏ j, ‖M c (z (q j))‖) / ∏ j, ‖M c (z (p j))‖ : ℝ) : ℂ) := by
    rw [ratio_eigenvalueRegular hc hq, ratio_eigenvalueRegular hc hp]
    push_cast; simp only [div_eq_mul_inv, mul_inv_rev]; ring
  rw [hquot]; congr 1
  have hsym (j : Fin m) : ‖M c (z (p (Fin.rev j)))‖ = ‖M c (z (p j))‖ := by
    rw [show p (Fin.rev j) = -p j from hp.2.2 j, ratio_M_neg, Complex.norm_conj]
  subst m
  have hsplit : (∏ j : Fin (s + n + s), ‖M c (z (p j))‖) =
      (∏ j : Fin n, ‖M c (z (p ⟨j.val + s, by omega⟩))‖) * (∏ j : Fin s, ‖M c (z (p ⟨j.val, by omega⟩))‖) ^ 2 := by
    have hR : (∏ j : Fin s, ‖M c (z (p ⟨s + n + j.val, by omega⟩))‖) = ∏ j : Fin s, ‖M c (z (p ⟨j.val, by omega⟩))‖ := by
      calc _ = ∏ j : Fin s, ‖M c (z (p ⟨(Fin.rev j).val, by omega⟩))‖ := prod_congr rfl fun j _ => by
              rw [← hsym ⟨(Fin.rev j).val, by omega⟩]; congr 4
              exact Fin.ext (by simp only [Fin.val_rev]; omega)
        _ = _ := Equiv.prod_comp (Fin.revPerm : Equiv.Perm (Fin s)) fun j => ‖M c (z (p ⟨j.val, by omega⟩))‖
    have hmid : (∏ j : Fin n, ‖M c (z (p ⟨s + j.val, by omega⟩))‖) = ∏ j : Fin n, ‖M c (z (p ⟨j.val + s, by omega⟩))‖ :=
      prod_congr rfl fun j _ => by congr 4; exact Fin.ext (show s + j.val = j.val + s from Nat.add_comm _ _)
    have hprod : (∏ j : Fin (s + n + s), ‖M c (z (p j))‖) =
        (∏ j : Fin s, ‖M c (z (p ⟨j.val, by omega⟩))‖) *
        (∏ j : Fin n, ‖M c (z (p ⟨s + j.val, by omega⟩))‖) *
        ∏ j : Fin s, ‖M c (z (p ⟨s + n + j.val, by omega⟩))‖ := by
      rw [Fin.prod_univ_add, Fin.prod_univ_add]; rfl
    rw [hprod, hR, hmid]; ring
  rw [hsplit, prod_div_distrib]; simp only [div_eq_mul_inv, mul_inv_rev]; ring

private noncomputable def ratioZeroCoefficient {n : ℕ} (Δ c : ℝ) (N : ℕ) (q : Fin n → ℝ) (l : Fin n) : ℝ :=
  2 + c ^ 2 * ((N : ℝ) - 1) + c ^ 2 * ∑ j ∈ univ.erase l, d1Theta Δ 0 (q j)

private theorem ratio_odd_A_tendsto {Δ : ℝ} (hΔ : Δ < -1) (c : ℝ) (r : ℕ) (N n : ℕ → ℕ)
    (q : ∀ i, Fin (n i) → ℝ) (hq : ∀ i, q i ∈ S_n (n i)) (hn : ∀ i, 0 < n i) (hs : ∀ i, 2 * n i ≤ N i)
    (hcount : ∀ i, N i = 2 * (n i + r)) (hNlim : Tendsto (fun i => (N i : ℝ)) atTop atTop)
    (hb : ∀ i, BddAbove (range fun α : Icc (-Real.pi) Real.pi =>
      |Xi (lamOf Δ) α * (rootStepDensity (N i) (n i) (q i) (hq i) (hn i) (hs i)
        (kMap (lamOf Δ) α) - rho Δ (kMap (lamOf Δ) α))|))
    (hlim : Tendsto (fun i => densityNorm Δ hΔ
      (fun x => rootStepDensity (N i) (n i) (q i) (hq i) (hn i) (hs i) x - rho Δ x) (hb i)) atTop (𝓝 0))
    (l : ∀ i, Fin (n i)) (hl : ∀ i, q i (l i) = 0) :
    Tendsto (fun i => ratioZeroCoefficient Δ c (N i) (q i) (l i) / (2 * N i)) atTop
      (𝓝 (c ^ 2 * Real.pi * rho Δ 0)) := by
  have hweak := theorem26_sums_of_pos hΔ r N n q hq hn hs hcount hNlim hb hlim (d1Theta Δ 0)
    ((continuous_d1Theta_pair hΔ).comp (continuous_const.prodMk continuous_id))
  have hcb := rho_isCBESolution hΔ 0 ⟨by linarith [Real.pi_pos], Real.pi_pos.le⟩
  change 2 * Real.pi * rho Δ 0 = 1 + ∫ x in (-Real.pi)..Real.pi, d1Theta Δ 0 x * rho Δ x at hcb
  have ht := (((tendsto_const_nhds (x := (1 : ℝ))).add hweak).const_mul (c ^ 2 / 2)).add
    ((tendsto_inv_atTop_zero.comp hNlim).const_mul ((2 - c ^ 2 - c ^ 2 * d1Theta Δ 0 0) / 2))
  rw [show c ^ 2 / 2 * (1 + ∫ x in (-Real.pi)..Real.pi, d1Theta Δ 0 x * rho Δ x) +
      ((2 - c ^ 2 - c ^ 2 * d1Theta Δ 0 0) / 2) * 0 = c ^ 2 * Real.pi * rho Δ 0 by rw [← hcb]; ring] at ht
  refine ht.congr fun i => ?_
  have hN : (N i : ℝ) ≠ 0 := by exact_mod_cast (show N i ≠ 0 by have := hn i; have := hs i; omega)
  have he := sum_erase_add (s := (univ : Finset (Fin (n i)))) (fun j => d1Theta Δ 0 (q i j)) (mem_univ (l i))
  rw [hl i] at he; unfold ratioZeroCoefficient; dsimp only [Function.comp_def]; field_simp; nlinarith only [he]

private theorem ratio_odd_quotient_factors {c : ℝ} (hc : 2 < c) (s N : ℕ) (h4 : 4 ∣ N)
    (hr : 2 * s + 1 ≤ N / 2) (hn : 0 < N / 2 - (2 * s + 1))
    (p : Fin (N / 2) → ℝ) (hp : p ∈ S_n (N / 2))
    (q : Fin (N / 2 - (2 * s + 1)) → ℝ) (hq : q ∈ S_n (N / 2 - (2 * s + 1)))
    (l : Fin (N / 2 - (2 * s + 1))) (hl : q l = 0) :
    eigenvalueZero N c q l / eigenvalueRegular c p =
      (((ratioZeroCoefficient (anisotropy c) c N q l / (2 * N)) *
        ((N : ℝ) * ‖M c (z (ratioPositiveRoot N h4 p ⟨0, by obtain ⟨z, hz⟩ := h4; omega⟩))‖⁻¹) *
        (‖M c (z (p ⟨s, by omega⟩))‖ * (∏ j : Fin s, ‖M c (z (p ⟨j.val, by omega⟩))‖) ^ 2)⁻¹ *
        Real.exp (∑ j : Fin (N / 4 - s - 1), ratioMidpointLog c N h4 p s j) *
        Real.exp (∑ j, (ratioEll c (q j) - ratioEll c (alignedRoot N (2 * s + 1) hr p j))) : ℝ) : ℂ) := by
  let m := N / 4; let t := N / 4 - s - 1
  have hNcount : 2 * m = N / 2 := by dsimp [m]; obtain ⟨z, hz⟩ := h4; omega
  have hmt : t + 1 + s = m := by dsimp [m, t]; obtain ⟨z, hz⟩ := h4; omega
  have hqcount : 2 * t + 1 = N / 2 - (2 * s + 1) := by omega
  have first_lt : 0 < N / 4 := by obtain ⟨z, hz⟩ := h4; omega
  let first : Fin (N / 4) := ⟨0, first_lt⟩
  have hlogcorr : (∑ j, ratioEll c (alignedRoot N (2 * s + 1) hr p j)) - (∑ j, ratioEll c (p j)) =
      (∑ j : Fin t, ratioMidpointLog c N h4 p s j) -
        ratioEll c (ratioPositiveRoot N h4 p first) - ratioEll c (p ⟨s, by omega⟩) -
        2 * ∑ j : Fin s, ratioEll c (p ⟨j.val, by omega⟩) := by
    have href (j : Fin (N / 2)) : ratioEll c (p (Fin.rev j)) = ratioEll c (p j) := by
      rw [show p (Fin.rev j) = -p j from hp.2.2 j, ratio_ell_neg]
    let f : Fin m → ℝ := fun j => ratioEll c (ratioPositiveRoot N h4 p j)
    let g : Fin t → ℝ := fun j => ratioEll c
      ((ratioPositiveRoot N h4 p ⟨j.val, by omega⟩ + ratioPositiveRoot N h4 p ⟨j.val + 1, by omega⟩) / 2)
    have hP : (∑ j, ratioEll c (p j)) = 2 * ∑ j, f j := by
      have hs := sum_fin_split_block (m := N / 2) (a := m) (n := m) (b := 0) (by omega) (fun j => ratioEll c (p j))
      simp only [Fin.sum_univ_zero, add_zero] at hs
      have hleft : (∑ j : Fin m, ratioEll c (p ⟨j.val, by omega⟩)) = ∑ j, f j := by
        calc _ = ∑ j : Fin m, ratioEll c (p ⟨m + (Fin.rev j).val, by omega⟩) := sum_congr rfl fun j _ => by
                rw [← href ⟨m + (Fin.rev j).val, by omega⟩]; congr 2
                exact Fin.ext (by simp only [Fin.val_rev]; omega)
          _ = _ := Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin m)) f
      have hmid : (∑ j : Fin m, ratioEll c (p ⟨j.val + m, by omega⟩)) = ∑ j, f j :=
        sum_congr rfl fun j _ => by dsimp [f, ratioPositiveRoot]; congr 2; exact Fin.ext (show j.val + m = m + j.val from Nat.add_comm _ _)
      linarith only [hs, hleft, hmid]
    have hA : (∑ j, ratioEll c (alignedRoot N (2 * s + 1) hr p j)) = 2 * ∑ j, g j := by
      let A := fun j => ratioEll c (alignedRoot N (2 * s + 1) hr p j)
      have hsA (j) : A (Fin.rev j) = A j := by dsimp [A]; rw [alignedRoot_rev hr hp, ratio_ell_neg]
      have hzA : A ⟨t, by omega⟩ = 0 := by
        have h := alignedRoot_rev hr hp ⟨t, by omega⟩
        rw [show Fin.rev (⟨t, by omega⟩ : Fin (N / 2 - (2 * s + 1))) = ⟨t, by omega⟩ from
          Fin.ext (by simp only [Fin.val_rev]; omega)] at h
        dsimp [A]; rw [show alignedRoot N (2 * s + 1) hr p ⟨t, by omega⟩ = 0 by linarith, ratio_ell_zero]
      have hs := sum_fin_split_block (m := N / 2 - (2 * s + 1)) (a := t) (n := 1) (b := t) (by omega) A
      simp only [Fin.sum_univ_one, Fin.val_zero, hzA, zero_add] at hs
      have hleft : (∑ j : Fin t, A ⟨j.val, by omega⟩) = ∑ j : Fin t, A ⟨t + 1 + j.val, by omega⟩ := by
        calc _ = ∑ j : Fin t, A ⟨t + 1 + (Fin.rev j).val, by omega⟩ := sum_congr rfl fun j _ => by
                rw [← hsA ⟨t + 1 + (Fin.rev j).val, by omega⟩]; congr 1
                exact Fin.ext (by simp only [Fin.val_rev]; omega)
          _ = _ := Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin t)) fun j => A ⟨t + 1 + j.val, by omega⟩
      have hmid : (∑ j : Fin t, A ⟨t + 1 + j.val, by omega⟩) = ∑ j, g j := sum_congr rfl fun j _ => by
        have hodd : (2 * s + 1) % 2 ≠ 0 := by omega
        dsimp [A, g, ratioPositiveRoot]; simp only [alignedRoot, ite_eq_right hodd]
        rw [show (⟨t + 1 + j.val + (2 * s + 1 - 1) / 2, by omega⟩ : Fin (N / 2)) = ⟨m + j.val, by omega⟩ from Fin.ext (by dsimp; omega),
          show (⟨t + 1 + j.val + (2 * s + 1 + 1) / 2, by omega⟩ : Fin (N / 2)) = ⟨m + (j.val + 1), by omega⟩ from Fin.ext (by dsimp; omega)]
      linarith only [hs, hleft, hmid]
    let F : Fin (t + 1) → ℝ := fun j => f ⟨j.val, by omega⟩
    have h₀ := Fin.sum_univ_succ F; have h₁ := Fin.sum_univ_castSucc F
    have hsF := sum_fin_split_block (m := m) (a := t + 1) (n := s) (b := 0) (by omega) f
    simp only [Fin.sum_univ_zero, add_zero] at hsF
    change (∑ j, f j) = (∑ j : Fin s, f ⟨j.val + (t + 1), by omega⟩) + ∑ j : Fin (t + 1), F j at hsF
    change (∑ j : Fin (t + 1), F j) = f ⟨0, by omega⟩ + ∑ j : Fin t, f ⟨j.val + 1, by omega⟩ at h₀
    change (∑ j : Fin (t + 1), F j) = (∑ j : Fin t, f ⟨j.val, by omega⟩) + f ⟨t, by omega⟩ at h₁
    have hft : f ⟨t, by omega⟩ = ratioEll c (p ⟨s, by omega⟩) := by
      change ratioEll c (p ⟨m + t, by omega⟩) = _; rw [← href ⟨m + t, by omega⟩]
      congr 2; exact Fin.ext (by simp only [Fin.val_rev]; omega)
    have htail : (∑ j : Fin s, f ⟨j.val + (t + 1), by omega⟩) = ∑ j : Fin s, ratioEll c (p ⟨j.val, by omega⟩) := by
      calc _ = ∑ j : Fin s, ratioEll c (p ⟨(Fin.rev j).val, by omega⟩) := sum_congr rfl fun j _ => by
              change ratioEll c (p ⟨m + (j.val + (t + 1)), by omega⟩) = _
              rw [← href ⟨m + (j.val + (t + 1)), by omega⟩]; congr 2
              exact Fin.ext (by simp only [Fin.val_rev]; omega)
        _ = _ := Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin s)) fun j => ratioEll c (p ⟨j.val, by omega⟩)
    have hmidSum : (∑ j : Fin t, ratioMidpointLog c N h4 p s j) =
        2 * (∑ j, g j) - (∑ j : Fin t, f ⟨j.val, by omega⟩) - ∑ j : Fin t, f ⟨j.val + 1, by omega⟩ := by
      change (∑ j : Fin t, (2 * g j - f ⟨j.val, by omega⟩ - f ⟨j.val + 1, by omega⟩)) = _
      rw [sum_sub_distrib, sum_sub_distrib, ← mul_sum]
    rw [hA, hP, hmidSum, ← hft, ← htail]; dsimp [first]; linarith only [h₀, h₁, hsF]
  have hfullQ : (∏ j ∈ univ.erase l, ‖M c (z (q j))‖) = ∏ j, ‖M c (z (q j))‖ := by
    simpa only [hl, z_zero, M, sub_self, div_zero, sub_zero, norm_one, mul_one] using
      prod_erase_mul univ (fun j => ‖M c (z (q j))‖) (mem_univ l)
  have hquot : eigenvalueZero N c q l / eigenvalueRegular c p =
      (((ratioZeroCoefficient (anisotropy c) c N q l / 2) *
        ((∏ j, ‖M c (z (q j))‖) / ∏ j, ‖M c (z (p j))‖) : ℝ) : ℂ) := by
    rw [ratio_eigenvalueZero hc hq l hl, ratio_eigenvalueRegular hc hp, hfullQ]
    unfold ratioZeroCoefficient d1Theta; push_cast; ring
  rw [hquot]; apply congrArg (fun x : ℝ => (x : ℂ))
  have hbulk : (∏ j, ‖M c (z (q j))‖) / (∏ j, ‖M c (z (p j))‖) =
      Real.exp (∑ j, (ratioEll c (q j) - ratioEll c (alignedRoot N (2 * s + 1) hr p j))) *
        Real.exp ((∑ j, ratioEll c (alignedRoot N (2 * s + 1) hr p j)) - ∑ j, ratioEll c (p j)) := by
    rw [← Real.exp_add, sum_sub_distrib, sub_add_sub_cancel, Real.exp_sub, ratio_exp_sum_ell hc q, ratio_exp_sum_ell hc p]
  have hcorr : Real.exp ((∑ j, ratioEll c (alignedRoot N (2 * s + 1) hr p j)) - ∑ j, ratioEll c (p j)) =
      ‖M c (z (ratioPositiveRoot N h4 p first))‖⁻¹ *
        (‖M c (z (p ⟨s, by omega⟩))‖ * (∏ j : Fin s, ‖M c (z (p ⟨j.val, by omega⟩))‖) ^ 2)⁻¹ *
          Real.exp (∑ j : Fin (N / 4 - s - 1), ratioMidpointLog c N h4 p s j) := by
    have hexp2 : Real.exp (2 * ∑ j : Fin s, ratioEll c (p ⟨j.val, by omega⟩)) =
        (Real.exp (∑ j : Fin s, ratioEll c (p ⟨j.val, by omega⟩))) ^ 2 := by
      rw [two_mul, Real.exp_add, pow_two]
    dsimp [t] at hlogcorr
    rw [hlogcorr, Real.exp_sub, Real.exp_sub, Real.exp_sub, ratio_exp_ell hc, ratio_exp_ell hc,
      hexp2, ratio_exp_sum_ell hc (fun j : Fin s => p ⟨j.val, by omega⟩)]
    simp only [div_eq_mul_inv, mul_inv_rev]; ring
  rw [hbulk, hcorr]
  have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hn₀ := norm_ne_zero_iff.mpr (ratio_M_ne_zero hc (ratioPositiveRoot N h4 p first))
  have hn₁ := norm_ne_zero_iff.mpr (ratio_M_ne_zero hc (p ⟨s, by omega⟩))
  have hprod : (∏ j : Fin s, ‖M c (z (p ⟨j.val, by omega⟩))‖) ≠ 0 :=
    prod_ne_zero_iff.mpr fun _ _ => norm_ne_zero_iff.mpr (ratio_M_ne_zero hc _)
  dsimp [first]; field_simp [hNne, hn₀, hn₁, hprod]

private theorem ratio_integral_eq_fourier {Δ c : ℝ} (hΔ : Δ < -1) (hc : 2 < c) (hcΔ : anisotropy c = Δ) :
    (∫ x in (-Real.pi)..Real.pi, ratioEllPrime c x * tauCont Δ x) =
      (∫ x in (-Real.pi)..Real.pi, PottsDiscontinuity.fourierEllPrime (lamOf Δ) x * tau (-Real.cosh (lamOf Δ)) x) := by
  have hlam : 0 < lamOf Δ := lamOf_pos hΔ
  have hcosh : Real.cosh (lamOf Δ) = -Δ := cosh_lamOf hΔ
  have hc2 : c ^ 2 = 2 + 2 * Real.cosh (lamOf Δ) := by unfold anisotropy at hcΔ; nlinarith
  apply intervalIntegral.integral_congr_ae_restrict
  filter_upwards [ae_restrict_mem measurableSet_uIoc, ae_restrict_of_ae (Measure.ae_ne volume Real.pi)] with x hx hxp
  have hxIoc : x ∈ Ioc (-Real.pi) Real.pi := by simpa [uIoc_of_le (neg_le_self Real.pi_nonneg)] using hx
  have hxIoo : x ∈ Ioo (-Real.pi) Real.pi := ⟨hxIoc.1, lt_of_le_of_ne hxIoc.2 hxp⟩
  have hprime : ratioEllPrime c x = PottsDiscontinuity.fourierEllPrime (lamOf Δ) x := by
    by_cases hx0 : x = 0
    · subst x; simp [ratioEllPrime, ratioNumerator, PottsDiscontinuity.fourierEllPrime]
    have hfun : ratioEll c =ᶠ[𝓝 x] PottsDiscontinuity.fourierEll (lamOf Δ) := by
      filter_upwards [Ioo_mem_nhds hxIoo.1 hxIoo.2, eventually_ne_nhds hx0] with y hy hy0
      simpa [ratioEll, BetheAnsatz.z] using (PottsDiscontinuity.fourierEll_eq_log_norm hlam hc2 hy hy0).symm
    rw [← ((ratio_hasDerivAt_ell hc hxIoo hx0).congr_of_eventuallyEq hfun.symm).deriv,
      (PottsDiscontinuity.fourierEll_hasDerivAt hlam hxIoo hx0).deriv]
  rw [hprime, show -Real.cosh (lamOf Δ) = Δ by rw [hcosh]; ring, tau_eq_tauCont hΔ hxIoo]

/-! ### 4. Main Section: Bulk Log-Limit and Fourier Eigenvalue-Ratio Limits -/

section

variable {Δ : ℝ} (hΔ : Δ < -1) (r : ℕ) (N : ℕ → ℕ) (h4 : ∀ i, 4 ∣ N i)
    (hr : ∀ i, r ≤ N i / 2) (hN : ∀ i, 0 < N i) (hn : ∀ i, 0 < N i / 2 - r)
    (p : ∀ i, Fin (N i / 2) → ℝ) (q : ∀ i, Fin (N i / 2 - r) → ℝ)
    (hp : ∀ i, p i ∈ S_n (N i / 2)) (hq : ∀ i, q i ∈ S_n (N i / 2 - r))
    (hpBE : ∀ i, DiscreteBetheEquation Δ (N i) (N i / 2) (p i))
    (hqBE : ∀ i, DiscreteBetheEquation Δ (N i) (N i / 2 - r) (q i))
    (hNlim : Tendsto (fun i => (N i : ℝ)) atTop atTop)
    (hbp : ∀ i, BddAbove (range fun α : Icc (-Real.pi) Real.pi =>
      |Xi (lamOf Δ) α *
        (rootStepDensity (N i) (N i / 2) (p i) (hp i) (half_pos_of_half_sub_pos N r hn i) (two_mul_half_le N i)
          (kMap (lamOf Δ) α) - rho Δ (kMap (lamOf Δ) α))|))
    (hbq : ∀ i, BddAbove (range fun α : Icc (-Real.pi) Real.pi =>
      |Xi (lamOf Δ) α *
        (rootStepDensity (N i) (N i / 2 - r) (q i) (hq i) (hn i) (two_mul_half_sub_le N r i)
          (kMap (lamOf Δ) α) - rho Δ (kMap (lamOf Δ) α))|))
    {K : ℝ} (hK : 0 ≤ K)
    (hrate : ∀ᶠ i in atTop,
      densityNorm Δ hΔ (fun x => rootStepDensity (N i) (N i / 2) (p i) (hp i)
        (half_pos_of_half_sub_pos N r hn i) (two_mul_half_le N i) x - rho Δ x) (hbp i) ≤ K / N i ∧
      densityNorm Δ hΔ (fun x => rootStepDensity (N i) (N i / 2 - r) (q i) (hq i)
        (hn i) (two_mul_half_sub_le N r i) x - rho Δ x) (hbq i) ≤ K / N i)

include hΔ h4 hr hN hp hq hpBE hqBE hNlim hbp hbq hK hrate

private theorem ratio_bulk_log_limit {c : ℝ} (hc : 2 < c) :
    Tendsto (fun i => ∑ j, (ratioEll c (q i j) -
      ratioEll c (alignedRoot (N i) r (hr i) (p i) j))) atTop
      (𝓝 ((r : ℝ) * ∫ x in (-Real.pi)..Real.pi, ratioEllPrime c x * tauCont Δ x)) := by
  let Pρ : ℕ → ℝ → ℝ := fun i =>
    rootStepDensity (N i) (N i / 2) (p i) (hp i) (half_pos_of_half_sub_pos N r hn i) (two_mul_half_le N i)
  let Qρ : ℕ → ℝ → ℝ := fun i =>
    rootStepDensity (N i) (N i / 2 - r) (q i) (hq i) (hn i) (two_mul_half_sub_le N r i)
  have hnormQ : Tendsto (fun i => densityNorm Δ hΔ (fun x => Qρ i x - rho Δ x) (hbq i)) atTop (𝓝 0) :=
    ratio_densityNorm_tendsto_of_rate hΔ N hNlim _ hbq (hrate.mono fun _ h => h.2)
  let w := Real.sinh (lamOf Δ) / (Real.cosh (lamOf Δ) + 1)
  have hw := density_weight_lower_pos hΔ
  have herror : ∀ᶠ i in atTop, ∀ x ∈ Icc (-Real.pi) Real.pi,
      |Pρ i x - rho Δ x| ≤ (K / w) / N i ∧ |Qρ i x - rho Δ x| ≤ (K / w) / N i := by
    filter_upwards [hrate] with i hi x hx
    exact ⟨(abs_le_densityNorm_div hΔ _ (hbp i) hx).trans ((div_le_div_of_nonneg_right hi.1 hw.le).trans_eq (by ring)),
      (abs_le_densityNorm_div hΔ _ (hbq i) hx).trans ((div_le_div_of_nonneg_right hi.2 hw.le).trans_eq (by ring))⟩
  obtain ⟨_, _, _, DQ, _, _, _, hDQ, G, hgeom⟩ :=
    eventually_offset_estimates_of_density_rate hΔ r N h4 hr hN hn p q hp hq hNlim (div_nonneg hK hw.le) herror
  obtain ⟨M, hM, hupper⟩ := ratio_density_eventually_bounded hΔ Qρ hbq hnormQ
  have hU := theorem29_convergence hΔ r N h4 hr hN hn p q hp hq hpBE hqBE hNlim hbp hbq hK hrate
  let k : ℕ → ℕ := fun i => N i / 2 - r - 1
  have hk (i : ℕ) : k i + 1 = N i / 2 - r := by dsimp [k]; have := hn i; omega
  let q' : ∀ i, Fin (k i + 1) → ℝ := fun i j => q i (Fin.cast (hk i) j)
  let a' : ∀ i, Fin (k i + 1) → ℝ := fun i j => alignedRoot (N i) r (hr i) (p i) (Fin.cast (hk i) j)
  have hq' (i : ℕ) : q' i ∈ S_n (k i + 1) := mem_S_n_cast (hk i) (hq i)
  have ha' (i : ℕ) (j : Fin (k i + 1)) : a' i j ∈ Ioo (-Real.pi) Real.pi := by
    dsimp [a']; unfold alignedRoot; split
    · exact (hp i).1 _
    · exact ⟨by linarith [((hp i).1 ⟨(Fin.cast (hk i) j).val + (r - 1) / 2, by have := hr i; omega⟩).1,
        ((hp i).1 ⟨(Fin.cast (hk i) j).val + (r + 1) / 2, by have := hr i; omega⟩).1],
      by linarith [((hp i).1 ⟨(Fin.cast (hk i) j).val + (r - 1) / 2, by have := hr i; omega⟩).2,
        ((hp i).1 ⟨(Fin.cast (hk i) j).val + (r + 1) / 2, by have := hr i; omega⟩).2]⟩
  have hs' (i : ℕ) : 2 * (k i + 1) ≤ N i := by rw [hk i]; omega
  have hρcast (i : ℕ) (x : ℝ) : rootStepDensity (N i) (k i + 1) (q' i) (hq' i) (by omega) (hs' i) x = Qρ i x :=
    congrFun (rootStepDensity_cast (hk i) (q i) (hq i) (by omega) (hn i) (hs' i) (by omega)) x
  let d : ℕ → ℝ := fun i => DQ / N i
  have hd : Tendsto d atTop (𝓝 0) := tendsto_const_nhds.div_atTop hNlim
  have hd0 (i : ℕ) : 0 ≤ d i := div_nonneg hDQ (Nat.cast_nonneg _)
  have hmesh : ∀ᶠ i in atTop, ∀ j : Fin (k i + 1 + 1),
      rootPartitionPoint (k i + 1) (q' i) (by omega) j.succ -
        rootPartitionPoint (k i + 1) (q' i) (by omega) j.castSucc ≤ d i :=
    hgeom.mono fun i hi => ratio_root_mesh_cast (hk i) (by omega) (hn i) (q i) hi.meshQ
  have hshift : ∀ᶠ i in atTop, ∀ j, |(N i : ℝ) * (q' i j - a' i j)| ≤ (G : ℝ) * |q' i j| := by
    filter_upwards [hgeom] with i hi j
    change |(N i : ℝ) * (q i (Fin.cast (hk i) j) - alignedRoot (N i) r (hr i) (p i) (Fin.cast (hk i) j))| ≤ _
    rw [← offsetDisplacement_eq_alignedRoot (N i) r (h4 i)]
    have hp2 := hi.pair (Fin.cast (hk i) j) (Fin.rev (Fin.cast (hk i) j))
    rw [offsetDisplacement_rev (h4 i) (hr i) (hp i) (hq i), show q i (Fin.rev _) = -q i _ from (hq i).2.2 _] at hp2
    have he2 (z : ℝ) : |z - -z| = 2 * |z| := by rw [sub_neg_eq_add, ← two_mul, abs_mul, abs_of_pos two_pos]
    rw [he2, he2] at hp2; dsimp [q']; linarith
  let B := Real.pi * (c ^ 2 - 1) / (c ^ 2 - 2) ^ 2 + Real.pi ^ 2 / 4
  have hB : 0 ≤ B := add_nonneg (div_nonneg (mul_nonneg Real.pi_pos.le (by nlinarith)) (sq_nonneg _)) (by positivity)
  let L := 2 * B * (G : ℝ)
  let F : ℕ → ℝ → ℝ := fun i => ratioInteriorTest (N i) (q' i) (hq' i)
    (fun j => (N i : ℝ) * (ratioEll c (q' i j) - ratioEll c (a' i j)))
  let E : ℝ → ℝ := fun x => (r : ℝ) * tauCont Δ x / rho Δ x
  let g : ℝ → ℝ := (Icc (-Real.pi) Real.pi).indicator (fun x => ratioEllPrime c x * E x * rho Δ x)
  let bound : ℝ → ℝ := (Icc (-Real.pi) Real.pi).indicator (fun _ => L * M)
  have hsupp {i : ℕ} {x : ℝ} (hx : x ∉ Icc (-Real.pi) Real.pi) : F i x = 0 := by
    apply ratio_interiorTest_outside (hq' i)
    by_cases hlo : x < -Real.pi
    · exact Or.inl (hlo.trans ((hq' i).1 0).1)
    · exact Or.inr ((((hq' i).1 (Fin.last (k i))).2.le).trans (lt_of_not_ge fun h => hx ⟨le_of_not_gt hlo, h⟩).le)
  have hmeas : ∀ᶠ i in atTop, AEStronglyMeasurable (F i) := Eventually.of_forall fun i =>
    (integrable_finsetSum _ fun j _ => (integrable_indicator_iff measurableSet_Ico).mpr
      (integrableOn_const (by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top))).aestronglyMeasurable
  have hbound : ∀ᶠ i in atTop, ∀ᵐ x, ‖F i x‖ ≤ bound x := by
    filter_upwards [hshift, hupper, hNlim.eventually (eventually_ge_atTop (2 * (G : ℝ)))] with i hi hu hiN
    refine Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs]
    by_cases hx : x ∈ Icc (-Real.pi) Real.pi
    · rw [show bound x = L * M from indicator_of_mem hx _]; dsimp only [F]
      by_cases hl : x < q' i 0
      · rw [ratio_interiorTest_outside (hq' i) _ (Or.inl hl), abs_zero]; positivity
      · by_cases hr' : q' i (Fin.last (k i)) ≤ x
        · rw [ratio_interiorTest_outside (hq' i) _ (Or.inr hr'), abs_zero]; positivity
        · obtain ⟨j0, hj0, hjx⟩ := exists_interior_root_cell (by omega : 0 < k i + 1) (q' i)
            (le_of_not_gt hl) (lt_of_not_ge hr')
          let m : Fin (k i) := ⟨j0.val, by omega⟩
          have hxcell : q' i m.castSucc ≤ x ∧ x < q' i m.succ := hjx
          rw [ratio_interiorTest_eq_density (hq' i) (hs' i) _ m hxcell, abs_mul]
          have hrnonneg : 0 ≤ rootStepDensity (N i) (k i + 1) (q' i) (hq' i) (by omega) (hs' i) x := by
            rw [rootStepDensity_interior (hq' i) (hs' i) m hxcell]
            exact div_nonneg zero_le_one (mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr ((hq' i).2.1.monotone (Fin.castSucc_le_succ m))))
          rw [abs_of_nonneg hrnonneg]
          exact mul_le_mul (ratio_scaled_root_log_bound hc (hN i) G.2 hiN ((hq' i).1 _) (ha' i _) (hi _))
            (by rw [hρcast]; exact hu x hx) hrnonneg (by positivity)
    · rw [hsupp hx, abs_zero, show bound x = 0 from indicator_of_notMem hx _]
  have hpoint : ∀ᵐ x, Tendsto (fun i => F i x) atTop (𝓝 (g x)) := by
    filter_upwards [Measure.ae_ne volume (0 : ℝ), Measure.ae_ne volume Real.pi, Measure.ae_ne volume (-Real.pi)]
      with x hx0 hxp hxm
    by_cases hx : x ∈ Icc (-Real.pi) Real.pi
    · have hxoo : x ∈ Ioo (-Real.pi) Real.pi := ⟨lt_of_le_of_ne hx.1 (Ne.symm hxm), lt_of_le_of_ne hx.2 hxp⟩
      rw [show g x = ratioEllPrime c x * E x * rho Δ x from indicator_of_mem hx _]
      let u : ℕ → ℝ := fun i => q' i (ratioRootIndex (by omega) (q' i) x)
      let v : ℕ → ℝ := fun i => a' i (ratioRootIndex (by omega) (q' i) x)
      have hfirst := ratio_tendsto_root_left_of_eventual_mesh (fun i => k i + 1) (fun _ => by omega) q' hq' d hd hd0 hmesh (fun _ => 0) 0 (fun _ => le_rfl)
      have hlast_r : Tendsto (fun i => q' i (Fin.last (k i))) atTop (𝓝 Real.pi) := by
        simpa only [show ∀ i, q' i (Fin.last (k i)) = -q' i 0 from fun i => by simpa only [Fin.rev_zero] using (hq' i).2.2 0, neg_neg] using hfirst.neg
      have hu : Tendsto u atTop (𝓝 x) := by
        refine Metric.tendsto_nhds.mpr fun ε hε => ?_
        filter_upwards [hmesh, hfirst.eventually (gt_mem_nhds hxoo.1), hlast_r.eventually (lt_mem_nhds hxoo.2),
          hd.eventually (gt_mem_nhds hε)] with i hi hleft hright hdi
        have hright' : x < q' i ⟨k i + 1 - 1, by omega⟩ := by
          simpa only [show (⟨k i + 1 - 1, by omega⟩ : Fin (k i + 1)) = Fin.last (k i) from Fin.ext (by simp)] using hright
        obtain ⟨hj, hcell⟩ := ratio_rootIndex_cell (by omega : 0 < k i + 1) (q' i) (hq' i).2.1 hleft.le hright'
        have hgap := root_interior_gap_of_mesh (q' i) (by omega) hi (ratioRootIndex (by omega) (q' i) x).val hj
        rw [Real.dist_eq]; dsimp only [u]
        rw [abs_of_nonpos (sub_nonpos.mpr hcell.1)]
        exact (by linarith [hcell.2] : -(q' i (ratioRootIndex _ (q' i) x) - x) ≤ d i).trans_lt hdi
      have he_lim : Tendsto (fun i => (N i : ℝ) * (u i - v i)) atTop (𝓝 (E x)) := by
        refine ((hU.tendsto_at hx).div_const (rho Δ x)).congr fun i => ?_
        have hproj : (N i : ℝ) * (u i - v i) = offsetFunction (N i) r (h4 i) (hr i) (p i) (q i) (hn i) x := by
          change (N i : ℝ) * (q i (Fin.cast (hk i) (ratioRootIndex (by omega) (q' i) x)) -
            alignedRoot (N i) r (hr i) (p i) (Fin.cast (hk i) (ratioRootIndex (by omega) (q' i) x))) = _
          rw [← offsetDisplacement_eq_alignedRoot (N i) r (h4 i),
            ratio_rootIndex_cast (hk i) (by omega) (hn i) (q i) x,
            ← ratio_offsetFunction_eq_predecessor (h4 i) (hr i) (hn i) (p i) (q i) (hq i)]
        rw [hproj]; field_simp [(rho_pos hΔ x).ne']
      have hv : Tendsto v atTop (𝓝 x) := by
        refine (by simpa only [sub_zero] using hu.sub (he_lim.div_atTop hNlim) : Tendsto _ _ (𝓝 x)).congr fun i => ?_
        have : (N i : ℝ) ≠ 0 := by exact_mod_cast (hN i).ne'
        field_simp; ring
      have hstrict : HasStrictDerivAt (ratioEll c) (ratioEllPrime c x) x :=
        hasStrictDerivAt_of_hasDerivAt_of_continuousAt
          (by filter_upwards [Ioo_mem_nhds hxoo.1 hxoo.2, eventually_ne_nhds hx0] with y hy hy0 using ratio_hasDerivAt_ell hc hy hy0)
          (ratio_continuousAt_ellPrime hc hx hx0)
      have hrem : (fun i => ratioEll c (u i) - ratioEll c (v i) - (u i - v i) * ratioEllPrime c x) =o[atTop] (fun i => u i - v i) := by
        simpa only [Function.comp_def, ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul] using
          (hasStrictDerivAt_iff_hasStrictFDerivAt.mp hstrict).isLittleO.comp_tendsto (hu.prodMk_nhds hv)
      have hlog : Tendsto (fun i => (N i : ℝ) * (ratioEll c (u i) - ratioEll c (v i))) atTop (𝓝 (ratioEllPrime c x * E x)) := by
        have hz : Tendsto (fun i => (N i : ℝ) * (ratioEll c (u i) - ratioEll c (v i) - (u i - v i) * ratioEllPrime c x)) atTop (𝓝 0) :=
          ((isBigO_refl (fun i => (N i : ℝ)) atTop).smul_isLittleO hrem).tendsto_zero_of_tendsto (by simpa only [Pi.smul_apply, smul_eq_mul] using he_lim)
        refine (by simpa only [zero_add] using hz.add (he_lim.const_mul (ratioEllPrime c x)) : Tendsto _ _ _).congr fun _ => by ring
      have hρ_lim : Tendsto (fun i => rootStepDensity (N i) (k i + 1) (q' i) (hq' i) (by omega) (hs' i) x) atTop (𝓝 (rho Δ x)) := by
        simp_rw [hρcast]
        refine Metric.tendsto_nhds.mpr fun ε hε => ?_
        filter_upwards [(tendsto_densityNorm_div hΔ (fun i y => Qρ i y - rho Δ y) hbq hnormQ).eventually (gt_mem_nhds hε)] with i hi
        rw [Real.dist_eq]; exact (abs_le_densityNorm_div hΔ (fun y => Qρ i y - rho Δ y) (hbq i) hx).trans_lt hi
      refine (hlog.mul hρ_lim).congr' ?_
      filter_upwards [hfirst.eventually (gt_mem_nhds hxoo.1), hlast_r.eventually (lt_mem_nhds hxoo.2)] with i hleft hright
      obtain ⟨hj, hcell⟩ := ratio_rootIndex_cell (by omega : 0 < k i + 1) (q' i) (hq' i).2.1 hleft.le
        (by simpa only [show (⟨k i + 1 - 1, by omega⟩ : Fin (k i + 1)) = Fin.last (k i) from Fin.ext (by simp)] using hright)
      let j : Fin (k i) := ⟨(ratioRootIndex (by omega) (q' i) x).val, by omega⟩
      have hjcast : j.castSucc = ratioRootIndex (by omega) (q' i) x := Fin.ext rfl
      dsimp only [F]
      rw [ratio_interiorTest_eq_density (hq' i) (hs' i) _ j hcell, hjcast]
    · simp only [g, hsupp hx, indicator_of_notMem hx]; exact tendsto_const_nhds
  have hInt := tendsto_integral_filter_of_dominated_convergence bound hmeas hbound
    ((integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const (by simp))) hpoint
  rw [show (∫ x, g x) = ∫ x in Icc (-Real.pi) Real.pi, ratioEllPrime c x * E x * rho Δ x from integral_indicator measurableSet_Icc] at hInt
  have hlast_term : Tendsto (fun i => ratioEll c (q' i (Fin.last (k i))) - ratioEll c (a' i (Fin.last (k i)))) atTop (𝓝 0) := by
    have hLlim : Tendsto (fun i => L / (N i : ℝ)) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hNlim
    refine Metric.tendsto_nhds.mpr fun ε hε => ?_
    filter_upwards [hshift, hNlim.eventually (eventually_ge_atTop (2 * (G : ℝ))), hLlim.eventually (gt_mem_nhds hε)]
      with i hi hiN hLi
    have hb := ratio_scaled_root_log_bound hc (hN i) G.2 hiN ((hq' i).1 _) (ha' i _) (hi (Fin.last (k i)))
    have hNp : (0 : ℝ) < N i := Nat.cast_pos.mpr (hN i)
    rw [abs_mul, abs_of_pos hNp, mul_comm] at hb; rw [Real.dist_eq, sub_zero]
    exact ((le_div_iff₀ hNp).mpr (by dsimp only [L, B]; exact hb)).trans_lt hLi
  have hi_int (i : ℕ) : (∫ x, F i x) = ∑ j : Fin (k i), (ratioEll c (q' i j.castSucc) - ratioEll c (a' i j.castSucc)) := by
    dsimp [F]; unfold ratioInteriorTest
    rw [integral_finsetSum _ fun j _ => (integrable_indicator_iff measurableSet_Ico).mpr
      (integrableOn_const (by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top))]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hgap := sub_pos.mpr ((hq' i).2.1 (show j.castSucc < j.succ from Nat.lt_succ_self j.val))
    have hNp : (N i : ℝ) ≠ 0 := by exact_mod_cast (hN i).ne'
    rw [integral_indicator_const _ measurableSet_Ico, Real.volume_real_Ico, smul_eq_mul, max_eq_left hgap.le]
    field_simp [hgap.ne', hNp]
  have hInt_eq : (∫ x in Icc (-Real.pi) Real.pi, ratioEllPrime c x * E x * rho Δ x) =
      (r : ℝ) * ∫ x in (-Real.pi)..Real.pi, ratioEllPrime c x * tauCont Δ x := by
    rw [setIntegral_congr_fun measurableSet_Icc (fun x _ =>
        show ratioEllPrime c x * E x * rho Δ x = (r : ℝ) * (ratioEllPrime c x * tauCont Δ x) by
          dsimp [E]; field_simp [(rho_pos hΔ x).ne']),
      integral_const_mul, intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), integral_Icc_eq_integral_Ioc]
  rw [hInt_eq] at hInt
  refine (by simpa only [add_zero] using hInt.add hlast_term : Tendsto _ _ _).congr fun i => ?_
  rw [hi_int i, ← Fin.sum_univ_castSucc (fun j => ratioEll c (q' i j) - ratioEll c (a' i j))]
  exact Equiv.sum_comp (finCongr (hk i))
    (fun j => ratioEll c (q i j) - ratioEll c (alignedRoot (N i) r (hr i) (p i) j))

/-- Even-branch Fourier eigenvalue-ratio limit for `c > 2`. -/
theorem ratio_even_eigenvalue_limit_fourier (heven : r % 2 = 0) (_hrpos : 1 ≤ r)
    {c : ℝ} (hc : 2 < c) (hcΔ : anisotropy c = Δ) :
    ∃ S : ℝ,
      Tendsto (PottsDiscontinuity.altTanhPartial (lamOf Δ)) atTop (𝓝 S) ∧
      Tendsto (fun i => eigenvalueRegular c (q i) / eigenvalueRegular c (p i)) atTop
        (𝓝 ((Real.exp (-(r : ℝ) * (lamOf Δ + 2 * S)) : ℝ) : ℂ)) := by
  obtain ⟨S, hS, hW15⟩ := PottsDiscontinuity.fourierRatioExponent (lam := lamOf Δ) (r := (r : ℝ)) (lamOf_pos hΔ)
  have hExponent : -(r : ℝ) * Real.log |Δ| +
      (r : ℝ) * ∫ x in (-Real.pi)..Real.pi, ratioEllPrime c x * tauCont Δ x = -(r : ℝ) * (lamOf Δ + 2 * S) := by
    have hparam : -Real.cosh (lamOf Δ) = Δ := by rw [cosh_lamOf hΔ]; ring
    simpa only [show Real.log |Δ| = Real.log |-(Real.cosh (lamOf Δ))| by rw [hparam],
      ratio_integral_eq_fourier hΔ hc hcΔ] using hW15
  refine ⟨S, hS, ?_⟩
  let s := r / 2
  have hcount (i : ℕ) : s + (N i / 2 - r) + s = N i / 2 := by dsimp [s]; have := hr i; omega
  have hbulk : Tendsto (fun i => ∏ j, ‖M c (z (q i j))‖ / ‖M c (z (p i ⟨j.val + s, by have := hcount i; omega⟩))‖)
      atTop (𝓝 (Real.exp ((r : ℝ) * ∫ x in (-Real.pi)..Real.pi, ratioEllPrime c x * tauCont Δ x))) :=
    ((Real.continuous_exp.tendsto _).comp
      (ratio_bulk_log_limit hΔ r N h4 hr hN hn p q hp hq hpBE hqBE hNlim hbp hbq hK hrate hc)).congr fun i => by
      dsimp only [Function.comp_def]; rw [Real.exp_sum]
      exact prod_congr rfl fun j _ => by
        rw [Real.exp_sub, ratio_exp_ell hc, ratio_exp_ell hc]
        simp only [alignedRoot, heven, ite_eq_left, s]
  have hnormP := ratio_densityNorm_tendsto_of_rate hΔ N hNlim _ hbp (hrate.mono fun _ hi => hi.1)
  have hnP (i : ℕ) : 0 < N i / 2 := by have := hn i; omega
  have hx (j : Fin s) : Tendsto (fun i => p i ⟨j.val, by have := hcount i; omega⟩) atTop (𝓝 (-Real.pi)) :=
    ratio_tendsto_root_left hΔ 0 N (fun i => N i / 2) p hp hnP (fun _ => by omega)
      (fun i => by obtain ⟨z, _⟩ := h4 i; omega) hNlim hbp hnormP
      (fun i => ⟨j.val, by have := hcount i; omega⟩) s (fun _ => show j.val ≤ s by omega)
  have hprod_end := tendsto_finsetProd univ fun j _ => ratio_modulus_tendsto_endpoint (hx j) c
  simp only [prod_const, card_univ, Fintype.card_fin] at hprod_end
  have habs : 0 < |Δ| := abs_pos.mpr (by linarith)
  have hboundary : Tendsto (fun i => ((∏ j : Fin s, ‖M c (z (p i ⟨j.val, by have := hcount i; omega⟩))‖) ^ 2)⁻¹)
      atTop (𝓝 (Real.exp (-(r : ℝ) * Real.log |Δ|))) := by
    have hne : (|anisotropy c| ^ s) ^ 2 ≠ 0 := pow_ne_zero 2 (pow_ne_zero s (hcΔ ▸ habs.ne'))
    have ht := (hprod_end.pow 2).inv₀ hne
    have hbval : ((|anisotropy c| ^ s) ^ 2)⁻¹ = Real.exp (-(r : ℝ) * Real.log |Δ|) := by
      rw [hcΔ, ← pow_mul, show s * 2 = r by dsimp [s]; omega,
        ← show Real.exp ((r : ℝ) * Real.log |Δ|) = |Δ| ^ r by rw [Real.exp_nat_mul, Real.exp_log habs],
        ← Real.exp_neg]; congr 1; ring
    rwa [hbval] at ht
  have hreal := hbulk.mul hboundary
  rw [show Real.exp ((r : ℝ) * ∫ x in (-Real.pi)..Real.pi, ratioEllPrime c x * tauCont Δ x) *
      Real.exp (-(r : ℝ) * Real.log |Δ|) = Real.exp (-(r : ℝ) * (lamOf Δ + 2 * S)) by
    rw [← Real.exp_add, add_comm, hExponent]] at hreal
  refine (Complex.continuous_ofReal.continuousAt.tendsto.comp hreal).congr fun i => ?_
  dsimp only [Function.comp_def]
  exact (ratio_even_quotient_split (hcount i) hc (hp i) (hq i)).symm

/-- Odd-branch Fourier eigenvalue-ratio limit for `c > 2`. -/
theorem ratio_odd_eigenvalue_limit_fourier (hodd : r % 2 ≠ 0) (_hrpos : 1 ≤ r)
    {c : ℝ} (hc : 2 < c) (hcΔ : anisotropy c = Δ) :
    ∃ S : ℝ,
      Tendsto (PottsDiscontinuity.altTanhPartial (lamOf Δ)) atTop (𝓝 S) ∧
      Tendsto (fun i => eigenvalueZero (N i) c (q i)
        ⟨(N i / 2 - r) / 2, Nat.div_lt_self (hn i) Nat.one_lt_two⟩ /
          eigenvalueRegular c (p i)) atTop
        (𝓝 ((Real.exp (-(r : ℝ) * (lamOf Δ + 2 * S)) : ℝ) : ℂ)) := by
  obtain ⟨S, hS, hW15⟩ := PottsDiscontinuity.fourierRatioExponent (lam := lamOf Δ) (r := (r : ℝ)) (lamOf_pos hΔ)
  have hExponent : -(r : ℝ) * Real.log |Δ| +
      (r : ℝ) * ∫ x in (-Real.pi)..Real.pi, ratioEllPrime c x * tauCont Δ x = -(r : ℝ) * (lamOf Δ + 2 * S) := by
    have hparam : -Real.cosh (lamOf Δ) = Δ := by rw [cosh_lamOf hΔ]; ring
    simpa only [show Real.log |Δ| = Real.log |-(Real.cosh (lamOf Δ))| by rw [hparam],
      ratio_integral_eq_fourier hΔ hc hcΔ] using hW15
  refine ⟨S, hS, ?_⟩
  obtain ⟨s, hrs⟩ : ∃ s : ℕ, r = 2 * s + 1 := ⟨r / 2, by omega⟩
  subst r
  let n : ℕ → ℕ := fun i => N i / 2 - (2 * s + 1)
  have hcountN (i : ℕ) : N i = 2 * (n i + (2 * s + 1)) := by dsimp [n]; obtain ⟨m, _⟩ := h4 i; have := hr i; omega
  have hsQ (i : ℕ) : 2 * n i ≤ N i := by dsimp [n]; omega
  have hnodd (i : ℕ) : n i = 2 * (N i / 4 - s - 1) + 1 := by dsimp [n]; obtain ⟨m, _⟩ := h4 i; have := hr i; omega
  let l : ∀ i, Fin (n i) := fun i => ⟨N i / 4 - s - 1, by have := hnodd i; omega⟩
  have hzero (i : ℕ) : q i (l i) = 0 := by
    have hsym := (hq i).2.2 (l i)
    rw [show Fin.rev (l i) = l i from Fin.ext (by simp only [Fin.val_rev]; dsimp [l]; have := hnodd i; omega)] at hsym
    linarith
  have hcenter (i : ℕ) : l i = ⟨(N i / 2 - (2 * s + 1)) / 2, Nat.div_lt_self (hn i) (by omega)⟩ :=
    Fin.ext (show N i / 4 - s - 1 = (N i / 2 - (2 * s + 1)) / 2 by obtain ⟨m, _⟩ := h4 i; have := hr i; omega)
  have hnormP : Tendsto (fun i => densityNorm Δ hΔ
      (fun x => rootStepDensity (N i) (N i / 2) (p i) (hp i)
        (by have := hn i; omega) (by omega) x - rho Δ x) (hbp i)) atTop (𝓝 0) :=
    ratio_densityNorm_tendsto_of_rate hΔ N hNlim _ hbp (hrate.mono fun _ hi => hi.1)
  have hnormQ : Tendsto (fun i => densityNorm Δ hΔ
      (fun x => rootStepDensity (N i) (n i) (q i) (hq i) (hn i) (hsQ i) x - rho Δ x) (hbq i)) atTop (𝓝 0) := by
    simpa [n] using ratio_densityNorm_tendsto_of_rate hΔ N hNlim
      (fun i x => rootStepDensity (N i) (N i / 2 - (2 * s + 1)) (q i) (hq i)
        (hn i) (by have := hr i; omega) x - rho Δ x) hbq (hrate.mono fun _ hi => hi.2)
  have hA : Tendsto (fun i => ratioZeroCoefficient (anisotropy c) c (N i) (q i) (l i) / (2 * (N i : ℝ)))
      atTop (𝓝 (c ^ 2 * Real.pi * rho Δ 0)) := by
    simpa only [hcΔ] using ratio_odd_A_tendsto hΔ c (2 * s + 1) N n q hq hn hsQ hcountN hNlim (fun i => hbq i) hnormQ l hzero
  have hfirstBound (i : ℕ) : 0 < N i / 4 := by obtain ⟨m, _⟩ := h4 i; have := hN i; omega
  let x : ℕ → ℝ := fun i => ratioPositiveRoot (N i) (h4 i) (p i) ⟨0, hfirstBound i⟩
  have hscale := ratio_full_positive_rank_scaling hΔ N h4 hN p hp hNlim hbp hnormP 0 hfirstBound
  have hxlim : Tendsto x atTop (𝓝 0) := (hscale.div_atTop hNlim).congr fun i => by
    dsimp [x]; have : (N i : ℝ) ≠ 0 := by exact_mod_cast (hN i).ne'
    field_simp
  have hC := ratio_scaled_inverse_norm_tendsto hc (fun i => (N i : ℝ)) x
    (fun i => (hp i).1 _) (fun i => ratio_positiveRoot_pos (h4 i) (hp i) _) hxlim hscale
  have hnP (i : ℕ) : 0 < N i / 2 := by have := hN i; have := h4 i; omega
  have hcountP (i : ℕ) : N i = 2 * (N i / 2 + 0) := by obtain ⟨m, _⟩ := h4 i; omega
  let xb : ℕ → Fin s → ℝ := fun i j => p i ⟨j.val, by have := hr i; omega⟩
  let yb : ℕ → ℝ := fun i => p i ⟨s, by have := hr i; omega⟩
  have hxb (j : Fin s) : Tendsto (fun i => xb i j) atTop (𝓝 (-Real.pi)) :=
    ratio_tendsto_root_left hΔ 0 N (fun i => N i / 2) p hp hnP (fun _ => by omega) hcountP hNlim hbp hnormP
      (fun i => ⟨j.val, by have := hr i; omega⟩) s (fun _ => show j.val ≤ s by omega)
  have hyb : Tendsto yb atTop (𝓝 (-Real.pi)) :=
    ratio_tendsto_root_left hΔ 0 N (fun i => N i / 2) p hp hnP (fun _ => by omega) hcountP hNlim hbp hnormP
      (fun i => ⟨s, by have := hr i; omega⟩) s (fun _ => le_rfl)
  have hprod_end := tendsto_finsetProd univ fun j _ => ratio_modulus_tendsto_endpoint (hxb j) c
  simp only [prod_const, card_univ, Fintype.card_fin] at hprod_end
  have habs : 0 < |Δ| := abs_pos.mpr (by linarith)
  have hB : Tendsto (fun i => (‖M c (z (yb i))‖ * (∏ j, ‖M c (z (xb i j))‖) ^ 2)⁻¹)
      atTop (𝓝 (Real.exp (-((2 * s + 1 : ℕ) : ℝ) * Real.log |Δ|))) := by
    have hlimB := (ratio_modulus_tendsto_endpoint hyb c).mul (hprod_end.pow 2)
    rw [show |anisotropy c| * (|anisotropy c| ^ s) ^ 2 = |anisotropy c| ^ (2 * s + 1) by
      rw [show 2 * s + 1 = s * 2 + 1 by omega, pow_add, pow_mul]; ring] at hlimB
    have ht := hlimB.inv₀ (pow_ne_zero _ (hcΔ ▸ habs.ne'))
    have hbval : (|anisotropy c| ^ (2 * s + 1))⁻¹ = Real.exp (-((2 * s + 1 : ℕ) : ℝ) * Real.log |Δ|) := by
      rw [hcΔ, ← show Real.exp (((2 * s + 1 : ℕ) : ℝ) * Real.log |Δ|) = |Δ| ^ (2 * s + 1) by
        rw [Real.exp_nat_mul, Real.exp_log habs], ← Real.exp_neg]; congr 1; ring
    rwa [hbval] at ht
  have hW := ratio_source_midpoint_limit hΔ hc s N h4 hN p hp hNlim hbp hnormP
  have hBulkExp := (Real.continuous_exp.tendsto _).comp
    (ratio_bulk_log_limit hΔ (2 * s + 1) N h4 hr hN hn p q hp hq hpBE hqBE hNlim hbp hbq hK hrate hc)
  have hρ : 0 < rho Δ 0 := rho_pos hΔ 0
  have hc0 : c ≠ 0 := by linarith
  have hsmall := (hA.mul hC).mul hW
  rw [show (c ^ 2 * Real.pi * rho Δ 0) * (((((0 : ℕ) : ℝ) + 1 / 2) / rho Δ 0) / c ^ 2) * (2 / Real.pi) = 1 by
    field_simp [hρ.ne', hc0, Real.pi_ne_zero]; ring] at hsmall
  have hreal := hsmall.mul (hB.mul hBulkExp)
  rw [one_mul, ← Real.exp_add, hExponent] at hreal
  refine (Complex.continuous_ofReal.continuousAt.tendsto.comp hreal).congr fun i => ?_
  dsimp only [Function.comp_def]
  have hf := ratio_odd_quotient_factors hc s (N i) (h4 i) (by have := hr i; omega) (by have := hn i; omega)
    (p i) (hp i) (q i) (hq i) (l i) (hzero i)
  rw [hcenter i] at hf; rw [hf]; apply congrArg (fun z : ℝ => (z : ℂ)); rw [← hcenter i]
  have hNi : (N i : ℝ) ≠ 0 := by exact_mod_cast (hN i).ne'
  have hfirst := norm_ne_zero_iff.mpr (ratio_M_ne_zero hc (x i))
  have hy := norm_ne_zero_iff.mpr (ratio_M_ne_zero hc (yb i))
  have hprod : (∏ j : Fin s, ‖M c (z (xb i j))‖) ≠ 0 :=
    prod_ne_zero_iff.mpr fun _ _ => norm_ne_zero_iff.mpr (ratio_M_ne_zero hc _)
  dsimp [x, yb, xb]; field_simp [hNi, hfirst, hy, hprod]

end

end PottsDiscontinuity.Bethe
