module

public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Tactic

/-!
# Second-order linear ODEs: uniqueness and a Rellich-type decay lemma

* `ode2_unique`: a solution of `y'' + p y' + q y = 0` (bounded `p, q`) on an interval vanishing
  together with its derivative at one point vanishes identically.
* `ode_rellich`: a solution of `w'' + (E - c/r²) w = 0` on `(R, ∞)` (`E > 0`) which is
  square integrable at infinity vanishes identically.
-/

@[expose] public section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

noncomputable section

namespace PolyaNeumann

/-- Uniqueness for a second-order linear ODE with bounded coefficients. -/
theorem ode2_unique {a b : ℝ} {p q : ℝ → ℂ} {P Q : ℝ} (hp : ∀ r ∈ Ioo a b, ‖p r‖ ≤ P)
    (hq : ∀ r ∈ Ioo a b, ‖q r‖ ≤ Q) {y y' : ℝ → ℂ}
    (hy : ∀ r ∈ Ioo a b, HasDerivAt y (y' r) r)
    (hy' : ∀ r ∈ Ioo a b, HasDerivAt y' (-(p r * y' r) - q r * y r) r) {r₀ : ℝ}
    (hr₀ : r₀ ∈ Ioo a b) (h0 : y r₀ = 0) (h1 : y' r₀ = 0) : ∀ r ∈ Ioo a b, y r = 0 := by
  set V : ℝ → ℂ × ℂ → ℂ × ℂ := fun r z => (z.2, -(p r * z.2) - q r * z.1)
  set K : ℝ≥0 := ⟨1 + |P| + |Q|, by positivity⟩
  have hV : ∀ r ∈ Ioo a b, LipschitzOnWith K (V r) univ := by
    intro r hr
    refine (LipschitzWith.of_dist_le_mul fun z w => ?_).lipschitzOnWith
    have hP := (hp r hr).trans (le_abs_self _)
    have hQ := (hq r hr).trans (le_abs_self _)
    rw [dist_eq_norm, dist_eq_norm]
    have e : V r z - V r w = (z.2 - w.2, -(p r * (z.2 - w.2)) - q r * (z.1 - w.1)) := by
      simp only [V, Prod.mk_sub_mk]; ring
    rw [e]
    have h1 : ‖z.1 - w.1‖ ≤ ‖z - w‖ := by
      rw [← Prod.fst_sub]; exact norm_fst_le _
    have h2 : ‖z.2 - w.2‖ ≤ ‖z - w‖ := by
      rw [← Prod.snd_sub]; exact norm_snd_le _
    have hn : 0 ≤ ‖z - w‖ := norm_nonneg _
    rw [show (K : ℝ) = 1 + |P| + |Q| from rfl]
    refine max_le ?_ ?_
    · nlinarith [abs_nonneg P, abs_nonneg Q]
    · refine (norm_sub_le _ _).trans ?_
      rw [norm_neg, norm_mul, norm_mul]
      have := mul_le_mul hP h2 (norm_nonneg _) (abs_nonneg _)
      have := mul_le_mul hQ h1 (norm_nonneg _) (abs_nonneg _)
      nlinarith [abs_nonneg P, abs_nonneg Q]
  have heq := ODE_solution_unique_of_mem_Ioo (f := fun r => (y r, y' r)) (g := fun _ => (0, 0))
    (s := fun _ => univ) hV hr₀
    (fun r hr => ⟨(hy r hr).prodMk (hy' r hr), mem_univ _⟩)
    (fun r hr => ⟨by convert hasDerivAt_const (𝕜 := ℝ) r ((0 : ℂ), (0 : ℂ)) using 1; aesop, mem_univ _⟩)
    (by simp_all)
  intro r hr
  grind

/-- The oscillator energy is bounded above and below by integrating its
relative derivative bound. A nonzero lower bound contradicts the square
integrability of `w`, by integrating `(Re ⟪w,w'⟫)'`. -/
theorem ode_rellich {E c R : ℝ} (hE : 0 < E) (hR : 0 < R) {w w' : ℝ → ℂ}
    (hw : ∀ r ∈ Ioi R, HasDerivAt w (w' r) r)
    (hw' : ∀ r ∈ Ioi R, HasDerivAt w' (-(((E - c / r ^ 2 : ℝ) : ℂ) * w r)) r)
    (hint : IntegrableOn (fun r => ‖w r‖ ^ 2) (Ioi R)) : ∀ r ∈ Ioi R, w r = 0 := by
  let N (r : ℝ) := ‖w r‖ ^ 2
  let D (r : ℝ) := ‖w' r‖ ^ 2
  let H (r : ℝ) := D r + E * N r
  let P (r : ℝ) := inner ℝ (w r) (w' r)
  let q (r : ℝ) := E - c / r ^ 2
  let J (r : ℝ) := D r - q r * N r
  have hn (r : ℝ) : 0 ≤ N r := sq_nonneg _
  have hH (r : ℝ) : 0 ≤ H r := by dsimp [H, D]; positivity
  have hd r (hr : r ∈ Ioi R) : HasDerivAt w' ((-q r) • w r) r := by
    simpa only [Complex.real_smul, q, Complex.ofReal_neg, neg_mul] using hw' r hr
  have hP' r (hr : r ∈ Ioi R) : HasDerivAt P (J r) r := by
    convert (hw r hr).inner ℝ (hd r hr) using 1
    simp only [J, D, real_inner_self_eq_norm_sq, real_inner_smul_right]
    ring
  let dH (r : ℝ) := 2 * c / r ^ 2 * P r
  have hH' r (hr : r ∈ Ioi R) : HasDerivAt H (dH r) r := by
    convert (hd r hr).norm_sq.add ((hw r hr).norm_sq.const_mul E) using 1
    simp only [dH, P, q, real_inner_smul_right, real_inner_comm (w' r) (w r)]
    ring
  let K := 1 + 1 / E
  have hK : 0 ≤ K := by positivity
  have hP r : |P r| ≤ K * H r / 2 := by
    have hn' : N r ≤ H r / E := by rw [le_div_iff₀ hE]; simp [H, D, mul_comm]
    have hd' : D r ≤ H r := by dsimp [H]; linarith [mul_nonneg hE.le (hn r)]
    calc
      _ ≤ ‖w r‖ * ‖w' r‖ := abs_real_inner_le_norm _ _
      _ ≤ (N r + D r) / 2 := by dsimp [N]; nlinarith [sq_nonneg (‖w r‖ - ‖w' r‖)]
      _ ≤ _ := by
        dsimp [K]
        rw [add_mul, one_mul, one_div_mul_eq_div]
        linarith
  let A := |c| * K
  have hA : 0 ≤ A := by positivity
  have hbound r (hr : r ∈ Ioi R) : |dH r| ≤ (A / r ^ 2) * H r := by
    rw [show |dH r| = (2 * |c| / r ^ 2) * |P r| by
      simp [dH, abs_mul, abs_div, sq_abs]]
    calc
      _ ≤ (2 * |c| / r ^ 2) * (K * H r / 2) := by gcongr; exact hP r
      _ = _ := by dsimp [A]; ring
  have hder a r (hr : r ∈ Ioi R) : HasDerivAt (fun t => Real.exp (a / t) * H t)
      (Real.exp (a / r) * (dH r - a / r ^ 2 * H r)) r := by
    convert (((hasDerivAt_id r).inv (hR.trans hr).ne').const_mul a).exp.mul (hH' r hr) using 1
    · funext t; simp [div_eq_mul_inv]
    · simp only [Pi.inv_apply, id_eq, div_eq_mul_inv]; ring
  have hmono : MonotoneOn (fun t => Real.exp (-A / t) * H t) (Ioi R) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioi _)
      (fun r hr => (hder (-A) r hr).continuousAt.continuousWithinAt)
      (fun r hr => (hder (-A) r (interior_subset hr)).hasDerivWithinAt) (fun r hr => by
        rw [interior_Ioi] at hr
        refine mul_nonneg (Real.exp_pos _).le ?_
        rw [neg_div, neg_mul, sub_neg_eq_add]
        linarith [neg_abs_le (dH r), hbound r hr])
  have hanti : AntitoneOn (fun t => Real.exp (A / t) * H t) (Ioi R) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioi _)
      (fun r hr => (hder A r hr).continuousAt.continuousWithinAt)
      (fun r hr => (hder A r (interior_subset hr)).hasDerivWithinAt) (fun r hr => by
        rw [interior_Ioi] at hr
        exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
          (sub_nonpos.mpr ((le_abs_self _).trans (hbound r hr))))
  intro a ha
  by_contra hne
  have ha0 : 0 < a := hR.trans ha
  let δ := Real.exp (-A / a) * H a
  have hδ : 0 < δ := by dsimp [δ, H, N]; positivity
  let C := K * (Real.exp (A / a) * H a) / 2
  have hC : 0 ≤ C := by positivity
  have hlow b (hb : a ≤ b) : δ ≤ H b :=
    (hmono ha (ha.trans_le hb) hb).trans (mul_le_of_le_one_left (hH b)
      (Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hA) (ha0.le.trans hb))))
  have hPbound b (hb : a ≤ b) : |P b| ≤ C := by
    have hexp : 1 ≤ Real.exp (A / b) := Real.one_le_exp_iff.mpr (by
      have := ha0.trans_le hb; positivity)
    have h := (le_mul_of_one_le_left (hH b) hexp).trans (hanti ha (ha.trans_le hb) hb)
    exact (hP b).trans (by dsimp [C]; gcongr)
  let B := 2 * E + |c| / a ^ 2
  have hB : 0 ≤ B := by positivity
  let M := 2 * C + B * ∫ t in Ioi R, N t
  let b := a + (|M| + 1) / δ
  have hab : a ≤ b := by dsimp [b]; linarith [show 0 ≤ (|M| + 1) / δ by positivity]
  have hsub : uIcc a b ⊆ Ioi R := by rw [uIcc_of_le hab]; exact fun r hr => ha.trans_le hr.1
  have hNc : ContinuousOn N (uIcc a b) := fun r hr =>
    (hw r (hsub hr)).continuousAt.norm.pow 2 |>.continuousWithinAt
  have hDc : ContinuousOn D (uIcc a b) := fun r hr =>
    (hd r (hsub hr)).continuousAt.norm.pow 2 |>.continuousWithinAt
  have hqc : ContinuousOn q (uIcc a b) := by
    exact continuousOn_const.sub (continuousOn_const.div (continuousOn_id.pow 2)
      fun r hr => pow_ne_zero _ (hR.trans (hsub hr)).ne')
  have hiH : IntervalIntegrable H volume a b := (hDc.add (hNc.const_mul E)).intervalIntegrable (μ := volume)
  have hiJ : IntervalIntegrable J volume a b := (hDc.sub (hqc.mul hNc)).intervalIntegrable (μ := volume)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r hr => hP' r (hsub hr)) hiJ
  have htop : (∫ t in a..b, H t) ≤ (∫ t in a..b, J t + B * N t) := by
    refine intervalIntegral.integral_mono_on hab hiH (hiJ.add (hNc.intervalIntegrable.const_mul B)) fun t ht => ?_
    have hta := ht.1
    have ht0 := ha0.trans_le hta
    have h := calc -c / t ^ 2 ≤ |c| / t ^ 2 := by gcongr; exact neg_le_abs c
                  _ ≤ |c| / a ^ 2 := by gcongr
    have := mul_le_mul_of_nonneg_right h (hn t)
    dsimp [H, J, q, B]
    ring_nf at this ⊢
    linarith
  rw [intervalIntegral.integral_add hiJ (hNc.intervalIntegrable.const_mul B), hftc,
    intervalIntegral.integral_const_mul] at htop
  have hI : ∫ t in a..b, N t ≤ ∫ t in Ioi R, N t := by
    rw [intervalIntegral.integral_of_le hab]
    exact setIntegral_mono_set hint (ae_of_all _ hn)
      (ae_of_all _ fun t ht => ha.trans ht.1)
  have hlo := intervalIntegral.integral_mono_on (f := fun _ => δ) hab intervalIntegrable_const hiH
    (fun t ht => hlow t ht.1)
  rw [intervalIntegral.integral_const, smul_eq_mul] at hlo
  have hlen : (b - a) * δ = |M| + 1 := by dsimp [b]; field_simp; ring
  rw [hlen] at hlo
  have hPa := (abs_le.mp (hPbound a le_rfl)).1
  have hPb := (abs_le.mp (hPbound b hab)).2
  have hBi := mul_le_mul_of_nonneg_left hI hB
  dsimp [M] at hlo ⊢
  linarith [le_abs_self M]

/-- The Rellich lemma for Bessel's equation `m'' + m'/r + (E - c/r²) m = 0`: a solution on
`(R, ∞)` with `∫ r |m|² dr < ∞` vanishes identically. -/
theorem bessel_rellich {E c R : ℝ} (hE : 0 < E) (hR : 0 < R) {m m' : ℝ → ℂ}
    (hm : ∀ r ∈ Ioi R, HasDerivAt m (m' r) r)
    (hm' : ∀ r ∈ Ioi R, HasDerivAt m' (-(m' r / r) - ((E - c / r ^ 2 : ℝ) : ℂ) * m r) r)
    (hint : IntegrableOn (fun r => r * ‖m r‖ ^ 2) (Ioi R)) : ∀ r ∈ Ioi R, m r = 0 := by
  set w : ℝ → ℂ := fun r => (Real.sqrt r : ℂ) * m r with hwdef
  set w' : ℝ → ℂ := fun r => ((1 / (2 * Real.sqrt r) : ℝ) : ℂ) * m r + (Real.sqrt r : ℂ) * m' r
    with hw'def
  have hsq_d : ∀ r, 0 < r → HasDerivAt (fun r => (Real.sqrt r : ℂ)) ((1 / (2 * Real.sqrt r) : ℝ) : ℂ) r :=
    fun r hr => (Real.hasDerivAt_sqrt hr.ne').ofReal_comp
  have hisq_d : ∀ r, 0 < r → HasDerivAt (fun r => ((1 / (2 * Real.sqrt r) : ℝ) : ℂ))
      ((-(1 / (4 * Real.sqrt r ^ 3)) : ℝ) : ℂ) r := fun r hr => by
    have hs := Real.sqrt_pos.mpr hr
    have h := ((Real.hasDerivAt_sqrt hr.ne').const_mul 2).inv (by positivity)
    have h2 := h.ofReal_comp
    convert h2 using 1
    simp
    ring
  have hw : ∀ r ∈ Ioi R, HasDerivAt w (w' r) r := fun r hr => by
    have h := (hsq_d r (hR.trans hr)).mul (hm r hr)
    assumption
  have hw' : ∀ r ∈ Ioi R, HasDerivAt w' (-((((E - (c - 1 / 4) / r ^ 2) : ℝ) : ℂ) * w r)) r :=
    fun r hr => by
    have hr0 := hR.trans hr
    have hs := Real.sqrt_pos.mpr hr0
    have hss := Real.sq_sqrt hr0.le
    have h := ((hisq_d r hr0).mul (hm r hr)).add ((hsq_d r hr0).mul (hm' r hr))
    convert h using 1
    simp only [hwdef]
    have hsC : (Real.sqrt r : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
    have hssC : (Real.sqrt r : ℂ) ^ 2 = r := by norm_cast
    push_cast
    field_simp
    rw [show (r : ℂ) = (Real.sqrt r : ℂ) ^ 2 from hssC.symm]
    ring
  have hint' : IntegrableOn (fun r => ‖w r‖ ^ 2) (Ioi R) := by
    refine hint.congr_fun (fun r hr => ?_) measurableSet_Ioi
    have hr0 := hR.trans hr
    simp  [hwdef, Complex.norm_real, Real.norm_eq_abs, mul_pow, Real.sq_sqrt hr0.le]
  have h0 := ode_rellich hE hR hw hw' hint'
  intro r hr
  have hs : (Real.sqrt r : ℂ) ≠ 0 := by
    have := Real.sqrt_pos.mpr (hR.trans hr)
    exact_mod_cast this.ne'
  have := h0 r hr
  simp only [hwdef, mul_eq_zero] at this
  tauto

end PolyaNeumann
