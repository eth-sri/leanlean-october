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
    
    
    rw [dist_eq_norm, dist_eq_norm]
    have e : V r z - V r w = (z.2 - w.2, -(p r * (z.2 - w.2)) - q r * (z.1 - w.1)) := by
      simp only [V, Prod.mk_sub_mk]; congr 1; ring
    rw [e, Prod.norm_def]
    have h1 : ‖z.1 - w.1‖ ≤ ‖z - w‖ := by
      rw [← Prod.fst_sub]; exact norm_fst_le _
    have h2 : ‖z.2 - w.2‖ ≤ ‖z - w‖ := by
      rw [← Prod.snd_sub]; exact norm_snd_le _
    have hn : 0 ≤ ‖z - w‖ := norm_nonneg _
    rw [show K = 1 + |P| + |Q| from rfl]
    refine max_le ?_ ?_
    · nlinarith [abs_nonneg P, abs_nonneg Q]
    · refine (norm_sub_le _ _).trans ?_
      rw [norm_neg, norm_mul, norm_mul]
      have := mul_le_mul ((hp r hr).trans (le_abs_self _)) h2 (norm_nonneg _) (abs_nonneg _)
      have := mul_le_mul ((hq r hr).trans (le_abs_self _)) h1 (norm_nonneg _) (abs_nonneg _)
      nlinarith [abs_nonneg P, abs_nonneg Q]
  have heq := ODE_solution_unique_of_mem_Ioo  
     hV hr₀
    (fun r hr => ⟨(hy r hr).prodMk (hy' r hr), mem_univ _⟩)
    (fun r hr => ⟨by convert hasDerivAt_const  r ((0 : ℂ), (0 : ℂ)) using 1; simp [V], mem_univ _⟩)
    (by simp [h0, h1])
  intro r hr
  grind [heq hr]

/-- A nondecreasing energy with limit zero starts nonpositive. -/
private lemma nonpos_of_deriv_nonneg_of_tendsto {W f : ℝ → ℝ} {a : ℝ}
    (hd : ∀ r ∈ Ici a, HasDerivAt W (f r) r) (hn : ∀ r ∈ Ioi a, 0 ≤ f r)
    (h : Tendsto W atTop (𝓝 0)) : W a ≤ 0 := by
  have hi := setIntegral_nonneg (μ := volume) measurableSet_Ioi hn
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' hd hn h, zero_sub] at hi
  linarith

/-- A Rellich-type lemma: a solution of `w'' + (E - c/r²) w = 0` on `(R, ∞)` (`E > 0`, `R > 0`)
which is square integrable at infinity vanishes identically. -/
theorem ode_rellich {E c R : ℝ} (hE : 0 < E) (hR : 0 < R) {w w' : ℝ → ℂ}
    (hw : ∀ r ∈ Ioi R, HasDerivAt w (w' r) r)
    (hw' : ∀ r ∈ Ioi R, HasDerivAt w' (-(((E - c / r ^ 2 : ℝ) : ℂ) * w r)) r)
    (hint : IntegrableOn (fun r => ‖w r‖ ^ 2) (Ioi R)) : ∀ r ∈ Ioi R, w r = 0 := by
  set q : ℝ → ℝ := fun r => E - c / r ^ 2 with hqdef
  set q' : ℝ → ℝ := fun r => 2 * c / r ^ 3 with hq'def
  set N : ℝ → ℝ := fun r => ‖w r‖ ^ 2 with hNdef
  set D : ℝ → ℝ := fun r => ‖w' r‖ ^ 2 with hDdef
  set W : ℝ → ℝ := fun r => D r + q r * N r with hWdef
  set P : ℝ → ℝ := fun r => inner ℝ (w r) (w' r) with hPdef
  set f : ℝ → ℝ := fun r => q' r * N r with hfdef
  have hqLim : Tendsto q atTop (𝓝 E) := by
    simpa [q] using (tendsto_const_nhds (x := E)).sub
      ((tendsto_const_nhds (x := c)).div_atTop (tendsto_pow_atTop (α := ℝ) (n := 2) (by decide)))
  have hq'Lim : Tendsto q' atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by decide))
  obtain ⟨r1, htail⟩ := eventually_atTop.mp
    ((eventually_gt_atTop R).and ((hqLim.eventually (Ioo_mem_nhds (half_lt_self hE) (by linarith : E < 2 * E))).and
      (hq'Lim.norm.eventually (gt_mem_nhds (by simp : ‖(0 : ℝ)‖ < 1)))))
  have hmem r (hr : r1 ≤ r) := (htail r hr).1
  have hq_lo r (hr : r1 ≤ r) := (htail r hr).2.1.1.le
  have hq_hi r (hr : r1 ≤ r) := (htail r hr).2.1.2.le
  have hqpos r (hr : r1 ≤ r) := (half_pos hE).trans_le (hq_lo r hr)
  have hN0 r : 0 ≤ N r := sq_nonneg _
  have hD0 r : 0 ≤ D r := sq_nonneg _
  have hW0 r (hr : r1 ≤ r) : 0 ≤ W r := add_nonneg (hD0 r) (mul_nonneg (hqpos r hr).le (hN0 r))
  -- derivatives
  have hq_d : ∀ r, 0 < r → HasDerivAt q (q' r) r := fun r hr => by
    
    have h' := (((hasDerivAt_pow 2 r).inv (pow_ne_zero 2 hr.ne')).const_mul (-c)).const_add E
    convert h' using 1
    · funext t; simp only [hqdef, Pi.inv_apply]; ring
    · simp only [hq'def]; field_simp; ring
  have hN_d : ∀ r ∈ Ioi R, HasDerivAt N (2 * P r) r := fun r hr => (hw r hr).norm_sq
  have acc r (hr : r ∈ Ioi R) : HasDerivAt w' (-q r • w r) r := by
    convert hw' r hr using 1
    simp [q, Complex.real_smul]; ring
  have hD_d r (hr : r ∈ Ioi R) : HasDerivAt D (-(2 * q r * P r)) r := by
    convert (acc r hr).norm_sq using 1
    rw [real_inner_smul_right, real_inner_comm]
    dsimp [P]; ring
  have hW_d : ∀ r ∈ Ioi R, HasDerivAt W (f r) r := fun r hr => by
    
    convert ((hD_d r hr).add ((hq_d r (hR.trans hr)).mul (hN_d r hr))) using 1
    ring
  have hP_d : ∀ r ∈ Ioi R, HasDerivAt P (D r - q r * N r) r := fun r hr => by
    convert (hw r hr).inner ℝ (acc r hr) using 1
    rw [real_inner_smul_right, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
    dsimp [N,D]; ring
  -- continuity
  have hNc : ContinuousOn N (Ioi R) := fun r hr => (hN_d r hr).continuousAt.continuousWithinAt
  have hDc : ContinuousOn D (Ioi R) := fun r hr => (hD_d r hr).continuousAt.continuousWithinAt
  have hqc : ContinuousOn q (Ioi R) := fun r hr =>
    (hq_d r (hR.trans hr)).continuousAt.continuousWithinAt
  have hq'c : ContinuousOn q' (Ioi R) := fun r hr => by
    have : r ≠ 0 := (hR.trans hr).ne'
    exact (continuousAt_const.div (continuousAt_id.pow 3) (pow_ne_zero 3 this)).continuousWithinAt
  have hfc : ContinuousOn f (Ioi R) := hq'c.mul hNc
  have hr1R := hmem r1 le_rfl
  have hNi : IntegrableOn N (Ioi r1) := hint.mono_set (Ioi_subset_Ioi hr1R.le)
  have hfi : IntegrableOn f (Ioi r1) := by
    apply hNi.mono' ((hfc.mono (Ioi_subset_Ioi hr1R.le)).aestronglyMeasurable measurableSet_Ioi)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    simpa [f, norm_mul, Real.norm_of_nonneg (hN0 r)] using
      mul_le_of_le_one_left (hN0 r) (htail r hr.le).2.2.le
  have hqNi : IntegrableOn (fun r => q r * N r) (Ioi r1) := by
    refine (hNi.const_mul (2*E)).mono' (((hqc.mul hNc).mono (Ioi_subset_Ioi hr1R.le)).aestronglyMeasurable measurableSet_Ioi) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    rw [Real.norm_of_nonneg (mul_nonneg (hqpos r hr.le).le (hN0 r))]
    exact mul_le_mul_of_nonneg_right (hq_hi r hr.le) (hN0 r)
  -- W has an integrable derivative, hence is eventually bounded, as is P.
  obtain ⟨B, hB⟩ := (tendsto_limUnder_of_hasDerivAt_of_integrableOn_Ioi
    (fun r hr => hW_d r (hmem r hr.le)) hfi).isBoundedUnder_le
  have hPbound : ∀ᶠ r in atTop, P r ≤ B + 2 * B / E := by
    filter_upwards [eventually_ge_atTop r1, hB] with r hr hWB
    have hP : P r ≤ N r + D r := by
      refine (real_inner_le_norm _ _).trans ?_
      dsimp [N,D]; nlinarith [sq_nonneg (‖w r‖ - ‖w' r‖), sq_nonneg ‖w r‖, sq_nonneg ‖w' r‖]
    change D r + q r * N r ≤ B at hWB
    have hN : N r ≤ 2*B/E := by
      rw [le_div_iff₀ hE]
      nlinarith [mul_le_mul_of_nonneg_right (hq_lo r hr) (hN0 r), hD0 r]
    linarith [mul_nonneg (hqpos r hr).le (hN0 r)]
  -- Integrate W = P' + 2qN.  Both terms have bounded primitives on the tail.
  have hWi : IntegrableOn W (Ioi r1) := by
    have hi (b : ℝ) : IntegrableOn W (Ioc r1 b) :=
      ((hDc.add (hqc.mul hNc)).mono (fun _ ht => hmem _ ht.1)).integrableOn_Icc.mono_set Ioc_subset_Icc_self
    apply integrableOn_Ioi_of_intervalIntegral_norm_bounded
      (B + 2 * B / E - P r1 + 2 * ∫ t in Ioi r1, q t * N t) r1 hi tendsto_id
    filter_upwards [eventually_ge_atTop r1, hPbound] with b hb hP
    have hqN : IntegrableOn (fun r => q r * N r) (Ioc r1 b) := hqNi.mono_set Ioc_subset_Ioi_self
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := P) (a := r1) (b := b)
      (fun x hx => hP_d x (hmem x ((uIcc_of_le hb ▸ hx).1)))
      (((hDc.sub (hqc.mul hNc)).mono (fun _ hx => hmem _ hx.1)).intervalIntegrable_of_Icc (μ := volume) hb)
    rw [intervalIntegral.integral_of_le hb, integral_sub] at hFTC
    · have hmono := setIntegral_mono_set hqNi (ae_restrict_of_forall_mem measurableSet_Ioi
          fun t ht => mul_nonneg (hqpos t ht.le).le (hN0 t)) (Eventually.of_forall Ioc_subset_Ioi_self : Ioc r1 b ≤ᵐ[volume] Ioi r1)
      rw [intervalIntegral.integral_of_le hb, setIntegral_congr_fun measurableSet_Ioc
        (fun r hr => Real.norm_of_nonneg (hW0 r hr.1.le))]
      dsimp only [W]
      rw [integral_add _ hqN]
      · linarith
      · exact (hDc.mono (fun _ hx => hmem _ hx.1)).integrableOn_Icc.mono_set Ioc_subset_Icc_self
    · exact (hDc.mono (fun _ hx => hmem _ hx.1)).integrableOn_Icc.mono_set Ioc_subset_Icc_self
    · exact hqN
  have hWlim := tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi (fun r hr => hW_d r (hmem r hr.le)) hfi hWi
  -- For c ≥ 0 use W; for c ≤ 0 use W/q.  In either case the energy is
  -- nondecreasing to zero, so its initial value vanishes.
  have hWle : W r1 ≤ 0 := by
    rcases le_total 0 c with hc | hc
    · apply nonpos_of_deriv_nonneg_of_tendsto (fun r hr => hW_d r (hmem r hr)) _ hWlim
      intro r hr
      have : 0 < r := hR.trans (hmem r hr.le)
      dsimp [f,q']; positivity
    · have hd r (hr : r ∈ Ici r1) := (hW_d r (hmem r hr)).div (hq_d r (hR.trans (hmem r hr))) (hqpos r hr).ne'
      have ht := hWlim.div hqLim hE.ne'
      rw [zero_div] at ht
      have hle := nonpos_of_deriv_nonneg_of_tendsto hd (fun r hr => by
        refine div_nonneg ?_ (sq_nonneg _)
        have hq' : q' r ≤ 0 := div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by norm_num) hc) (pow_nonneg (hR.trans (hmem r hr.le)).le 3)
        dsimp [f,W]
        nlinarith [mul_nonpos_of_nonneg_of_nonpos (hD0 r) hq']) ht
      simpa using (div_le_iff₀ (hqpos r1 le_rfl)).mp hle
  have h0 := le_antisymm hWle (hW0 r1 le_rfl)
  obtain ⟨hd, hn⟩ := (add_eq_zero_iff_of_nonneg (hD0 r1) (mul_nonneg (hqpos r1 le_rfl).le (hN0 r1))).mp h0
  have hw1 : w r1 = 0 := by simpa [N] using (mul_eq_zero.mp hn).resolve_left (hqpos r1 le_rfl).ne'
  have hw'1 : w' r1 = 0 := by simpa [D] using hd
  -- uniqueness
  intro r hr
  have hrR : R < r := hr
  set b := max r r1 + 1
  refine ode2_unique (a := R) (b := b) (p := fun _ => 0)
    (q := fun t => ((E - c / t ^ 2 : ℝ) : ℂ)) (P := 0) (Q := E + |c| / R ^ 2)
    (fun t _ => by simp) (fun t ht => ?_) (fun t ht => hw t ht.1) (fun t ht => ?_)
    (r₀ := r1) ⟨hr1R, by simp only [b]; linarith [le_max_right r r1]⟩ hw1 hw'1 r
    ⟨hrR, by simp only [b]; linarith [le_max_left r r1]⟩
  · have ht0 : 0 < t := hR.trans ht.1
    have hRt : R ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ hR.le ht.1.le 2
    rw [Complex.norm_real, Real.norm_eq_abs]
    refine (abs_sub _ _).trans ?_
    rw [abs_of_pos hE, abs_div, abs_of_pos (by positivity : (0 : ℝ) < t ^ 2)]
    have : |c| / t ^ 2 ≤ |c| / R ^ 2 :=
      div_le_div_of_nonneg_left (abs_nonneg c) (by positivity) hRt
    linarith
  · convert hw' t ht.1 using 1
    ring

/-- The Rellich lemma for Bessel's equation `m'' + m'/r + (E - c/r²) m = 0`: a solution on
`(R, ∞)` with `∫ r |m|² dr < ∞` vanishes identically. -/
theorem bessel_rellich {E c R : ℝ} (hE : 0 < E) (hR : 0 < R) {m m' : ℝ → ℂ}
    (hm : ∀ r ∈ Ioi R, HasDerivAt m (m' r) r)
    (hm' : ∀ r ∈ Ioi R, HasDerivAt m' (-(m' r / r) - ((E - c / r ^ 2 : ℝ) : ℂ) * m r) r)
    (hint : IntegrableOn (fun r => r * ‖m r‖ ^ 2) (Ioi R)) : ∀ r ∈ Ioi R, m r = 0 := by
  set w : ℝ → ℂ := fun r => (Real.sqrt r) * m r with hwdef
  set w' : ℝ → ℂ := fun r => ((1 / (2 * Real.sqrt r) : ℝ) : ℂ) * m r + (Real.sqrt r) * m' r
    with hw'def
  have hsq_d : ∀ r, 0 < r → HasDerivAt (fun r => (Real.sqrt r : ℂ)) ((1 / (2 * Real.sqrt r) : ℝ) : ℂ) r :=
    fun r hr => (Real.hasDerivAt_sqrt hr.ne').ofReal_comp
  have hisq_d : ∀ r, 0 < r → HasDerivAt (fun r => ((1 / (2 * Real.sqrt r) : ℝ) : ℂ))
      ((-(1 / (4 * Real.sqrt r ^ 3)) : ℝ) : ℂ) r := fun r hr => by
    
    have h := ((Real.hasDerivAt_sqrt hr.ne').const_mul 2).inv (by positivity)
    
    convert h.ofReal_comp using 1
    · simp [one_div]
    · congr 1
      have  := Real.sq_sqrt hr.le
      field_simp
      norm_num
  
  have hw' : ∀ r ∈ Ioi R, HasDerivAt w' (-((((E - (c - 1 / 4) / r ^ 2) : ℝ) : ℂ) * w r)) r :=
    fun r hr => by
    have hr0  := hR.trans hr
    have hs  := Real.sqrt_pos.mpr hr0
    
    
    convert (((hisq_d r hr0).mul (hm r hr)).add ((hsq_d r hr0).mul (hm' r hr))) using 1
    
    have hsC : (Real.sqrt r : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
    have hssC : (Real.sqrt r : ℂ) ^ 2 = r := by exact_mod_cast (Real.sq_sqrt hr0.le)
    push_cast
    field_simp
    rw [show r = (Real.sqrt r : ℂ) ^ 2 from hssC.symm]
    ring
  have hint' : IntegrableOn (fun r => ‖w r‖ ^ 2) (Ioi R) := by
    refine hint.congr_fun (fun r hr => ?_) measurableSet_Ioi
    
    simp only [hwdef, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg r), mul_pow, Real.sq_sqrt (hR.trans hr).le]
  have h0 := ode_rellich hE hR (fun r hr => by
    have h := (hsq_d r (hR.trans hr)).mul (hm r hr)
    convert h using 1) hw' hint'
  intro r hr
  
  have := h0 r hr
  simp only [hwdef, mul_eq_zero] at this
  apply this.resolve_left
  have : 0 < Real.sqrt r := Real.sqrt_pos.mpr (hR.trans hr)
  exact_mod_cast this.ne'

end PolyaNeumann
