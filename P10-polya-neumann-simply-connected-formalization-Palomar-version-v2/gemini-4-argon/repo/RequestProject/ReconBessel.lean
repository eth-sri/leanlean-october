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

variable {E c R : ℝ}

/-- Uniqueness for a second-order linear ODE with bounded coefficients. -/
theorem ode2_unique {a b : ℝ} {p q : ℝ → ℂ}  (hp : ∀ r ∈ Ioo a b, ‖p r‖ ≤ P)
    (hq : ∀ r ∈ Ioo a b, ‖q r‖ ≤ Q) {y y' : ℝ → ℂ}
    (hy : ∀ r ∈ Ioo a b, HasDerivAt y (y' r) r)
    (hy' : ∀ r ∈ Ioo a b, HasDerivAt y' (-(p r * y' r) - q r * y r) r) {r₀ : ℝ}
    (hr₀ : r₀ ∈ Ioo a b) (h0 : y r₀ = 0) (h1 : y' r₀ = 0) : ∀ r ∈ Ioo a b, y r = 0 := by
  set V : ℝ → ℂ × ℂ → ℂ × ℂ := fun r z => (z.2, -(p r * z.2) - q r * z.1)
  set K : ℝ≥0 := ⟨1 + |P| + |Q|, by positivity⟩
  intro r hr
  have := (ODE_solution_unique_of_mem_Ioo (f := fun r => (y r, y' r)) (g := fun _ => (0, 0)) (s := fun _ => univ) (show ∀ r ∈ Ioo a b, LipschitzOnWith K (V r) univ by
    intro r hr
    refine (LipschitzWith.of_dist_le_mul fun z w => ?_).lipschitzOnWith
    have hQ := (hq r hr).trans (le_abs_self _)
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
      have := mul_le_mul hQ h1 (norm_nonneg _) (abs_nonneg _)
      nlinarith [abs_nonneg P, abs_nonneg Q]) hr₀ (fun r hr => ⟨(hy r hr).prodMk (hy' r hr), mem_univ _⟩) (fun r hr => ⟨by convert hasDerivAt_const (𝕜 := ℝ) r ((0 : ℂ), (0 : ℂ)) using 1; simp [V], mem_univ _⟩) (by simp [h0, h1])) hr
  simp at this
  exact this.1

/-- The decay iteration of the Rellich argument. -/
lemma decay_iter {W N f : ℝ → ℝ} {r1 B E c : ℝ} (hE : 0 < E) (hB0 : 0 ≤ B) (hr1 : 0 < r1)
    (hWB : ∀ s, r1 ≤ s → W s ≤ B) (hNW : ∀ s, r1 ≤ s → N s ≤ 2 / E * W s)
    (hf : ∀ t, r1 ≤ t → ‖f t‖ ≤ 2 * |c| / t ^ 3 * N t) (hfi : IntegrableOn f (Ioi r1))
    (htail : ∀ s, r1 ≤ s → W s ≤ ∫ t in Ioi s, ‖f t‖)
    (hcs : ∀ s, r1 ≤ s → 4 * |c| ≤ E * s ^ 2) :
    ∀ k : ℕ, ∀ s, r1 ≤ s → W s ≤ B / 2 ^ k := by
  intro k
  induction k with
  | zero => intro s hs; simpa using hWB s hs
  | succ k ih =>
    intro s hs
    have hs0 := lt_of_lt_of_le hr1 hs
    set K := 4 * |c| * B / (E * 2 ^ k) with hKdef
    have hK0 : 0 ≤ K := by positivity
    have hbound : ∀ t ∈ Ioi s, ‖f t‖ ≤ K * t ^ (-3 : ℝ) := fun t ht => by
      have ht1 := hs.trans (le_of_lt ht)
      have ht0 := hs0.trans ht
      have h2 :=
        (hNW t ht1).trans (mul_le_mul_of_nonneg_left (ih t ht1) (by positivity))
      rw [show t ^ (-3 : ℝ) = (t ^ 3)⁻¹ by
        rw [show (-3 : ℝ) = -((3 : ℕ) : ℝ) by norm_num, Real.rpow_neg ht0.le, Real.rpow_natCast]]
      calc _ ≤ _ := hf t ht1
        _ ≤ _ :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = _ := by rw [hKdef]; field_simp; ring
    have hI : ∫ t in Ioi s, K * t ^ (-3 : ℝ) = K * (s ^ (-2 : ℝ) / 2) := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hs0]
      congr 1
      norm_num
    have h5 :=
      setIntegral_mono_on (hfi.mono_set (Ioi_subset_Ioi hs)).norm ((integrableOn_Ioi_rpow_of_lt (by norm_num) hs0).const_mul K) measurableSet_Ioi hbound
    have hsq : 0 < s ^ 2 := by positivity
    have h6 : K * (s ^ (-2 : ℝ) / 2) ≤ B / 2 ^ (k + 1) := by
      rw [show K * (s ^ (-2 : ℝ) / 2) = 4 * |c| / (E * s ^ 2) * (B / 2 ^ (k + 1)) by
        rw [show s ^ (-2 : ℝ) = (s ^ 2)⁻¹ by
          rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hs0.le, Real.rpow_natCast], hKdef]; field_simp; ring]
      exact mul_le_of_le_one_left (by positivity) ((div_le_one (by positivity)).mpr (hcs s hs))
    linarith [htail s hs]

/-- A Rellich-type lemma: a solution of `w'' + (E - c/r²) w = 0` on `(R, ∞)` (`E > 0`, `R > 0`)
which is square integrable at infinity vanishes identically. -/
local notation "Φ0" => Ioi R

theorem ode_rellich  (hE : 0 < E) (hR : 0 < R) {w w' : ℝ → ℂ}
    (hw : ∀ r ∈ Φ0, HasDerivAt w (w' r) r)
    (hw' : ∀ r ∈ Φ0, HasDerivAt w' (-(((E - c / r ^ 2 : ℝ) : ℂ) * w r)) r)
    (hint : IntegrableOn (fun r => ‖w r‖ ^ 2) (Φ0)) : ∀ r ∈ Φ0, w r = 0 := by
  set q : ℝ → ℝ := fun r => E - c / r ^ 2 with hqdef
  set q' : ℝ → ℝ := fun r => 2 * c / r ^ 3 with hq'def
  set N : ℝ → ℝ := fun r => ‖w r‖ ^ 2 with hNdef
  set D : ℝ → ℝ := fun r => ‖w' r‖ ^ 2 with hDdef
  set W : ℝ → ℝ := fun r => D r + q r * N r with hWdef
  set P : ℝ → ℝ := fun r => inner ℝ (w r) (w' r) with hPdef
  set f : ℝ → ℝ := fun r => q' r * N r with hfdef
  set r1 : ℝ := R + 1 + 4 * |c| / E with hr1def
  have hc4 : 0 ≤ 4 * |c| / E := by positivity
  have hr1R : R < r1 := by linarith
  have hr1pos : 0 < r1 := by linarith
  have hcs : ∀ r, r1 ≤ r → 4 * |c| ≤ E * r ^ 2 := fun r hr => by
    have h1 : 4 * |c| / E ≤ r := by linarith
    have h2 : r ≤ r ^ 2 := by nlinarith
    have h3 : 4 * |c| ≤ E * r := by rw [div_le_iff₀ hE] at h1; linarith
    nlinarith
  have hmem : ∀ r, r1 ≤ r → r ∈ Φ0 := fun r hr => lt_of_lt_of_le hr1R hr
  -- derivatives
  have hq_d : ∀ r, 0 < r → HasDerivAt q (q' r) r := fun r hr => by
    have h := ((hasDerivAt_pow 2 r).inv (pow_ne_zero 2 hr.ne')).const_mul (-c)
    convert (h.const_add E) using 1
    · funext t; simp [hqdef]; ring
    · simp only [hq'def]; field_simp; ring
  have hN_d : ∀ r ∈ Φ0, HasDerivAt N (2 * P r) r := fun r hr => (hw r hr).norm_sq
  have hD_d : ∀ r ∈ Φ0, HasDerivAt D (-(2 * q r * P r)) r := fun r hr => by
    have h := (hw' r hr).norm_sq
    convert h using 1
    rw [show (-((E - c / r ^ 2 : ℝ) * w r)) = (-(q r)) • w r by
      rw [Complex.real_smul]; simp [hqdef]; ring, real_inner_smul_right,
      real_inner_comm]
    ring
  have hW_d : ∀ r ∈ Φ0, HasDerivAt W (f r) r := fun r hr => by
    have h := (hD_d r hr).add ((hq_d r (hR.trans hr)).mul (hN_d r hr))
    convert h using 1
    simp [hfdef]; ring
  have hP_d : ∀ r ∈ Φ0, HasDerivAt P (D r - q r * N r) r := fun r hr => by
    have h := (hw r hr).inner ℝ (hw' r hr)
    convert h using 1
    rw [show (-((E - c / r ^ 2 : ℝ) * w r)) = (-(q r)) • w r by
      rw [Complex.real_smul]; simp [hqdef]; ring, real_inner_smul_right,
      real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
    simp [hDdef, hNdef]; ring
  -- continuity
  have hNc : ContinuousOn N (Φ0) := fun r hr => (hN_d r hr).continuousAt.continuousWithinAt
  have hDc : ContinuousOn D (Φ0) := fun r hr => (hD_d r hr).continuousAt.continuousWithinAt
  have hqc : ContinuousOn q (Φ0) := fun r hr =>
    (hq_d r (hR.trans hr)).continuousAt.continuousWithinAt
  have hq'c : ContinuousOn q' (Φ0) := fun r hr => by
    exact (continuousAt_const.div (continuousAt_id.pow 3) (pow_ne_zero 3 ((hR.trans hr).ne'))).continuousWithinAt
  -- pointwise bounds on `[r1, ∞)`
  have hq_lo : ∀ r, r1 ≤ r → E / 2 ≤ q r := fun r hr => by
    have h := hcs r hr
    have hr2 : 0 < r ^ 2 := by nlinarith
    have : c / r ^ 2 ≤ E / 4 := by
      rw [div_le_iff₀ hr2]; nlinarith [le_abs_self c]
    simp [hqdef]; linarith
  have hq_hi : ∀ r, r1 ≤ r → q r ≤ 2 * E := fun r hr => by
    have h := hcs r hr
    have hr2 : 0 < r ^ 2 := by nlinarith
    have : -E / 4 ≤ c / r ^ 2 := by
      rw [le_div_iff₀ hr2]; nlinarith [neg_abs_le c]
    simp [hqdef]; linarith
  have hN0 : ∀ r, 0 ≤ N r := fun r => by positivity
  have hD0 : ∀ r, 0 ≤ D r := fun r => by positivity
  have hW0 : ∀ r, r1 ≤ r → 0 ≤ W r := fun r hr => by
    have := hq_lo r hr
    have := hN0 r; have := hD0 r
    simp [hWdef]; nlinarith
  have hNW : ∀ r, r1 ≤ r → N r ≤ 2 / E * W r := fun r hr => by
    have h1 := hq_lo r hr
    have := hN0 r; have := hD0 r
    rw [div_mul_eq_mul_div, le_div_iff₀ hE]
    simp [hWdef]; nlinarith
  have hf_le : ∀ r, r1 ≤ r → ‖f r‖ ≤ 2 * |c| * N r := fun r hr => by
    have h3 : 1 ≤ r ^ 3 := one_le_pow₀ ((show 1 ≤ r1 by linarith).trans hr)
    simp only [hfdef, hq'def, Real.norm_eq_abs, abs_mul, abs_div, abs_of_nonneg (hN0 r),
      abs_of_pos (by positivity : 0 < r ^ 3), abs_two]
    exact mul_le_mul_of_nonneg_right (div_le_self (by positivity) h3) (hN0 r)
  -- integrability on `(r1, ∞)`
  have hNi := hint.mono_set (Ioi_subset_Ioi hr1R.le)
  have hfi : IntegrableOn f (Ioi r1) := by
    refine (hNi.const_mul (2 * |c|)).mono' (((hq'c.mul hNc).mono (Ioi_subset_Ioi hr1R.le)).aestronglyMeasurable
      measurableSet_Ioi) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun r hr => ?_)
    exact hf_le r (le_of_lt hr)
  -- FTC for `W`
  have hW_ftc : ∀ r, r1 ≤ r → W r = W r1 + ∫ t in r1..r, f t := fun r hr => by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := W) (f' := f) (a := r1) (b := r)
      (fun x hx => by
        rw [uIcc_of_le hr] at hx
        exact hW_d x (hmem x hx.1))
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hr).mpr (hfi.mono_set Ioc_subset_Ioi_self))
    linarith
  set B := W r1 + ∫ t in Ioi r1, ‖f t‖ with hBdef
  have hWB : ∀ r, r1 ≤ r → W r ≤ B := fun r hr => by
    rw [hW_ftc r hr, hBdef]
    have h1 : ∫ t in r1..r, f t ≤ ∫ t in r1..r, ‖f t‖ :=
      intervalIntegral.integral_mono_on hr
        ((intervalIntegrable_iff_integrableOn_Ioc_of_le hr).mpr (hfi.mono_set Ioc_subset_Ioi_self))
        ((intervalIntegrable_iff_integrableOn_Ioc_of_le hr).mpr
          ((show IntegrableOn (fun t => ‖f t‖) (Ioi r1) volume from hfi.norm).mono_set
            Ioc_subset_Ioi_self))
        (fun t _ => Real.le_norm_self _)
    have h2 : ∫ t in r1..r, ‖f t‖ ≤ ∫ t in Ioi r1, ‖f t‖ := by
      rw [intervalIntegral.integral_of_le hr]
      exact setIntegral_mono_set hfi.norm (Eventually.of_forall fun _ => norm_nonneg _)
        (Eventually.of_forall Ioc_subset_Ioi_self)
    linarith
  -- `P` is bounded
  set PB : ℝ := (2 / E + 1) * B with hPBdef
  have hDW : ∀ r, r1 ≤ r → D r ≤ W r := fun r hr => by
    have := hq_lo r hr; have := hN0 r
    simp [hWdef]; nlinarith
  have hPB : ∀ r, r1 ≤ r → |P r| ≤ PB := fun r hr => by
    have h1 : |P r| ≤ ‖w r‖ * ‖w' r‖ := abs_real_inner_le_norm _ _
    have h2 : ‖w r‖ * ‖w' r‖ ≤ N r + D r := by
      simp [hNdef, hDdef]
      nlinarith [sq_nonneg (‖w r‖ - ‖w' r‖), norm_nonneg (w r), norm_nonneg (w' r)]
    have h3 := hNW r hr
    have h4 := hDW r hr
    have h5 := hWB r hr
    have h6 := mul_le_mul_of_nonneg_left h5 (le_of_lt (div_pos two_pos hE))
    simp [hPBdef]
    nlinarith
  -- `D` and `W` are integrable
  have hNii : ∀ b, r1 ≤ b → IntervalIntegrable N volume r1 b := fun b hb =>
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hb).mpr (hNi.mono_set Ioc_subset_Ioi_self)
  have hDi : IntegrableOn D (Ioi r1) := by
    refine integrableOn_Ioi_of_intervalIntegral_norm_bounded
      (2 * PB + 2 * E * ∫ t in Ioi r1, N t) r1 (b := fun i : ℕ => r1 + i) (fun i => ?_)
      (tendsto_atTop_add_const_left _ r1 tendsto_natCast_atTop_atTop)
      (Eventually.of_forall fun i => ?_)
    · have hb : r1 ≤ r1 + i := by simp
      exact ((hDc.mono fun t ht => hmem t ht.1).integrableOn_Icc (μ := volume)).mono_set
        Ioc_subset_Icc_self
    · set b := r1 + i
      have hb : r1 ≤ b := by simp [b]
      have hsub : ∀ t ∈ Icc r1 b, t ∈ Φ0 := fun t ht => hmem t ht.1
      have hiD := (hDc.mono hsub).intervalIntegrable_of_Icc (μ := volume) hb
      have hiqN := ((hqc.mul hNc).mono hsub).intervalIntegrable_of_Icc (μ := volume) hb
      have hP_ftc :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt
          (fun x hx => hP_d x (hsub x (by rwa [uIcc_of_le hb] at hx))) (hiD.sub hiqN)
      have e1 : ∫ t in r1..b, ‖D t‖ = ∫ t in r1..b, D t := by
        congr 1; funext t; exact Real.norm_of_nonneg (hD0 t)
      have h3 : ∫ t in r1..b, q t * N t ≤ 2 * E * ∫ t in Ioi r1, N t := by
        calc _ ≤ _ :=
              intervalIntegral.integral_mono_on hb hiqN ((hNii b hb).const_mul _)
                (fun t ht => mul_le_mul_of_nonneg_right (hq_hi t ht.1) (hN0 t))
          _ = _ := intervalIntegral.integral_const_mul _ _
          _ ≤ _ := by
              gcongr
              rw [intervalIntegral.integral_of_le hb]
              exact setIntegral_mono_set hNi (Eventually.of_forall hN0)
                (Eventually.of_forall Ioc_subset_Ioi_self)
      have h4 := abs_le.mp (hPB b hb)
      have h5 := abs_le.mp (hPB r1 le_rfl)
      rw [e1, show ∫ t in r1..b, D t = P b - P r1 + ∫ t in r1..b, q t * N t by
        have e3 : ∫ t in r1..b, D t - q t * N t =
            (∫ t in r1..b, D t) - ∫ t in r1..b, q t * N t := intervalIntegral.integral_sub hiD hiqN
        linarith]
      linarith [h4.1, h4.2, h5.1, h5.2]
  have hWi : IntegrableOn W (Ioi r1) := by
    exact hDi.add (by
      refine (hNi.const_mul (2 * E)).mono'
        (((hqc.mul hNc).mono (Ioi_subset_Ioi hr1R.le)).aestronglyMeasurable measurableSet_Ioi) ?_
      refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun r hr => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by linarith [hq_lo r hr.le]) (hN0 r))]
      exact mul_le_mul_of_nonneg_right (hq_hi r hr.le) (hN0 r))
  -- the limit of `W` is `0`
  set L := W r1 + ∫ t in Ioi r1, f t with hLdef
  have hWlim : Tendsto W atTop (𝓝 L) := by
    have h := (intervalIntegral_tendsto_integral_Ioi r1 hfi tendsto_id).const_add (W r1)
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop r1] with r hr
    rw [hW_ftc r hr]; rfl
  have hW_tail : ∀ r, r1 ≤ r → W r = -∫ t in Ioi r, f t := fun r hr => by
    have := hW_ftc r hr
    have h0 := show L = 0 by
      have hLnn : 0 ≤ L := ge_of_tendsto hWlim (by
        filter_upwards [eventually_ge_atTop r1] with r hr using hW0 r hr)
      by_contra hne
      have hLpos := lt_of_le_of_ne hLnn (Ne.symm hne)
      obtain ⟨r2, hr2⟩ := eventually_atTop.mp (hWlim.eventually (lt_mem_nhds (half_lt_self hLpos)))
      set r3 := max r1 r2
      have hc : IntegrableOn (fun _ => L / 2) (Ioi r3) := by
        refine (hWi.mono_set (Ioi_subset_Ioi (le_max_left _ _))).mono' aestronglyMeasurable_const ?_
        refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun r hr => ?_)
        rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
        exact (hr2 r ((le_max_right _ _).trans hr.le)).le
      rw [integrableOn_const_iff] at hc
      rcases hc with h | h
      · simp at h; linarith
      · simp at h
    rw [hLdef, show ∫ t in Ioi r1, f t = (∫ t in r1..r, f t) + ∫ t in Ioi r, f t by
      rw [intervalIntegral.integral_of_le hr, ← setIntegral_union Ioc_disjoint_Ioi_same
        measurableSet_Ioi (hfi.mono_set Ioc_subset_Ioi_self) (hfi.mono_set (Ioi_subset_Ioi hr)),
        Ioc_union_Ioi_eq_Ioi hr]] at h0
    linarith
  -- iteration: `W ≤ B / 2^k`
  have hiter := decay_iter hE (by
    have := hW0 r1 le_rfl
    have : 0 ≤ ∫ t in Ioi r1, ‖f t‖ := integral_nonneg fun _ => norm_nonneg _
    linarith) hr1pos hWB hNW (fun t ht => by
      have ht0 : 0 < t := lt_of_lt_of_le hr1pos ht
      simp only [hfdef, hq'def, Real.norm_eq_abs, abs_mul, abs_div, abs_of_nonneg (hN0 t),
        abs_of_pos (pow_pos ht0 3), abs_two]
      exact le_rfl) hfi
    (fun s hs => by
      rw [hW_tail s hs]
      exact (neg_le_abs _).trans (by rw [← Real.norm_eq_abs]; exact norm_integral_le_integral_norm _))
    hcs
  have hW_zero : ∀ s, r1 ≤ s → W s = 0 := fun s hs => by
    exact le_antisymm (ge_of_tendsto' (tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)) fun k => hiter k s hs) (hW0 s hs)
  -- the initial data at `r1` vanish
  have h0 := hW_zero r1 le_rfl
  have hq1 := hq_lo r1 le_rfl
  have h0' := h0
  have hqN : 0 ≤ q r1 * N r1 := mul_nonneg (by linarith) (hN0 r1)
  -- uniqueness
  intro r hr
  set b := max r r1 + 1
  refine ode2_unique (a := R) (b := b) (p := fun _ => 0)
    (q := fun t => (E - c / t ^ 2 : ℝ)) (P := 0) (Q := E + |c| / R ^ 2)
    (fun t _ => by simp) (fun t ht => ?_) (fun t ht => hw t ht.1) (fun t ht => ?_)
    (r₀ := r1) ⟨hr1R, by simp [b]; linarith [le_max_right r r1]⟩ (by
      simpa [hNdef] using show N r1 = 0 by
        have hqN0 : q r1 * N r1 = 0 := by linarith [hD0 r1]
        rcases mul_eq_zero.mp hqN0 with h | h
        · linarith
        · exact h) (by
      simpa [hDdef] using show D r1 = 0 by linarith [hD0 r1]) r
    ⟨hr, by simp [b]; linarith [le_max_left r r1]⟩
  · have ht0 := hR.trans ht.1
    rw [Complex.norm_real, Real.norm_eq_abs]
    refine (abs_sub _ _).trans ?_
    rw [abs_of_pos hE, abs_div, abs_of_pos (by positivity : 0 < t ^ 2)]
    have:=
      div_le_div_of_nonneg_left (abs_nonneg c) (by positivity) (pow_le_pow_left₀ hR.le ht.1.le 2)
    linarith
  · convert hw' t ht.1 using 1
    ring

/-- The Rellich lemma for Bessel's equation `m'' + m'/r + (E - c/r²) m = 0`: a solution on
`(R, ∞)` with `∫ r |m|² dr < ∞` vanishes identically. -/
theorem bessel_rellich  (hE : 0 < E) (hR : 0 < R) 
    (hm : ∀ r ∈ Φ0, HasDerivAt m (m' r) r)
    (hm' : ∀ r ∈ Φ0, HasDerivAt m' (-(m' r / r) - ((E - c / r ^ 2 : ℝ) : ℂ) * m r) r)
    (hint : IntegrableOn (fun r => r * ‖m r‖ ^ 2) (Φ0)) : ∀ r ∈ Φ0, m r = 0 := by
  set w : ℝ → ℂ := fun r => (Real.sqrt r : ℂ) * m r with hwdef
  set w' : ℝ → ℂ := fun r => ((1 / (2 * Real.sqrt r) : ℝ) : ℂ) * m r + (Real.sqrt r : ℂ) * m' r
    with hw'def
  have hsq_d : ∀ r, 0 < r → HasDerivAt (fun r => (Real.sqrt r : ℂ)) ((1 / (2 * Real.sqrt r) : ℝ) : ℂ) r :=
    fun r hr => (Real.hasDerivAt_sqrt hr.ne').ofReal_comp
  have hisq_d : ∀ r, 0 < r → HasDerivAt (fun r => ((1 / (2 * Real.sqrt r) : ℝ) : ℂ))
      ((-(1 / (4 * Real.sqrt r ^ 3)) : ℝ) : ℂ) r := fun r hr => by
    have hs := Real.sqrt_pos.mpr hr
    have h := ((Real.hasDerivAt_sqrt hr.ne').const_mul 2).inv (by positivity)
    convert h.ofReal_comp using 1
    · funext t; simp
    · congr 1
      field_simp
      norm_num
  have hw : ∀ r ∈ Φ0, HasDerivAt w (w' r) r := fun r hr => by
    have h := (hsq_d r (hR.trans hr)).mul (hm r hr)
    convert h using 1
  have hw' : ∀ r ∈ Φ0, HasDerivAt w' (-((((E - (c - 1 / 4) / r ^ 2) : ℝ) : ℂ) * w r)) r :=
    fun r hr => by
    have hr0 := hR.trans hr
    have hs := Real.sqrt_pos.mpr hr0
    convert (((hisq_d r hr0).mul (hm r hr)).add ((hsq_d r hr0).mul (hm' r hr))) using 1
    simp [hwdef]
    have hsC : (Real.sqrt r : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
    field_simp
    rw [show (r : ℂ) = (Real.sqrt r : ℂ) ^ 2 from (show (Real.sqrt r : ℂ) ^ 2 = r by exact_mod_cast (Real.sq_sqrt hr0.le)).symm]
    ring
  intro r hr
  have := (ode_rellich hE hR hw hw' (by
    refine hint.congr_fun (fun r hr => ?_) measurableSet_Ioi
    simp [hwdef, abs_of_nonneg (Real.sqrt_nonneg r), mul_pow, Real.sq_sqrt (hR.trans hr).le])) r hr
  simp only [hwdef, mul_eq_zero] at this
  exact this.resolve_left (by
    exact_mod_cast (Real.sqrt_pos.mpr (hR.trans hr)).ne')

end PolyaNeumann
