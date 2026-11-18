module

public import RequestProject.ReconBasic
public import RequestProject.ReconDensity
public import RequestProject.WeakConstancy
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
# Vanishing of `L²` Helmholtz solutions on unbounded connected open sets

Combines ODE uniqueness and Rellich decay (`ode2_unique`, `bessel_rellich`), angular Fourier modes
(`angMode_bessel`), disc unique continuation (`eq_zero_on_ball_of_helmholtz`), exterior vanishing
(`eq_zero_outside_of_helmholtz`), and mollification to prove `ae_eq_zero_of_helmholtz`.
-/

@[expose] public section

open MeasureTheory Set Filter Metric Topology
open scoped ComplexConjugate Real NNReal ENNReal

noncomputable section

namespace PolyaNeumann

/-! ### Second-order ODE uniqueness and Rellich decay -/

theorem ode2_unique {a b : ℝ} {p q : ℝ → ℂ} {P Q : ℝ} (hp : ∀ r ∈ Ioo a b, ‖p r‖ ≤ P)
    (hq : ∀ r ∈ Ioo a b, ‖q r‖ ≤ Q) {y y' : ℝ → ℂ}
    (hy : ∀ r ∈ Ioo a b, HasDerivAt y (y' r) r)
    (hy' : ∀ r ∈ Ioo a b, HasDerivAt y' (-(p r * y' r) - q r * y r) r) {r₀ : ℝ}
    (hr₀ : r₀ ∈ Ioo a b) (h0 : y r₀ = 0) (h1 : y' r₀ = 0) : ∀ r ∈ Ioo a b, y r = 0 := by
  set V : ℝ → ℂ × ℂ → ℂ × ℂ := fun r z => (z.2, -(p r * z.2) - q r * z.1)
  set K : ℝ≥0 := ⟨1 + |P| + |Q|, by positivity⟩
  have hV : ∀ r ∈ Ioo a b, LipschitzOnWith K (V r) univ := fun r hr => by
    refine (LipschitzWith.of_dist_le_mul fun z w => ?_).lipschitzOnWith
    have hP : ‖p r‖ ≤ |P| := (hp r hr).trans (le_abs_self _)
    have hQ : ‖q r‖ ≤ |Q| := (hq r hr).trans (le_abs_self _)
    rw [dist_eq_norm, dist_eq_norm,
      show V r z - V r w = (z.2 - w.2, -(p r * (z.2 - w.2)) - q r * (z.1 - w.1)) by
        simp only [V, Prod.mk_sub_mk]; congr 1; ring,
      Prod.norm_def, show (K : ℝ) = 1 + |P| + |Q| from rfl]
    have h1' : ‖z.1 - w.1‖ ≤ ‖z - w‖ := by rw [← Prod.fst_sub]; exact norm_fst_le _
    have h2' : ‖z.2 - w.2‖ ≤ ‖z - w‖ := by rw [← Prod.snd_sub]; exact norm_snd_le _
    have hn := norm_nonneg (z - w)
    refine max_le (by nlinarith [abs_nonneg P, abs_nonneg Q]) ((norm_sub_le _ _).trans ?_)
    rw [norm_neg, norm_mul, norm_mul]
    nlinarith [mul_le_mul hP h2' (norm_nonneg _) (abs_nonneg _),
      mul_le_mul hQ h1' (norm_nonneg _) (abs_nonneg _), abs_nonneg P, abs_nonneg Q]
  have heq := ODE_solution_unique_of_mem_Ioo (f := fun r => (y r, y' r)) (g := fun _ => (0, 0))
    (s := fun _ => univ) hV hr₀
    (fun r hr => ⟨(hy r hr).prodMk (hy' r hr), mem_univ _⟩)
    (fun r _ => ⟨by convert hasDerivAt_const (𝕜 := ℝ) r ((0 : ℂ), (0 : ℂ)) using 1; simp [V],
      mem_univ _⟩)
    (by simp [h0, h1])
  exact fun _ hr => (Prod.mk.inj (heq hr)).1

theorem ode_rellich {E c R : ℝ} (hE : 0 < E) (hR : 0 < R) {w w' : ℝ → ℂ}
    (hw : ∀ r ∈ Ioi R, HasDerivAt w (w' r) r)
    (hw' : ∀ r ∈ Ioi R, HasDerivAt w' (-(((E - c / r ^ 2 : ℝ) : ℂ) * w r)) r)
    (hint : IntegrableOn (fun r => ‖w r‖ ^ 2) (Ioi R)) : ∀ r ∈ Ioi R, w r = 0 := by
  set q : ℝ → ℝ := fun r => E - c / r ^ 2 with hqdef
  set q' : ℝ → ℝ := fun r => 2 * c / r ^ 3 with hq'def
  set N : ℝ → ℝ := fun r => ‖w r‖ ^ 2 with hNdef
  set D : ℝ → ℝ := fun r => ‖w' r‖ ^ 2 with hDdef
  set W : ℝ → ℝ := fun r => D r + q r * N r with hWdef
  set P : ℝ → ℝ := fun r => inner ℝ (w r) (w' r)
  set f : ℝ → ℝ := fun r => q' r * N r with hfdef
  set r1 : ℝ := R + 1 + 4 * |c| / E
  have hc4 : 0 ≤ 4 * |c| / E := by positivity
  have hr1R : R < r1 := by linarith
  have hr1 : 1 ≤ r1 := by linarith
  have hr1pos : 0 < r1 := by linarith
  have hcs : ∀ r, r1 ≤ r → 4 * |c| ≤ E * r ^ 2 := fun r hr => by
    have h1 : 4 * |c| / E ≤ r := by linarith
    have h2 : r ≤ r ^ 2 := by nlinarith
    rw [div_le_iff₀ hE] at h1
    nlinarith
  have hmem : ∀ r, r1 ≤ r → r ∈ Ioi R := fun _ hr => lt_of_lt_of_le hr1R hr
  have hqw : ∀ r, -(((E - c / r ^ 2 : ℝ) : ℂ) * w r) = (-(q r)) • w r := fun r => by
    rw [Complex.real_smul]; simp only [hqdef]; push_cast; ring
  have hq_d : ∀ r, 0 < r → HasDerivAt q (q' r) r := fun r hr => by
    convert (((hasDerivAt_pow 2 r).inv (pow_ne_zero 2 hr.ne')).const_mul (-c)).const_add E using 1
    · funext t; simp only [hqdef, Pi.inv_apply]; ring
    · simp only [hq'def]; field_simp; ring
  have hN_d : ∀ r ∈ Ioi R, HasDerivAt N (2 * P r) r := fun r hr => (hw r hr).norm_sq
  have hD_d : ∀ r ∈ Ioi R, HasDerivAt D (-(2 * q r * P r)) r := fun r hr => by
    convert (hw' r hr).norm_sq using 1
    rw [hqw, real_inner_smul_right, real_inner_comm]; ring
  have hW_d : ∀ r ∈ Ioi R, HasDerivAt W (f r) r := fun r hr => by
    convert (hD_d r hr).add ((hq_d r (hR.trans hr)).mul (hN_d r hr)) using 1
    simp only [hfdef]; ring
  have hP_d : ∀ r ∈ Ioi R, HasDerivAt P (D r - q r * N r) r := fun r hr => by
    convert (hw r hr).inner ℝ (hw' r hr) using 1
    rw [hqw, real_inner_smul_right, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
    simp only [hDdef, hNdef]; ring
  have hNc : ContinuousOn N (Ioi R) := fun r hr => (hN_d r hr).continuousAt.continuousWithinAt
  have hDc : ContinuousOn D (Ioi R) := fun r hr => (hD_d r hr).continuousAt.continuousWithinAt
  have hqc : ContinuousOn q (Ioi R) := fun r hr =>
    (hq_d r (hR.trans hr)).continuousAt.continuousWithinAt
  have hq'c : ContinuousOn q' (Ioi R) := fun r hr =>
    (continuousAt_const.div (continuousAt_id.pow 3)
      (pow_ne_zero 3 (hR.trans hr).ne')).continuousWithinAt
  have hfc : ContinuousOn f (Ioi R) := hq'c.mul hNc
  have hq_lo : ∀ r, r1 ≤ r → E / 2 ≤ q r := fun r hr => by
    have hr2 : 0 < r ^ 2 := by nlinarith
    have : c / r ^ 2 ≤ E / 4 := (div_le_iff₀ hr2).mpr (by nlinarith [hcs r hr, le_abs_self c])
    simp only [hqdef]; linarith
  have hq_hi : ∀ r, r1 ≤ r → q r ≤ 2 * E := fun r hr => by
    have hr2 : 0 < r ^ 2 := by nlinarith
    have : -(E / 4) ≤ c / r ^ 2 := (le_div_iff₀ hr2).mpr (by nlinarith [hcs r hr, neg_abs_le c])
    simp only [hqdef]; linarith
  have hN0 : ∀ r, 0 ≤ N r := fun _ => by positivity
  have hD0 : ∀ r, 0 ≤ D r := fun _ => by positivity
  have hW0 : ∀ r, r1 ≤ r → 0 ≤ W r := fun r hr => by
    simp only [hWdef]; nlinarith [hq_lo r hr, hN0 r, hD0 r]
  have hNW : ∀ r, r1 ≤ r → N r ≤ 2 / E * W r := fun r hr => by
    rw [div_mul_eq_mul_div, le_div_iff₀ hE]
    simp only [hWdef]; nlinarith [hq_lo r hr, hN0 r, hD0 r]
  have hNi : IntegrableOn N (Ioi r1) := hint.mono_set (Ioi_subset_Ioi hr1R.le)
  have hfi : IntegrableOn f (Ioi r1) := by
    refine (hNi.const_mul (2 * |c|)).mono'
      ((hfc.mono (Ioi_subset_Ioi hr1R.le)).aestronglyMeasurable measurableSet_Ioi)
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun r hr => ?_))
    have h3 : 1 ≤ r ^ 3 := one_le_pow₀ (hr1.trans hr.le)
    simp only [hfdef, hq'def, Real.norm_eq_abs, abs_mul, abs_div, abs_of_nonneg (hN0 r),
      abs_of_pos (by positivity : (0 : ℝ) < r ^ 3), abs_two]
    exact mul_le_mul_of_nonneg_right (div_le_self (by positivity) h3) (hN0 r)
  have hW_ftc : ∀ r, r1 ≤ r → W r = W r1 + ∫ t in r1..r, f t := fun r hr => by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := W) (f' := f) (a := r1) (b := r)
      (fun x hx => hW_d x (hmem x (by rw [uIcc_of_le hr] at hx; exact hx.1)))
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hr).mpr (hfi.mono_set Ioc_subset_Ioi_self))
    linarith
  set B : ℝ := W r1 + ∫ t in Ioi r1, ‖f t‖
  have hB0 : 0 ≤ B := add_nonneg (hW0 r1 le_rfl) (integral_nonneg fun _ => norm_nonneg _)
  have hWB : ∀ r, r1 ≤ r → W r ≤ B := fun r hr => by
    have h1 : ∫ t in r1..r, f t ≤ ∫ t in r1..r, ‖f t‖ :=
      (Real.le_norm_self _).trans (intervalIntegral.norm_integral_le_integral_norm hr)
    have h2 : ∫ t in r1..r, ‖f t‖ ≤ ∫ t in Ioi r1, ‖f t‖ := by
      rw [intervalIntegral.integral_of_le hr]
      exact setIntegral_mono_set hfi.norm (Eventually.of_forall fun _ => norm_nonneg _)
        (Eventually.of_forall Ioc_subset_Ioi_self)
    linarith [hW_ftc r hr]
  set PB : ℝ := (2 / E + 1) * B
  have hPB : ∀ r, r1 ≤ r → |P r| ≤ PB := fun r hr => by
    have h1 : |P r| ≤ N r + D r := (abs_real_inner_le_norm _ _).trans <| by
      simp only [hNdef, hDdef]
      nlinarith [sq_nonneg (‖w r‖ - ‖w' r‖), norm_nonneg (w r), norm_nonneg (w' r)]
    have hDW : D r ≤ W r := by simp only [hWdef]; nlinarith [hq_lo r hr, hN0 r]
    nlinarith [hNW r hr, hWB r hr, mul_le_mul_of_nonneg_left (hWB r hr) (div_pos two_pos hE).le]
  have hDi : IntegrableOn D (Ioi r1) := by
    refine integrableOn_Ioi_of_intervalIntegral_norm_bounded
      (2 * PB + 2 * E * ∫ t in Ioi r1, N t) r1 (b := fun i : ℕ => r1 + i)
      (fun i => ((hDc.mono fun t ht => hmem t ht.1).integrableOn_Icc
        (μ := volume)).mono_set Ioc_subset_Icc_self)
      (tendsto_atTop_add_const_left _ r1 tendsto_natCast_atTop_atTop)
      (Eventually.of_forall fun i => ?_)
    set b := r1 + (i : ℝ)
    have hb : r1 ≤ b := by simp [b]
    have hsub : ∀ t ∈ Icc r1 b, t ∈ Ioi R := fun t ht => hmem t ht.1
    have hiD := (hDc.mono hsub).intervalIntegrable_of_Icc (μ := volume) hb
    have hiqN := ((hqc.mul hNc).mono hsub).intervalIntegrable_of_Icc (μ := volume) hb
    have hP_ftc : ∫ t in r1..b, (D t - q t * N t) = P b - P r1 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun x hx => hP_d x (hsub x (by rwa [uIcc_of_le hb] at hx))) (hiD.sub hiqN)
    have e0 : ∫ t in r1..b, ‖D t‖ = ∫ t in r1..b, D t := by
      congr 1; funext t; exact Real.norm_of_nonneg (hD0 t)
    have e1 : ∫ t in r1..b, D t = (P b - P r1) + ∫ t in r1..b, q t * N t := by
      have e3 : ∫ t in r1..b, (D t - q t * N t) =
          (∫ t in r1..b, D t) - ∫ t in r1..b, q t * N t := intervalIntegral.integral_sub hiD hiqN
      linarith
    have h3 : ∫ t in r1..b, q t * N t ≤ 2 * E * ∫ t in Ioi r1, N t := by
      have hNii : IntervalIntegrable N volume r1 b :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le hb).mpr (hNi.mono_set Ioc_subset_Ioi_self)
      calc ∫ t in r1..b, q t * N t ≤ ∫ t in r1..b, 2 * E * N t :=
            intervalIntegral.integral_mono_on hb hiqN (hNii.const_mul _)
              fun t ht => mul_le_mul_of_nonneg_right (hq_hi t ht.1) (hN0 t)
        _ = 2 * E * ∫ t in r1..b, N t := intervalIntegral.integral_const_mul _ _
        _ ≤ 2 * E * ∫ t in Ioi r1, N t := by
            gcongr; rw [intervalIntegral.integral_of_le hb]
            exact setIntegral_mono_set hNi (Eventually.of_forall hN0)
              (Eventually.of_forall Ioc_subset_Ioi_self)
    rw [e0, e1]
    linarith [(abs_le.mp (hPB b hb)).1, (abs_le.mp (hPB b hb)).2,
      (abs_le.mp (hPB r1 le_rfl)).1, (abs_le.mp (hPB r1 le_rfl)).2]
  have hWi : IntegrableOn W (Ioi r1) := hDi.add <|
    (hNi.const_mul (2 * E)).mono'
      (((hqc.mul hNc).mono (Ioi_subset_Ioi hr1R.le)).aestronglyMeasurable measurableSet_Ioi)
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun r hr => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by linarith [hq_lo r hr.le]) (hN0 r))]
        exact mul_le_mul_of_nonneg_right (hq_hi r hr.le) (hN0 r)))
  set L : ℝ := W r1 + ∫ t in Ioi r1, f t with hLdef
  have hWlim : Tendsto W atTop (𝓝 L) :=
    ((intervalIntegral_tendsto_integral_Ioi r1 hfi tendsto_id).const_add (W r1)).congr' <| by
      filter_upwards [eventually_ge_atTop r1] with r hr using (hW_ftc r hr).symm
  have hL0 : L = 0 := by
    have hLnn : 0 ≤ L := ge_of_tendsto hWlim
      ((eventually_ge_atTop r1).mono fun r hr => hW0 r hr)
    by_contra hne
    have hLpos : 0 < L := lt_of_le_of_ne hLnn (Ne.symm hne)
    obtain ⟨r2, hr2⟩ := eventually_atTop.mp (hWlim.eventually (lt_mem_nhds (half_lt_self hLpos)))
    have hc : IntegrableOn (fun _ : ℝ => L / 2) (Ioi (max r1 r2)) :=
      (hWi.mono_set (Ioi_subset_Ioi (le_max_left _ _))).mono' aestronglyMeasurable_const
        ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun r hr => by
          rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
          exact (hr2 r ((le_max_right _ _).trans hr.le)).le))
    rw [integrableOn_const_iff] at hc
    rcases hc with h | h <;> [ (simp at h; linarith); simp at h ]
  have htail : ∀ s, r1 ≤ s → W s ≤ ∫ t in Ioi s, ‖f t‖ := fun s hs => by
    have hsplit : ∫ t in Ioi r1, f t = (∫ t in r1..s, f t) + ∫ t in Ioi s, f t := by
      rw [intervalIntegral.integral_of_le hs, ← setIntegral_union Ioc_disjoint_Ioi_same
        measurableSet_Ioi (hfi.mono_set Ioc_subset_Ioi_self) (hfi.mono_set (Ioi_subset_Ioi hs)),
        Ioc_union_Ioi_eq_Ioi hs]
    have hWt : W s = -∫ t in Ioi s, f t := by linarith [hW_ftc s hs, hL0, hLdef, hsplit]
    rw [hWt]
    exact (neg_le_abs _).trans (by rw [← Real.norm_eq_abs]; exact norm_integral_le_integral_norm _)
  have hiter : ∀ k : ℕ, ∀ s, r1 ≤ s → W s ≤ B / 2 ^ k := by
    intro k; induction k with
    | zero => intro s hs; simpa using hWB s hs
    | succ k ih =>
      intro s hs
      have hs0 : 0 < s := lt_of_lt_of_le hr1pos hs
      set K : ℝ := 4 * |c| * B / (E * 2 ^ k) with hKdef
      have h5 : ∫ t in Ioi s, ‖f t‖ ≤ ∫ t in Ioi s, K * t ^ (-3 : ℝ) := by
        refine setIntegral_mono_on (hfi.mono_set (Ioi_subset_Ioi hs)).norm
          ((integrableOn_Ioi_rpow_of_lt (by norm_num) hs0).const_mul K) measurableSet_Ioi
          fun t ht => ?_
        have ht1 : r1 ≤ t := hs.trans ht.le
        have ht0 : 0 < t := hs0.trans ht
        rw [show (-3 : ℝ) = -((3 : ℕ) : ℝ) by norm_num, Real.rpow_neg ht0.le, Real.rpow_natCast]
        have hf_t : ‖f t‖ = 2 * |c| / t ^ 3 * N t := by
          simp [hfdef, hq'def, Real.norm_eq_abs, abs_of_nonneg (hN0 t), abs_of_pos ht0]
        calc ‖f t‖ ≤ 2 * |c| / t ^ 3 * (2 / E * (B / 2 ^ k)) := by
              rw [hf_t]
              exact mul_le_mul_of_nonneg_left
                ((hNW t ht1).trans (mul_le_mul_of_nonneg_left (ih t ht1) (by positivity)))
                (by positivity)
          _ = K * (t ^ 3)⁻¹ := by rw [hKdef]; field_simp; ring
      have hI : ∫ t in Ioi s, K * t ^ (-3 : ℝ) = 4 * |c| / (E * s ^ 2) * (B / 2 ^ (k + 1)) := by
        rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hs0,
          show (-3 : ℝ) + 1 = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hs0.le, Real.rpow_natCast,
          hKdef]
        field_simp; ring
      have hle1 : 4 * |c| / (E * s ^ 2) ≤ 1 := (div_le_one (by positivity)).mpr (hcs s hs)
      exact (htail s hs).trans (h5.trans (hI.le.trans (mul_le_of_le_one_left (by positivity) hle1)))
  have h0 : D r1 + q r1 * N r1 = 0 :=
    le_antisymm (ge_of_tendsto'
      (tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt one_lt_two))
      fun k => hiter k r1 le_rfl) (hW0 r1 le_rfl)
  have hq1 := hq_lo r1 le_rfl
  have hD1 : D r1 = 0 := by nlinarith [hN0 r1, hD0 r1]
  have hN1 : N r1 = 0 := by nlinarith [hN0 r1, hD0 r1]
  intro r hr
  set b := max r r1 + 1
  refine ode2_unique (a := R) (b := b) (p := fun _ => 0)
    (q := fun t => ((E - c / t ^ 2 : ℝ) : ℂ)) (P := 0) (Q := E + |c| / R ^ 2)
    (fun _ _ => by simp) (fun t ht => ?_) (fun t ht => hw t ht.1)
    (fun t ht => by convert hw' t ht.1 using 1; ring)
    (r₀ := r1) ⟨hr1R, by simp only [b]; linarith [le_max_right r r1]⟩
    (by simpa [hNdef] using hN1) (by simpa [hDdef] using hD1) r
    ⟨hr, by simp only [b]; linarith [le_max_left r r1]⟩
  have ht0 : 0 < t := hR.trans ht.1
  rw [Complex.norm_real, Real.norm_eq_abs]
  refine (abs_sub _ _).trans ?_
  rw [abs_of_pos hE, abs_div, abs_of_pos (by positivity : (0 : ℝ) < t ^ 2)]
  linarith [div_le_div_of_nonneg_left (abs_nonneg c) (by positivity)
    (pow_le_pow_left₀ hR.le ht.1.le 2)]

theorem bessel_rellich {E c R : ℝ} (hE : 0 < E) (hR : 0 < R) {m m' : ℝ → ℂ}
    (hm : ∀ r ∈ Ioi R, HasDerivAt m (m' r) r)
    (hm' : ∀ r ∈ Ioi R, HasDerivAt m' (-(m' r / r) - ((E - c / r ^ 2 : ℝ) : ℂ) * m r) r)
    (hint : IntegrableOn (fun r => r * ‖m r‖ ^ 2) (Ioi R)) : ∀ r ∈ Ioi R, m r = 0 := by
  set w : ℝ → ℂ := fun r => (Real.sqrt r : ℂ) * m r with hwdef
  set w' : ℝ → ℂ := fun r => ((1 / (2 * Real.sqrt r) : ℝ) : ℂ) * m r + (Real.sqrt r : ℂ) * m' r
  have hsq_d : ∀ r, 0 < r →
      HasDerivAt (fun r => (Real.sqrt r : ℂ)) ((1 / (2 * Real.sqrt r) : ℝ) : ℂ) r :=
    fun _ hr => (Real.hasDerivAt_sqrt hr.ne').ofReal_comp
  have hisq_d : ∀ r, 0 < r → HasDerivAt (fun r => ((1 / (2 * Real.sqrt r) : ℝ) : ℂ))
      ((-(1 / (4 * Real.sqrt r ^ 3)) : ℝ) : ℂ) r := fun r hr => by
    have hs : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr
    convert (((Real.hasDerivAt_sqrt hr.ne').const_mul 2).inv (by positivity)).ofReal_comp using 1
    · funext _; simp [one_div]
    · congr 1; have := Real.sq_sqrt hr.le; field_simp; norm_num
  have hw : ∀ r ∈ Ioi R, HasDerivAt w (w' r) r := fun r hr => by
    convert (hsq_d r (hR.trans hr)).mul (hm r hr) using 1
  have hw' : ∀ r ∈ Ioi R, HasDerivAt w' (-((((E - (c - 1 / 4) / r ^ 2) : ℝ) : ℂ) * w r)) r :=
    fun r hr => by
      have hr0 : 0 < r := hR.trans hr
      have hsC : (Real.sqrt r : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hr0).ne'
      have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
      have hssC : (Real.sqrt r : ℂ) ^ 2 = r := by exact_mod_cast Real.sq_sqrt hr0.le
      convert ((hisq_d r hr0).mul (hm r hr)).add ((hsq_d r hr0).mul (hm' r hr)) using 1
      simp only [hwdef]; push_cast; field_simp
      rw [show (r : ℂ) = (Real.sqrt r : ℂ) ^ 2 from hssC.symm]; ring
  have h0 := ode_rellich hE hR hw hw' <| hint.congr_fun (fun r hr => by
    simp [hwdef, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg r), mul_pow, Real.sq_sqrt (hR.trans hr).le])
    measurableSet_Ioi
  intro r hr
  have hs : (Real.sqrt r : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr (hR.trans hr)).ne'
  exact (mul_eq_zero.mp (h0 r hr)).resolve_left hs

/-! ### Angular Fourier modes and Bessel's equation -/

private lemma hasDerivAt_intervalIntegral_param {F F' : ℝ → ℝ → ℂ}
    (hF : ∀ r θ, HasDerivAt (fun r => F r θ) (F' r θ) r)
    (hFc : Continuous (Function.uncurry F)) (hF'c : Continuous (Function.uncurry F'))
    (a b r₀ : ℝ) :
    HasDerivAt (fun r => ∫ θ in a..b, F r θ) (∫ θ in a..b, F' r₀ θ) r₀ := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_uIcc :
    IsCompact (Icc (r₀ - 1) (r₀ + 1) ×ˢ uIcc a b)).exists_bound_of_continuousOn hF'c.continuousOn
  exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound := fun _ => C)
    (s := Ioo (r₀ - 1) (r₀ + 1)) (Ioo_mem_nhds (by linarith) (by linarith))
    (Eventually.of_forall fun _ =>
      (hFc.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    ((hFc.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _)
    (hF'c.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    (Eventually.of_forall fun θ hθ r hr => hC (r, θ) ⟨⟨hr.1.le, hr.2.le⟩, uIoc_subset_uIcc hθ⟩)
    intervalIntegrable_const (Eventually.of_forall fun θ _ r _ => hF r θ)).2

def eI (θ : ℝ) : ℂ := Complex.exp (θ * Complex.I)

private lemma continuous_eI : Continuous eI := by unfold eI; fun_prop

private lemma hasDerivAt_eI (θ : ℝ) : HasDerivAt eI (Complex.I * eI θ) θ := by
  convert ((hasDerivAt_id θ).ofReal_comp.mul_const Complex.I).cexp using 1
  · funext _; simp [eI]
  · simp [eI]; ring

private lemma eI_periodic : Function.Periodic eI (2 * π) := fun θ => by
  simp only [eI]; push_cast; rw [add_mul, Complex.exp_add]; simp

def angChar (n : ℤ) (θ : ℝ) : ℂ := Complex.exp (-(n * θ * Complex.I))

private lemma continuous_angChar (n : ℤ) : Continuous (angChar n) := by unfold angChar; fun_prop

def circPt (x₀ : ℂ) (r θ : ℝ) : ℂ := x₀ + r * eI θ

private lemma continuous_circPt (x₀ : ℂ) : Continuous (Function.uncurry (circPt x₀)) := by
  unfold circPt
  exact continuous_const.add
    ((Complex.continuous_ofReal.comp continuous_fst).mul (continuous_eI.comp continuous_snd))

private lemma dist_circPt (x₀ : ℂ) {r : ℝ} (hr : 0 ≤ r) (θ : ℝ) : dist (circPt x₀ r θ) x₀ = r := by
  simp [circPt, dist_eq_norm, eI, Complex.norm_exp, abs_of_nonneg hr]

def angMode (v : ℂ → ℂ) (x₀ : ℂ) (n : ℤ) (r : ℝ) : ℂ :=
  ∫ θ in (0 : ℝ)..2 * π, angChar n θ * v (circPt x₀ r θ)

def angMode1 (v : ℂ → ℂ) (x₀ : ℂ) (n : ℤ) (r : ℝ) : ℂ :=
  ∫ θ in (0 : ℝ)..2 * π, angChar n θ * fderiv ℝ v (circPt x₀ r θ) (eI θ)

def angMode2 (v : ℂ → ℂ) (x₀ : ℂ) (n : ℤ) (r : ℝ) : ℂ :=
  ∫ θ in (0 : ℝ)..2 * π, angChar n θ * fderiv ℝ (fderiv ℝ v) (circPt x₀ r θ) (eI θ) (eI θ)

section Smooth

variable {v : ℂ → ℂ} (hv : ContDiff ℝ 2 v) (x₀ : ℂ) (n : ℤ)
include hv

private lemma hasDerivAt_angMode (r : ℝ) : HasDerivAt (angMode v x₀ n) (angMode1 v x₀ n r) r := by
  have hd : Differentiable ℝ v := hv.differentiable (by norm_num)
  have hcr : ∀ r θ, HasDerivAt (fun r => circPt x₀ r θ) (eI θ) r := fun r θ => by
    simpa [circPt] using ((hasDerivAt_id r).ofReal_comp.mul_const (eI θ)).const_add x₀
  exact hasDerivAt_intervalIntegral_param
    (fun r θ => ((hd _).hasFDerivAt.comp_hasDerivAt r (hcr r θ)).const_mul _)
    (((continuous_angChar n).comp continuous_snd).mul (hv.continuous.comp (continuous_circPt x₀)))
    (((continuous_angChar n).comp continuous_snd).mul
      (((hv.continuous_fderiv (by norm_num)).comp (continuous_circPt x₀)).clm_apply
        (continuous_eI.comp continuous_snd))) _ _ r

private lemma hasDerivAt_angMode1 (r : ℝ) : HasDerivAt (angMode1 v x₀ n) (angMode2 v x₀ n r) r := by
  have hcd1 : ContDiff ℝ 1 (fderiv ℝ v) := hv.fderiv_right (m := 1) (by norm_num)
  have hd : Differentiable ℝ (fderiv ℝ v) := hcd1.differentiable one_ne_zero
  have hcr : ∀ r θ, HasDerivAt (fun r => circPt x₀ r θ) (eI θ) r := fun r θ => by
    simpa [circPt] using ((hasDerivAt_id r).ofReal_comp.mul_const (eI θ)).const_add x₀
  refine hasDerivAt_intervalIntegral_param
    (F := fun r θ => angChar n θ * fderiv ℝ v (circPt x₀ r θ) (eI θ))
    (F' := fun r θ => angChar n θ * fderiv ℝ (fderiv ℝ v) (circPt x₀ r θ) (eI θ) (eI θ))
    (fun r θ => ?_)
    (((continuous_angChar n).comp continuous_snd).mul
      (((hv.continuous_fderiv (by norm_num)).comp (continuous_circPt x₀)).clm_apply
        (continuous_eI.comp continuous_snd)))
    (((continuous_angChar n).comp continuous_snd).mul
      ((((hcd1.continuous_fderiv one_ne_zero).comp (continuous_circPt x₀)).clm_apply
        (continuous_eI.comp continuous_snd)).clm_apply (continuous_eI.comp continuous_snd)))
    _ _ r
  have h2 := ((hd _).hasFDerivAt.comp_hasDerivAt r (hcr r θ)).clm_apply (hasDerivAt_const r (eI θ))
  simp only [ContinuousLinearMap.map_zero, add_zero] at h2
  exact h2.const_mul _

private theorem angMode_bessel {E r : ℝ} (hr : r ≠ 0)
    (hhelm : ∀ θ, lap v (circPt x₀ r θ) + E * v (circPt x₀ r θ) = 0) :
    angMode2 v x₀ n r = -(angMode1 v x₀ n r / r) -
      ((E - (n : ℝ) ^ 2 / r ^ 2 : ℝ) : ℂ) * angMode v x₀ n r := by
  have hcd1 : ContDiff ℝ 1 (fderiv ℝ v) := hv.fderiv_right (m := 1) (by norm_num)
  have hd : Differentiable ℝ v := hv.differentiable (by norm_num)
  have hd1 : Differentiable ℝ (fderiv ℝ v) := hcd1.differentiable one_ne_zero
  have hc1 : Continuous (fderiv ℝ v) := hv.continuous_fderiv (by norm_num)
  have hc2 : Continuous (fderiv ℝ (fderiv ℝ v)) := hcd1.continuous_fderiv one_ne_zero
  have hcp : Continuous fun θ => circPt x₀ r θ :=
    (continuous_circPt x₀).comp (continuous_const.prodMk continuous_id)
  have hcθ : ∀ θ, HasDerivAt (fun θ => circPt x₀ r θ) (r * (Complex.I * eI θ)) θ := fun θ => by
    simpa [circPt] using ((hasDerivAt_eI θ).const_mul (r : ℂ)).const_add x₀
  set D := fderiv ℝ (fderiv ℝ v)
  set g : ℝ → ℂ := fun θ => v (circPt x₀ r θ)
  set g1 : ℝ → ℂ := fun θ => fderiv ℝ v (circPt x₀ r θ) (r * (Complex.I * eI θ))
  set g2 : ℝ → ℂ := fun θ => D (circPt x₀ r θ) (r * (Complex.I * eI θ)) (r * (Complex.I * eI θ)) +
    fderiv ℝ v (circPt x₀ r θ) (r * (Complex.I * (Complex.I * eI θ)))
  have hg : ∀ θ, HasDerivAt g (g1 θ) θ := fun θ => (hd _).hasFDerivAt.comp_hasDerivAt θ (hcθ θ)
  have hg1 : ∀ θ, HasDerivAt g1 (g2 θ) θ := fun θ => by
    convert ((hd1 _).hasFDerivAt.comp_hasDerivAt θ (hcθ θ)).clm_apply
      (((hasDerivAt_eI θ).const_mul Complex.I).const_mul (r : ℂ)) using 1 <;> rfl
  have hg1c : Continuous g1 :=
    (hc1.comp hcp).clm_apply (continuous_const.mul (continuous_const.mul continuous_eI))
  have hg2c : Continuous g2 :=
    (((hc2.comp hcp).clm_apply (continuous_const.mul (continuous_const.mul continuous_eI))).clm_apply
      (continuous_const.mul (continuous_const.mul continuous_eI))).add
      ((hc1.comp hcp).clm_apply (continuous_const.mul (continuous_const.mul
        (continuous_const.mul continuous_eI))))
  have hibp_ang : ∀ {h h' : ℝ → ℂ}, (∀ θ, HasDerivAt h (h' θ) θ) → Continuous h' →
      h (2 * π) = h 0 → ∫ θ in (0 : ℝ)..2 * π, angChar n θ * h' θ =
        (n * Complex.I) * ∫ θ in (0 : ℝ)..2 * π, angChar n θ * h θ := by
    intro h h' hh hh'c hper
    have hdac : ∀ θ, HasDerivAt (angChar n) (-(n * Complex.I) * angChar n θ) θ := fun θ => by
      convert (((hasDerivAt_id θ).ofReal_comp.const_mul (n : ℂ)).mul_const Complex.I).neg.cexp
        using 1
      · funext _; simp [angChar]
      · simp only [angChar, Pi.neg_apply, id, Complex.ofReal_one]; ring
    have h2pi : angChar n (2 * π) = angChar n 0 := by
      simp only [angChar, Complex.ofReal_zero, mul_zero, zero_mul, neg_zero, Complex.exp_zero]
      exact Complex.exp_eq_one_iff.mpr ⟨-n, by push_cast; ring⟩
    rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul (fun θ _ => hdac θ) (fun θ _ => hh θ)
        ((continuous_const.mul (continuous_angChar n)).intervalIntegrable _ _)
        (hh'c.intervalIntegrable _ _),
      h2pi, hper, sub_self, zero_sub, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_neg]
    congr 1; funext _; ring
  have heI2pi : eI (2 * π) = eI 0 := by simpa using eI_periodic 0
  have hI2 : ∫ θ in (0 : ℝ)..2 * π, angChar n θ * g2 θ = -((n : ℂ) ^ 2) * angMode v x₀ n r := by
    rw [hibp_ang hg1 hg2c (by simp [g1, circPt, heI2pi]),
      hibp_ang hg hg1c (by simp [g, circPt, heI2pi])]
    simp only [angMode]; ring_nf; rw [Complex.I_sq]; ring
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  have hpt : ∀ θ, angChar n θ * lap v (circPt x₀ r θ) =
      angChar n θ * D (circPt x₀ r θ) (eI θ) (eI θ) +
        (angChar n θ * fderiv ℝ v (circPt x₀ r θ) (eI θ)) / r +
        (angChar n θ * g2 θ) / (r : ℂ) ^ 2 := fun θ => by
    have hlap : lap v (circPt x₀ r θ) =
        D (circPt x₀ r θ) (eI θ) (eI θ) +
          D (circPt x₀ r θ) (Complex.I * eI θ) (Complex.I * eI θ) := by
      have key : ∀ w : ℂ, dirD (dirD v w) w (circPt x₀ r θ) = D (circPt x₀ r θ) w w := fun w => by
        unfold dirD; rw [fderiv_clm_apply (hd1 _) (differentiableAt_const w)]; simp [D]
      rw [lap, key, key]
      set B := D (circPt x₀ r θ)
      have he : eI θ = (Real.cos θ) • (1 : ℂ) + (Real.sin θ) • Complex.I := by
        simp [eI, Complex.exp_mul_I, Complex.real_smul, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
      have hie : Complex.I * eI θ = (-Real.sin θ) • (1 : ℂ) + (Real.cos θ) • Complex.I := by
        rw [he]; simp only [Complex.real_smul, mul_one, Complex.ofReal_neg]
        ring_nf; rw [Complex.I_sq]; ring
      rw [hie, he]
      simp only [map_add, map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
      simp only [Complex.real_smul, Complex.ofReal_neg]
      have hcs : ((Real.cos θ : ℂ)) ^ 2 + (Real.sin θ : ℂ) ^ 2 = 1 := by
        exact_mod_cast Real.cos_sq_add_sin_sq θ
      linear_combination -(B 1 1 + B Complex.I Complex.I) * hcs
    rw [hlap]
    have hsm : ∀ (L : ℂ →L[ℝ] ℂ) (w : ℂ), L ((r : ℂ) * w) = (r : ℂ) * L w := fun L w => by
      rw [← Complex.real_smul, map_smul, Complex.real_smul]
    have hsm2 : ∀ (B : ℂ →L[ℝ] ℂ →L[ℝ] ℂ) (w z : ℂ), B ((r : ℂ) * w) z = (r : ℂ) * B w z :=
      fun B w z => by
        rw [← Complex.real_smul, map_smul, ContinuousLinearMap.smul_apply, Complex.real_smul]
    simp only [g2]
    rw [hsm2, hsm, hsm, show Complex.I * (Complex.I * eI θ) = -eI θ by
      rw [← mul_assoc, Complex.I_mul_I]; ring, map_neg]
    field_simp; ring
  have hi1 : IntervalIntegrable (fun θ => angChar n θ * D (circPt x₀ r θ) (eI θ) (eI θ))
      volume 0 (2 * π) :=
    ((continuous_angChar n).mul (((hc2.comp hcp).clm_apply continuous_eI).clm_apply
      continuous_eI)).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun θ => (angChar n θ * fderiv ℝ v (circPt x₀ r θ) (eI θ)) / r)
      volume 0 (2 * π) :=
    (((continuous_angChar n).mul ((hc1.comp hcp).clm_apply continuous_eI)).div_const
      _).intervalIntegrable _ _
  have hi3 : IntervalIntegrable (fun θ => (angChar n θ * g2 θ) / (r : ℂ) ^ 2) volume 0 (2 * π) :=
    (((continuous_angChar n).mul hg2c).div_const _).intervalIntegrable _ _
  have hlapI : ∫ θ in (0 : ℝ)..2 * π, angChar n θ * lap v (circPt x₀ r θ) =
      -(E : ℂ) * angMode v x₀ n r := by
    simp only [angMode]; rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun θ _ => by linear_combination angChar n θ * hhelm θ
  rw [intervalIntegral.integral_congr (fun θ _ => hpt θ),
    intervalIntegral.integral_add (hi1.add hi2) hi3, intervalIntegral.integral_add hi1 hi2,
    intervalIntegral.integral_div, intervalIntegral.integral_div, hI2] at hlapI
  change angMode2 v x₀ n r + angMode1 v x₀ n r / r +
    -((n : ℂ) ^ 2) * angMode v x₀ n r / (r : ℂ) ^ 2 = -(E : ℂ) * angMode v x₀ n r at hlapI
  have hlapI' : angMode2 v x₀ n r + angMode1 v x₀ n r / r -
      ((n : ℂ) ^ 2 / (r : ℂ) ^ 2) * angMode v x₀ n r = -(E : ℂ) * angMode v x₀ n r := by
    rw [← hlapI]; field_simp; ring
  push_cast
  linear_combination hlapI'

end Smooth

/-! ### Disc unique continuation and exterior vanishing -/

private lemma eq_zero_of_angMode_zero {v : ℂ → ℂ} (hv : Continuous v) {x₀ z : ℂ}
    (hm : ∀ n : ℤ, angMode v x₀ n ‖z - x₀‖ = 0) : v z = 0 := by
  haveI : Fact (0 < 2 * π) := ⟨by positivity⟩
  set r := ‖z - x₀‖
  set f : ℝ → ℂ := fun θ => v (circPt x₀ r θ)
  have hf : Continuous f := hv.comp ((continuous_circPt x₀).comp (Continuous.prodMk_right r))
  have hper : Function.Periodic f (2 * π) := fun θ => by simp only [f, circPt, eI_periodic θ]
  let F : C(AddCircle (2 * π), ℂ) := ⟨hper.lift, continuous_quot_lift _ hf⟩
  have hF : ∀ x : ℝ, F (x : AddCircle (2 * π)) = f x := fun _ => rfl
  have hc : ∀ n : ℤ, fourierCoeff F n = 0 := fun n => by
    rw [fourierCoeff_eq_intervalIntegral _ n 0, zero_add,
      show ∫ x in (0 : ℝ)..2 * π, (fourier (-n)) (x : AddCircle (2 * π)) • F x =
        angMode v x₀ n r by
        unfold angMode; congr 1; funext x
        rw [hF, fourier_coe_apply, smul_eq_mul, angChar]
        congr 2; have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
        field_simp; push_cast; ring,
      hm n, smul_zero]
  have hs := has_pointwise_sum_fourier_series_of_summable (f := F)
    (by rw [show fourierCoeff (⇑F) = 0 from funext hc]; exact summable_zero)
    (Complex.arg (z - x₀) : AddCircle (2 * π))
  simp only [hc, zero_smul] at hs
  have h0 : f (Complex.arg (z - x₀)) = 0 := by rw [← hF]; exact (hasSum_zero.unique hs).symm
  simpa only [f, circPt, eI, r, Complex.norm_mul_exp_arg_mul_I, add_sub_cancel] using h0

theorem eq_zero_on_ball_of_helmholtz {v : ℂ → ℂ} (hv : ContDiff ℝ 2 v) {E : ℝ} {y : ℂ}
    {ρ δ : ℝ} (hδ : 0 < δ) (hhelm : ∀ z ∈ ball y ρ, lap v z + E * v z = 0)
    (h0 : ∀ z ∈ ball y δ, v z = 0) : ∀ z ∈ ball y ρ, v z = 0 := by
  intro z hz
  by_cases hzδ : z ∈ ball y δ
  · exact h0 z hzδ
  have hδρ : δ < ρ := lt_of_le_of_lt (not_lt.mp hzδ) (mem_ball.mp hz)
  set a := δ / 4
  have ha : 0 < a := by positivity
  have hmode : ∀ n : ℤ, ∀ r ∈ Ioo a ρ, angMode v y n r = 0 := fun n => by
    have hloc : ∀ r ∈ Ioo a δ, angMode v y n r = 0 := fun r hr => by
      simp only [angMode]
      refine intervalIntegral.integral_zero_ae (Eventually.of_forall fun θ _ => ?_)
      rw [h0 _ (by rw [mem_ball, dist_circPt y (by linarith [hr.1]) θ]; exact hr.2), mul_zero]
    refine ode2_unique (p := fun r => ((1 / r : ℝ) : ℂ))
      (q := fun r => ((E - (n : ℝ) ^ 2 / r ^ 2 : ℝ) : ℂ)) (P := 1 / a)
      (Q := |E| + (n : ℝ) ^ 2 / a ^ 2) ?_ ?_ (fun r _ => hasDerivAt_angMode hv y n r) ?_
      (r₀ := δ / 2) ⟨by simp only [a]; linarith, by linarith⟩
      (hloc _ ⟨by simp only [a]; linarith, by linarith⟩) ?_
    · intro r hr
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr (ha.trans hr.1))]
      exact one_div_le_one_div_of_le ha hr.1.le
    · intro r hr
      have hr0 : 0 < r := ha.trans hr.1
      rw [Complex.norm_real, Real.norm_eq_abs]
      refine (abs_sub _ _).trans ?_
      gcongr; rw [abs_of_nonneg (by positivity)]; gcongr; exact hr.1.le
    · intro r hr
      have hr0 : 0 < r := ha.trans hr.1
      have hb := angMode_bessel hv y n (E := E) hr0.ne' fun θ =>
        hhelm _ (by rw [mem_ball, dist_circPt y hr0.le θ]; exact hr.2)
      convert hasDerivAt_angMode1 hv y n r using 1
      rw [hb]; push_cast; ring
    · have hev : angMode v y n =ᶠ[𝓝 (δ / 2)] fun _ => 0 := by
        filter_upwards [Ioo_mem_nhds (show a < δ / 2 by simp only [a]; linarith)
          (by linarith : δ / 2 < δ)] with r hr using hloc r hr
      exact (hasDerivAt_angMode hv y n (δ / 2)).unique
        ((hasDerivAt_const (δ / 2) (0 : ℂ)).congr_of_eventuallyEq hev)
  have hr : ‖z - y‖ ∈ Ioo a ρ := by
    refine ⟨?_, by simpa [dist_eq_norm] using mem_ball.mp hz⟩
    have : δ ≤ ‖z - y‖ := by simpa [dist_eq_norm] using not_lt.mp (mt mem_ball.mpr hzδ)
    simp only [a]; linarith
  exact eq_zero_of_angMode_zero hv.continuous fun n => hmode n _ hr

theorem eq_zero_outside_of_helmholtz {v : ℂ → ℂ} (hv : ContDiff ℝ 2 v) (hL2 : MemLp v 2 volume)
    {E : ℝ} (hE : 0 < E) {R : ℝ} (hR : 0 < R)
    (hhelm : ∀ z : ℂ, R < ‖z‖ → lap v z + E * v z = 0) : ∀ z : ℂ, R < ‖z‖ → v z = 0 := by
  have hcm : IntegrableOn (fun r => r * ∫ θ in (0 : ℝ)..2 * π, ‖v (circPt 0 r θ)‖ ^ 2) (Ioi 0) := by
    have hcp : Continuous fun p : ℝ × ℝ => v (circPt 0 p.1 p.2) := hv.continuous.comp (continuous_circPt 0)
    set g : ℝ × ℝ → ℝ≥0∞ := fun p => ENNReal.ofReal p.1 * ‖v (circPt 0 p.1 p.2)‖ₑ ^ 2
    have hgm : Measurable g :=
      (ENNReal.measurable_ofReal.comp measurable_fst).mul (hcp.measurable.enorm.pow_const 2)
    have hpolar := Complex.lintegral_comp_polarCoord_symm (fun z => ‖v z‖ₑ ^ 2)
    have hp_eq : ∀ p : ℝ × ℝ, Complex.polarCoord.symm p = circPt 0 p.1 p.2 := fun p => by
      rw [Complex.polarCoord_symm_apply, circPt, eI, Complex.exp_mul_I]; push_cast; ring
    simp only [hp_eq, smul_eq_mul] at hpolar
    rw [polarCoord_target, Measure.volume_eq_prod, ← Measure.prod_restrict,
      lintegral_prod _ hgm.aemeasurable] at hpolar
    have hfin : ∫⁻ z, ‖v z‖ₑ ^ 2 < ∞ := by
      simpa [HasFiniteIntegral, enorm_pow] using
        (hL2.integrable_norm_pow two_ne_zero).hasFiniteIntegral
    set K : ℝ → ℝ≥0∞ := fun r => ∫⁻ θ in Ioo (-π) π, g (r, θ)
    have hKm : Measurable K := Measurable.lintegral_prod_right' (ν := volume.restrict (Ioo (-π) π)) hgm
    have hKi : IntegrableOn (fun r => (K r).toReal) (Ioi 0) :=
      integrable_toReal_of_lintegral_ne_top hKm.aemeasurable
        (by change ∫⁻ r in Ioi 0, K r ≠ ⊤; rw [hpolar]; exact hfin.ne)
    refine hKi.congr_fun (fun r hr => ?_) measurableSet_Ioi
    have hr0 : 0 ≤ r := hr.le
    have hc : Continuous fun θ => r * ‖v (circPt 0 r θ)‖ ^ 2 :=
      continuous_const.mul ((hv.continuous.comp ((continuous_circPt 0).comp
        (Continuous.prodMk_right r))).norm.pow 2)
    have e1 : K r = ENNReal.ofReal (∫ θ in Ioo (-π) π, r * ‖v (circPt 0 r θ)‖ ^ 2) := by
      rw [ofReal_integral_eq_lintegral_ofReal]
      · refine lintegral_congr fun θ => ?_
        simp only [g]
        rw [ENNReal.ofReal_mul hr0, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
      · exact (hc.integrableOn_Icc (a := -π) (b := π)).mono_set Ioo_subset_Icc_self
      · exact Eventually.of_forall fun _ => by positivity
    have hper : Function.Periodic (fun θ => r * ‖v (circPt 0 r θ)‖ ^ 2) (2 * π) := fun θ => by
      simp only [circPt, eI_periodic θ]
    have e2 : ∫ θ in Ioo (-π) π, r * ‖v (circPt 0 r θ)‖ ^ 2 =
        ∫ θ in (0 : ℝ)..2 * π, r * ‖v (circPt 0 r θ)‖ ^ 2 := by
      rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
      have := hper.intervalIntegral_add_eq (-π) 0
      rwa [show -π + 2 * π = π by ring, zero_add] at this
    show (K r).toReal = _
    rw [e1, e2, ENNReal.toReal_ofReal (intervalIntegral.integral_nonneg (by positivity)
      fun _ _ => by positivity), intervalIntegral.integral_const_mul]
  have hmode : ∀ n : ℤ, ∀ r ∈ Ioi R, angMode v 0 n r = 0 := fun n => by
    have hmc : Continuous (angMode v 0 n) :=
      continuous_iff_continuousAt.2 fun r => (hasDerivAt_angMode hv 0 n r).continuousAt
    refine bessel_rellich (c := (n : ℝ) ^ 2) hE hR (fun r _ => hasDerivAt_angMode hv 0 n r)
      (fun r hr => ?_) ?_
    · have hr0 : 0 < r := hR.trans hr
      rw [← angMode_bessel hv 0 n (E := E) hr0.ne' fun θ =>
        hhelm _ (by rw [← dist_zero_right, dist_circPt 0 hr0.le θ]; exact hr)]
      exact hasDerivAt_angMode1 hv 0 n r
    · refine Integrable.mono' ((hcm.mono_set (Ioi_subset_Ioi hR.le)).const_mul (2 * π))
        (continuous_id.mul (hmc.norm.pow 2)).aestronglyMeasurable
        ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun r hr => ?_))
      have hr0 : 0 ≤ r := (hR.trans hr).le
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hc : Continuous fun θ => ‖v (circPt 0 r θ)‖ :=
        (hv.continuous.comp ((continuous_circPt 0).comp (Continuous.prodMk_right r))).norm
      have h1 : ‖angMode v 0 n r‖ ≤ ∫ θ in (0 : ℝ)..2 * π, ‖v (circPt 0 r θ)‖ :=
        (intervalIntegral.norm_integral_le_integral_norm (by positivity)).trans_eq <| by
          congr 1; funext θ; simp [angChar, Complex.norm_exp]
      set S := ∫ θ in (0 : ℝ)..2 * π, ‖v (circPt 0 r θ)‖ with hS
      set I2 := ∫ θ in (0 : ℝ)..2 * π, ‖v (circPt 0 r θ)‖ ^ 2 with hI2
      set m := S / (2 * π) with hm
      have hnn : 0 ≤ ∫ θ in (0 : ℝ)..2 * π, (‖v (circPt 0 r θ)‖ - m) ^ 2 :=
        intervalIntegral.integral_nonneg (by positivity) fun _ _ => sq_nonneg _
      have hi1 : IntervalIntegrable (fun θ => ‖v (circPt 0 r θ)‖ ^ 2) volume 0 (2 * π) :=
        (hc.pow 2).intervalIntegrable 0 (2 * π)
      have hi2 : IntervalIntegrable (fun θ => 2 * m * ‖v (circPt 0 r θ)‖) volume 0 (2 * π) :=
        (continuous_const.mul hc).intervalIntegrable 0 (2 * π)
      have hexp : ∫ θ in (0 : ℝ)..2 * π, (‖v (circPt 0 r θ)‖ - m) ^ 2 =
          I2 - 2 * m * S + m ^ 2 * (2 * π) := by
        rw [show (fun θ => (‖v (circPt 0 r θ)‖ - m) ^ 2) =
            fun θ => (‖v (circPt 0 r θ)‖ ^ 2 - 2 * m * ‖v (circPt 0 r θ)‖) + m ^ 2 from
              funext fun _ => by ring,
          intervalIntegral.integral_add (hi1.sub hi2) intervalIntegrable_const,
          intervalIntegral.integral_sub hi1 hi2, intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const, smul_eq_mul, ← hI2, ← hS]
        ring
      rw [hexp, hm] at hnn
      field_simp at hnn
      have h2 : S ^ 2 ≤ 2 * π * I2 := by nlinarith
      have hsq := (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2
      nlinarith [mul_le_mul_of_nonneg_left hsq hr0]
  intro z hz
  exact eq_zero_of_angMode_zero hv.continuous fun n => hmode n _ (by simpa using hz)

/-! ### Mollification and vanishing on unbounded connected open sets -/

private lemma integrable_mollify_flip {g : ℂ → ℝ} (hg : Continuous g) (hgs : HasCompactSupport g)
    {U : ℂ → ℂ} (hU : LocallyIntegrable U volume) (x : ℂ) :
    Integrable (fun t => g (x - t) • U t) volume := by
  simpa using (HasCompactSupport.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ)
    hgs hg hU x).integrable.comp_sub_left x

private def kerD (g : ℂ → ℝ) (v : ℂ) : ℂ → ℝ := fun z => fderiv ℝ g z v

private lemma contDiff_kerD {g : ℂ → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (v : ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (kerD g v) :=
  (hg.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const

private lemma hasCompactSupport_kerD {g : ℂ → ℝ} (hgs : HasCompactSupport g) (v : ℂ) :
    HasCompactSupport (kerD g v) := hgs.fderiv_apply ℝ v

private lemma dirD_mollify {g : ℂ → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgs : HasCompactSupport g)
    {U : ℂ → ℂ} (hU : LocallyIntegrable U volume) (v : ℂ) :
    dirD (mollify g U) v = mollify (kerD g v) U := by
  funext x
  set L : ℝ →L[ℝ] ℂ →L[ℝ] ℂ := ContinuousLinearMap.lsmul ℝ ℝ
  have hd := HasCompactSupport.hasFDerivAt_convolution_left L hgs (hg.of_le (by simp)) hU x
  have hint := HasCompactSupport.convolutionExists_left (ContinuousLinearMap.precompL ℂ L)
    (hgs.fderiv ℝ) (hg.continuous_fderiv (by simp)) hU x
  simp only [dirD, mollify]
  rw [hd.fderiv, convolution_def, ContinuousLinearMap.integral_apply hint, convolution_def]
  simp [ContinuousLinearMap.precompL_apply, L, kerD]

private def lapK (g : ℂ → ℝ) : ℂ → ℝ := kerD (kerD g 1) 1 + kerD (kerD g Complex.I) Complex.I

private def reflK (g : ℂ → ℝ) (x : ℂ) : ℂ → ℂ := fun t => ((g (x - t) : ℝ) : ℂ)

private lemma dirD_reflK {g : ℂ → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (x v : ℂ) :
    dirD (reflK g x) v = -reflK (kerD g v) x := by
  funext t
  have hρ : HasFDerivAt g (fderiv ℝ g (x - t)) (x - t) :=
    ((hg.differentiable (by simp)) _).hasFDerivAt
  have h := (Complex.ofRealCLM.hasFDerivAt).comp t (hρ.comp t ((hasFDerivAt_id t).const_sub x))
  have hr : reflK g x = Complex.ofRealCLM ∘ g ∘ HSub.hSub x := rfl
  simp only [dirD]
  rw [hr, h.fderiv]
  simp [reflK, kerD]

private lemma mollify_helmholtz {E : ℝ} {D : Set ℂ} {u : ℂ → ℂ} (hu : LocallyIntegrable u volume)
    (hhelm : ∀ φ : ℂ → ℂ, TestFunction D φ → ∫ z, u z * (lap φ z + E * φ z) = 0)
    (φ : ContDiffBump (0 : ℂ)) {x : ℂ} (hx : closedBall x φ.rOut ⊆ D) :
    lap (mollify (φ.normed volume) u) x + E * mollify (φ.normed volume) u x = 0 := by
  set g := φ.normed volume
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := φ.contDiff_normed
  have hgs : HasCompactSupport g := φ.hasCompactSupport_normed
  have h := hhelm (reflBump φ x) (testFunction_reflBump φ x hx)
  change ∫ z, u z * (lap (reflK g x) z + E * reflK g x z) = 0 at h
  have hlapm : lap (mollify g u) x = mollify (lapK g) u x := by
    simp only [lap, dirD_mollify hg hgs hu,
      dirD_mollify (contDiff_kerD hg _) (hasCompactSupport_kerD hgs _) hu, lapK,
      mollify_eq_flip, Pi.add_apply, add_smul]
    exact (integral_add
      (integrable_mollify_flip (contDiff_kerD (contDiff_kerD hg 1) 1).continuous
        (hasCompactSupport_kerD (hasCompactSupport_kerD hgs 1) 1) hu x)
      (integrable_mollify_flip (contDiff_kerD (contDiff_kerD hg Complex.I) Complex.I).continuous
        (hasCompactSupport_kerD (hasCompactSupport_kerD hgs Complex.I) Complex.I) hu x)).symm
  have hlapr : ∀ t, lap (reflK g x) t = reflK (lapK g) x t := fun t => by
    have hdd : ∀ v, dirD (dirD (reflK g x) v) v = reflK (kerD (kerD g v) v) x := fun v => by
      rw [dirD_reflK hg]; funext s
      rw [show dirD (-reflK (kerD g v) x) v s = -dirD (reflK (kerD g v) x) v s by
        simp only [dirD]; rw [fderiv_neg]; rfl, dirD_reflK (contDiff_kerD hg v)]
      simp
    simp only [lap, hdd, reflK, lapK, Pi.add_apply]; push_cast; ring
  have hlgc : Continuous (lapK g) :=
    ((contDiff_kerD (contDiff_kerD hg _) _).add (contDiff_kerD (contDiff_kerD hg _) _)).continuous
  have hlgs : HasCompactSupport (lapK g) :=
    (hasCompactSupport_kerD (hasCompactSupport_kerD hgs _) _).add
      (hasCompactSupport_kerD (hasCompactSupport_kerD hgs _) _)
  rw [hlapm, mollify_eq_flip, mollify_eq_flip, ← integral_const_mul,
    ← integral_add (integrable_mollify_flip hlgc hlgs hu x)
      ((integrable_mollify_flip hg.continuous hgs hu x).const_mul _), ← h]
  congr 1; funext t; rw [hlapr]; simp only [reflK, Complex.real_smul]; ring

private lemma ae_eq_zero_of_mollify_eq_zero {u : ℂ → ℂ} (hu : MemLp u 2 volume) {W : Set ℂ}
    (hW : MeasurableSet W)
    (h : ∀ᶠ k in atTop, ∀ z ∈ W, mollify ((stdBump k).normed volume) u z = 0) :
    ∀ᵐ z ∂(volume.restrict W), u z = 0 := by
  have hle : ∀ᶠ k in atTop, eLpNorm u 2 (volume.restrict W) ≤
      eLpNorm (mollify ((stdBump k).normed volume) u - u) 2 volume := by
    filter_upwards [h] with k hk
    refine (le_of_eq ?_).trans (eLpNorm_restrict_le _ _ _ W)
    rw [← eLpNorm_neg]
    exact eLpNorm_congr_ae ((ae_restrict_iff' hW).2 (Eventually.of_forall fun z hz => by
      simp [hk z hz]))
  exact (eLpNorm_eq_zero_iff two_ne_zero).mp
    (le_antisymm (ge_of_tendsto (tendsto_mollify_L2 tendsto_stdBump_rOut hu) hle) zero_le')

theorem ae_eq_zero_of_helmholtz {E : ℝ} (hE : 0 < E) {D : Set ℂ} (hDo : IsOpen D)
    (hDc : IsConnected D) {R : ℝ} (hR : ∀ z : ℂ, R < ‖z‖ → z ∈ D) {u : ℂ → ℂ}
    (hu : MemLp u 2 volume)
    (hhelm : ∀ φ : ℂ → ℂ, TestFunction D φ → ∫ z, u z * (lap φ z + E * φ z) = 0) :
    ∀ᵐ z ∂(volume.restrict D), u z = 0 := by
  have hul : LocallyIntegrable u volume := hu.locallyIntegrable one_le_two
  set uk : ℕ → ℂ → ℂ := fun k => mollify ((stdBump k).normed volume) u
  have hsm : ∀ k, ContDiff ℝ 2 (uk k) := fun _ =>
    HasCompactSupport.contDiff_convolution_left _ (stdBump _).hasCompactSupport_normed
      (stdBump _).contDiff_normed hul
  have hrk : ∀ k, (stdBump k).rOut ≤ 1 := fun k => by
    rw [stdBump_rOut, div_le_one (by positivity)]; linarith [Nat.cast_nonneg (α := ℝ) k]
  set R' : ℝ := max R 0 + 1
  have hout : ∀ k, ∀ z : ℂ, R' < ‖z‖ → uk k z = 0 := fun k =>
    eq_zero_outside_of_helmholtz (hsm k) (memLp_mollify _ hu) hE (by positivity) fun x hx =>
      mollify_helmholtz hul hhelm _ fun w hw => hR w <| by
        rw [mem_closedBall, dist_eq_norm, norm_sub_rev] at hw
        linarith [norm_sub_norm_le x w, hrk k, le_max_left R 0]
  set S : Set ℂ := {x | ∃ r > 0, ∀ᵐ z ∂(volume.restrict (ball x r)), u z = 0}
  have hSo : IsOpen S := Metric.isOpen_iff.mpr fun x ⟨r, hr, hx⟩ =>
    ⟨r, hr, fun y hy => ⟨r - dist y x, by rw [mem_ball] at hy; linarith,
      ae_restrict_of_ae_restrict_of_subset (fun w hw => by
        rw [mem_ball] at hw ⊢; linarith [dist_triangle w y x]) hx⟩⟩
  have hne : (D ∩ S).Nonempty := by
    refine ⟨((R' + 1 : ℝ) : ℂ), hR _ ?_, 1, one_pos, ?_⟩
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      linarith [le_max_left R 0]
    · refine ae_restrict_of_ae_restrict_of_subset (fun w hw => ?_)
        (ae_eq_zero_of_mollify_eq_zero hu (W := {z : ℂ | R' < ‖z‖})
          (measurableSet_lt measurable_const measurable_norm) (Eventually.of_forall hout))
      rw [mem_ball, dist_eq_norm] at hw
      have h1 := norm_sub_norm_le (((R' + 1 : ℝ) : ℂ)) w
      rw [norm_sub_rev, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)] at h1
      show R' < ‖w‖; linarith
  have hcl : closure S ∩ D ⊆ S := by
    rintro x ⟨hxc, hxD⟩
    obtain ⟨ε, hε, hεD⟩ := Metric.isOpen_iff.mp hDo x hxD
    set r := ε / 4
    have hr : 0 < r := by positivity
    obtain ⟨y, ⟨δ, hδ, hy⟩, hxy⟩ := Metric.mem_closure_iff.mp hxc r hr
    set η := min r δ / 2
    have hk : ∀ᶠ k in atTop, ∀ z ∈ ball y (2 * r), uk k z = 0 := by
      filter_upwards [tendsto_stdBump_rOut.eventually (gt_mem_nhds (by positivity : 0 < η))] with k hk
      refine eq_zero_on_ball_of_helmholtz (hsm k) (E := E) (δ := δ - (stdBump k).rOut)
        (by have := min_le_right r δ; simp only [η] at hk; linarith) ?_ ?_
      · intro z hz
        refine mollify_helmholtz hul hhelm _ fun w hw => hεD ?_
        rw [mem_closedBall] at hw; rw [mem_ball] at hz ⊢
        have := min_le_left r δ
        have hrε : ε = 4 * r := by simp only [r]; ring
        simp only [η] at hk
        linarith [dist_triangle w z x, dist_triangle z y x, dist_comm x y]
      · intro z hz
        dsimp only [uk]; rw [mollify_eq_flip]; refine integral_eq_zero_of_ae ?_
        filter_upwards [(ae_restrict_iff' measurableSet_ball).mp hy] with t ht
        by_cases hzt : z - t ∈ Function.support ((stdBump k).normed volume)
        · rw [(stdBump k).support_normed_eq, mem_ball_zero_iff] at hzt
          have htu : u t = 0 := ht <| by
            rw [mem_ball, dist_eq_norm] at hz ⊢
            calc ‖t - y‖ = ‖(z - y) - (z - t)‖ := by congr 1; ring
              _ ≤ ‖z - y‖ + ‖z - t‖ := norm_sub_le _ _
              _ < δ := by linarith
          simp [htu]
        · simp [Function.notMem_support.mp hzt]
    exact ⟨r, hr, ae_restrict_of_ae_restrict_of_subset
      (fun w hw => by rw [mem_ball] at hw ⊢; linarith [dist_triangle w x y])
      (ae_eq_zero_of_mollify_eq_zero hu measurableSet_ball hk)⟩
  have hDS : D ⊆ S := hDc.isPreconnected.subset_of_closure_inter_subset hSo hne hcl
  have hnull : volume (D ∩ {z | u z ≠ 0}) = 0 := by
    refine measure_null_of_locally_null _ fun x hx => ?_
    obtain ⟨r, hr, hxr⟩ := hDS hx.1
    refine ⟨D ∩ {z | u z ≠ 0} ∩ ball x r, inter_mem_nhdsWithin _ (ball_mem_nhds x hr), ?_⟩
    rw [ae_restrict_iff' measurableSet_ball] at hxr
    refine measure_mono_null (fun _ hw => ?_) (ae_iff.mp hxr)
    exact fun h => hw.1.2 (h hw.2)
  rw [ae_restrict_iff' hDo.measurableSet, ae_iff]
  exact measure_mono_null (fun w hw => by
    by_contra hc; exact hw fun hwD => by_contra fun hu0 => hc ⟨hwD, hu0⟩) hnull

end PolyaNeumann

end
