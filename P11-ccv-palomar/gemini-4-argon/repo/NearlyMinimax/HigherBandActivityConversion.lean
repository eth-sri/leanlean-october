module
public import Mathlib
public import NearlyMinimax.Rates
public import NearlyMinimax.SaddleAsymptotics
public import Mathlib.Analysis.SpecialFunctions.Stirling
public import NearlyMinimax.HigherBandFamily
@[expose] public section
noncomputable section
open Filter MeasureTheory
open scoped Topology BigOperators
namespace NearlyMinimax
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
section
variable {a b d m θ C x τ Cτ s cf CG : ℝ} {τM : ℕ → ℝ}
def densityIntervalExponent (a b : ℝ) : ℝ :=
  Real.log ((Real.sqrt b + Real.sqrt a) / (Real.sqrt b - Real.sqrt a))
def shrunkDensityExponent (a b : ℝ) (M : ℕ) : ℝ :=
  densityIntervalExponent (a + (M : ℝ)⁻¹) (b - (M : ℝ)⁻¹)
theorem densityIntervalExponent_pos  (ha : 0 < a) (hab : a < b) :
    0 < densityIntervalExponent a b := by
  have := Real.sqrt_pos.2 ha
  apply Real.log_pos
  exact (one_lt_div (sub_pos.2 (Real.sqrt_lt_sqrt ha.le hab))).2 (by linarith)
theorem exists_shrunkDensityExponent_control  (ha : 0 < a) (hab : a < b) :
    ∃ Cτ, 0 ≤ Cτ ∧ ∀ᶠ M : ℕ in atTop,
      densityIntervalExponent a b ≤ shrunkDensityExponent a b M ∧
      (shrunkDensityExponent a b M - densityIntervalExponent a b) * M ≤ Cτ := by
  have h_densityIntervalExponent_differentiable_shrink : DifferentiableAt ℝ (fun t => densityIntervalExponent (a + t) (b - t)) 0 := by
    have hb  := ha.trans hab
    have  := (Real.sqrt_pos.2 ha).ne'
    have hden  :=
      (sub_pos.2 (Real.sqrt_lt_sqrt ha.le hab)).ne'
    have hratio : (Real.sqrt b + Real.sqrt a) / (Real.sqrt b - Real.sqrt a) ≠ 0 := by positivity
    apply DifferentiableAt.log
    · apply DifferentiableAt.div
      · apply DifferentiableAt.add
        · exact ((differentiableAt_const b).sub differentiableAt_id).sqrt (by simpa using hb.ne')
        · exact ((differentiableAt_const a).add differentiableAt_id).sqrt (by simpa using ha.ne')
      · apply DifferentiableAt.sub
        · exact ((differentiableAt_const b).sub differentiableAt_id).sqrt (by simpa using hb.ne')
        · exact ((differentiableAt_const a).add differentiableAt_id).sqrt (by simpa using ha.ne')
      · simpa using hden
    · simpa using hratio
  obtain ⟨K, hK⟩ := (h_densityIntervalExponent_differentiable_shrink).isBigO_sub.bound
  have ht : Tendsto (fun M : ℕ => (M : ℝ)⁻¹) atTop (𝓝 0) := by
    exact tendsto_natCast_atTop_atTop.inv_tendsto_atTop
  refine ⟨max K 0, le_max_right _ _, ?_⟩
  filter_upwards [ht.eventually hK, ht.eventually (gt_mem_nhds (by linarith : 0 < (b - a) / 2)), eventually_ge_atTop (1 : ℕ)] with M hbound hMsmall hM
  have hMpos : 0 < (M : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hM)
  have hMinv  := inv_nonneg.2 hMpos.le
  have h_densityIntervalExponent_shrink_mono {t : ℝ} {b : ℝ} (ht : 0 ≤ t) (hab : a + t < b - t) : densityIntervalExponent a b ≤ densityIntervalExponent (a + t) (b - t) := by
    have hab0 : a < b := by linarith
    have := Real.sqrt_nonneg a
    have hB := Real.sqrt_nonneg (b - t)
    have hAA : Real.sqrt a ≤ Real.sqrt (a + t) := Real.sqrt_le_sqrt (by linarith)
    have hBB : Real.sqrt (b - t) ≤ Real.sqrt b := Real.sqrt_le_sqrt (by linarith)
    have hden := sub_pos.2 (Real.sqrt_lt_sqrt ha.le hab0)
    have hden' := sub_pos.2 (Real.sqrt_lt_sqrt (by linarith) hab)
    apply Real.log_le_log (by positivity)
    apply (div_le_div_iff₀ hden hden').2
    have := mul_le_mul hAA hBB hB (Real.sqrt_nonneg (a + t))
    nlinarith
  have hmono := (h_densityIntervalExponent_shrink_mono hMinv (by linarith : a + (M : ℝ)⁻¹ < b - (M : ℝ)⁻¹))
  constructor
  · exact hmono
  · simp only [Real.norm_eq_abs, sub_zero, add_zero, abs_of_nonneg hMinv] at hbound
    rw [abs_of_nonneg (sub_nonneg.2 hmono)] at hbound
    have hb := mul_le_mul_of_nonneg_right hbound hMpos.le
    rw [mul_assoc, inv_mul_cancel₀ hMpos.ne', mul_one] at hb
    exact hb.trans (le_max_left _ _)
def lowerSaddleM (m x : ℝ) : ℕ := Nat.ceil (m * Real.sqrt (Real.log x))
def lowerSaddleD (d m x : ℝ) : ℕ := Nat.ceil ((d + 8) / 4 * lowerSaddleM m x)
def lowerSaddleOmegaZero (m θ C x : ℝ) : ℝ :=
  θ * lowerSaddleM m x - Real.log (lowerSaddleM m x) + C
def lowerSaddleGridBase (d m θ C x : ℝ) : ℝ :=
  Real.exp ((Real.log x + lowerSaddleOmegaZero m θ C x) / d)
def lowerSaddleGrid (d m θ C x : ℝ) : ℕ := Nat.ceil (lowerSaddleGridBase d m θ C x)
def lowerSaddleH (d m θ C x : ℝ) : ℝ := (lowerSaddleGrid d m θ C x )⁻¹
def lowerSaddleMu (d m θ C x : ℝ) : ℝ := x * (lowerSaddleH d m θ C x) ^ d
def lowerSaddleOmega (d m θ C x : ℝ) : ℝ :=
  d * Real.log (lowerSaddleGrid d m θ C x) - Real.log x
theorem lowerSaddleM_rounding  (hm : 0 ≤ m) :
    m * Real.sqrt (Real.log x) ≤ (lowerSaddleM m x ) ∧
      (lowerSaddleM m x ) < m * Real.sqrt (Real.log x) + 1 := ⟨Nat.le_ceil _, Nat.ceil_lt_add_one (mul_nonneg hm (Real.sqrt_nonneg _))⟩
theorem lowerSaddleM_tendsto_atTop  (hm : 0 < m) :
    Tendsto (fun x : ℝ => (lowerSaddleM m x : ℝ)) atTop atTop := by
  apply tendsto_atTop_mono (fun x => (lowerSaddleM_rounding hm.le).1)
  exact tendsto_sqrt_log_atTop.const_mul_atTop hm
theorem lowerSaddleM_div_sqrt_log_limit  (hm : 0 < m) :
    Tendsto (fun x => (lowerSaddleM m x ) / Real.sqrt (Real.log x))
      atTop (𝓝 m) := by
  have herr : Tendsto (fun x =>
      ((lowerSaddleM m x ) - m * Real.sqrt (Real.log x)) /
        Real.sqrt (Real.log x)) atTop (𝓝 0) := by
    have hu : Tendsto (fun x => 1 / Real.sqrt (Real.log x)) atTop (𝓝 0) := by
      simpa only [one_div] using! tendsto_sqrt_log_atTop.inv_tendsto_atTop
    apply squeeze_zero' _ _ hu
    · filter_upwards [eventually_gt_atTop 1] with x hx
      exact div_nonneg (sub_nonneg.2 (lowerSaddleM_rounding hm.le).1) (Real.sqrt_nonneg _)
    · filter_upwards [eventually_gt_atTop 1] with x hx
      exact div_le_div_of_nonneg_right (by linarith [(lowerSaddleM_rounding (x := x) hm.le).2])
        (Real.sqrt_nonneg _)
  have hh := (tendsto_const_nhds (x := m)).add herr
  simp only [add_zero] at hh
  refine hh.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with x hx
  have  := (Real.sqrt_pos.2 (Real.log_pos hx)).ne'
  field_simp
  ring
theorem lowerSaddleM_sq_div_log_limit  (hm : 0 < m) :
    Tendsto (fun x => (lowerSaddleM m x ) ^ 2 / Real.log x) atTop (𝓝 (m ^ 2)) := by
  refine ((lowerSaddleM_div_sqrt_log_limit hm).pow 2).congr' ?_
  filter_upwards [eventually_gt_atTop 1] with x hx
  simp only [div_pow, Real.sq_sqrt (Real.log_pos hx).le]
theorem lowerSaddleOmegaZero_div_M_limit  (hm : 0 < m) (θ C ) :
    Tendsto (fun x : ℝ => lowerSaddleOmegaZero m θ C x / lowerSaddleM m x)
      atTop (𝓝 θ) := by
  have ht := lowerSaddleM_tendsto_atTop hm
  have hh := ((tendsto_const_nhds (x := θ)).sub (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp ht)).add (by simpa [div_eq_mul_inv] using ht.inv_tendsto_atTop.const_mul C)
  simp only [sub_zero, add_zero] at hh
  refine hh.congr' ?_
  filter_upwards [ht.eventually (eventually_gt_atTop 0)] with x hx
  simp only [Function.comp_apply, id_eq]
  unfold lowerSaddleOmegaZero
  field_simp
theorem lowerSaddleGrid_positive (d m θ C x ) : 0 < (lowerSaddleGrid d m θ C x : ℝ) := (Real.exp_pos _).trans_le (Nat.le_ceil (lowerSaddleGridBase d m θ C x))
theorem lowerSaddleH_positive (d m θ C x ) : 0 < lowerSaddleH d m θ C x :=
  inv_pos.2 (lowerSaddleGrid_positive d m θ C x)
theorem lowerSaddleGridBase_tendsto_atTop 
    (hd : 0 < d) (hm : 0 < m) (hθ : 0 < θ) (C ) :
    Tendsto (lowerSaddleGridBase d m θ C) atTop atTop := by
  exact Real.tendsto_exp_atTop.comp
    ((Real.tendsto_log_atTop.atTop_add_atTop (by have ht := lowerSaddleM_tendsto_atTop hm; refine (ht.atTop_mul_pos hθ (lowerSaddleOmegaZero_div_M_limit hm θ C)).congr' ?_; filter_upwards [ht.eventually (eventually_gt_atTop ↑0)] with x hx; exact mul_div_cancel₀ _ hx.ne')).atTop_div_const hd)
theorem lowerSaddleGrid_tendsto_atTop 
    (hd : 0 < d) (hm : 0 < m) (hθ : 0 < θ) (C ) :
    Tendsto (fun x : ℝ => (lowerSaddleGrid d m θ C x : ℝ)) atTop atTop := by
  apply tendsto_atTop_mono (fun x => Nat.le_ceil _)
  exact lowerSaddleGridBase_tendsto_atTop hd hm hθ C
theorem lowerSaddleOmega_rounding_limit 
    (hd : 0 < d) (hm : 0 < m) (hθ : 0 < θ) (C ) :
    Tendsto (fun x => lowerSaddleOmega d m θ C x - lowerSaddleOmegaZero m θ C x)
      atTop (𝓝 0) := by
  have h_lowerSaddleG : Tendsto (fun x => (lowerSaddleGrid d m θ C x ) / lowerSaddleGridBase d m θ C x)
      atTop (𝓝 1) := by
    have hb := lowerSaddleGridBase_tendsto_atTop hd hm hθ C
    have herr : Tendsto (fun x =>
        ((lowerSaddleGrid d m θ C x ) - lowerSaddleGridBase d m θ C x) /
          lowerSaddleGridBase d m θ C x) atTop (𝓝 0) := by
      have hu : Tendsto (fun x => 1 / lowerSaddleGridBase d m θ C x) atTop (𝓝 0) := by
        simpa only [one_div] using! hb.inv_tendsto_atTop
      apply squeeze_zero' (Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_) hu
      · exact div_nonneg (sub_nonneg.2 (Nat.le_ceil _)) (Real.exp_pos _).le
      · apply div_le_div_of_nonneg_right _ (show 0 ≤ lowerSaddleGridBase d m θ C x from (Real.exp_pos _).le)
        have hh := Nat.ceil_lt_add_one (show 0 ≤ lowerSaddleGridBase d m θ C x from (Real.exp_pos _).le)
        change (lowerSaddleGrid d m θ C x ) < lowerSaddleGridBase d m θ C x + 1 at hh
        linarith
    have hh := (tendsto_const_nhds (x := 1)).add herr
    simp only [add_zero] at hh
    refine hh.congr (fun x => ?_)
    have : lowerSaddleGridBase d m θ C x ≠ 0 := (Real.exp_pos _).ne'
    field_simp
    ring
  have hh := ((Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp
    h_lowerSaddleG).const_mul d
  simp only [Real.log_one, mul_zero] at hh
  refine hh.congr (fun x => ?_)
  simp only [Function.comp_apply]
  rw [Real.log_div (lowerSaddleGrid_positive d m θ C x).ne'
    (show lowerSaddleGridBase d m θ C x ≠ 0 from (Real.exp_pos _).ne')]
  unfold lowerSaddleGridBase lowerSaddleOmega
  rw [Real.log_exp]
  field_simp
  ring
theorem lowerSaddleMu_eq_exp  (hx : 0 < x) :
    lowerSaddleMu d m θ C x = Real.exp (-lowerSaddleOmega d m θ C x) := by
  unfold lowerSaddleMu
  calc
    _ = Real.exp (Real.log x) * Real.exp (Real.log (lowerSaddleH d m θ C x) * d) := by
      rw [Real.exp_log hx, Real.rpow_def_of_pos (lowerSaddleH_positive d m θ C x)]
    _ = Real.exp (Real.log x + Real.log (lowerSaddleH d m θ C x) * d) := (Real.exp_add _ _).symm
    _ = _ := by
      congr 1
      unfold lowerSaddleH lowerSaddleOmega
      rw [Real.log_inv]
      ring
theorem lowerSaddleH_eq_exp  (hd : d ≠ 0) :
    lowerSaddleH d m θ C x =
      Real.exp (-(Real.log x + lowerSaddleOmega d m θ C x) / d) := by
  unfold lowerSaddleH lowerSaddleOmega
  have hh : -(Real.log x + (d * Real.log (lowerSaddleGrid d m θ C x) - Real.log x)) / d =
      -Real.log (lowerSaddleGrid d m θ C x) := by field_simp; ring
  rw [hh, Real.exp_neg, Real.exp_log (lowerSaddleGrid_positive d m θ C x)]
theorem lowerSaddleOmega_div_M_limit 
    (hd : 0 < d) (hm : 0 < m) (hθ : 0 < θ) (C ) :
    Tendsto (fun x : ℝ => lowerSaddleOmega d m θ C x / lowerSaddleM m x) atTop (𝓝 θ) := by
  have hr := (lowerSaddleOmega_rounding_limit hd hm hθ C).mul
    (lowerSaddleM_tendsto_atTop hm).inv_tendsto_atTop
  have hh := (lowerSaddleOmegaZero_div_M_limit hm θ C).add hr
  simp only [mul_zero, add_zero] at hh
  convert! hh using 1
  funext x
  change lowerSaddleOmega d m θ C x / (lowerSaddleM m x : ℝ) =
    lowerSaddleOmegaZero m θ C x / (lowerSaddleM m x : ℝ) +
    (lowerSaddleOmega d m θ C x - lowerSaddleOmegaZero m θ C x) / (lowerSaddleM m x : ℝ)
  simp only [div_eq_mul_inv]
  ring
theorem lowerSaddleOmega_tendsto_atTop 
    (hd : 0 < d) (hm : 0 < m) (hθ : 0 < θ) (C ) :
    Tendsto (lowerSaddleOmega d m θ C) atTop atTop := by
  have ht := lowerSaddleM_tendsto_atTop hm
  refine (ht.atTop_mul_pos hθ (lowerSaddleOmega_div_M_limit hd hm hθ C)).congr' ?_
  filter_upwards [ht.eventually (eventually_gt_atTop ↑0)] with x hx
  exact mul_div_cancel₀ _ hx.ne'
theorem lowerSaddleM_div_log_limit  (hm : 0 < m) :
    Tendsto (fun x => (lowerSaddleM m x ) / Real.log x) atTop (𝓝 0) := by
  have hh := (lowerSaddleM_div_sqrt_log_limit hm).mul tendsto_sqrt_log_div_log
  simp only [mul_zero] at hh
  refine hh.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with x hx
  have  := (Real.sqrt_pos.2 (Real.log_pos hx)).ne'
  field_simp
theorem lowerSaddleOmega_div_log_limit 
    (hd : 0 < d) (hm : 0 < m) (hθ : 0 < θ) (C ) :
    Tendsto (fun x => lowerSaddleOmega d m θ C x / Real.log x) atTop (𝓝 0) := by
  have hh := (lowerSaddleOmega_div_M_limit hd hm hθ C).mul (lowerSaddleM_div_log_limit hm)
  simp only [mul_zero] at hh
  refine hh.congr' ?_
  filter_upwards [(lowerSaddleM_tendsto_atTop hm).eventually (eventually_gt_atTop 0)] with x hx
  field_simp
def lowerSaddleN (s d m θ C : ℝ) (τM : ℕ → ℝ) (x : ℝ) : ℝ :=
  Real.exp (lowerSaddleLogN s d (Real.log x) (lowerSaddleOmega d m θ C x)
    (τM (lowerSaddleM m x)) (lowerSaddleM m x))
def lowerSaddleEta (s d m θ C cf x : ℝ) : ℝ := cf * (lowerSaddleH d m θ C x) ^ s
def lowerSaddleActivity (s d m θ C : ℝ) (τM : ℕ → ℝ) (x : ℝ) : ℝ :=
  (lowerSaddleN s d m θ C τM x) ^ 2 * Real.exp (τM (lowerSaddleM m x) * lowerSaddleM m x)
def lowerSaddleRisk (s d m θ C cf : ℝ) (τM : ℕ → ℝ) (x : ℝ) : ℝ :=
  (lowerSaddleEta s d m θ C cf x) ^ 2 / lowerSaddleActivity s d m θ C τM x
def lowerSaddleEnergyOne (s d m θ C : ℝ) (τM : ℕ → ℝ) (x : ℝ) : ℝ :=
  x ^ 2 * (lowerSaddleH d m θ C x) ^ (d + 4 * s) *
    (lowerSaddleN s d m θ C τM x) ^ (-d)
def lowerSaddleEnergyTwo (s d m θ C CG : ℝ) (τM : ℕ → ℝ) (x : ℝ) : ℝ :=
  x * (lowerSaddleH d m θ C x) ^ (4 * s) *
    Real.exp (2 * τM (lowerSaddleM m x) * lowerSaddleM m x) *
    (lowerSaddleN s d m θ C τM x) ^ (4 - d) *
    (CG * lowerSaddleMu d m θ C x) ^ lowerSaddleM m x /
      ((lowerSaddleM m x + 1).factorial : ℝ)
def lowerSaddleEnergyThree (s d m θ C CG : ℝ) (τM : ℕ → ℝ) (x : ℝ) : ℝ :=
  x * (lowerSaddleH d m θ C x) ^ (4 * s) *
    (lowerSaddleActivity s d m θ C τM x) ^ 2 *
    (CG * lowerSaddleMu d m θ C x) ^ lowerSaddleD d m x /
      ((lowerSaddleD d m x + 1).factorial : ℝ)
theorem lowerSaddleN_positive (s d m θ C τM x) :
    0 < lowerSaddleN s d m θ C τM x := Real.exp_pos _
theorem lowerSaddleActivity_positive (s d m θ C τM x) :
    0 < lowerSaddleActivity s d m θ C τM x := mul_pos (sq_pos_of_pos (lowerSaddleN_positive s d m θ C τM x)) (Real.exp_pos _)
def LowerExponentControl (τM : ℕ → ℝ) (τ Cτ : ℝ) : Prop :=
  ∀ᶠ M : ℕ in atTop, τ ≤ τM M ∧ (τM M - τ) * M ≤ Cτ
theorem lowerSaddleM_nat_tendsto_atTop  (hm : 0 < m) :
    Tendsto (lowerSaddleM m) atTop atTop :=
  tendsto_natCast_atTop_iff.1 (lowerSaddleM_tendsto_atTop hm)
theorem lowerSaddleTau_limit  
    (hm : 0 < m) (hcontrol : LowerExponentControl τM τ Cτ) :
    Tendsto (fun x => τM (lowerSaddleM m x)) atTop (𝓝 τ) := by
  have ht := lowerSaddleM_tendsto_atTop hm
  have he := (lowerSaddleM_nat_tendsto_atTop hm).eventually hcontrol
  have hh : Tendsto (fun x : ℝ => τM (lowerSaddleM m x) - τ) atTop (𝓝 0) := by
    apply squeeze_zero' (he.mono fun x hx => sub_nonneg.2 hx.1) _ (by simpa [div_eq_mul_inv] using! ht.inv_tendsto_atTop.const_mul Cτ)
    filter_upwards [he, ht.eventually (eventually_gt_atTop ↑0)] with x hx hM
    exact (le_div_iff₀ hM).2 hx.2
  have h := hh.add_const τ
  simp only [zero_add, sub_add_cancel] at h
  exact h
theorem lowerSaddleLogN_div_log_limit  
    (hd : 0 < d) (hm : 0 < m) (hθ : 0 < θ)
    (hcontrol : LowerExponentControl τM τ Cτ) (s C ) :
    Tendsto (fun x => Real.log (lowerSaddleN s d m θ C τM x) / Real.log x)
      atTop (𝓝 ((d - 4 * s) / (d * (d + 4)))) := by
  have hh := (((tendsto_const_nhds (x := (d - 4 * s) / d)).sub ((lowerSaddleOmega_div_log_limit hd hm hθ C).const_mul (1 + 4 * s / d))).sub
    (((lowerSaddleTau_limit hm hcontrol).mul (lowerSaddleM_div_log_limit hm)).const_mul 2)).div_const (d + 4)
  simp only [mul_zero, sub_zero] at hh
  rw [div_div _ _ _] at hh
  refine hh.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with x hx
  unfold lowerSaddleN lowerSaddleLogN
  rw [Real.log_exp]
  field_simp [(Real.log_pos hx).ne']
theorem lowerSaddleLogN_div_M_sq_limit  
    (hd : 0 < d) (hm : 0 < m) (hθ : 0 < θ)
    (hcontrol : LowerExponentControl τM τ Cτ) (s C ) :
    Tendsto (fun x => Real.log (lowerSaddleN s d m θ C τM x) / (lowerSaddleM m x ) ^ 2)
      atTop (𝓝 (((d - 4 * s) / (d * (d + 4))) / m ^ 2)) := by
  have hh := (lowerSaddleLogN_div_log_limit hd hm hθ hcontrol s C).div
    (lowerSaddleM_sq_div_log_limit hm) (pow_ne_zero 2 hm.ne')
  refine hh.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with x hx
  change (Real.log (lowerSaddleN s d m θ C τM x) / Real.log x) /
    ((lowerSaddleM m x ) ^ 2 / Real.log x) =
      Real.log (lowerSaddleN s d m θ C τM x) / (lowerSaddleM m x ) ^ 2
  field_simp [(Real.log_pos hx).ne']
theorem lowerSaddleN_tendsto_atTop  
    (hs : 1 < s) (hd : 4 * s < d) (hm : 0 < m) (hθ : 0 < θ)
    (hcontrol : LowerExponentControl τM τ Cτ) (C ) :
    Tendsto (lowerSaddleN s d m θ C τM) atTop atTop := by
  have hd0 : 0 < d := by linarith
  have hγ : 0 < (d - 4 * s) / (d * (d + 4)) := by positivity
  have hh := Real.tendsto_log_atTop.atTop_mul_pos hγ
    (lowerSaddleLogN_div_log_limit hd0 hm hθ hcontrol s C)
  exact (Real.tendsto_exp_atTop.comp (by refine hh.congr' ?_; filter_upwards [eventually_gt_atTop 1] with x hx; exact mul_div_cancel₀ _ (Real.log_pos hx).ne')).congr (fun x => Real.exp_log (lowerSaddleN_positive s d m θ C τM x))
theorem lowerSaddleMu_tends_zero 
    (hd : 0 < d) (hm : 0 < m) (hθ : 0 < θ) (C ) :
    Tendsto (lowerSaddleMu d m θ C) atTop (𝓝 0) := by
  have hh := Real.tendsto_exp_atBot.comp
    (tendsto_neg_atTop_atBot.comp (lowerSaddleOmega_tendsto_atTop hd hm hθ C))
  refine hh.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  exact (lowerSaddleMu_eq_exp hx).symm
theorem lowerSaddleEta_tends_zero 
    (hs : 0 < s) (hd : 0 < d) (hm : 0 < m) (hθ : 0 < θ) (C cf ) :
    Tendsto (lowerSaddleEta s d m θ C cf) atTop (𝓝 0) := by
  simpa only [Real.zero_rpow hs.ne', mul_zero] using! ((((lowerSaddleGrid_tendsto_atTop hd hm hθ C).inv_tendsto_atTop).rpow_const (Or.inr hs.le)).const_mul cf)
theorem tendsto_atBot_of_div_negative {f g : ℝ → ℝ} 
    (hg : Tendsto g atTop atTop) (hf : Tendsto (fun x => f x / g x) atTop (𝓝 c))
    (hc : c < 0) : Tendsto f atTop atBot := by
  refine (hg.atTop_mul_neg hc hf).congr' ?_
  filter_upwards [hg.eventually (eventually_gt_atTop 0)] with x hx
  exact mul_div_cancel₀ _ hx.ne'
theorem lowerSaddleRisk_positive  (hcf : 0 < cf) (τM ) :
    0 < lowerSaddleRisk s d m θ C cf τM x := by
  exact div_pos (sq_pos_of_pos (mul_pos hcf
    (Real.rpow_pos_of_pos (lowerSaddleH_positive d m θ C x) s)))
    (lowerSaddleActivity_positive s d m θ C τM x)
theorem log_factorial_succ_lower (M : ℕ) (hM : 1 ≤ M) :
    ↑M * Real.log M - M ≤ Real.log ((M + 1).factorial : ℝ) := by
  have := Stirling.le_log_factorial_stirling (Nat.ne_of_gt (by omega : 0 < M))
  have : 0 ≤ Real.log M := Real.log_nonneg (by exact_mod_cast hM)
  have : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hfac : M.factorial ≤ ((M + 1).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (Nat.le_succ M)
  have := Real.log_le_log (by positivity : 0 < (M.factorial : ℝ)) hfac
  linarith
def lowerSaddleAliasUpper (s d m θ C CG : ℝ) (τM : ℕ → ℝ) (x : ℝ) : ℝ :=
  (d ^ 2 - 16 * s) / (d * (d + 4)) * lowerSaddleOmega d m θ C x +
    (2 * d * τM (lowerSaddleM m x) / (d + 4) + Real.log CG + 1 - C) * lowerSaddleM m x
theorem lowerSaddleD_div_M_limit  (hd : 0 < d) (hm : 0 < m) :
    Tendsto (fun x : ℝ => (lowerSaddleD d m x : ℝ) / lowerSaddleM m x)
      atTop (𝓝 ((d + 8) / 4)) := by
  have ht := lowerSaddleM_tendsto_atTop hm
  have hu : Tendsto (fun x : ℝ => 1 / (lowerSaddleM m x : ℝ)) atTop (𝓝 0) := by
    simpa only [one_div] using! ht.inv_tendsto_atTop
  have herr : Tendsto (fun x : ℝ =>
      ((lowerSaddleD d m x : ℝ) - (d + 8) / 4 * lowerSaddleM m x) / lowerSaddleM m x)
      atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_) hu
    · exact div_nonneg (sub_nonneg.2 (Nat.le_ceil _)) (by positivity)
    · apply div_le_div_of_nonneg_right _ (by positivity)
      have hc : 0 ≤ (d + 8) / 4 * (lowerSaddleM m x ) := by positivity
      have hh := Nat.ceil_lt_add_one hc
      change (lowerSaddleD d m x ) < (d + 8) / 4 * lowerSaddleM m x + 1 at hh
      linarith
  have hh := (tendsto_const_nhds (x := (d + 8) / 4)).add herr
  simp only [add_zero] at hh
  refine hh.congr' ?_
  filter_upwards [ht.eventually (eventually_gt_atTop 0)] with x hx
  field_simp
  ring
def lowerSaddleCountUpper (s d m θ C CG x : ℝ) : ℝ :=
  (1 - 4 * s / d) * Real.log x +
    lowerSaddleD d m x  * (Real.log CG - lowerSaddleOmega d m θ C x)
theorem eventually_lowerSaddle_numeric_cost  
    (hs : 1 < s) (hd : 4 * s < d) (hm : 0 < m) (hθ : 0 < θ) (hCG : 0 < CG)
    (hcontrol : LowerExponentControl τM τ Cτ)
    (hbalance : θ * m ^ 2 = 4 * ((d - 4 * s) / (d * (d + 4))))
    (hC : 1 + Real.log CG + (d ^ 2 - 16 * s) / (d * (d + 4)) * θ +
      2 * d * τ / (d + 4) < C) :
    ∀ᶠ x : ℝ in atTop,
      CG * ((lowerSaddleActivity s d m θ C τM x) ^ 2 +
        lowerSaddleEnergyOne s d m θ C τM x + lowerSaddleEnergyTwo s d m θ C CG τM x +
        lowerSaddleEnergyThree s d m θ C CG τM x) ≤
          3 * CG * (lowerSaddleActivity s d m θ C τM x) ^ 2 := by
  have hd0 : 0 < d := by linarith
  have h_lowerSaddleE : Tendsto (fun x => lowerSaddleEnergyTwo s d m θ C CG τM x /
      (lowerSaddleActivity s d m θ C τM x) ^ 2) atTop (𝓝 0) := by
    have h_lowerSaddleA : Tendsto (fun x => lowerSaddleAliasUpper s d m θ C CG τM x / lowerSaddleM m x)
        atTop (𝓝 ((d ^ 2 - 16 * s) / (d * (d + 4)) * θ +
          2 * d * τ / (d + 4) + Real.log CG + 1 - C)) := by
      have hω := (lowerSaddleOmega_div_M_limit hd0 hm hθ C).const_mul
        ((d ^ 2 - 16 * s) / (d * (d + 4)))
      have hτ := (((lowerSaddleTau_limit hm hcontrol).const_mul (2 * d)).div_const (d + 4)).add_const
        (Real.log CG + 1 - C)
      have hh := hω.add hτ
      have hid : (d ^ 2 - 16 * s) / (d * (d + 4)) * θ +
          (2 * d * τ / (d + 4) + (Real.log CG + 1 - C)) =
          (d ^ 2 - 16 * s) / (d * (d + 4)) * θ +
            2 * d * τ / (d + 4) + Real.log CG + 1 - C := by ring
      rw [hid] at hh
      refine hh.congr' ?_
      filter_upwards [(lowerSaddleM_tendsto_atTop hm).eventually (eventually_gt_atTop ↑0)] with x hx
      unfold lowerSaddleAliasUpper
      field_simp
      ring
    have hu := tendsto_atBot_of_div_negative (lowerSaddleM_tendsto_atTop hm)
      h_lowerSaddleA (by linarith)
    apply squeeze_zero' _ _ (Real.tendsto_exp_atBot.comp hu)
    · filter_upwards [eventually_gt_atTop 0] with x hx
      have hH := lowerSaddleH_positive d m θ C x
      have hN := lowerSaddleN_positive s d m θ C τM x
      have hA := lowerSaddleActivity_positive s d m θ C τM x
      unfold lowerSaddleEnergyTwo lowerSaddleMu
      positivity
    have h_eventually_l : ∀ᶠ x : ℝ in atTop,
        Real.log (lowerSaddleEnergyTwo s d m θ C CG τM x /
          (lowerSaddleActivity s d m θ C τM x) ^ 2) ≤ lowerSaddleAliasUpper s d m θ C CG τM x := by
      filter_upwards [eventually_gt_atTop 1,
        (lowerSaddleM_tendsto_atTop hm).eventually (eventually_ge_atTop 1),
        (lowerSaddleGridBase_tendsto_atTop hd0 hm hθ C).eventually (eventually_ge_atTop 1)]
        with x hx hM hb
      have := log_factorial_succ_lower (lowerSaddleM m x) (by exact_mod_cast hM)
      have h_lowerSaddleO : lowerSaddleOmegaZero m θ C x ≤ lowerSaddleOmega d m θ C x ∧
          lowerSaddleOmega d m θ C x ≤ lowerSaddleOmegaZero m θ C x + d * Real.log 2 := by
        have hpos : 0 < lowerSaddleGridBase d m θ C x := Real.exp_pos _
        have hlow := Real.log_le_log hpos (Nat.le_ceil (lowerSaddleGridBase d m θ C x))
        change Real.log (lowerSaddleGridBase d m θ C x) ≤
          Real.log (lowerSaddleGrid d m θ C x) at hlow
        have hceil : (lowerSaddleGrid d m θ C x ) ≤ 2 * lowerSaddleGridBase d m θ C x := by
          have hh := Nat.ceil_lt_add_one hpos.le
          change (lowerSaddleGrid d m θ C x ) < lowerSaddleGridBase d m θ C x + 1 at hh
          linarith
        have hhigh := Real.log_le_log (lowerSaddleGrid_positive d m θ C x) hceil
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hpos.ne'] at hhigh
        unfold lowerSaddleGridBase at hlow hhigh
        rw [Real.log_exp] at hlow hhigh
        unfold lowerSaddleOmega
        constructor <;> nlinarith [mul_le_mul_of_nonneg_left hlow hd0.le,
          mul_le_mul_of_nonneg_left hhigh hd0.le, mul_div_cancel₀
            (Real.log x + lowerSaddleOmegaZero m θ C x) hd0.ne']
      have hω := h_lowerSaddleO.1
      have := mul_le_mul_of_nonneg_left hω (show 0 ≤ (lowerSaddleM m x : ℝ) by positivity)
      have h_lowerSaddleM_square_balance {γ} {x} (hbalance : θ * m ^ 2 = 4 * γ) (hx : 1 ≤ x) : 4 * γ * Real.log x ≤ θ * (lowerSaddleM m x ) ^ 2 := by
        have hsq := (sq_le_sq₀ (by positivity : 0 ≤ m * Real.sqrt (Real.log x)) (by positivity)).2 ((lowerSaddleM_rounding (x := x) hm.le).1)
        rw [mul_pow, Real.sq_sqrt (Real.log_nonneg hx)] at hsq
        have hh := mul_le_mul_of_nonneg_left hsq hθ.le
        rw [← mul_assoc, hbalance] at hh
        exact hh
      have := (h_lowerSaddleM_square_balance hbalance hx.le)
      have h_log_lowerSad : Real.log (lowerSaddleEnergyTwo s d m θ C CG τM x /
          (lowerSaddleActivity s d m θ C τM x) ^ 2) =
        4 * ((d - 4 * s) / (d * (d + 4))) * Real.log x +
          ((d ^ 2 - 16 * s) / (d * (d + 4)) - lowerSaddleM m x) * lowerSaddleOmega d m θ C x +
          (2 * d * τM (lowerSaddleM m x) / (d + 4) + Real.log CG) * lowerSaddleM m x -
          Real.log ((lowerSaddleM m x + 1).factorial : ℝ) := by
        have hx : 0 < x := by linarith
        have hMu : 0 < lowerSaddleMu d m θ C x := by
          unfold lowerSaddleMu
          exact mul_pos hx (Real.rpow_pos_of_pos (lowerSaddleH_positive d m θ C x) d)
        have hH := lowerSaddleH_positive d m θ C x
        have hN := lowerSaddleN_positive s d m θ C τM x
        have hA := lowerSaddleActivity_positive s d m θ C τM x
        have hfac : 0 < ((lowerSaddleM m x + 1).factorial : ℝ) := by positivity
        unfold lowerSaddleEnergyTwo
        rw [Real.log_div (by positivity) (pow_ne_zero 2 hA.ne'),
          Real.log_div (by positivity) hfac.ne', Real.log_pow]
        repeat rw [Real.log_mul (by positivity) (by positivity)]
        rw [Real.log_rpow hH, Real.log_exp, Real.log_rpow hN, Real.log_pow,
          Real.log_mul hCG.ne' hMu.ne', lowerSaddleMu_eq_exp hx, Real.log_exp]
        unfold lowerSaddleActivity lowerSaddleN
        rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_pow, Real.log_exp, Real.log_exp,
          lowerSaddleH_eq_exp hd0.ne', Real.log_exp]
        unfold lowerSaddleLogN
        field_simp
        ring
      rw [h_log_lowerSad]
      unfold lowerSaddleAliasUpper lowerSaddleOmegaZero at *
      nlinarith
    · filter_upwards [eventually_gt_atTop 0,
        h_eventually_l] with x hx hlog
      have hH := lowerSaddleH_positive d m θ C x
      have := lowerSaddleN_positive s d m θ C τM x
      have hA := lowerSaddleActivity_positive s d m θ C τM x
      change _ ≤ Real.exp (lowerSaddleAliasUpper s d m θ C CG τM x)
      exact (Real.exp_log (by unfold lowerSaddleEnergyTwo lowerSaddleMu; positivity)).symm.trans_le (Real.exp_le_exp.2 hlog)
  have h_lowerSaddleEnergyThree_ratio_tends_zero : Tendsto (fun x => lowerSaddleEnergyThree s d m θ C CG τM x /
      (lowerSaddleActivity s d m θ C τM x) ^ 2) atTop (𝓝 0) := by
    have hd0 : 0 < d := by linarith
    have hc : 1 - 4 * s / d - (d + 8) / 4 * θ * m ^ 2 < 0 := by
      rw [mul_assoc ((d + 8) / 4), hbalance]
      have hid : 1 - 4 * s / d - (d + 8) / 4 * (4 * ((d - 4 * s) / (d * (d + 4)))) =
        -4 * ((d - 4 * s) / (d * (d + 4))) := by field_simp; ring
      rw [hid]
      have : 0 < (d - 4 * s) / (d * (d + 4)) := by positivity
      linarith
    have h_lowerSaddleC : Tendsto (fun x => lowerSaddleCountUpper s d m θ C CG x / Real.log x)
        atTop (𝓝 (1 - 4 * s / d - (d + 8) / 4 * θ * m ^ 2)) := by
      have hD := lowerSaddleD_div_M_limit hd0 hm
      have hω := lowerSaddleOmega_div_M_limit hd0 hm hθ C
      have hM := lowerSaddleM_sq_div_log_limit hm
      have hconst : Tendsto (fun x : ℝ => Real.log CG / (lowerSaddleM m x : ℝ)) atTop (𝓝 0) := by
        simpa [div_eq_mul_inv] using! (lowerSaddleM_tendsto_atTop hm).inv_tendsto_atTop.const_mul (Real.log CG)
      have hh := (tendsto_const_nhds (x := 1 - 4 * s / d)).add
        ((hD.mul (hconst.sub hω)).mul hM)
      have hid : 1 - 4 * s / d + (d + 8) / 4 * (0 - θ) * m ^ 2 =
          1 - 4 * s / d - (d + 8) / 4 * θ * m ^ 2 := by ring
      rw [hid] at hh
      refine hh.congr' ?_
      filter_upwards [eventually_gt_atTop 1,
        (lowerSaddleM_tendsto_atTop hm).eventually (eventually_gt_atTop 0)] with x hx hMpos
      unfold lowerSaddleCountUpper
      field_simp [(Real.log_pos hx).ne']
    have hu := tendsto_atBot_of_div_negative Real.tendsto_log_atTop
      h_lowerSaddleC hc
    apply squeeze_zero' _ _ (Real.tendsto_exp_atBot.comp hu)
    · filter_upwards [eventually_gt_atTop 0] with x hx
      have hH := lowerSaddleH_positive d m θ C x
      have hA := lowerSaddleActivity_positive s d m θ C τM x
      unfold lowerSaddleEnergyThree lowerSaddleMu
      positivity
    have h_eventually_l : ∀ᶠ x : ℝ in atTop,
        Real.log (lowerSaddleEnergyThree s d m θ C CG τM x /
          (lowerSaddleActivity s d m θ C τM x) ^ 2) ≤ lowerSaddleCountUpper s d m θ C CG x := by
      have : 0 ≤ s := by linarith
      filter_upwards [eventually_gt_atTop 0,
        (lowerSaddleOmega_tendsto_atTop hd0 hm hθ C).eventually (eventually_ge_atTop 0)]
        with x hx hω
      have h_log_lowerSad : Real.log (lowerSaddleEnergyThree s d m θ C CG τM x /
          (lowerSaddleActivity s d m θ C τM x) ^ 2) =
          (1 - 4 * s / d) * Real.log x - 4 * s / d * lowerSaddleOmega d m θ C x +
          lowerSaddleD d m x  * (Real.log CG - lowerSaddleOmega d m θ C x) -
            Real.log ((lowerSaddleD d m x + 1).factorial : ℝ) := by
        have hMu : 0 < lowerSaddleMu d m θ C x := by
          exact mul_pos hx (Real.rpow_pos_of_pos (lowerSaddleH_positive d m θ C x) d)
        have hA := lowerSaddleActivity_positive s d m θ C τM x
        have hH := lowerSaddleH_positive d m θ C x
        unfold lowerSaddleEnergyThree
        rw [Real.log_div (by positivity) (pow_ne_zero 2 hA.ne'),
          Real.log_div (by positivity) (by positivity)]
        repeat rw [Real.log_mul (by positivity) (by positivity)]
        rw [Real.log_rpow hH, Real.log_pow, Real.log_pow, Real.log_mul hCG.ne' hMu.ne',
          lowerSaddleMu_eq_exp hx, Real.log_exp, lowerSaddleH_eq_exp hd0.ne', Real.log_exp]
        field_simp
        ring
      rw [h_log_lowerSad]
      have : 0 ≤ Real.log ((lowerSaddleD d m x + 1).factorial : ℝ) :=
        Real.log_nonneg (by exact_mod_cast Nat.factorial_pos (lowerSaddleD d m x + 1))
      unfold lowerSaddleCountUpper
      have : 0 ≤ 4 * s / d * lowerSaddleOmega d m θ C x := by positivity
      linarith
    · filter_upwards [eventually_gt_atTop 0,
        h_eventually_l] with x hx hlog
      change _ ≤ Real.exp (lowerSaddleCountUpper s d m θ C CG x)
      exact (Real.exp_log (by have := lowerSaddleH_positive d m θ C x; have hA := lowerSaddleActivity_positive s d m θ C τM x; unfold lowerSaddleEnergyThree lowerSaddleMu; positivity)).symm.trans_le (Real.exp_le_exp.2 hlog)
  filter_upwards [eventually_gt_atTop ↑0,
    h_lowerSaddleE.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    h_lowerSaddleEnergyThree_ratio_tends_zero.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with x hx h2 h3
  have hA  :=
    sq_pos_of_pos (lowerSaddleActivity_positive s d m θ C τM x)
  have h2' := (div_lt_iff₀ hA).1 h2
  have h3' := (div_lt_iff₀ hA).1 h3
  have h_lowerSaddleE : lowerSaddleEnergyOne s d m θ C τM x = (lowerSaddleActivity s d m θ C τM x) ^ 2 := by
    have : d + 4 ≠ 0 := by linarith
    have hx2 : x ^ 2 = Real.exp (2 * Real.log x) := by
      change x ^ (2 : ℕ) = Real.exp (((2 : ℕ) : ℝ) * Real.log x)
      rw [Real.exp_nat_mul, Real.exp_log hx]
    unfold lowerSaddleEnergyOne lowerSaddleActivity lowerSaddleN
    rw [hx2, Real.rpow_def_of_pos (lowerSaddleH_positive d m θ C x),
      Real.rpow_def_of_pos (Real.exp_pos _), mul_pow]
    simp only [Real.log_exp, ← Real.exp_nat_mul, ← Real.exp_add]
    rw [lowerSaddleH_eq_exp hd0.ne', Real.log_exp]
    congr 1
    unfold lowerSaddleLogN
    field_simp
    ring
  rw [h_lowerSaddleE]
  calc
    _ ≤ CG * (3 * (lowerSaddleActivity s d m θ C τM x) ^ 2) :=
      mul_le_mul_of_nonneg_left (by linarith only [h2', h3']) hCG.le
    _ = _ := by ring
theorem lowerSaddleRisk_residual_identity  (τM )
    (hs : 1 < s) (hd : 4 * s < d) (hcf : 0 < cf)
    (hθrelation : 2 * (s - 1) * θ = d * τ) :
    Real.log (lowerSaddleRisk s d m θ C cf τM x) -
      rateLog (rateExponent s d) (2 * d * τ / (d + 4) * m) (lowerLogPower s d) x =
      2 * Real.log cf - 2 * (s - 1) / (d + 4) * C -
      (2 * d * τ / (d + 4)) * ((lowerSaddleM m x ) - m * Real.sqrt (Real.log x)) +
      (2 * (s - 1) / (d + 4)) * (Real.log (lowerSaddleM m x) - Real.log (Real.log x) / 2) -
      (2 * (s - 1) / (d + 4)) * (lowerSaddleOmega d m θ C x - lowerSaddleOmegaZero m θ C x) -
      (d / (d + 4)) * ((τM (lowerSaddleM m x) - τ) * lowerSaddleM m x) := by
  have hθeq : θ = d * τ / (2 * (s - 1)) :=
    (eq_div_iff (by linarith)).2 (by simpa only [mul_comm] using hθrelation)
  have h_log_lowerSad : Real.log (lowerSaddleRisk s d m θ C cf τM x) =
      2 * Real.log cf - rateExponent s d * Real.log x -
        (2 * (s - 1) * lowerSaddleOmega d m θ C x +
          d * τM (lowerSaddleM m x) * lowerSaddleM m x) / (d + 4) := by
    have hd0 : 0 < d := by linarith
    have hH := lowerSaddleH_positive d m θ C x
    have hN := lowerSaddleN_positive s d m θ C τM x
    have hEta : 0 < lowerSaddleEta s d m θ C cf x :=
      mul_pos hcf (Real.rpow_pos_of_pos hH s)
    unfold lowerSaddleRisk
    rw [Real.log_div (pow_ne_zero 2 hEta.ne') (lowerSaddleActivity_positive s d m θ C τM x).ne',
      Real.log_pow]
    unfold lowerSaddleEta lowerSaddleActivity
    rw [Real.log_mul hcf.ne' (Real.rpow_pos_of_pos hH s).ne', Real.log_rpow hH,
      Real.log_mul (pow_ne_zero 2 hN.ne') (Real.exp_pos _).ne', Real.log_pow, Real.log_exp,
      lowerSaddleH_eq_exp hd0.ne', Real.log_exp]
    unfold lowerSaddleN
    rw [Real.log_exp]
    have h_lower_saddle_rate (L) (ω) (τ) (M) : -2 * s / d * (L + ω) - 2 * lowerSaddleLogN s d L ω τ M - τ * M =
        -rateExponent s d * L - (2 * (s - 1) * ω + d * τ * M) / (d + 4) := by
      have : d ≠ 0 := by linarith
      have : d + 4 ≠ 0 := by linarith
      unfold lowerSaddleLogN rateExponent
      field_simp
      ring
    have hh := h_lower_saddle_rate (Real.log x) (lowerSaddleOmega d m θ C x) (τM (lowerSaddleM m x)) (lowerSaddleM m x)
    ring_nf at hh ⊢
    linarith
  rw [h_log_lowerSad]
  unfold rateLog lowerLogPower lowerSaddleOmegaZero
  rw [hθeq]
  field_simp [show s - 1 ≠ 0 by linarith, show d + 4 ≠ 0 by linarith]
  ring
theorem eventually_lowerSaddleRisk_rate_bracket  
    (hs : 1 < s) (hd : 4 * s < d) (hm : 0 < m) (hθ : 0 < θ) (hcf : 0 < cf)
    (hcontrol : LowerExponentControl τM τ Cτ) (hθrelation : 2 * (s - 1) * θ = d * τ) :
    ∃ c A, 0 < c ∧ 0 < A ∧ ∀ᶠ x : ℝ in atTop,
      c * rateScale (rateExponent s d) (2 * d * τ / (d + 4) * m) (lowerLogPower s d) x ≤
        lowerSaddleRisk s d m θ C cf τM x ∧
      lowerSaddleRisk s d m θ C cf τM x ≤
        A * rateScale (rateExponent s d) (2 * d * τ / (d + 4) * m) (lowerLogPower s d) x := by
  have hd0 : 0 < d := by linarith
  have hceil : (fun x : ℝ => (lowerSaddleM m x : ℝ) - m * Real.sqrt (Real.log x))
      =O[atTop] (fun _ : ℝ => (1 : ℝ)) := by
    apply Asymptotics.IsBigO.of_bound 1
    filter_upwards [] with x
    simp only [Real.norm_eq_abs, norm_one, mul_one]
    rw [abs_of_nonneg (sub_nonneg.2 (lowerSaddleM_rounding hm.le).1)]
    linarith [(lowerSaddleM_rounding (x := x) hm.le).2]
  have h_log_lowerSad : Tendsto (fun x : ℝ => Real.log (lowerSaddleM m x) - Real.log (Real.log x) / 2)
      atTop (𝓝 (Real.log m)) := by
    refine ((Real.continuousAt_log hm.ne').tendsto.comp (lowerSaddleM_div_sqrt_log_limit hm)).congr' ?_
    filter_upwards [eventually_gt_atTop 1,
      (lowerSaddleM_tendsto_atTop hm).eventually (eventually_gt_atTop (0 : ℝ))] with x hx hM
    simp only [Function.comp_apply]
    rw [Real.log_div hM.ne' (Real.sqrt_pos.2 (Real.log_pos hx)).ne',
      Real.log_sqrt (Real.log_pos hx).le]
  have hlog := h_log_lowerSad.isBigO_one ℝ
  have hω := (lowerSaddleOmega_rounding_limit hd0 hm hθ C).isBigO_one ℝ
  have hτ : (fun x : ℝ => (τM (lowerSaddleM m x) - τ) * lowerSaddleM m x)
      =O[atTop] (fun _ : ℝ => (1 : ℝ)) := by
    apply Asymptotics.IsBigO.of_bound Cτ
    filter_upwards [(lowerSaddleM_nat_tendsto_atTop hm).eventually hcontrol] with x hx
    simp only [Real.norm_eq_abs, norm_one, mul_one]
    rw [abs_of_nonneg (mul_nonneg (sub_nonneg.2 hx.1) (by positivity))]
    exact hx.2
  have hc := Asymptotics.isBigO_const_one
    (2 * Real.log cf - 2 * (s - 1) / (d + 4) * C) (atTop : Filter ℝ) (F := ℝ)
  have hh := (((hc.sub (hceil.const_mul_left (2 * d * τ / (d + 4)))).add
    (hlog.const_mul_left (2 * (s - 1) / (d + 4)))).sub
    (hω.const_mul_left (2 * (s - 1) / (d + 4)))).sub (hτ.const_mul_left (d / (d + 4)))
  have h_lowerSaddleR := hh.congr_left (fun x => (lowerSaddleRisk_residual_identity τM hs hd hcf hθrelation).symm)
  obtain ⟨K, hK⟩ := h_lowerSaddleR.bound
  refine ⟨Real.exp (-K), Real.exp K, Real.exp_pos _, Real.exp_pos _, ?_⟩
  filter_upwards [hK] with x hx
  simp only [Real.norm_eq_abs, norm_one, mul_one] at hx
  have hp := lowerSaddleRisk_positive (s := s) (d := d) (m := m) (θ := θ) (C := C) (x := x) hcf τM
  rcases abs_le.1 hx with ⟨hl, hu⟩
  unfold rateScale
  rw [← Real.exp_add, ← Real.exp_add]
  constructor
  · rw [← Real.exp_log hp]
    exact Real.exp_le_exp.2 ((le_sub_iff_add_le).1 hl)
  · rw [← Real.exp_log hp]
    exact Real.exp_le_exp.2 ((sub_le_iff_le_add).1 hu)
def lowerSaddleTheta (s d τ : ℝ) : ℝ := d * τ / (2 * (s - 1))
theorem lowerSaddleCoefficient_pos 
    (hs : 1 < s) (hd : 4 * s < d) (hτ : 0 < τ) :
    0 < lowerSaddleCoefficient s d τ := by
  have : 0 < d := by linarith
  apply Real.sqrt_pos.2
  positivity
theorem lowerSaddleTheta_pos 
    (hs : 1 < s) (hd : 4 * s < d) (hτ : 0 < τ) : 0 < lowerSaddleTheta s d τ := by
  have : 0 < d := by linarith
  unfold lowerSaddleTheta
  positivity
theorem lowerSaddleTheta_relation  (hs : 1 < s) :
    2 * (s - 1) * lowerSaddleTheta s d τ = d * τ := by
  unfold lowerSaddleTheta
  field_simp [show s - 1 ≠ 0 by linarith]
theorem lowerSaddle_canonical_balance 
    (hs : 1 < s) (hd : 4 * s < d) (hτ : 0 < τ) :
    lowerSaddleTheta s d τ * (lowerSaddleCoefficient s d τ) ^ 2 =
      4 * ((d - 4 * s) / (d * (d + 4))) := by
  have : 0 < d := by linarith
  unfold lowerSaddleTheta lowerSaddleCoefficient
  rw [Real.sq_sqrt (by positivity)]
  field_simp [show s - 1 ≠ 0 by linarith]
  ring
theorem exists_actual_lowerExponentControl  (ha : 0 < a) (hab : a < b) :
    ∃ Cτ, 0 ≤ Cτ ∧ LowerExponentControl (shrunkDensityExponent a b)
      (densityIntervalExponent a b) Cτ := exists_shrunkDensityExponent_control ha hab
def lowerSaddleResponseQuantity (s d m θ C cf : ℝ) (q : ℕ) (τM : ℕ → ℝ) (x : ℝ) : ℝ :=
  (lowerSaddleEta s d m θ C cf x) ^ (4 * q) * (lowerSaddleN s d m θ C τM x) ^ d
def lowerSaddleResponseOrder (s d : ℝ) : ℕ := max 2 (Nat.floor (d / (4 * s)))
def LowerSaddleReg (K η0 s d m θ C cf : ℝ) (M0 : ℕ) (τM : ℕ → ℝ) (x : ℝ) : Prop :=
  M0 ≤ lowerSaddleM m x ∧
  lowerSaddleD d m x = Nat.ceil ((d + 8) / 4 * lowerSaddleM m x) ∧
  1 ≤ lowerSaddleN s d m θ C τM x ∧
  0 < lowerSaddleMu d m θ C x ∧ lowerSaddleMu d m θ C x < 1 ∧
  (lowerSaddleM m x ) / K ≤ lowerSaddleOmega d m θ C x ∧
  lowerSaddleOmega d m θ C x ≤ K * lowerSaddleM m x ∧
  (lowerSaddleM m x ) ^ 2 / K ≤ Real.log (lowerSaddleN s d m θ C τM x) ∧
  Real.log (lowerSaddleN s d m θ C τM x) ≤ K * (lowerSaddleM m x ) ^ 2 ∧
  0 < lowerSaddleEta s d m θ C cf x ∧ lowerSaddleEta s d m θ C cf x ≤ η0 ∧
  lowerSaddleResponseQuantity s d m θ C cf (lowerSaddleResponseOrder s d) τM x ≤ 1
theorem eventually_lowerSaddleReg {K η0 s d m θ cf τ Cτ : ℝ} 
    (hs : 1 < s) (hd : 4 * s < d) (hm : 0 < m) (hθ : 0 < θ) (hcf : 0 < cf)
    (hη0 : 0 < η0) (_hK : 1 ≤ K) (hcontrol : LowerExponentControl τM τ Cτ)
    (hθlow : 1 / K < θ) (hθhigh : θ < K)
    (hNlow : 1 / K < ((d - 4 * s) / (d * (d + 4))) / m ^ 2)
    (hNhigh : ((d - 4 * s) / (d * (d + 4))) / m ^ 2 < K) (C M0) :
    ∀ᶠ x : ℝ in atTop, LowerSaddleReg K η0 s d m θ C cf M0 τM x := by
  have hd0 : 0 < d := by linarith
  have hω := lowerSaddleOmega_div_M_limit hd0 hm hθ C
  have hN := lowerSaddleLogN_div_M_sq_limit hd0 hm hθ hcontrol s C
  have h_lowerSaddleR : d / (4 * s) - 1 ≤ (lowerSaddleResponseOrder s d ) := by
    have : 0 < s := by linarith
    have := Nat.lt_floor_add_one (d / (4 * s))
    have : (Nat.floor (d / (4 * s)) : ℝ) ≤ lowerSaddleResponseOrder s d := by
      exact_mod_cast le_max_right 2 (Nat.floor (d / (4 * s)))
    linarith
  have : d / (4 * s) - 1 ≤ ((lowerSaddleResponseOrder s d) : ℝ) := h_lowerSaddleR
  have hd0 : 0 < d := by linarith
  have : 0 < (d - 4 * s) / (d * (d + 4)) := by positivity
  have : d ≤ 4 * s * (((lowerSaddleResponseOrder s d) : ℝ) + 1) := by
    have hh : d / (4 * s) ≤ ((lowerSaddleResponseOrder s d) : ℝ) + 1 := by linarith
    simpa only [mul_comm] using (div_le_iff₀ (by positivity)).1 hh
  have hid : (4 * (lowerSaddleResponseOrder s d) : ℝ) * (-s / d) + d * ((d - 4 * s) / (d * (d + 4))) =
      -4 * ((d - 4 * s) / (d * (d + 4))) + (d - 4 * s * (((lowerSaddleResponseOrder s d) : ℝ) + 1)) / d := by
    field_simp
    ring
  have h_log_lowerSad : Tendsto (fun x => Real.log (lowerSaddleEta s d m θ C cf x) / Real.log x)
      atTop (𝓝 (-s / d)) := by
    have hω := lowerSaddleOmega_div_log_limit hd0 hm hθ C
    have hh := (tendsto_const_div_log (Real.log cf)).sub (((tendsto_const_nhds (x := 1)).add hω).const_mul (s / d))
    simp only [add_zero, mul_one, zero_sub, ← neg_div] at hh
    refine hh.congr' ?_
    filter_upwards [eventually_gt_atTop 1] with x hx
    unfold lowerSaddleEta
    rw [Real.log_mul hcf.ne' (Real.rpow_pos_of_pos (lowerSaddleH_positive d m θ C x) s).ne',
      Real.log_rpow (lowerSaddleH_positive d m θ C x), lowerSaddleH_eq_exp hd0.ne', Real.log_exp]
    field_simp [(Real.log_pos hx).ne']
    ring
  have hh := (h_log_lowerSad.const_mul
    (4 * ((lowerSaddleResponseOrder s d) : ℝ))).add
    ((lowerSaddleLogN_div_log_limit hd0 hm hθ hcontrol s C).const_mul d)
  have hlog : Tendsto (fun x => Real.log (lowerSaddleResponseQuantity s d m θ C cf (lowerSaddleResponseOrder s d) τM x) / Real.log x)
      atTop (𝓝 ((4 * (lowerSaddleResponseOrder s d) : ℝ) * (-s / d) + d * ((d - 4 * s) / (d * (d + 4))))) := by
    refine hh.congr' ?_
    filter_upwards [eventually_gt_atTop 1] with x hx
    have hEta : 0 < lowerSaddleEta s d m θ C cf x :=
      mul_pos hcf (Real.rpow_pos_of_pos (lowerSaddleH_positive d m θ C x) s)
    unfold lowerSaddleResponseQuantity
    rw [Real.log_mul (pow_ne_zero (4 * lowerSaddleResponseOrder s d) hEta.ne')
      (Real.rpow_pos_of_pos (lowerSaddleN_positive s d m θ C τM x) d).ne',
      Real.log_pow, Real.log_rpow (lowerSaddleN_positive s d m θ C τM x)]
    push_cast
    ring
  have h_lowerSaddleR := (Real.tendsto_exp_atBot.comp (tendsto_atBot_of_div_negative Real.tendsto_log_atTop hlog (by rw [hid]; have : (d - 4 * s * (((lowerSaddleResponseOrder s d) : ℝ) + 1)) / d ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hd0.le; linarith))).congr (fun x => Real.exp_log (by
      unfold lowerSaddleResponseQuantity lowerSaddleEta
      have := lowerSaddleH_positive d m θ C x
      have hN := lowerSaddleN_positive s d m θ C τM x
      positivity))
  filter_upwards [eventually_gt_atTop 0,
    (lowerSaddleM_nat_tendsto_atTop hm).eventually (eventually_ge_atTop M0),
    (lowerSaddleM_tendsto_atTop hm).eventually (eventually_gt_atTop 0),
    (lowerSaddleN_tendsto_atTop hs hd hm hθ hcontrol C).eventually (eventually_ge_atTop 1),
    (lowerSaddleMu_tends_zero hd0 hm hθ C).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    hω.eventually (lt_mem_nhds hθlow), hω.eventually (gt_mem_nhds hθhigh),
    hN.eventually (lt_mem_nhds hNlow), hN.eventually (gt_mem_nhds hNhigh),
    (lowerSaddleEta_tends_zero (s := s) (by linarith) hd0 hm hθ C cf).eventually (gt_mem_nhds hη0),
    (h_lowerSaddleR).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))]
    with x hx hM0 hMpos hN1 hMu1 hωl hωu hNl hNu hEta0 hRsp
  have hMu  := mul_pos hx (Real.rpow_pos_of_pos (lowerSaddleH_positive d m θ C x) d)
  have hEta  :=
    mul_pos hcf (Real.rpow_pos_of_pos (lowerSaddleH_positive d m θ C x) s)
  have hωl' := (lt_div_iff₀ hMpos).1 hωl
  have hωu' := (div_lt_iff₀ hMpos).1 hωu
  have hNl' := (lt_div_iff₀ (sq_pos_of_pos hMpos)).1 hNl
  have hNu' := (div_lt_iff₀ (sq_pos_of_pos hMpos)).1 hNu
  refine ⟨hM0, rfl, hN1, hMu, hMu1, ?_, hωu'.le, ?_, hNu'.le, hEta, hEta0.le, hRsp.le⟩
  · simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one] using hωl'.le
  · simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one] using hNl'.le
theorem tendsto_sample_div_log : Tendsto (fun x => x / Real.log x) atTop atTop := by
  have hwithin : Tendsto (fun x => Real.log x / x) atTop (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.2
    refine ⟨by simpa only [Real.rpow_one] using tendsto_log_power_div_sample 1, ?_⟩
    filter_upwards [eventually_gt_atTop 1] with x hx
    exact div_pos (Real.log_pos hx) (by linarith)
  exact hwithin.inv_tendsto_nhdsGT_zero.congr (fun x => by
    change (Real.log x / x)⁻¹ = x / Real.log x
    rw [inv_div])
def lowerSaddleExceptionalTail (d m θ C c x : ℝ) : ℝ :=
  2 * Real.exp (-c / ((lowerSaddleM m x ) ^ 2 * (lowerSaddleH d m θ C x) ^ d))
theorem lowerSaddleExceptionalTail_over_rate_tends_zero 
    (hd : 0 < d) (hm : 0 < m) (hθ : 0 < θ) (hc : 0 < c) (C lam κ a ) :
    Tendsto (fun x => lowerSaddleExceptionalTail d m θ C c x / (rateScale lam κ a x) ^ 2)
      atTop (𝓝 0) := by
  have h_exponential_sample_log_tail_over_rate_tends_zero {c} (hc : 0 < c) : Tendsto (fun x => 2 * Real.exp (-c * x / Real.log x) / (rateScale lam κ a x) ^ 2)
      atTop (𝓝 0) := by
    have hs := tendsto_sample_div_log
    have hconst : Tendsto (fun x => Real.log 2 / (x / Real.log x)) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using! hs.inv_tendsto_atTop.const_mul (Real.log 2)
    have hrate : Tendsto (fun x => rateLog lam κ a x / Real.log x) atTop (𝓝 (-lam)) := by
      have hh := (tendsto_normalized_log_scale lam κ a 0).neg
      convert! hh using 1
      funext x
      ring
    have hcorr : Tendsto (fun x => rateLog lam κ a x / (x / Real.log x)) atTop (𝓝 0) := by
      have hh := hrate.mul (by simpa only [Real.rpow_two] using tendsto_log_power_div_sample 2)
      simp only [mul_zero] at hh
      refine hh.congr' ?_
      filter_upwards [eventually_gt_atTop 1] with x hx
      field_simp [(Real.log_pos hx).ne']
    have hh := (hconst.sub (tendsto_const_nhds (x := c))).sub (hcorr.const_mul 2)
    simp only [zero_sub, mul_zero, sub_zero] at hh
    have hlog : Tendsto (fun x =>
        (Real.log 2 - c * x / Real.log x - 2 * rateLog lam κ a x) / (x / Real.log x))
        atTop (𝓝 (-c)) := by
      refine hh.congr' ?_
      filter_upwards [eventually_gt_atTop 1] with x hx
      field_simp [(Real.log_pos hx).ne']
    refine (Real.tendsto_exp_atBot.comp (tendsto_atBot_of_div_negative hs hlog (neg_neg_of_pos hc))).congr (fun x => ?_)
    change Real.exp (Real.log 2 - c * x / Real.log x - 2 * rateLog lam κ a x) = _
    rw [Real.exp_sub, Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    unfold rateScale
    rw [show 2 * rateLog lam κ a x = ((2 : ℕ) : ℝ) * rateLog lam κ a x by rfl, Real.exp_nat_mul, show -c * x / Real.log x = -(c * x / Real.log x) by ring, Real.exp_neg]
    ring
  apply squeeze_zero' (Eventually.of_forall fun x => by
    unfold lowerSaddleExceptionalTail rateScale
    positivity) _ ((h_exponential_sample_log_tail_over_rate_tends_zero (show 0 < c / (2 * m ^ 2) by positivity)))
  have h_eventually_l : ∀ᶠ x : ℝ in atTop, lowerSaddleExceptionalTail d m θ C c x ≤
      2 * Real.exp (-(c / (2 * m ^ 2)) * x / Real.log x) := by
    have h_eventually_l : ∀ᶠ x : ℝ in atTop,
        (lowerSaddleM m x ) ^ 2 * (lowerSaddleH d m θ C x) ^ d ≤
          2 * m ^ 2 * Real.log x / x := by
      filter_upwards [eventually_gt_atTop 1,
        (lowerSaddleM_sq_div_log_limit hm).eventually (gt_mem_nhds (by nlinarith : m ^ 2 < 2 * m ^ 2)),
        (lowerSaddleMu_tends_zero hd hm hθ C).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))]
        with x hx hM hMu
      have hx0 : 0 < x := by linarith
      have hM' := (div_lt_iff₀ (Real.log_pos hx)).1 hM
      calc
        _ ≤ (lowerSaddleM m x ) ^ 2 * (1 / x) := mul_le_mul_of_nonneg_left (by apply (le_div_iff₀ hx0).2; unfold lowerSaddleMu at hMu; simpa only [mul_comm] using hMu.le) (sq_nonneg _)
        _ ≤ 2 * m ^ 2 * Real.log x / x := by
          simpa only [one_div, div_eq_mul_inv, mul_assoc, one_mul] using
            mul_le_mul_of_nonneg_right hM'.le (inv_nonneg.2 hx0.le)
    filter_upwards [eventually_gt_atTop 1,
      (lowerSaddleM_tendsto_atTop hm).eventually (eventually_gt_atTop ↑0),
      h_eventually_l] with x hx hM hbound
    have hden  :=
      mul_pos (sq_pos_of_pos hM) (Real.rpow_pos_of_pos (lowerSaddleH_positive d m θ C x) d)
    have hh := div_le_div_of_nonneg_left hc.le hden hbound
    have hid : c / (2 * m ^ 2 * Real.log x / x) = (c / (2 * m ^ 2)) * x / Real.log x := by field_simp
    rw [hid] at hh
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
    apply Real.exp_le_exp.2
    convert neg_le_neg hh using 1 <;> ring
  filter_upwards [h_eventually_l] with x hx
  exact div_le_div_of_nonneg_right hx (sq_nonneg _)
theorem exists_regime_window  (hu : 0 < u) (hv : 0 < v) :
    ∃ K : ℝ, 1 ≤ K ∧ 1 / K < u ∧ u < K ∧ 1 / K < v ∧ v < K := by
  let K := 2 + u + v + 1 / u + 1 / v
  have : 0 < 1 / u := by positivity
  have : 0 < 1 / v := by positivity
  have hK : 0 < K := by dsimp [K]; linarith
  have h1u : 1 / u < K := by dsimp [K]; linarith
  have h1v : 1 / v < K := by dsimp [K]; linarith
  refine ⟨K, ?_, (div_lt_iff₀ hK).2 ?_, ?_, (div_lt_iff₀ hK).2 ?_, ?_⟩
  · dsimp [K]; linarith
  · have hh := mul_lt_mul_of_pos_left h1u hu
    simpa only [one_div, mul_inv_cancel₀ hu.ne'] using hh
  · dsimp [K]; linarith
  · have hh := mul_lt_mul_of_pos_left h1v hv
    simpa only [one_div, mul_inv_cancel₀ hv.ne'] using hh
  · dsimp [K]; linarith
theorem eventually_actual_lowerSaddle_numeric_cost 
    (hs : 1 < s) (hd : 4 * s < d) (ha : 0 < a) (hab : a < b) (hCG : 0 < CG)
    (hC : 1 + Real.log CG + (d ^ 2 - 16 * s) / (d * (d + 4)) *
      lowerSaddleTheta s d (densityIntervalExponent a b) +
      2 * d * densityIntervalExponent a b / (d + 4) < C) :
    ∀ᶠ x : ℝ in atTop,
      let m := lowerSaddleCoefficient s d (densityIntervalExponent a b)
      let θ := lowerSaddleTheta s d (densityIntervalExponent a b)
      let τM := shrunkDensityExponent a b
      CG * ((lowerSaddleActivity s d m θ C τM x) ^ 2 + lowerSaddleEnergyOne s d m θ C τM x +
        lowerSaddleEnergyTwo s d m θ C CG τM x + lowerSaddleEnergyThree s d m θ C CG τM x) ≤
          3 * CG * (lowerSaddleActivity s d m θ C τM x) ^ 2 := by
  have hτ := densityIntervalExponent_pos ha hab
  obtain ⟨Cτ, _, hcontrol⟩ := exists_actual_lowerExponentControl ha hab
  exact eventually_lowerSaddle_numeric_cost hs hd (lowerSaddleCoefficient_pos hs hd hτ)
    (lowerSaddleTheta_pos hs hd hτ) hCG hcontrol (lowerSaddle_canonical_balance hs hd hτ) hC
theorem actual_lowerSaddle_fixed_regime_window 
    (hs : 1 < s) (hd : 4 * s < d) (ha : 0 < a) (hab : a < b) (hcf : 0 < cf) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (C η0 : ℝ) M0, 0 < η0 →
      ∀ᶠ x : ℝ in atTop,
        LowerSaddleReg K η0 s d (lowerSaddleCoefficient s d (densityIntervalExponent a b))
          (lowerSaddleTheta s d (densityIntervalExponent a b)) C cf M0 (shrunkDensityExponent a b) x := by
  have hτ := densityIntervalExponent_pos ha hab
  have hm := lowerSaddleCoefficient_pos hs hd hτ
  have hθ := lowerSaddleTheta_pos hs hd hτ
  have : 0 < d := by linarith
  have hγm : 0 < ((d - 4 * s) / (d * (d + 4))) /
      (lowerSaddleCoefficient s d (densityIntervalExponent a b)) ^ 2 := by positivity
  obtain ⟨K, hK, hθl, hθu, hNl, hNu⟩ := exists_regime_window hθ hγm
  obtain ⟨Cτ, _, hcontrol⟩ := exists_actual_lowerExponentControl ha hab
  refine ⟨K, hK, fun C η0 M0 hη0 => ?_⟩
  exact eventually_lowerSaddleReg hs hd hm hθ hcf hη0 hK hcontrol hθl hθu hNl hNu C M0
end
section
theorem log_profile_div_scale_tends_zero {f M : ℝ → ℝ} 
    (hM : Tendsto M atTop atTop) (p ) (hc : 0 < c)
    (hf : ∀ᶠ x in atTop, 0 < f x)
    (hr : Tendsto (fun x => f x / (M x)^p) atTop (𝓝 c)) :
    Tendsto (fun x => Real.log (f x) / M x) atTop (𝓝 0) := by
  have hh := (((Real.continuousAt_log hc.ne').tendsto.comp hr).mul hM.inv_tendsto_atTop).add ((Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hM).const_mul ↑p)
  simp only [mul_zero, add_zero] at hh
  refine hh.congr' ?_
  filter_upwards [hf, hM.eventually (eventually_gt_atTop 0)] with x hx hMx
  simp only [Function.comp_apply, id_eq, Pi.inv_apply]
  rw [Real.log_div hx.ne' (pow_pos hMx p).ne', Real.log_pow]
  field_simp [hMx.ne']
  ring
theorem positive_profile_tends_zero_of_log_div_negative {f M : ℝ → ℝ} 
    (hM : Tendsto M atTop atTop) (hc : c < 0) (hf : ∀ᶠ x in atTop, 0 < f x)
    (hr : Tendsto (fun x => Real.log (f x) / M x) atTop (𝓝 c)) :
    Tendsto f atTop (𝓝 0) := by
  refine (Real.tendsto_exp_atBot.comp (tendsto_atBot_of_div_negative hM hr hc)).congr' (hf.mono fun x hx => Real.exp_log hx)
def lowerAliasH (s d m θ C : ℝ) (τM : ℕ → ℝ) (x : ℝ) : ℝ :=
  1 + Real.log (lowerSaddleN s d m θ C τM x)
def lowerAliasQ (s d m θ C Cact a : ℝ) (τM : ℕ → ℝ) (x : ℝ) : ℝ :=
  Cact * lowerSaddleD d m x  * lowerAliasH s d m θ C τM x *
    (lowerSaddleMu d m θ C x * lowerAliasH s d m θ C τM x)^(a/d)
def lowerAliasCutoff (s d m θ C c0 : ℝ) (τM : ℕ → ℝ) (x : ℝ) : ℝ :=
  lowerSaddleN s d m θ C τM x * Real.exp (-c0 * lowerSaddleD d m x)
def lowerAliasTargetScale (s d m θ C : ℝ) (τM : ℕ → ℝ) (r : ℕ) (x : ℝ) : ℝ :=
  lowerSaddleN s d m θ C τM x *
    (lowerSaddleMu d m θ C x * lowerAliasH s d m θ C τM x)^((r-2)/d)
variable {s d m θ τ Cτ : ℝ} {τM : ℕ → ℝ}
theorem lowerAliasH_eventually_positive
    (hs : 1 < s) (hd : 4*s < d) (hm : 0 < m) (hθ : 0 < θ)
    (hcontrol : LowerExponentControl τM τ Cτ) (C ) :
    ∀ᶠ x in atTop, 0 < lowerAliasH s d m θ C τM x := by
  filter_upwards [(lowerSaddleN_tendsto_atTop hs hd hm hθ hcontrol C).eventually
    (eventually_gt_atTop 1)] with x hx
  unfold lowerAliasH
  linarith [Real.log_pos hx]
theorem log_lowerAliasH_div_M_tends_zero
    (hs : 1 < s) (hd : 4*s < d) (hm : 0 < m) (hθ : 0 < θ)
    (hcontrol : LowerExponentControl τM τ Cτ) (C ) :
    Tendsto (fun x => Real.log (lowerAliasH s d m θ C τM x) / lowerSaddleM m x)
      atTop (𝓝 0) := by
  have hd0 : 0 < d := by linarith
  apply log_profile_div_scale_tends_zero (lowerSaddleM_tendsto_atTop hm) 2
    (by positivity : 0 < ((d-4*s)/(d*(d+4)))/m^2)
    (lowerAliasH_eventually_positive hs hd hm hθ hcontrol C)
  have hh := ((lowerSaddleM_tendsto_atTop hm).inv_tendsto_atTop.pow 2).add (lowerSaddleLogN_div_M_sq_limit hd0 hm hθ hcontrol s C)
  simp only [zero_pow (by decide : 2 ≠ 0), zero_add] at hh
  convert hh using 1
  funext x
  simp only [lowerAliasH, add_div, one_div, Pi.inv_apply, inv_pow]
theorem log_lowerSaddleD_div_M_tends_zero (hd : 0 < d) (hm : 0 < m) :
    Tendsto (fun x => Real.log (lowerSaddleD d m x) / lowerSaddleM m x)
      atTop (𝓝 0) := by
  exact log_profile_div_scale_tends_zero (lowerSaddleM_tendsto_atTop hm) 1
    (by linarith : 0 < (d+8)/4) (by filter_upwards [(lowerSaddleM_tendsto_atTop hm).eventually (eventually_gt_atTop 0)] with x hx; exact lt_of_lt_of_le (by positivity : 0 < (d+8)/4 * lowerSaddleM m x ) (Nat.le_ceil _)) (by simpa only [pow_one] using lowerSaddleD_div_M_limit hd hm)
theorem lowerAliasMuH_log_div_M_limit
    (hs : 1 < s) (hd : 4*s < d) (hm : 0 < m) (hθ : 0 < θ)
    (hcontrol : LowerExponentControl τM τ Cτ) (C ) :
    Tendsto (fun x => Real.log (lowerSaddleMu d m θ C x * lowerAliasH s d m θ C τM x) /
      lowerSaddleM m x) atTop (𝓝 (-θ)) := by
  have hh := (lowerSaddleOmega_div_M_limit (d := d) (by linarith) hm hθ C).neg.add
    (log_lowerAliasH_div_M_tends_zero hs hd hm hθ hcontrol C)
  simp only [add_zero] at hh
  refine hh.congr' ?_
  filter_upwards [eventually_gt_atTop 0, lowerAliasH_eventually_positive hs hd hm hθ hcontrol C]
    with x hx hH
  rw [lowerSaddleMu_eq_exp hx, Real.log_mul (Real.exp_pos _).ne' hH.ne', Real.log_exp]
  ring
theorem lowerSaddleD_eventually_positive (hd : 0 < d) (hm : 0 < m) :
    ∀ᶠ x in atTop, 0 < (lowerSaddleD d m x : ℝ) := by
  filter_upwards [(lowerSaddleM_tendsto_atTop hm).eventually (eventually_gt_atTop ↑0)] with x hx
  exact lt_of_lt_of_le (by positivity : 0 < (d+8)/4 * (lowerSaddleM m x : ℝ)) (Nat.le_ceil _)
theorem lowerAliasMuH_eventually_positive
    (hs : 1 < s) (hd : 4*s < d) (hm : 0 < m) (hθ : 0 < θ)
    (hcontrol : LowerExponentControl τM τ Cτ) (C ) :
    ∀ᶠ x in atTop, 0 < lowerSaddleMu d m θ C x * lowerAliasH s d m θ C τM x := by
  filter_upwards [eventually_gt_atTop 0, lowerAliasH_eventually_positive hs hd hm hθ hcontrol C] with x hx hH
  rw [lowerSaddleMu_eq_exp hx]
  positivity
theorem lowerSaddleM_sq_tendsto_atTop (hm : 0 < m) :
    Tendsto (fun x => (lowerSaddleM m x : ℝ)^2) atTop atTop := by
  simpa only [pow_two] using (lowerSaddleM_tendsto_atTop hm).atTop_mul_atTop₀ (lowerSaddleM_tendsto_atTop hm)
theorem lowerSaddleD_div_M_sq_tends_zero (hd : 0 < d) (hm : 0 < m) :
    Tendsto (fun x => (lowerSaddleD d m x ) / (lowerSaddleM m x : ℝ)^2) atTop (𝓝 0) := by
  have hh := (lowerSaddleD_div_M_limit hd hm).mul (lowerSaddleM_tendsto_atTop hm).inv_tendsto_atTop
  simp only [mul_zero] at hh
  convert hh using 1
  funext x
  simp only [Pi.inv_apply, div_eq_mul_inv, pow_two, mul_inv, mul_assoc]
theorem fine_target_count_lt {N base H ω d c0 D r : ℝ}
    (hN : 0 < N) (hbase : 0 < base) (hd : 0 < d)
    (hgap : 0 < ω - Real.log H) (hlog : Real.log base = -ω + Real.log H)
    (hactive : N * Real.exp (-c0*D) < N * base^((r-2)/d)) :
    r < 2 + d*c0*D/(ω-Real.log H) := by
  have hln := Real.log_lt_log (Real.exp_pos _) ((mul_lt_mul_iff_right₀ hN).mp hactive)
  rw [Real.log_exp, Real.log_rpow hbase, hlog] at hln
  have hm := mul_lt_mul_of_pos_right hln hd
  have he : ((r-2)/d * (-ω + Real.log H))*d = -(r-2)*(ω-Real.log H) := by
    field_simp [hd.ne']
    ring
  rw [he] at hm
  have hp : (r-2)*(ω-Real.log H) < d*c0*D := by nlinarith
  have := (lt_div_iff₀ hgap).2 hp
  linarith
def lowerAliasFineTargetBound (d θ c0 : ℝ) : ℕ :=
  Nat.ceil (3 + d*c0*(((d+8)/4)/θ + 1))
def LowerAliasHierarchy (s d m θ C Cact Cs c0 : ℝ) (τM : ℕ → ℝ) (x : ℝ) : Prop :=
  1 < lowerAliasCutoff s d m θ C c0 τM x ∧
  τM (lowerSaddleM m x) ≤ c0 ∧
  lowerSaddleMu d m θ C x * lowerAliasH s d m θ C τM x ≤ 1 ∧
  Real.log (lowerAliasH s d m θ C τM x) ≤ lowerSaddleM m x ∧
  2 * Real.log (lowerAliasH s d m θ C τM x) < lowerSaddleOmega d m θ C x ∧
  lowerAliasQ s d m θ C Cact 2 τM x ≤ lowerAliasQ s d m θ C Cact 1 τM x ∧
  lowerAliasQ s d m θ C Cact 1 τM x ≤ 1/2 ∧
  (lowerSaddleD d m x )^2 * lowerAliasQ s d m θ C Cact 1 τM x ≤ 1 ∧
  Real.exp (τM (lowerSaddleM m x) * lowerSaddleD d m x) *
    lowerAliasCutoff s d m θ C c0 τM x / lowerSaddleN s d m θ C τM x ≤ 1 ∧
  Cs * lowerSaddleD d m x  * Real.exp (c0*((lowerSaddleD d m x )+1)) ≤
    lowerSaddleN s d m θ C τM x ∧
  lowerAliasFineTargetBound d θ c0 ≤ lowerSaddleM m x ∧
  ∀ r, lowerAliasCutoff s d m θ C c0 τM x < lowerAliasTargetScale s d m θ C τM r x →
    r ≤ lowerAliasFineTargetBound d θ c0
theorem eventually_lowerAlias_hierarchy
    (hs : 1 < s) (hd : 4*s < d) (hm : 0 < m) (hθ : 0 < θ)
    (hcontrol : LowerExponentControl τM τ Cτ) {Cact Cs c0 : ℝ}
    (hCact : 0 < Cact) (hCs : 0 < Cs) (hc0 : 0 < c0) (hτc0 : τ < c0) (C ) :
    ∀ᶠ x in atTop, LowerAliasHierarchy s d m θ C Cact Cs c0 τM x := by
  have h_lowerAliasQ_log_div_M_limit (a : ℝ) : Tendsto (fun x => Real.log (lowerAliasQ s d m θ C Cact a τM x) / lowerSaddleM m x)
      atTop (𝓝 (-θ * (a/d))) := by
    have hd0 : 0 < d := by linarith
    have hh := ((((lowerSaddleM_tendsto_atTop hm).inv_tendsto_atTop.const_mul (Real.log Cact)).add (log_lowerSaddleD_div_M_tends_zero hd0 hm)).add
      (log_lowerAliasH_div_M_tends_zero hs hd hm hθ hcontrol C)).add
        ((lowerAliasMuH_log_div_M_limit hs hd hm hθ hcontrol C).const_mul (a/d))
    simp only [mul_zero, zero_add, mul_comm (a/d)] at hh
    refine hh.congr' ?_
    filter_upwards [lowerSaddleD_eventually_positive hd0 hm,
      lowerAliasH_eventually_positive hs hd hm hθ hcontrol C,
      lowerAliasMuH_eventually_positive hs hd hm hθ hcontrol C] with x hD hH hbase
    simp only [Pi.inv_apply]
    unfold lowerAliasQ
    rw [Real.log_mul (mul_pos (mul_pos hCact hD) hH).ne' (Real.rpow_pos_of_pos hbase _).ne',
      Real.log_mul (mul_pos hCact hD).ne' hH.ne', Real.log_mul hCact.ne' hD.ne', Real.log_rpow hbase]
    ring
  have h_eventually_l : ∀ᶠ x in atTop,
      lowerSaddleMu d m θ C x * lowerAliasH s d m θ C τM x ≤ 1 ∧
      Real.log (lowerAliasH s d m θ C τM x) ≤ lowerSaddleM m x ∧
      2 * Real.log (lowerAliasH s d m θ C τM x) < lowerSaddleOmega d m θ C x ∧
      lowerAliasQ s d m θ C Cact 2 τM x ≤ lowerAliasQ s d m θ C Cact 1 τM x ∧
      lowerAliasQ s d m θ C Cact 1 τM x ≤ 1/2 ∧
      (lowerSaddleD d m x )^2 * lowerAliasQ s d m θ C Cact 1 τM x ≤ 1 := by
    have hd0 : 0 < d := by linarith
    have hgap := (lowerSaddleOmega_div_M_limit hd0 hm hθ C).sub
      ((log_lowerAliasH_div_M_tends_zero hs hd hm hθ hcontrol C).const_mul 2)
    simp only [mul_zero, sub_zero] at hgap
    have h_lowerAliasMu : Tendsto (fun x => lowerSaddleMu d m θ C x * lowerAliasH s d m θ C τM x) atTop (𝓝 0) := by
      apply positive_profile_tends_zero_of_log_div_negative (lowerSaddleM_tendsto_atTop hm)
        (neg_neg_of_pos hθ)
      · filter_upwards [eventually_gt_atTop 0, lowerAliasH_eventually_positive hs hd hm hθ hcontrol C] with x hx hH
        rw [lowerSaddleMu_eq_exp hx]
        positivity
      · exact lowerAliasMuH_log_div_M_limit hs hd hm hθ hcontrol C
    have h_lowerAliasQ_tends_zero {a : ℝ} (ha : 0 < a) : Tendsto (lowerAliasQ s d m θ C Cact a τM) atTop (𝓝 0) := by
      have hd0 : 0 < d := by linarith
      apply positive_profile_tends_zero_of_log_div_negative (lowerSaddleM_tendsto_atTop hm)
        (mul_neg_of_neg_of_pos (neg_neg_of_pos hθ) (div_pos ha hd0))
      · filter_upwards [lowerSaddleD_eventually_positive hd0 hm,
          lowerAliasH_eventually_positive hs hd hm hθ hcontrol C,
          lowerAliasMuH_eventually_positive hs hd hm hθ hcontrol C] with x hD hH hbase
        exact mul_pos (mul_pos (mul_pos hCact hD) hH) (Real.rpow_pos_of_pos hbase _)
      · exact h_lowerAliasQ_log_div_M_limit a
    have h_lowerAliasD_sq_Q_tends_zero {a : ℝ} (ha : 0 < a) : Tendsto (fun x => (lowerSaddleD d m x : ℝ)^2 * lowerAliasQ s d m θ C Cact a τM x)
        atTop (𝓝 0) := by
      have hd0 : 0 < d := by linarith
      have hh := ((log_lowerSaddleD_div_M_tends_zero hd0 hm).const_mul 2).add
        (h_lowerAliasQ_log_div_M_limit a)
      simp only [mul_zero, zero_add] at hh
      have hqpos : ∀ᶠ x in atTop, 0 < lowerAliasQ s d m θ C Cact a τM x := by
        filter_upwards [lowerSaddleD_eventually_positive hd0 hm,
          lowerAliasH_eventually_positive hs hd hm hθ hcontrol C,
          lowerAliasMuH_eventually_positive hs hd hm hθ hcontrol C] with x hD hH hbase
        exact mul_pos (mul_pos (mul_pos hCact hD) hH) (Real.rpow_pos_of_pos hbase _)
      apply positive_profile_tends_zero_of_log_div_negative (lowerSaddleM_tendsto_atTop hm)
        (mul_neg_of_neg_of_pos (neg_neg_of_pos hθ) (div_pos ha hd0))
      · filter_upwards [lowerSaddleD_eventually_positive hd0 hm, hqpos] with x hD hQ
        positivity
      · refine hh.congr' ?_
        filter_upwards [lowerSaddleD_eventually_positive hd0 hm, hqpos] with x hD hQ
        rw [Real.log_mul (sq_pos_of_pos hD).ne' hQ.ne', Real.log_pow]
        ring
    filter_upwards [
      h_lowerAliasMu.eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1)),
      (log_lowerAliasH_div_M_tends_zero hs hd hm hθ hcontrol C).eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1)),
      hgap.eventually (lt_mem_nhds hθ),
      (h_lowerAliasQ_tends_zero (by norm_num : (0 : ℝ)<1)).eventually
        (gt_mem_nhds (by norm_num : (0 : ℝ)<1/2)),
      (h_lowerAliasD_sq_Q_tends_zero (by norm_num : (0 : ℝ)<1)).eventually
        (gt_mem_nhds (by norm_num : (0 : ℝ)<1)),
      (lowerSaddleM_tendsto_atTop hm).eventually (eventually_gt_atTop (0 : ℝ)),
      lowerAliasMuH_eventually_positive hs hd hm hθ hcontrol C,
      lowerSaddleD_eventually_positive hd0 hm, lowerAliasH_eventually_positive hs hd hm hθ hcontrol C]
      with x hbase hlog hgap hq hsmall hM hbase0 hD hH
    refine ⟨hbase.le, by simpa only [one_mul] using ((div_lt_iff₀ hM).1 hlog).le, ?_, ?_, hq.le, hsmall.le⟩
    · have h := sub_pos.mp hgap
      exact (div_lt_div_iff_of_pos_right hM).mp (by simpa only [mul_div_assoc] using h)
    · unfold lowerAliasQ
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_ge hbase0 hbase.le (by apply div_le_div_of_nonneg_right (by norm_num) hd0.le))
        (by positivity)
  have h_eventually_lowerAlias_singleton_le : ∀ᶠ x in atTop, Cs * lowerSaddleD d m x  *
      Real.exp (c0*((lowerSaddleD d m x )+1)) ≤ lowerSaddleN s d m θ C τM x := by
    have h_lowerAliasSi : Tendsto (fun x => Cs * lowerSaddleD d m x  *
        Real.exp (c0*((lowerSaddleD d m x : ℝ)+1)) / lowerSaddleN s d m θ C τM x)
        atTop (𝓝 0) := by
      have hd0 : 0 < d := by linarith
      have hA : 0 < ((d-4*s)/(d*(d+4)))/m^2 := by positivity
      have hconst : Tendsto (fun x => Real.log Cs / (lowerSaddleM m x : ℝ)^2) atTop (𝓝 0) := by
        simpa only [Pi.inv_apply, div_eq_mul_inv, mul_zero] using (lowerSaddleM_sq_tendsto_atTop hm).inv_tendsto_atTop.const_mul (Real.log Cs)
      have h_log_lowe : Tendsto (fun x => Real.log (lowerSaddleD d m x) / (lowerSaddleM m x : ℝ)^2) atTop (𝓝 0) := by
        have hh := (log_lowerSaddleD_div_M_tends_zero hd0 hm).mul (lowerSaddleM_tendsto_atTop hm).inv_tendsto_atTop
        simp only [mul_zero] at hh
        convert hh using 1
        funext x
        simp only [Pi.inv_apply, div_eq_mul_inv, pow_two, mul_inv, mul_assoc]
      have hh := (((hconst.add h_log_lowe).add
        ((lowerSaddleD_div_M_sq_tends_zero hd0 hm).const_mul c0)).add (by simpa only [Pi.inv_apply, div_eq_mul_inv, mul_zero] using (lowerSaddleM_sq_tendsto_atTop hm).inv_tendsto_atTop.const_mul c0)).sub
          (lowerSaddleLogN_div_M_sq_limit hd0 hm hθ hcontrol s C)
      simp only [mul_zero, zero_add, zero_sub] at hh
      apply positive_profile_tends_zero_of_log_div_negative (lowerSaddleM_sq_tendsto_atTop hm) (neg_neg_of_pos hA)
      · filter_upwards [lowerSaddleD_eventually_positive hd0 hm] with x hD
        exact div_pos (mul_pos (mul_pos hCs hD) (Real.exp_pos _)) (lowerSaddleN_positive _ _ _ _ _ _ _)
      · refine hh.congr' ?_
        filter_upwards [lowerSaddleD_eventually_positive hd0 hm] with x hD
        rw [Real.log_div (mul_pos (mul_pos hCs hD) (Real.exp_pos _)).ne' (lowerSaddleN_positive _ _ _ _ _ _ _).ne',
          Real.log_mul (mul_pos hCs hD).ne' (Real.exp_pos _).ne', Real.log_mul hCs.ne' hD.ne', Real.log_exp]
        ring
    filter_upwards [h_lowerAliasSi.eventually
      (gt_mem_nhds (by norm_num : (0 : ℝ)<1))] with x hx
    simpa only [one_mul] using ((div_lt_iff₀ (lowerSaddleN_positive _ _ _ _ _ _ _)).1 hx).le
  have h_eventually_lowerAlias_cutoff_guards : ∀ᶠ x in atTop, 1 < lowerAliasCutoff s d m θ C c0 τM x ∧
      τM (lowerSaddleM m x) ≤ c0 ∧
      Real.exp (τM (lowerSaddleM m x) * lowerSaddleD d m x) *
        lowerAliasCutoff s d m θ C c0 τM x / lowerSaddleN s d m θ C τM x ≤ 1 := by
    have h_lowerAliasCu : Tendsto (lowerAliasCutoff s d m θ C c0 τM) atTop atTop := by
      have hd0 : 0 < d := by linarith
      have hh := (lowerSaddleLogN_div_M_sq_limit hd0 hm hθ hcontrol s C).sub
        ((lowerSaddleD_div_M_sq_tends_zero hd0 hm).const_mul c0)
      simp only [mul_zero, sub_zero] at hh
      have hlog : Tendsto (fun x => Real.log (lowerAliasCutoff s d m θ C c0 τM x) /
          (lowerSaddleM m x )^2) atTop (𝓝 (((d-4*s)/(d*(d+4)))/m^2)) := by
        convert hh using 1
        funext x
        rw [lowerAliasCutoff, Real.log_mul (lowerSaddleN_positive _ _ _ _ _ _ _).ne' (Real.exp_pos _).ne', Real.log_exp]
        ring
      have ht : Tendsto (fun x => Real.log (lowerAliasCutoff s d m θ C c0 τM x)) atTop atTop := by
        refine ((lowerSaddleM_sq_tendsto_atTop hm).atTop_mul_pos (by positivity) hlog).congr' ?_
        filter_upwards [(lowerSaddleM_tendsto_atTop hm).eventually (eventually_gt_atTop 0)] with x hx
        exact mul_div_cancel₀ _ (sq_pos_of_pos hx).ne'
      convert (Real.tendsto_exp_atTop.comp ht) using 1
      funext x
      exact (Real.exp_log (mul_pos (lowerSaddleN_positive _ _ _ _ _ _ _) (Real.exp_pos _))).symm
    filter_upwards [h_lowerAliasCu.eventually
      (eventually_gt_atTop 1), (lowerSaddleTau_limit hm hcontrol).eventually (gt_mem_nhds hτc0)] with x hell hτ
    have he : Real.exp (τM (lowerSaddleM m x) * lowerSaddleD d m x) *
        lowerAliasCutoff s d m θ C c0 τM x / lowerSaddleN s d m θ C τM x =
        Real.exp ((τM (lowerSaddleM m x)-c0)*lowerSaddleD d m x) := by
      unfold lowerAliasCutoff
      calc
        _ = Real.exp (τM (lowerSaddleM m x) * lowerSaddleD d m x) * Real.exp (-c0 * lowerSaddleD d m x) := by
          field_simp [(lowerSaddleN_positive s d m θ C τM x).ne']
        _ = _ := by rw [← Real.exp_add]; congr 1; ring
    exact ⟨hell, hτ.le, (by rw [he]; exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hτ.le) (Nat.cast_nonneg _)))⟩
  have h_eventually_lowerAlias_fine_targets : ∀ᶠ x in atTop,
      lowerAliasFineTargetBound d θ c0 ≤ lowerSaddleM m x ∧
      ∀ r, lowerAliasCutoff s d m θ C c0 τM x < lowerAliasTargetScale s d m θ C τM r x →
        r ≤ lowerAliasFineTargetBound d θ c0 := by
    have hd0 : 0 < d := by linarith
    have hglim := (lowerSaddleOmega_div_M_limit hd0 hm hθ C).sub
      (log_lowerAliasH_div_M_tends_zero hs hd hm hθ hcontrol C)
    simp only [sub_zero] at hglim
    have h_lowerAliasD_ : Tendsto (fun x => (lowerSaddleD d m x ) /
        (lowerSaddleOmega d m θ C x - Real.log (lowerAliasH s d m θ C τM x)))
        atTop (𝓝 (((d+8)/4)/θ)) := by
      have hd0 : 0 < d := by linarith
      have hgap := (lowerSaddleOmega_div_M_limit hd0 hm hθ C).sub
        (log_lowerAliasH_div_M_tends_zero hs hd hm hθ hcontrol C)
      simp only [sub_zero] at hgap
      refine ((lowerSaddleD_div_M_limit hd0 hm).div hgap hθ.ne').congr' ?_
      filter_upwards [(lowerSaddleM_tendsto_atTop hm).eventually (eventually_gt_atTop 0)] with x hx
      simp only [Pi.div_apply, ← sub_div, div_div_div_cancel_right₀ hx.ne']
    have hh := (h_lowerAliasD_.const_mul (d*c0)).const_add 2
    have hmargin : 2 + d*c0*(((d+8)/4)/θ) < 3 + d*c0*(((d+8)/4)/θ+1) := by nlinarith
    filter_upwards [hh.eventually (gt_mem_nhds hmargin),
      (lowerSaddleM_nat_tendsto_atTop hm).eventually (eventually_ge_atTop (lowerAliasFineTargetBound d θ c0)),
      hglim.eventually (lt_mem_nhds hθ),
      (lowerSaddleM_tendsto_atTop hm).eventually (eventually_gt_atTop 0),
      lowerAliasMuH_eventually_positive hs hd hm hθ hcontrol C,
      lowerAliasH_eventually_positive hs hd hm hθ hcontrol C, eventually_gt_atTop 0]
      with x hthreshold hM hgapnorm hMpos hbase hH hx
    refine ⟨hM, fun r hr => ?_⟩
    have hgap : 0 < lowerSaddleOmega d m θ C x - Real.log (lowerAliasH s d m θ C τM x) := by
      have hg : 0 < (lowerSaddleOmega d m θ C x - Real.log (lowerAliasH s d m θ C τM x)) / lowerSaddleM m x := by
        simpa only [sub_div] using hgapnorm
      simpa only [zero_mul] using (lt_div_iff₀ hMpos).1 hg
    have hbound : ↑r < (lowerAliasFineTargetBound d θ c0 : ℝ) := by
      apply (fine_target_count_lt (lowerSaddleN_positive s d m θ C τM x) hbase hd0 hgap (by rw [lowerSaddleMu_eq_exp hx, Real.log_mul (Real.exp_pos _).ne' hH.ne', Real.log_exp]) hr).trans
      have hthr : 2 + d*c0*(lowerSaddleD d m x : ℝ) /
          (lowerSaddleOmega d m θ C x - Real.log (lowerAliasH s d m θ C τM x)) <
          3 + d*c0*(((d+8)/4)/θ+1) := by simpa only [mul_div_assoc] using hthreshold
      exact hthr.trans_le (Nat.le_ceil _)
    exact Nat.le_of_lt (by exact_mod_cast hbound)
  filter_upwards [h_eventually_l,
    h_eventually_lowerAlias_cutoff_guards,
    h_eventually_lowerAlias_singleton_le,
    h_eventually_lowerAlias_fine_targets]
    with x hrow hcut hsingle hfine
  rcases hrow with ⟨hbase,hlog,hgap,hq21,hq1,hDq⟩
  exact ⟨hcut.1,hcut.2.1,hbase,hlog,hgap,hq21,hq1,hDq,hcut.2.2,hsingle,hfine⟩
theorem actual_lowerAlias_hierarchy {s d a b Cact Cs : ℝ}
    (hs : 1 < s) (hd : 4*s < d) (ha : 0 < a) (hab : a < b)
    (hCact : 0 < Cact) (hCs : 0 < Cs) (C ) :
    ∀ᶠ x in atTop,
      LowerAliasHierarchy s d
        (lowerSaddleCoefficient s d (densityIntervalExponent a b))
        (lowerSaddleTheta s d (densityIntervalExponent a b)) C Cact Cs
        (densityIntervalExponent a b + 1) (shrunkDensityExponent a b) x := by
  have hτ := densityIntervalExponent_pos ha hab
  obtain ⟨Cτ,_,hcontrol⟩ := exists_actual_lowerExponentControl ha hab
  exact eventually_lowerAlias_hierarchy hs hd (lowerSaddleCoefficient_pos hs hd hτ)
    (lowerSaddleTheta_pos hs hd hτ) hcontrol hCact hCs (by linarith) (by linarith) C
end
def higherBandInterpolationBase (d : ℕ) (lam : ℝ) : ℝ := 1024 * |lam| *d^2
def higherBandGeometricConstant (B Ci : ℝ) : ℝ := 2*(1+B)*(1+Ci)
def higherBandGeometricPrefactor (B Ci Rsp : ℝ) : ℝ := 8*Rsp*(1+B)^2*(1+Ci)
def higherBandGeometricRatio (d D : ℕ) (Cact H base a : ℝ) : ℝ :=
  Cact*D*H*base^(a/d)
theorem higher_band_coefficient_absorption {r : ℕ} (hr : 2 ≤ r) {b B Ci : ℝ}
    (hb : 0 ≤ b) (hB : 0 ≤ B) (hCi : 0 ≤ Ci) (hbB : b ≤ B) :
    b^r * Ci^(r-1) * (2*(r : ℝ)) ≤
      (8*(1+B)^2*(1+Ci)) * (higherBandGeometricConstant B Ci)^(r-2) := by
  have hrEq : r = r-2+2 := by omega
  have hrEq1 : r-1 = r-2+1 := by omega
  have hbpow : b^r ≤ (1+B)^2*(1+B)^(r-2) := by
    calc b^r ≤ (1+B)^r := pow_le_pow_left₀ hb (by linarith) r
         _ = _ := by nth_rw 1 [hrEq]; rw [pow_add]; ring
  have hcipow : Ci^(r-1) ≤ (1+Ci)*(1+Ci)^(r-2) := by
    calc Ci^(r-1) ≤ (1+Ci)^(r-1) := pow_le_pow_left₀ hCi (by linarith) _
         _ = _ := by rw [hrEq1, pow_succ]; ring
  have hrpow : (r : ℝ) ≤ (2 : ℝ)^r := by exact_mod_cast (show r < 2^r from Nat.lt_two_pow_self).le
  have hrcoef : 2*(r : ℝ) ≤ 8*(2 : ℝ)^(r-2) := by
    have he : (2 : ℝ)^r = 4*(2 : ℝ)^(r-2) := by rw [hrEq, pow_add]; norm_num; ring
    rw [he] at hrpow
    nlinarith
  have h := mul_le_mul (mul_le_mul hbpow hcipow (by positivity) (by positivity)) hrcoef
    (by positivity) (by positivity)
  apply h.trans_eq
  unfold higherBandGeometricConstant
  rw [mul_pow, mul_pow]
  ring
theorem higherBandTargetScale_eq {d r : ℕ} (hr : 2 ≤ r) (N mu )
    (hbase : 0 ≤ mu*(1+Real.log N)) :
    higherBandTargetScale d r N mu =
      N*((mu*(1+Real.log N))^(1/(d : ℝ)))^(r-2) := by
  unfold higherBandTargetScale
  congr 1
  have he : ((r : ℝ)-2)/(d : ℝ) = (1/(d : ℝ))*(r-2 : ℕ) := by
    rw [Nat.cast_sub hr]
    push_cast
    ring
  rw [he, Real.rpow_mul_natCast hbase]
theorem higherBandRowActivityCap_geometric_le {d r m D q : ℕ} (hr : 2 ≤ r)
    (a b C lam T B H base P alpha : ℝ) (hT : 1 ≤ T) (hB : 0 ≤ B)
    (hbase : 0 ≤ base) (hP : 0 ≤ P) (_hH : 0 ≤ H)
    (hbB : ordinaryDensityActivityBase a b ≤ B)
    (hlog : 1+Real.log T ≤ H)
    (hT2 : T^2 ≤ P*(base^(alpha/(d : ℝ)))^(r-2)) :
    higherBandRowActivityCap d r m D q a b C lam T ≤
      higherBandGeometricPrefactor B (higherBandInterpolationBase d lam)
        ((∑ h : Fin (2*q+2), |responseWeight q h|)*2*C^2) *
      (D : ℝ)^2 * Real.exp ((m : ℝ)*exteriorTau ((a+b)/(b-a))) * P *
      (higherBandGeometricRatio d D (higherBandGeometricConstant B (higherBandInterpolationBase d lam)) H base alpha)^(r-2) := by
  have hb0 : 0 ≤ ordinaryDensityActivityBase a b := by unfold ordinaryDensityActivityBase; positivity
  have hCi : 0 ≤ higherBandInterpolationBase d lam := by unfold higherBandInterpolationBase; positivity
  have hcoef := higher_band_coefficient_absorption hr hb0 hB hCi hbB
  have hlog0 : 0 ≤ 1+Real.log T := by linarith [Real.log_nonneg hT]
  have hlogpow := pow_le_pow_left₀ hlog0 hlog (r-2)
  have : 0 ≤ higherBandGeometricConstant B (higherBandInterpolationBase d lam) := by
    unfold higherBandGeometricConstant
    positivity
  have hDpower : (D : ℝ)^r = (D : ℝ)^2*(D : ℝ)^(r-2) := by
    nth_rw 1 [show r=r-2+2 by omega]
    rw [pow_add]
    ring
  have hscale := mul_le_mul hT2 hlogpow (by positivity) (by positivity)
  have h := mul_le_mul hcoef hscale (by positivity) (by positivity)
  have hh := mul_le_mul_of_nonneg_left h
    (show 0 ≤ (D : ℝ)^r * Real.exp ((m : ℝ)*exteriorTau ((a+b)/(b-a))) *
      ((∑ h : Fin (2*q+2), |responseWeight q h|)*2*C^2) by positivity)
  convert hh using 1 <;>
    simp only [higherBandRowActivityCap, higherBandInterpolationCap, higherBandGeometricPrefactor,
      higherBandGeometricRatio, higherBandInterpolationBase, hDpower, mul_pow] <;> ring
theorem higherBandTargetScale_le_N  (_hd : 0 < d) (hr : 2 ≤ r)
    {N mu : ℝ} (hN : 1 ≤ N) (hmu : 0 ≤ mu) (hbase1 : mu*(1+Real.log N) ≤ 1) :
    higherBandTargetScale d r N mu ≤ N := by
  have hH : 0 ≤ 1+Real.log N := by linarith [Real.log_nonneg hN]
  have hbase := mul_nonneg hmu hH
  have hpower := Real.rpow_le_one hbase hbase1
    (show 0 ≤ ((r : ℝ)-2)/(d : ℝ) by
      have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
      exact div_nonneg (sub_nonneg.mpr hrR) (Nat.cast_nonneg _))
  unfold higherBandTargetScale
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hpower (by linarith)
theorem ordinaryDensityActivityBase_eq  (ha : 0 < a) (hab : a < b) :
    ordinaryDensityActivityBase a b = Real.exp (1+densityIntervalExponent a b)*((b-a)/a) := by
  have he : b/densityMargin a b 0 = -((b-a)/a) := by
    unfold densityMargin
    field_simp [ha.ne', (ha.trans hab).ne', (sub_pos.mpr hab).ne']
    ring
  unfold ordinaryDensityActivityBase
  rw [he, abs_neg, abs_of_pos (div_pos (sub_pos.mpr hab) ha), exteriorTau_sqrt_ratio a b ha hab]
  rfl
def uniformOrdinaryDensityActivityBase (a b c0 : ℝ) : ℝ :=
  Real.exp (1+c0)*((b-a)/a)
theorem ordinaryDensityActivityBase_shrunk_le {a b t c0 : ℝ}
    (ha : 0 < a) (ht : 0 ≤ t) (hshrink : a+t < b-t)
    (htau : densityIntervalExponent (a+t) (b-t) ≤ c0) :
    ordinaryDensityActivityBase (a+t) (b-t) ≤ uniformOrdinaryDensityActivityBase a b c0 := by
  have hap : 0 < a+t := by linarith
  rw [ordinaryDensityActivityBase_eq hap hshrink]
  exact mul_le_mul (Real.exp_le_exp.mpr (by linarith)) (by apply (div_le_div_iff₀ hap ha).mpr; nlinarith)
    (div_pos (sub_pos.mpr hshrink) hap).le (Real.exp_pos _).le
def higherBandSourceCact (d : ℕ) (a b c0 lam : ℝ) : ℝ :=
  higherBandGeometricConstant (uniformOrdinaryDensityActivityBase a b c0) (higherBandInterpolationBase d lam)
theorem higherBandRowActivityCap_coarse_geometric_le  (hd : 0 < d) (hr : 2 ≤ r)
    (a b C lam N mu ell B ) (hN : 1 ≤ N) (hmu : 0 ≤ mu)
    (hbase1 : mu*(1+Real.log N) ≤ 1)
    (hT : 1 ≤ min ell (higherBandTargetScale d r N mu)) (hB : 0 ≤ B)
    (hbB : ordinaryDensityActivityBase a b ≤ B) :
    higherBandRowActivityCap d r D D q a b C lam (min ell (higherBandTargetScale d r N mu)) ≤
      higherBandGeometricPrefactor B (higherBandInterpolationBase d lam)
        ((∑ h : Fin (2*q+2), |responseWeight q h|)*2*C^2) *
      (D : ℝ)^2 * Real.exp ((D : ℝ)*exteriorTau ((a+b)/(b-a))) * (N*ell) *
      (higherBandGeometricRatio d D (higherBandGeometricConstant B (higherBandInterpolationBase d lam))
        (1+Real.log N) (mu*(1+Real.log N)) 1)^(r-2) := by
  have hH : 0 ≤ 1+Real.log N := by linarith [Real.log_nonneg hN]
  have hbase := mul_nonneg hmu hH
  have hell : 0 ≤ ell := by linarith [min_le_left ell (higherBandTargetScale d r N mu)]
  have hnu := higherBandTargetScale_le_N hd hr hN hmu hbase1
  have hTN : min ell (higherBandTargetScale d r N mu) ≤ N := (min_le_right _ _).trans hnu
  apply higherBandRowActivityCap_geometric_le hr a b C lam _ B _ _ (N*ell) 1 hT hB hbase (by positivity) hH hbB
  · exact add_le_add_right (Real.log_le_log (by linarith : 0 < min ell (higherBandTargetScale d r N mu)) hTN) 1
  · have ht0 : 0 ≤ min ell (higherBandTargetScale d r N mu) := by linarith
    have h := mul_le_mul (min_le_left ell (higherBandTargetScale d r N mu))
      (min_le_right ell (higherBandTargetScale d r N mu)) ht0 hell
    calc
      _ ≤ ell * higherBandTargetScale d r N mu := by simpa only [pow_two] using h
      _ = _ := by rw [higherBandTargetScale_eq hr N mu hbase]; ring
theorem higherBandRowActivityCap_fine_geometric_le  (hd : 0 < d) (hr : 2 ≤ r)
    (a b C lam N mu B ) (hN : 1 ≤ N) (hmu : 0 ≤ mu)
    (hbase1 : mu*(1+Real.log N) ≤ 1) (hT : 1 ≤ higherBandTargetScale d r N mu)
    (hB : 0 ≤ B) (hbB : ordinaryDensityActivityBase a b ≤ B) :
    higherBandRowActivityCap d r M D q a b C lam (higherBandTargetScale d r N mu) ≤
      higherBandGeometricPrefactor B (higherBandInterpolationBase d lam)
        ((∑ h : Fin (2*q+2), |responseWeight q h|)*2*C^2) *
      D^2 * Real.exp ((M : ℝ)*exteriorTau ((a+b)/(b-a))) * N^2 *
      (higherBandGeometricRatio d D (higherBandGeometricConstant B (higherBandInterpolationBase d lam))
        (1+Real.log N) (mu*(1+Real.log N)) 2)^(r-2) := by
  have hH : 0 ≤ 1+Real.log N := by linarith [Real.log_nonneg hN]
  have hbase := mul_nonneg hmu hH
  apply higherBandRowActivityCap_geometric_le hr a b C lam _ B _ _ (N^2) 2 hT hB hbase (by positivity) hH hbB
  · exact add_le_add_right (Real.log_le_log (by linarith : 0 < higherBandTargetScale d r N mu) (higherBandTargetScale_le_N hd hr hN hmu hbase1)) 1
  · apply le_of_eq
    rw [higherBandTargetScale_eq hr N mu hbase, mul_pow]
    have he : ((mu*(1+Real.log N))^(1/(d : ℝ)))^2 = (mu*(1+Real.log N))^(2/(d : ℝ)) := by
      rw [← Real.rpow_mul_natCast hbase]
      congr 1
      push_cast
      ring
    rw [← pow_mul, Nat.mul_comm (r-2) 2, pow_mul, he]
end NearlyMinimax
