module

public import NearlyMinimax.Rates
public import NearlyMinimax.LogSlope
public import NearlyMinimax.LowerEndpoint
public import Mathlib.Analysis.SpecialFunctions.Stirling

@[expose] public section

/-!
# The actual lower saddle allocation

This file constructs and analyzes the scalar parameters of `lem:saddle` in
`sections/lower_fisher.tex`. Natural ceilings are used for the polynomial
degree and the spatial grid. The statements in this file are deterministic
numeric allocation results; they do not postulate the local score construction
or its statistical energy estimate.
-/

noncomputable section
open Filter
open scoped Topology

namespace NearlyMinimax

def lowerSaddleM (m x : ℝ) : ℕ := Nat.ceil (m * Real.sqrt (Real.log x))

def lowerSaddleD (d m x : ℝ) : ℕ := Nat.ceil ((d + 8) / 4 * lowerSaddleM m x)

def lowerSaddleOmegaZero (m θ C x : ℝ) : ℝ :=
  θ * lowerSaddleM m x - Real.log (lowerSaddleM m x) + C

def lowerSaddleGridBase (d m θ C x : ℝ) : ℝ :=
  Real.exp ((Real.log x + lowerSaddleOmegaZero m θ C x) / d)

def lowerSaddleGrid (d m θ C x : ℝ) : ℕ := Nat.ceil (lowerSaddleGridBase d m θ C x)

def lowerSaddleH (d m θ C x : ℝ) : ℝ := (lowerSaddleGrid d m θ C x : ℝ)⁻¹

def lowerSaddleMu (d m θ C x : ℝ) : ℝ := x * (lowerSaddleH d m θ C x) ^ d

def lowerSaddleOmega (d m θ C x : ℝ) : ℝ :=
  d * Real.log (lowerSaddleGrid d m θ C x) - Real.log x

theorem lowerSaddleM_rounding {m x : ℝ} (hm : 0 ≤ m) :
    m * Real.sqrt (Real.log x) ≤ (lowerSaddleM m x : ℝ) ∧
      (lowerSaddleM m x : ℝ) < m * Real.sqrt (Real.log x) + 1 := ⟨Nat.le_ceil _, Nat.ceil_lt_add_one (mul_nonneg hm (Real.sqrt_nonneg _))⟩

section
variable {m : ℝ} (hm : 0 < m)
include hm

theorem lowerSaddleM_tendsto_atTop :
    Tendsto (fun x : ℝ => (lowerSaddleM m x : ℝ)) atTop atTop := by
  apply tendsto_atTop_mono (fun x => (lowerSaddleM_rounding hm.le).1)
  exact tendsto_sqrt_log_atTop.const_mul_atTop hm

private theorem eventually_lowerSaddleM_pos :
    ∀ᶠ x : ℝ in atTop, 0 < (lowerSaddleM m x : ℝ) :=
  (lowerSaddleM_tendsto_atTop hm).eventually (eventually_gt_atTop (0 : ℝ))

theorem lowerSaddleM_div_sqrt_log_limit :
    Tendsto (fun x : ℝ => (lowerSaddleM m x : ℝ) / Real.sqrt (Real.log x))
      atTop (𝓝 m) :=
  (tendsto_nat_ceil_mul_div_atTop hm.le).comp tendsto_sqrt_log_atTop

theorem lowerSaddleM_sq_div_log_limit :
    Tendsto (fun x : ℝ => (lowerSaddleM m x : ℝ) ^ 2 / Real.log x) atTop (𝓝 (m ^ 2)) := by
  have hh := (lowerSaddleM_div_sqrt_log_limit hm).pow 2
  refine hh.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  simp only [div_pow, Real.sq_sqrt (Real.log_pos hx).le]

theorem log_lowerSaddleM_residual_limit :
    Tendsto (fun x : ℝ => Real.log (lowerSaddleM m x) - Real.log (Real.log x) / 2)
      atTop (𝓝 (Real.log m)) := by
  have hh := (Real.continuousAt_log hm.ne').tendsto.comp (lowerSaddleM_div_sqrt_log_limit hm)
  refine hh.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    eventually_lowerSaddleM_pos hm] with x hx hM
  simp [Real.log_div hM.ne' (Real.sqrt_pos.2 (Real.log_pos hx)).ne', Real.log_sqrt (Real.log_pos hx).le]

theorem lowerSaddleOmegaZero_div_M_limit (θ C : ℝ) :
    Tendsto (fun x : ℝ => lowerSaddleOmegaZero m θ C x / lowerSaddleM m x)
      atTop (𝓝 θ) := by
  have ht := lowerSaddleM_tendsto_atTop hm
  have hl := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp ht
  have hc := ht.const_div_atTop C
  have hh := ((tendsto_const_nhds (x := θ)).sub hl).add hc
  simp only [sub_zero, add_zero] at hh
  refine hh.congr' ?_
  filter_upwards [ht.eventually (eventually_gt_atTop (0 : ℝ))] with x hx
  simp only [Function.comp_apply, id_eq]
  unfold lowerSaddleOmegaZero
  field_simp

end

theorem lowerSaddleOmegaZero_tendsto_atTop {m θ : ℝ} (hm : 0 < m) (hθ : 0 < θ) (C : ℝ) :
    Tendsto (lowerSaddleOmegaZero m θ C) atTop atTop :=
  tendsto_atTop_of_div_positive (lowerSaddleM_tendsto_atTop hm) (lowerSaddleOmegaZero_div_M_limit hm θ C) hθ

section
variable (d m θ C x : ℝ)

theorem lowerSaddleGrid_positive : 0 < (lowerSaddleGrid d m θ C x : ℝ) := by
  have hh := Nat.le_ceil (lowerSaddleGridBase d m θ C x)
  exact (Real.exp_pos _).trans_le hh

theorem lowerSaddleH_positive : 0 < lowerSaddleH d m θ C x :=
  inv_pos.2 (lowerSaddleGrid_positive d m θ C x)

end

section
variable {d m θ : ℝ}
    (hd : 0 < d) (hm : 0 < m) (hθ : 0 < θ) (C : ℝ)
include hd hm hθ

theorem lowerSaddleGridBase_tendsto_atTop :
    Tendsto (lowerSaddleGridBase d m θ C) atTop atTop := by
  exact Real.tendsto_exp_atTop.comp
    ((Real.tendsto_log_atTop.atTop_add_atTop (lowerSaddleOmegaZero_tendsto_atTop hm hθ C)).atTop_div_const hd)

theorem lowerSaddleGrid_tendsto_atTop :
    Tendsto (fun x : ℝ => (lowerSaddleGrid d m θ C x : ℝ)) atTop atTop := by
  apply tendsto_atTop_mono (fun x => Nat.le_ceil _)
  exact lowerSaddleGridBase_tendsto_atTop hd hm hθ C

theorem lowerSaddleGrid_div_base_limit :
    Tendsto (fun x : ℝ => (lowerSaddleGrid d m θ C x : ℝ) / lowerSaddleGridBase d m θ C x)
      atTop (𝓝 1) :=
  tendsto_nat_ceil_div_atTop.comp (lowerSaddleGridBase_tendsto_atTop hd hm hθ C)

theorem lowerSaddleOmega_rounding_limit :
    Tendsto (fun x : ℝ => lowerSaddleOmega d m θ C x - lowerSaddleOmegaZero m θ C x)
      atTop (𝓝 0) := by
  have hh := ((Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp
    (lowerSaddleGrid_div_base_limit hd hm hθ C)).const_mul d
  simp only [Real.log_one, mul_zero] at hh
  refine hh.congr (fun x => ?_)
  simp only [Function.comp_apply]
  rw [Real.log_div (lowerSaddleGrid_positive d m θ C x).ne'
    (show lowerSaddleGridBase d m θ C x ≠ 0 from (Real.exp_pos _).ne')]
  unfold lowerSaddleGridBase lowerSaddleOmega
  grind [Real.log_exp]

end

section
variable {d m θ C x : ℝ}

theorem lowerSaddleOmegaZero_le (hd : 0 < d) :
    lowerSaddleOmegaZero m θ C x ≤ lowerSaddleOmega d m θ C x := by
  have h := Real.log_le_log (Real.exp_pos _) (Nat.le_ceil (lowerSaddleGridBase d m θ C x))
  change Real.log (lowerSaddleGridBase d m θ C x) ≤ Real.log (lowerSaddleGrid d m θ C x) at h
  rw [lowerSaddleGridBase, Real.log_exp, div_le_iff₀ hd] at h
  unfold lowerSaddleOmega
  linarith

theorem lowerSaddleMu_eq_exp (hx : 0 < x) :
    lowerSaddleMu d m θ C x = Real.exp (-lowerSaddleOmega d m θ C x) := by
  unfold lowerSaddleMu
  calc
    _ = Real.exp (Real.log x) * Real.exp (Real.log (lowerSaddleH d m θ C x) * d) := by
      rw [Real.exp_log hx, Real.rpow_def_of_pos (lowerSaddleH_positive d m θ C x)]
    _ = Real.exp (Real.log x + Real.log (lowerSaddleH d m θ C x) * d) := (Real.exp_add _ _).symm
    _ = _ := by
      congr 1
      unfold lowerSaddleH lowerSaddleOmega
      grind [Real.log_inv]

private theorem log_lowerSaddleH (hd : d ≠ 0) :
    Real.log (lowerSaddleH d m θ C x) = -(Real.log x + lowerSaddleOmega d m θ C x) / d := by
  unfold lowerSaddleH lowerSaddleOmega
  rw [Real.log_inv]
  field_simp
  ring

end

section
variable {d m θ : ℝ}
    (hd : 0 < d) (hm : 0 < m) (hθ : 0 < θ) (C : ℝ)
include hd hm hθ

theorem lowerSaddleOmega_div_M_limit :
    Tendsto (fun x : ℝ => lowerSaddleOmega d m θ C x / lowerSaddleM m x) atTop (𝓝 θ) := by
  have hr := (lowerSaddleOmega_rounding_limit hd hm hθ C).mul
    (lowerSaddleM_tendsto_atTop hm).inv_tendsto_atTop
  have hh := (lowerSaddleOmegaZero_div_M_limit hm θ C).add hr
  simp only [mul_zero, add_zero] at hh
  convert! hh using 1
  simp_all <;> field_simp <;> ring

theorem lowerSaddleOmega_tendsto_atTop :
    Tendsto (lowerSaddleOmega d m θ C) atTop atTop :=
  tendsto_atTop_of_div_positive (lowerSaddleM_tendsto_atTop hm) (lowerSaddleOmega_div_M_limit hd hm hθ C) hθ

end

theorem lowerSaddleM_div_log_limit {m : ℝ} (hm : 0 < m) :
    Tendsto (fun x : ℝ => (lowerSaddleM m x : ℝ) / Real.log x) atTop (𝓝 0) := by
  simpa using tendsto_ratio_comp (lowerSaddleM_div_sqrt_log_limit hm) tendsto_sqrt_log_div_log
    ((eventually_gt_atTop (1 : ℝ)).mono fun _ hx => (Real.sqrt_pos.2 (Real.log_pos hx)).ne')

theorem lowerSaddleOmega_div_log_limit {d m θ : ℝ}
    (hd : 0 < d) (hm : 0 < m) (hθ : 0 < θ) (C : ℝ) :
    Tendsto (fun x : ℝ => lowerSaddleOmega d m θ C x / Real.log x) atTop (𝓝 0) := by
  simpa using tendsto_ratio_comp (lowerSaddleOmega_div_M_limit hd hm hθ C) (lowerSaddleM_div_log_limit hm)
    ((eventually_lowerSaddleM_pos hm).mono fun _ hx => hx.ne')

/-- `τM` denotes the interval exponent evaluated at the actual natural degree. -/
def lowerSaddleN (s d m θ C : ℝ) (τM : ℕ → ℝ) (x : ℝ) : ℝ :=
  Real.exp (lowerSaddleLogN s d (Real.log x) (lowerSaddleOmega d m θ C x)
    (τM (lowerSaddleM m x)) (lowerSaddleM m x))

def lowerSaddleEta (s d m θ C cf x : ℝ) : ℝ := cf * (lowerSaddleH d m θ C x) ^ s

def lowerSaddleActivity (s d m θ C : ℝ) (τM : ℕ → ℝ) (x : ℝ) : ℝ :=
  (lowerSaddleN s d m θ C τM x) ^ 2 * Real.exp (τM (lowerSaddleM m x) * lowerSaddleM m x)

def lowerSaddleRisk (s d m θ C cf : ℝ) (τM : ℕ → ℝ) (x : ℝ) : ℝ :=
  (lowerSaddleEta s d m θ C cf x) ^ 2 / lowerSaddleActivity s d m θ C τM x

def lowerSaddleEnergyOne (s d m θ C : ℝ) (τM : ℕ → ℝ) (x : ℝ) : ℝ :=
  x ^ (2 : ℕ) * (lowerSaddleH d m θ C x) ^ (d + 4 * s) *
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

section
variable (s d m θ C : ℝ) (τM : ℕ → ℝ) (x : ℝ)

theorem lowerSaddleN_positive :
    0 < lowerSaddleN s d m θ C τM x := Real.exp_pos _

theorem lowerSaddleActivity_positive :
    0 < lowerSaddleActivity s d m θ C τM x := mul_pos (sq_pos_of_pos (lowerSaddleN_positive s d m θ C τM x)) (Real.exp_pos _)

end

section
variable {s d m θ C x : ℝ} {τM : ℕ → ℝ}

private theorem log_lowerSaddleN :
    Real.log (lowerSaddleN s d m θ C τM x) =
      lowerSaddleLogN s d (Real.log x) (lowerSaddleOmega d m θ C x)
        (τM (lowerSaddleM m x)) (lowerSaddleM m x) := Real.log_exp _

private theorem log_lowerSaddleActivity :
    Real.log (lowerSaddleActivity s d m θ C τM x) =
      2 * Real.log (lowerSaddleN s d m θ C τM x) + τM (lowerSaddleM m x) * lowerSaddleM m x := by
  have hN := lowerSaddleN_positive s d m θ C τM x
  simp (disch := positivity) only [lowerSaddleActivity, Real.log_mul, Real.log_pow,
    Real.log_exp, Nat.cast_ofNat]

section
variable {cf : ℝ} (hcf : 0 < cf)
include hcf

private theorem lowerSaddleEta_positive : 0 < lowerSaddleEta s d m θ C cf x :=
  mul_pos hcf (Real.rpow_pos_of_pos (lowerSaddleH_positive d m θ C x) s)

private theorem log_lowerSaddleEta :
    Real.log (lowerSaddleEta s d m θ C cf x) = Real.log cf + s * Real.log (lowerSaddleH d m θ C x) := by
  have hH := lowerSaddleH_positive d m θ C x
  simp (disch := positivity) only [lowerSaddleEta, Real.log_mul, Real.log_rpow]

end

theorem lowerSaddleEnergyOne_eq_activity_sq
    (hd : 0 < d) (hd4 : d + 4 ≠ 0) (hx : 0 < x) (τM : ℕ → ℝ) :
    lowerSaddleEnergyOne s d m θ C τM x = (lowerSaddleActivity s d m θ C τM x) ^ 2 := by
  have hH := lowerSaddleH_positive d m θ C x
  have hN := lowerSaddleN_positive s d m θ C τM x
  have hA := lowerSaddleActivity_positive s d m θ C τM x
  apply Real.log_injOn_pos (show 0 < _ by unfold lowerSaddleEnergyOne; positivity)
    (show 0 < _ by positivity)
  simp (disch := positivity) only [lowerSaddleEnergyOne, Real.log_mul, Real.log_pow,
    Real.log_rpow, log_lowerSaddleH hd.ne', log_lowerSaddleActivity, log_lowerSaddleN,
    lowerSaddleLogN, Nat.cast_ofNat]
  field_simp
  ring

end

/-- The fixed endpoint estimate `τ≤τ_M≤τ+Cτ/M`, expressed without division. -/
def LowerExponentControl (τM : ℕ → ℝ) (τ Cτ : ℝ) : Prop :=
  ∀ᶠ M : ℕ in atTop, τ ≤ τM M ∧ (τM M - τ) * (M : ℝ) ≤ Cτ

theorem lowerSaddleM_nat_tendsto_atTop {m : ℝ} (hm : 0 < m) :
    Tendsto (lowerSaddleM m) atTop atTop :=
  tendsto_natCast_atTop_iff.1 (lowerSaddleM_tendsto_atTop hm)

theorem lowerSaddleTau_limit {m τ Cτ : ℝ} {τM : ℕ → ℝ}
    (hm : 0 < m) (hcontrol : LowerExponentControl τM τ Cτ) :
    Tendsto (fun x : ℝ => τM (lowerSaddleM m x)) atTop (𝓝 τ) := by
  have ht := lowerSaddleM_tendsto_atTop hm
  have he := (lowerSaddleM_nat_tendsto_atTop hm).eventually hcontrol
  have hu := ht.const_div_atTop Cτ
  have hh : Tendsto (fun x : ℝ => τM (lowerSaddleM m x) - τ) atTop (𝓝 0) := by
    apply squeeze_zero' (he.mono fun x hx => sub_nonneg.2 hx.1) _ hu
    filter_upwards [he, ht.eventually (eventually_gt_atTop (0 : ℝ))] with x hx hM
    exact (le_div_iff₀ hM).2 hx.2
  simpa using hh.add_const τ

section
variable {d m θ τ Cτ : ℝ} {τM : ℕ → ℝ}
    (hd : 0 < d) (hm : 0 < m) (hθ : 0 < θ)
    (hcontrol : LowerExponentControl τM τ Cτ) (s C : ℝ)
include hd hm hθ hcontrol

theorem lowerSaddleLogN_div_log_limit :
    Tendsto (fun x : ℝ => Real.log (lowerSaddleN s d m θ C τM x) / Real.log x)
      atTop (𝓝 ((d - 4 * s) / (d * (d + 4)))) := by
  have hcost := (lowerSaddleTau_limit hm hcontrol).mul (lowerSaddleM_div_log_limit hm)
  have homega := (lowerSaddleOmega_div_log_limit hd hm hθ C).const_mul (1 + 4 * s / d)
  have hh := (((tendsto_const_nhds (x := (d - 4 * s) / d)).sub homega).sub
    (hcost.const_mul 2)).div_const (d + 4)
  simp only [mul_zero, sub_zero] at hh
  rw [div_div] at hh
  refine hh.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  unfold lowerSaddleN lowerSaddleLogN
  rw [Real.log_exp]
  field_simp [(Real.log_pos hx).ne']

theorem lowerSaddleLogN_div_M_sq_limit :
    Tendsto (fun x : ℝ => Real.log (lowerSaddleN s d m θ C τM x) / (lowerSaddleM m x : ℝ) ^ 2)
      atTop (𝓝 (((d - 4 * s) / (d * (d + 4))) / m ^ 2)) := by
  exact tendsto_ratio_div (lowerSaddleLogN_div_log_limit hd hm hθ hcontrol s C)
    (lowerSaddleM_sq_div_log_limit hm) (pow_ne_zero 2 hm.ne')
    ((eventually_gt_atTop (1 : ℝ)).mono fun _ hx => (Real.log_pos hx).ne')

end

theorem lowerSaddleN_tendsto_atTop {s d m θ τ Cτ : ℝ} {τM : ℕ → ℝ}
    (hs : 1 < s) (hd : 4 * s < d) (hm : 0 < m) (hθ : 0 < θ)
    (hcontrol : LowerExponentControl τM τ Cτ) (C : ℝ) :
    Tendsto (lowerSaddleN s d m θ C τM) atTop atTop := by
  have hd0 : 0 < d := by linarith
  exact (LogSlope.mk (.of_forall (lowerSaddleN_positive s d m θ C τM))
    (lowerSaddleLogN_div_log_limit hd0 hm hθ hcontrol s C)).tends_top Real.tendsto_log_atTop (by positivity)

section
variable {d m θ : ℝ}
    (hd : 0 < d) (hm : 0 < m) (hθ : 0 < θ) (C : ℝ)
include hd hm hθ

theorem lowerSaddleMu_tends_zero :
    Tendsto (lowerSaddleMu d m θ C) atTop (𝓝 0) := by
  have hh := Real.tendsto_exp_atBot.comp
    (tendsto_neg_atTop_atBot.comp (lowerSaddleOmega_tendsto_atTop hd hm hθ C))
  refine hh.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  exact (lowerSaddleMu_eq_exp hx).symm

theorem lowerSaddleH_tends_zero :
    Tendsto (lowerSaddleH d m θ C) atTop (𝓝 0) := (lowerSaddleGrid_tendsto_atTop hd hm hθ C).inv_tendsto_atTop

end

theorem lowerSaddleEta_tends_zero {s d m θ : ℝ}
    (hs : 0 < s) (hd : 0 < d) (hm : 0 < m) (hθ : 0 < θ) (C cf : ℝ) :
    Tendsto (lowerSaddleEta s d m θ C cf) atTop (𝓝 0) := by
  have hh := ((lowerSaddleH_tends_zero hd hm hθ C).rpow_const (Or.inr hs.le)).const_mul cf
  simpa only [Real.zero_rpow hs.ne', mul_zero] using! hh

section
variable {d m θ : ℝ} (hd : 0 < d) (hm : 0 < m) (hθ : 0 < θ) (C : ℝ)
include hd hm hθ

theorem lowerSaddleMu_logSlope :
    LogSlope atTop (fun x => (lowerSaddleM m x : ℝ)) (lowerSaddleMu d m θ C) (-θ) := by
  have ht : Tendsto (fun x => -lowerSaddleOmega d m θ C x / (lowerSaddleM m x : ℝ)) atTop (𝓝 (-θ)) := by
    simpa only [neg_div] using (lowerSaddleOmega_div_M_limit hd hm hθ C).neg
  apply (LogSlope.exp ht).congr
  exact (eventually_gt_atTop 0).mono fun x hx => (lowerSaddleMu_eq_exp hx).symm

theorem lowerSaddleM_mul_mu_tends_zero :
    Tendsto (fun x : ℝ => (lowerSaddleM m x : ℝ) * lowerSaddleMu d m θ C x) atTop (𝓝 0) :=
  ((LogSlope.self (lowerSaddleM_tendsto_atTop hm)).mul
    (lowerSaddleMu_logSlope hd hm hθ C)).tends_zero (lowerSaddleM_tendsto_atTop hm) (by linarith)

end

section
variable {s d m θ C cf x : ℝ}

theorem lowerSaddleRisk_positive (hcf : 0 < cf) (τM : ℕ → ℝ) :
    0 < lowerSaddleRisk s d m θ C cf τM x :=
  div_pos (sq_pos_of_pos (lowerSaddleEta_positive hcf)) (lowerSaddleActivity_positive s d m θ C τM x)

theorem log_lowerSaddleRisk
    (hs : 1 < s) (hd : 4 * s < d) (hcf : 0 < cf) (τM : ℕ → ℝ) :
    Real.log (lowerSaddleRisk s d m θ C cf τM x) =
      2 * Real.log cf - rateExponent s d * Real.log x -
        (2 * (s - 1) * lowerSaddleOmega d m θ C x +
          d * τM (lowerSaddleM m x) * lowerSaddleM m x) / (d + 4) := by
  have hd0 : 0 < d := by linarith
  have hEta := lowerSaddleEta_positive (s := s) (d := d) (m := m) (θ := θ) (C := C) (x := x) hcf
  have hA := lowerSaddleActivity_positive s d m θ C τM x
  simp (disch := positivity) only [lowerSaddleRisk, Real.log_div, Real.log_pow, Nat.cast_ofNat,
    log_lowerSaddleEta hcf, log_lowerSaddleH hd0.ne', log_lowerSaddleActivity, log_lowerSaddleN]
  have hh := lower_saddle_rate hs hd (Real.log x) (lowerSaddleOmega d m θ C x)
    (τM (lowerSaddleM m x)) (lowerSaddleM m x)
  linear_combination hh

end

theorem log_factorial_succ_lower (M : ℕ) (hM : 1 ≤ M) :
    (M : ℝ) * Real.log M - M ≤ Real.log ((M + 1).factorial : ℝ) := by
  have hs := Stirling.le_log_factorial_stirling (Nat.ne_of_gt (by omega : 0 < M))
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg (by simp_all)
  have hlogpi : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hfac : (M.factorial : ℝ) ≤ ((M + 1).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (Nat.le_succ M)
  have hl := Real.log_le_log (by positivity : 0 < (M.factorial : ℝ)) hfac
  linarith

private theorem log_saddle_count_base {d m θ C CG x : ℝ} (hx : 0 < x) (hCG : 0 < CG) :
    Real.log (CG * lowerSaddleMu d m θ C x) = Real.log CG - lowerSaddleOmega d m θ C x := by
  rw [lowerSaddleMu_eq_exp hx, Real.log_mul hCG.ne' (Real.exp_pos _).ne', Real.log_exp, sub_eq_add_neg]

private theorem log_lowerSaddleEnergyTwo_ratio {s d m θ C CG x : ℝ}
    (hd : 0 < d) (hCG : 0 < CG) (hx : 0 < x) (τM : ℕ → ℝ) :
    Real.log (lowerSaddleEnergyTwo s d m θ C CG τM x /
      (lowerSaddleActivity s d m θ C τM x) ^ 2) =
    4 * ((d - 4 * s) / (d * (d + 4))) * Real.log x +
      ((d ^ 2 - 16 * s) / (d * (d + 4)) - lowerSaddleM m x) * lowerSaddleOmega d m θ C x +
      (2 * d * τM (lowerSaddleM m x) / (d + 4) + Real.log CG) * lowerSaddleM m x -
      Real.log ((lowerSaddleM m x + 1).factorial : ℝ) := by
  have hH := lowerSaddleH_positive d m θ C x
  have hN := lowerSaddleN_positive s d m θ C τM x
  have hA := lowerSaddleActivity_positive s d m θ C τM x
  have hMu : 0 < lowerSaddleMu d m θ C x := mul_pos hx (Real.rpow_pos_of_pos hH _)
  simp (disch := positivity) only [lowerSaddleEnergyTwo, Real.log_div, Real.log_mul, Real.log_rpow,
    Real.log_pow, Real.log_exp, log_saddle_count_base hx hCG, log_lowerSaddleH hd.ne',
    log_lowerSaddleActivity, log_lowerSaddleN, lowerSaddleLogN, Nat.cast_ofNat]
  field_simp
  ring

theorem lowerSaddleM_square_balance {m θ γ x : ℝ}
    (hm : 0 < m) (hθ : 0 < θ) (hbalance : θ * m ^ 2 = 4 * γ)
    (hx : 1 ≤ x) : 4 * γ * Real.log x ≤ θ * (lowerSaddleM m x : ℝ) ^ 2 := by
  have hr := (lowerSaddleM_rounding (x := x) hm.le).1
  have hsq := (sq_le_sq₀ (by positivity : 0 ≤ m * Real.sqrt (Real.log x)) (by positivity)).2 hr
  rw [mul_pow, Real.sq_sqrt (Real.log_nonneg hx)] at hsq
  have hh := mul_le_mul_of_nonneg_left hsq hθ.le
  simp_all [← mul_assoc]

theorem lowerSaddleEnergyTwo_ratio_tends_zero {s d m θ C CG τ Cτ : ℝ} {τM : ℕ → ℝ}
    (hd : 0 < d) (hm : 0 < m) (hθ : 0 < θ) (hCG : 0 < CG)
    (hcontrol : LowerExponentControl τM τ Cτ)
    (hbalance : θ * m ^ 2 = 4 * ((d - 4 * s) / (d * (d + 4))))
    (hC : 1 + Real.log CG + (d ^ 2 - 16 * s) / (d * (d + 4)) * θ +
      2 * d * τ / (d + 4) < C) :
    Tendsto (fun x : ℝ => lowerSaddleEnergyTwo s d m θ C CG τM x /
      (lowerSaddleActivity s d m θ C τM x) ^ 2) atTop (𝓝 0) := by
  let A := (d ^ 2 - 16 * s) / (d * (d + 4))
  have hω := (lowerSaddleOmega_div_M_limit hd hm hθ C).const_mul A
  have hτ := (((lowerSaddleTau_limit hm hcontrol).const_mul (2*d)).div_const (d+4)).add_const
    (Real.log CG + 1 - C)
  refine tendsto_zero_of_scaled_log_bound (lowerSaddleM_tendsto_atTop hm) (hω.add hτ)
    (by dsimp [A]; linarith) ?_ ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have := lowerSaddleH_positive d m θ C x
    have := lowerSaddleN_positive s d m θ C τM x
    unfold lowerSaddleEnergyTwo lowerSaddleMu
    positivity
  · filter_upwards [eventually_gt_atTop (1 : ℝ),
      (lowerSaddleM_nat_tendsto_atTop hm).eventually (eventually_ge_atTop 1)] with x hx hM
    have hMpos : 0 < (lowerSaddleM m x : ℝ) := by positivity
    have hf := log_factorial_succ_lower _ hM
    have hωx := mul_le_mul_of_nonneg_left (lowerSaddleOmegaZero_le (m := m) (θ := θ) (C := C) (x := x) hd) hMpos.le
    have hb := lowerSaddleM_square_balance hm hθ hbalance hx.le
    rw [log_lowerSaddleEnergyTwo_ratio hd hCG (by linarith) τM]
    simp only [add_mul, mul_assoc A, div_mul_cancel₀ _ hMpos.ne']
    unfold A lowerSaddleOmegaZero at *
    nlinarith

theorem lowerSaddleD_div_M_limit {d m : ℝ} (hd : 0 < d) (hm : 0 < m) :
    Tendsto (fun x : ℝ => (lowerSaddleD d m x : ℝ) / lowerSaddleM m x)
      atTop (𝓝 ((d + 8) / 4)) :=
  (tendsto_nat_ceil_mul_div_atTop (by positivity)).comp (lowerSaddleM_tendsto_atTop hm)

private theorem log_lowerSaddleEnergyThree_ratio {s d m θ C CG x : ℝ}
    (hd : 0 < d) (hCG : 0 < CG) (hx : 0 < x) (τM : ℕ → ℝ) :
    Real.log (lowerSaddleEnergyThree s d m θ C CG τM x /
      (lowerSaddleActivity s d m θ C τM x) ^ 2) =
      (1 - 4 * s / d) * Real.log x - 4 * s / d * lowerSaddleOmega d m θ C x +
      (lowerSaddleD d m x : ℝ) * (Real.log CG - lowerSaddleOmega d m θ C x) -
        Real.log ((lowerSaddleD d m x + 1).factorial : ℝ) := by
  have hH := lowerSaddleH_positive d m θ C x
  have hA := lowerSaddleActivity_positive s d m θ C τM x
  have hMu : 0 < lowerSaddleMu d m θ C x := mul_pos hx (Real.rpow_pos_of_pos hH _)
  simp (disch := positivity) only [lowerSaddleEnergyThree, Real.log_div, Real.log_mul, Real.log_rpow,
    Real.log_pow, log_saddle_count_base hx hCG, log_lowerSaddleH hd.ne', Nat.cast_ofNat]
  ring

/-- The genuine high-count factorial energy is negligible relative to squared activity. -/
theorem lowerSaddleEnergyThree_ratio_tends_zero {s d m θ C CG : ℝ} {τM : ℕ → ℝ}
    (hs : 1 < s) (hd : 4 * s < d) (hm : 0 < m) (hθ : 0 < θ) (hCG : 0 < CG)
    (hbalance : θ * m ^ 2 = 4 * ((d - 4 * s) / (d * (d + 4)))) :
    Tendsto (fun x : ℝ => lowerSaddleEnergyThree s d m θ C CG τM x /
      (lowerSaddleActivity s d m θ C τM x) ^ 2) atTop (𝓝 0) := by
  have hd0 : 0 < d := by linarith
  have hc : 1 - 4 * s / d - (d + 8) / 4 * θ * m ^ 2 < 0 := by
    rw [mul_assoc ((d + 8) / 4), hbalance]
    field_simp <;> linarith
  have hD := lowerSaddleD_div_M_limit hd0 hm
  have hω := lowerSaddleOmega_div_M_limit hd0 hm hθ C
  have hM := lowerSaddleM_sq_div_log_limit hm
  have hconst := (lowerSaddleM_tendsto_atTop hm).const_div_atTop (Real.log CG)
  refine tendsto_zero_of_scaled_log_bound Real.tendsto_log_atTop
    (tendsto_const_nhds (x := 1-4*s/d) |>.add ((hD.mul (hconst.sub hω)).mul hM)) (by simpa using hc) ?_ ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have := lowerSaddleH_positive d m θ C x
    unfold lowerSaddleEnergyThree lowerSaddleMu
    positivity
  · filter_upwards [eventually_gt_atTop (1 : ℝ), eventually_lowerSaddleM_pos hm,
      (lowerSaddleOmega_tendsto_atTop hd0 hm hθ C).eventually (eventually_ge_atTop (0 : ℝ))] with x hx hMx hωx
    rw [log_lowerSaddleEnergyThree_ratio hd0 hCG (zero_lt_one.trans hx) τM]
    have hf : 0 ≤ Real.log ((lowerSaddleD d m x + 1).factorial : ℝ) := Real.log_nonneg (by exact_mod_cast Nat.factorial_pos _)
    have hdiff : 0 ≤ 4*s/d*lowerSaddleOmega d m θ C x := by positivity
    calc
      _ ≤ (1 - 4*s/d)*Real.log x + (lowerSaddleD d m x : ℝ) *
          (Real.log CG - lowerSaddleOmega d m θ C x) := by linarith
      _ = _ := by
        field_simp [hMx.ne', (Real.log_pos hx).ne']

/-- The combined explicit numerical energy envelope is at most `3 CG B²` eventually. -/
theorem eventually_lowerSaddle_numeric_cost {s d m θ C CG τ Cτ : ℝ} {τM : ℕ → ℝ}
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
  have htwo := lowerSaddleEnergyTwo_ratio_tends_zero hd0 hm hθ hCG hcontrol hbalance hC
  have hthree := lowerSaddleEnergyThree_ratio_tends_zero (C := C) (τM := τM) hs hd hm hθ hCG hbalance
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    htwo.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    hthree.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with x hx h2 h3
  have hA :=
    sq_pos_of_pos (lowerSaddleActivity_positive s d m θ C τM x)
  have h2' := (div_lt_iff₀ hA).1 h2
  have h3' := (div_lt_iff₀ hA).1 h3
  rw [lowerSaddleEnergyOne_eq_activity_sq hd0 (by linarith) hx τM]
  calc
    _ ≤ CG * (3 * (lowerSaddleActivity s d m θ C τM x) ^ 2) :=
      mul_le_mul_of_nonneg_left (by linarith only [h2', h3']) hCG.le
    _ = _ := by ring

theorem lowerSaddleRisk_residual_identity {s d m θ C cf τ x : ℝ} (τM : ℕ → ℝ)
    (hs : 1 < s) (hd : 4 * s < d) (hcf : 0 < cf)
    (hθrelation : 2 * (s - 1) * θ = d * τ) :
    Real.log (lowerSaddleRisk s d m θ C cf τM x) -
      rateLog (rateExponent s d) (2 * d * τ / (d + 4) * m) (lowerLogPower s d) x =
      (2 * Real.log cf - 2 * (s - 1) / (d + 4) * C) -
      (2 * d * τ / (d + 4)) * ((lowerSaddleM m x : ℝ) - m * Real.sqrt (Real.log x)) +
      (2 * (s - 1) / (d + 4)) * (Real.log (lowerSaddleM m x) - Real.log (Real.log x) / 2) -
      (2 * (s - 1) / (d + 4)) * (lowerSaddleOmega d m θ C x - lowerSaddleOmegaZero m θ C x) -
      (d / (d + 4)) * ((τM (lowerSaddleM m x) - τ) * lowerSaddleM m x) := by
  rw [log_lowerSaddleRisk hs hd hcf τM]
  unfold rateLog lowerLogPower lowerSaddleOmegaZero
  grind

section
variable {s d m θ C cf τ Cτ : ℝ} {τM : ℕ → ℝ}
    (hs : 1 < s) (hd : 4 * s < d) (hm : 0 < m) (hθ : 0 < θ) (hcf : 0 < cf)
    (hcontrol : LowerExponentControl τM τ Cτ) (hθrelation : 2 * (s - 1) * θ = d * τ)
include hs hd hm hθ hcf hcontrol hθrelation

theorem lowerSaddleRisk_residual_isBigO :
    (fun x : ℝ => Real.log (lowerSaddleRisk s d m θ C cf τM x) -
      rateLog (rateExponent s d) (2 * d * τ / (d + 4) * m) (lowerLogPower s d) x)
      =O[atTop] (fun _ : ℝ => (1 : ℝ)) := by
  have hd0 : 0 < d := by linarith
  have hceil : (fun x : ℝ => (lowerSaddleM m x : ℝ) - m * Real.sqrt (Real.log x))
      =O[atTop] (fun _ : ℝ => (1 : ℝ)) := by
    apply Asymptotics.IsBigO.of_bound 1
    filter_upwards [] with x
    simp only [Real.norm_eq_abs, norm_one, mul_one]
    rw [abs_of_nonneg (sub_nonneg.2 (lowerSaddleM_rounding hm.le).1)]
    linarith [(lowerSaddleM_rounding (x := x) hm.le).2]
  have hlog := (log_lowerSaddleM_residual_limit hm).isBigO_one ℝ
  have hω := (lowerSaddleOmega_rounding_limit hd0 hm hθ C).isBigO_one ℝ
  have hτ : (fun x : ℝ => (τM (lowerSaddleM m x) - τ) * lowerSaddleM m x)
      =O[atTop] (fun _ : ℝ => (1 : ℝ)) := by
    apply Asymptotics.IsBigO.of_bound Cτ
    filter_upwards [(lowerSaddleM_nat_tendsto_atTop hm).eventually hcontrol] with x hx
    simp only [Real.norm_eq_abs, norm_one, mul_one]
    rw [abs_of_nonneg (mul_nonneg (sub_nonneg.2 hx.1) (by positivity))]
    linarith
  have hc := Asymptotics.isBigO_const_one
    (2 * Real.log cf - 2 * (s - 1) / (d + 4) * C) (atTop : Filter ℝ) (F := ℝ)
  have hh := (((hc.sub (hceil.const_mul_left (2 * d * τ / (d + 4)))).add
    (hlog.const_mul_left (2 * (s - 1) / (d + 4)))).sub
    (hω.const_mul_left (2 * (s - 1) / (d + 4)))).sub (hτ.const_mul_left (d / (d + 4)))
  exact hh.congr_left (fun x => (lowerSaddleRisk_residual_identity τM hs hd hcf hθrelation).symm)

/-- The actual rounded numeric risk is comparable to the exact displayed saddle scale. -/
theorem eventually_lowerSaddleRisk_rate_bracket :
    ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∀ᶠ x : ℝ in atTop,
      c * rateScale (rateExponent s d) (2 * d * τ / (d + 4) * m) (lowerLogPower s d) x ≤
        lowerSaddleRisk s d m θ C cf τM x ∧
      lowerSaddleRisk s d m θ C cf τM x ≤
        A * rateScale (rateExponent s d) (2 * d * τ / (d + 4) * m) (lowerLogPower s d) x := by
  obtain ⟨K, hK⟩ := (lowerSaddleRisk_residual_isBigO hs hd hm hθ hcf hcontrol hθrelation).bound
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

end

def lowerSaddleTheta (s d τ : ℝ) : ℝ := d * τ / (2 * (s - 1))

section
variable {s d τ : ℝ}
    (hs : 1 < s)
include hs

section
variable (hd : 4 * s < d) (hτ : 0 < τ)
include hd hτ

theorem lowerSaddleCoefficient_pos :
    0 < lowerSaddleCoefficient s d τ := by
  have hd0 : 0 < d := by linarith
  unfold lowerSaddleCoefficient
  apply Real.sqrt_pos.2
  positivity

theorem lowerSaddleTheta_pos : 0 < lowerSaddleTheta s d τ := by
  have hd0 : 0 < d := by linarith
  unfold lowerSaddleTheta
  positivity

end

theorem lowerSaddleTheta_relation :
    2 * (s - 1) * lowerSaddleTheta s d τ = d * τ := by
  unfold lowerSaddleTheta
  grind

theorem lowerSaddle_canonical_balance (hd : 4 * s < d) (hτ : 0 < τ) :
    lowerSaddleTheta s d τ * (lowerSaddleCoefficient s d τ) ^ 2 =
      4 * ((d - 4 * s) / (d * (d + 4))) := by
  have hd0 : 0 < d := by linarith
  have hp : 0 ≤ 8 * (d - 4 * s) * (s - 1) / (d ^ 2 * (d + 4) * τ) := by positivity
  unfold lowerSaddleTheta lowerSaddleCoefficient
  rw [Real.sq_sqrt hp]
  field_simp [show s - 1 ≠ 0 by linarith]
  ring

end

/-- The exact shrunk-endpoint exponent supplies the saddle's fixed control hypothesis. -/
theorem exists_actual_lowerExponentControl {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∃ Cτ : ℝ, 0 ≤ Cτ ∧ LowerExponentControl (shrunkDensityExponent a b)
      (densityIntervalExponent a b) Cτ := exists_shrunkDensityExponent_control ha hab

/-- With all the paper's fixed constants substituted, the actual risk has its displayed rate. -/
theorem actual_lowerSaddleRisk_rate_bracket {s d a b cf : ℝ}
    (hs : 1 < s) (hd : 4 * s < d) (ha : 0 < a) (hab : a < b) (hcf : 0 < cf) (C : ℝ) :
    ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∀ᶠ x : ℝ in atTop,
      c * rateScale (rateExponent s d) (stretchConstant s d (densityIntervalExponent a b))
        (lowerLogPower s d) x ≤
      lowerSaddleRisk s d (lowerSaddleCoefficient s d (densityIntervalExponent a b))
        (lowerSaddleTheta s d (densityIntervalExponent a b)) C cf (shrunkDensityExponent a b) x ∧
      lowerSaddleRisk s d (lowerSaddleCoefficient s d (densityIntervalExponent a b))
        (lowerSaddleTheta s d (densityIntervalExponent a b)) C cf (shrunkDensityExponent a b) x ≤
      A * rateScale (rateExponent s d) (stretchConstant s d (densityIntervalExponent a b))
        (lowerLogPower s d) x := by
  have hτ := densityIntervalExponent_pos ha hab
  obtain ⟨Cτ, _, hcontrol⟩ := exists_actual_lowerExponentControl ha hab
  have hh := eventually_lowerSaddleRisk_rate_bracket (C := C)
    hs hd (lowerSaddleCoefficient_pos hs hd hτ) (lowerSaddleTheta_pos hs hd hτ) hcf hcontrol
    (lowerSaddleTheta_relation hs)
  simpa only [lower_saddle_stretchConstant hs hd hτ] using hh

theorem log_lowerSaddleEta_div_log_limit {s d m θ cf : ℝ}
    (hd : 0 < d) (hm : 0 < m) (hθ : 0 < θ) (hcf : 0 < cf) (C : ℝ) :
    Tendsto (fun x : ℝ => Real.log (lowerSaddleEta s d m θ C cf x) / Real.log x)
      atTop (𝓝 (-s / d)) := by
  have hconst := tendsto_const_div_log (Real.log cf)
  have hω := lowerSaddleOmega_div_log_limit hd hm hθ C
  have hh := hconst.sub (((tendsto_const_nhds (x := (1 : ℝ))).add hω).const_mul (s / d))
  simp only [add_zero, mul_one, zero_sub, ← neg_div] at hh
  refine hh.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  rw [log_lowerSaddleEta hcf, log_lowerSaddleH hd.ne']
  field_simp [(Real.log_pos hx).ne']
  ring

def lowerSaddleResponseQuantity (s d m θ C cf : ℝ) (q : ℕ) (τM : ℕ → ℝ) (x : ℝ) : ℝ :=
  (lowerSaddleEta s d m θ C cf x) ^ (4 * q) * (lowerSaddleN s d m θ C τM x) ^ d

theorem lowerSaddleResponseQuantity_tends_zero {s d m θ cf τ Cτ : ℝ} {τM : ℕ → ℝ}
    (hs : 1 < s) (hd : 4 * s < d) (hm : 0 < m) (hθ : 0 < θ) (hcf : 0 < cf)
    (hcontrol : LowerExponentControl τM τ Cτ) (q : ℕ) (hq : d / (4 * s) - 1 ≤ (q : ℝ)) (C : ℝ) :
    Tendsto (lowerSaddleResponseQuantity s d m θ C cf q τM) atTop (𝓝 0) := by
  have hd0 : 0 < d := by linarith
  have hγ : 0 < (d - 4 * s) / (d * (d + 4)) := by positivity
  have hqmul : d ≤ 4 * s * ((q : ℝ) + 1) := by
    have hh : d / (4 * s) ≤ (q : ℝ) + 1 := by linarith
    simpa only [mul_comm] using (div_le_iff₀ (by positivity : 0 < 4 * s)).1 hh
  have hc : (4 * q : ℝ) * (-s / d) + d * ((d - 4 * s) / (d * (d + 4))) < 0 := by
    have hid : (4 * q : ℝ) * (-s / d) + d * ((d - 4 * s) / (d * (d + 4))) =
        -4 * ((d - 4 * s) / (d * (d + 4))) + (d - 4 * s * ((q : ℝ) + 1)) / d := by
      field_simp
      ring
    rw [hid]
    have hn : (d - 4 * s * ((q : ℝ) + 1)) / d ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hd0.le
    linarith
  have he : LogSlope atTop Real.log (lowerSaddleEta s d m θ C cf) (-s / d) :=
    ⟨.of_forall fun _ => lowerSaddleEta_positive hcf,
      log_lowerSaddleEta_div_log_limit hd0 hm hθ hcf C⟩
  have hn : LogSlope atTop Real.log (lowerSaddleN s d m θ C τM) ((d - 4 * s) / (d * (d + 4))) :=
    ⟨.of_forall (lowerSaddleN_positive s d m θ C τM), lowerSaddleLogN_div_log_limit hd0 hm hθ hcontrol s C⟩
  exact ((he.pow (4 * q)).mul (hn.rpow d)).tends_zero Real.tendsto_log_atTop (by exact_mod_cast hc)

def lowerSaddleResponseOrder (s d : ℝ) : ℕ := max 2 (Nat.floor (d / (4 * s)))

theorem lowerSaddleResponseOrder_bound {s d : ℝ} :
    d / (4 * s) - 1 ≤ (lowerSaddleResponseOrder s d : ℝ) := by
  have hfloor := Nat.lt_floor_add_one (d / (4 * s))
  have hmax : (Nat.floor (d / (4 * s)) : ℝ) ≤ lowerSaddleResponseOrder s d := by
    exact_mod_cast le_max_right 2 (Nat.floor (d / (4 * s)))
  linarith


/-- The remaining fixed grid and mass hypotheses of `lem:score-risk` hold eventually. -/
theorem eventually_lowerSaddle_grid_and_mass {d m θ cm Cmgf : ℝ}
    (hd : 0 < d) (hm : 0 < m) (hθ : 0 < θ) (hcm : 0 < cm) (hCmgf : 0 < Cmgf)
    (C : ℝ) (gridThreshold : ℕ) :
    ∀ᶠ x : ℝ in atTop, gridThreshold ≤ lowerSaddleGrid d m θ C x ∧
      8 * Cmgf * lowerSaddleMu d m θ C x ≤ cm / lowerSaddleM m x := by
  have hgrid :=
    tendsto_natCast_atTop_iff.1 (lowerSaddleGrid_tendsto_atTop hd hm hθ C)
  have hcap : 0 < cm / (8 * Cmgf) := by positivity
  filter_upwards [hgrid.eventually (eventually_ge_atTop gridThreshold),
    eventually_lowerSaddleM_pos hm,
    (lowerSaddleM_mul_mu_tends_zero hd hm hθ C).eventually (gt_mem_nhds hcap)] with x hx hM hmass
  refine ⟨hx, (le_div_iff₀ hM).2 ?_⟩
  have hh := (lt_div_iff₀ (by positivity : 0 < 8 * Cmgf)).1 hmass
  nlinarith only [hh]

theorem tendsto_sample_div_log : Tendsto (fun x : ℝ => x / Real.log x) atTop atTop := by
  have hh : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    simpa only [Real.rpow_one] using tendsto_log_power_div_sample 1
  have hwithin : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.2
    refine ⟨hh, ?_⟩
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact div_pos (Real.log_pos hx) (by linarith)
  apply hwithin.inv_tendsto_nhdsGT_zero.congr <;> simp_all

/-- The mass-tail envelope is negligible compared with the square of every displayed rate. -/
theorem exponential_sample_log_tail_over_rate_tends_zero {c : ℝ} (hc : 0 < c) (lam κ a : ℝ) :
    Tendsto (fun x : ℝ => 2 * Real.exp (-c * x / Real.log x) / (rateScale lam κ a x) ^ 2)
      atTop (𝓝 0) := by
  have hrate : Tendsto (fun x : ℝ => rateLog lam κ a x / Real.log x) atTop (𝓝 (-lam)) := by
    convert! (tendsto_normalized_log_scale lam κ a 0).neg using 1
    ring
  have hsq : Tendsto (fun x : ℝ => Real.log x / (x / Real.log x)) atTop (𝓝 0) := by
    simpa only [div_div_eq_mul_div, ← pow_two, Real.rpow_two] using tendsto_log_power_div_sample 2
  have hrate' := tendsto_ratio_comp hrate hsq
    ((eventually_gt_atTop (1 : ℝ)).mono fun _ hx => (Real.log_pos hx).ne')
  have hs := tendsto_sample_div_log
  have hexp : LogSlope atTop (fun x => x / Real.log x) (fun x => Real.exp (-c * x / Real.log x)) (-c) := by
    apply LogSlope.exp
    apply tendsto_const_nhds.congr'
    filter_upwards [hs.eventually (eventually_gt_atTop 0)] with x hx
    rw [mul_div_assoc, mul_div_cancel_right₀ _ hx.ne']
  have hr : LogSlope atTop (fun x => x / Real.log x) (rateScale lam κ a) 0 :=
    LogSlope.exp (by simpa using hrate')
  exact ((LogSlope.const hs (by norm_num : (0 : ℝ) < 2)).mul hexp |>.div (hr.pow 2)).tends_zero hs (by linarith)

def lowerSaddleExceptionalTail (d m θ C c x : ℝ) : ℝ :=
  2 * Real.exp (-c / ((lowerSaddleM m x : ℝ) ^ 2 * (lowerSaddleH d m θ C x) ^ d))

theorem eventually_lowerSaddle_mass_variance_bound {d m θ : ℝ}
    (hd : 0 < d) (hm : 0 < m) (hθ : 0 < θ) (C : ℝ) :
    ∀ᶠ x : ℝ in atTop,
      (lowerSaddleM m x : ℝ) ^ 2 * (lowerSaddleH d m θ C x) ^ d ≤
        2 * m ^ 2 * Real.log x / x := by
  have hsq := lowerSaddleM_sq_div_log_limit hm
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    hsq.eventually (gt_mem_nhds (by nlinarith : m ^ 2 < 2 * m ^ 2)),
    (lowerSaddleMu_tends_zero hd hm hθ C).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))]
    with x hx hM hMu
  have hx0 : 0 < x := by linarith
  have hH : (lowerSaddleH d m θ C x) ^ d ≤ 1 / x := by
    apply (le_div_iff₀ hx0).2
    unfold lowerSaddleMu at hMu
    linarith
  have hM' := (div_lt_iff₀ (Real.log_pos hx)).1 hM
  calc
    _ ≤ (lowerSaddleM m x : ℝ) ^ 2 * (1 / x) := mul_le_mul_of_nonneg_left hH (sq_nonneg _)
    _ ≤ 2 * m ^ 2 * Real.log x / x := by
      field_simp <;> linarith

section
variable {d m θ c : ℝ}
    (hd : 0 < d) (hm : 0 < m) (hθ : 0 < θ) (hc : 0 < c)
include hd hm hθ hc

theorem eventually_lowerSaddle_exceptionalTail_envelope (C : ℝ) :
    ∀ᶠ x : ℝ in atTop, lowerSaddleExceptionalTail d m θ C c x ≤
      2 * Real.exp (-(c / (2 * m ^ 2)) * x / Real.log x) := by
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    eventually_lowerSaddleM_pos hm,
    eventually_lowerSaddle_mass_variance_bound hd hm hθ C] with x hx hM hbound
  have hden :=
    mul_pos (sq_pos_of_pos hM) (Real.rpow_pos_of_pos (lowerSaddleH_positive d m θ C x) d)
  have hh := div_le_div_of_nonneg_left hc.le hden hbound
  have hid : c / (2 * m ^ 2 * Real.log x / x) = (c / (2 * m ^ 2)) * x / Real.log x := by field_simp
  rw [hid] at hh
  unfold lowerSaddleExceptionalTail
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  apply Real.exp_le_exp.2 <;> grind

/-- The paper's actual mass exception is `o(Psi²)`, without an exceptional-tail hypothesis. -/
theorem lowerSaddleExceptionalTail_over_rate_tends_zero (C lam κ a : ℝ) :
    Tendsto (fun x : ℝ => lowerSaddleExceptionalTail d m θ C c x / (rateScale lam κ a x) ^ 2)
      atTop (𝓝 0) := by
  have hb := exponential_sample_log_tail_over_rate_tends_zero
    (show 0 < c / (2 * m ^ 2) by positivity) lam κ a
  apply squeeze_zero' (Eventually.of_forall fun x => by
    unfold lowerSaddleExceptionalTail rateScale
    positivity) _ hb
  filter_upwards [eventually_lowerSaddle_exceptionalTail_envelope hd hm hθ hc C] with x hx
  gcongr

end

/-- The numerical cost estimate for the exact source parameters, including actual `τ_M`. -/
theorem eventually_actual_lowerSaddle_numeric_cost {s d a b CG C : ℝ}
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

/-- `epsilon_n` with the source's mass-tail coefficient is `o(Psi²)`. -/
theorem actual_lowerSaddle_exceptionalTail_over_Psi_tends_zero {s d a b cm Cmgf : ℝ}
    (hs : 1 < s) (hd : 4 * s < d) (ha : 0 < a) (hab : a < b)
    (hcm : 0 < cm) (hCmgf : 0 < Cmgf) (C : ℝ) :
    Tendsto (fun x : ℝ =>
      lowerSaddleExceptionalTail d (lowerSaddleCoefficient s d (densityIntervalExponent a b))
        (lowerSaddleTheta s d (densityIntervalExponent a b)) C (cm ^ 2 / (8 * Cmgf)) x /
        (rateScale (rateExponent s d) (stretchConstant s d (densityIntervalExponent a b))
          (lowerLogPower s d) x) ^ 2) atTop (𝓝 0) := by
  have hτ := densityIntervalExponent_pos ha hab
  exact lowerSaddleExceptionalTail_over_rate_tends_zero (by linarith)
    (lowerSaddleCoefficient_pos hs hd hτ) (lowerSaddleTheta_pos hs hd hτ)
    (by positivity) C (rateExponent s d) (stretchConstant s d (densityIntervalExponent a b)) (lowerLogPower s d)

end NearlyMinimax
