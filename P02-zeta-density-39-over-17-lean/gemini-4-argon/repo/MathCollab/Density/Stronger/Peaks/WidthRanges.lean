module
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Released under MIT-0; see ../../../../../third_party/twelfth/LICENSE-MIT-0.
Selected exact source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Provenance: ../../../../../third_party/twelfth/PEAK_AGGREGATION_MANIFEST.json.
Mathlib dependencies retain their Apache-2.0 attribution.
PointMeanInput and LocalMeanPacketInput remain explicit unproved analytic inputs.
No unconditional high-value, twelfth-moment or stronger-density bound is asserted.
-/
public import MathCollab.Density.Stronger.Peaks.ClusterCount

@[expose] public section

open Complex Filter MeasureTheory Set Topology Finset MathCollab.Density MathCollab.Density.Stronger
open scoped Interval
open TaoTrudgianYang2025 (eventually_const_log_pow_le_rpow
  eventually_const_height_log_pow_mul_rpow_le_rpow
  eventually_pointValue_sixth_power_source_range)
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Peaks


theorem eventually_pointValue_log_scales {P K q : ℝ}
    (hK : 0 < K) (hq : 0 < q) :
    ∀ᶠ H : ℝ in atTop, 20 ≤ H ∧ 1 ≤ Real.log (3*H) ∧
      2*P ≤ K*Real.log (3*H) ∧ 2*(Real.log (3*H))^2 ≤ H^q := by
  have hsmall := eventually_const_log_pow_le_rpow (8:ℝ) (by norm_num) 2 hq
  have hlog := Real.tendsto_log_atTop.eventually
    (eventually_ge_atTop (max 1 (2*P/K)))
  filter_upwards [hsmall,hlog,eventually_ge_atTop (20:ℝ)] with H hs hl hH
  have hH0 : 0 < H := by linarith
  have hmono : Real.log H ≤ Real.log (3*H) :=
    Real.log_le_log hH0 (by linarith)
  have hlog3 : Real.log 3 ≤ Real.log H :=
    Real.log_le_log (by norm_num) (by linarith)
  have hupper : Real.log (3*H) ≤ 2*Real.log H := by
    rw [Real.log_mul (by norm_num) hH0.ne']
    linarith
  have hP : 2*P/K ≤ Real.log (3*H) :=
    ((le_max_right _ _).trans hl).trans hmono
  have hPmul := (div_le_iff₀ hK).mp hP
  have hp := pow_le_pow_left₀
    (Real.log_nonneg (by linarith : 1 ≤ 3*H)) hupper 2
  refine ⟨hH,((le_max_left _ _).trans hl).trans hmono,by nlinarith,?_⟩
  nlinarith

theorem pointValueWidth_error_absorption {P C K L V : ℝ}
    (hP : 0 < P) (hK : 0 < K) (hL : 0 < L) (hKsize : 16*P*C ≤ K) :
    C*(V^2/(K*L^2))*L ≤ V^2/(16*P*L) := by
  have hc : C/K ≤ 1/(16*P) :=
    (div_le_div_iff₀ hK (by positivity)).mpr (by nlinarith)
  calc
    C*(V^2/(K*L^2))*L = (C/K)*(V^2/L) := by field_simp
    _ ≤ (1/(16*P))*(V^2/L) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = V^2/(16*P*L) := by field_simp





theorem eventually_pointValue_source_lower_range {K η : ℝ}
    (hK : 0 < K) (hη : 0 < η) :
    ∀ᶠ H : ℝ in atTop,
      K*(Real.log (3*H))^2*(2*H)^(1/4+η) ≤
        (H^(1/8+η))^2 := by
  have hs := eventually_const_height_log_pow_mul_rpow_le_rpow
    (C := K*2^((1/4:ℝ)+η)) (a := 1/4+η) (b := 1/4+2*η)
    (by positivity) 2 (by linarith)
  filter_upwards [hs,eventually_gt_atTop (0:ℝ)] with H hs hH
  have hp : (H^(1/8+η))^2 = H^(1/4+2*η) := by
    rw [← Real.rpow_mul_natCast hH.le]
    congr 1
    norm_num
    ring
  rw [hp,Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hH.le]
  nlinarith [hs]







