module

public import NearlyMinimax.CompleteSourceSaddleRegime
public import NearlyMinimax.LowerSaddleDegreeBounds
public import NearlyMinimax.FineFieldScaleBudget


@[expose] public section

/-! Every scalar guard used in the complete-source factorial energy bound
is a conclusion of the actual rounded saddle. Constants precede its shift
and sample size; no energy, regularity or desired-rate guard is assumed. -/
noncomputable section
open Filter Set
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

structure CompleteSaddleEnergyGuards {d : ℕ} (C : ModelConstants d) (Cω cf x : ℝ) : Prop where
  resolution : highCenterResolutionThreshold C ≤ (completeSaddleM C x : ℝ)
  degree_min : 3 ≤ completeSaddleD C x
  N_one : 1 ≤ completeSaddleN C Cω x
  mu_positive : 0 < completeSaddleMu C Cω x
  mu_one : completeSaddleMu C Cω x ≤ 1
  mu_log : completeSaddleMu C Cω x*(1+Real.log (completeSaddleN C Cω x)) ≤ 1
  response_taylor : (completeSaddleEta C Cω cf x)^(4*lowerSaddleResponseOrder C.smoothness d)*
    (completeSaddleN C Cω x)^d ≤ 1
  tau_nonneg : 0 ≤ completeSaddleTau C x
  tau_le : completeSaddleTau C x ≤ completeSaddleC0 C
  degree_multiple : (completeSaddleD C x : ℝ) ≤
    (((d : ℝ)+8)/4+1)*(completeSaddleM C x : ℝ)
  ell_one : 1 ≤ completeSaddleEll C Cω x
  ell_lt_N : completeSaddleEll C Cω x < completeSaddleN C Cω x
  field_scale_square : Real.exp (2*completeSaddleTau C x*(completeSaddleM C x : ℝ))*
    (completeSaddleMu C Cω x)^4*((completeSaddleEll C Cω x)^(2-(d : ℝ)))^2 ≤
      (completeSaddleMu C Cω x)^2*(completeSaddleN C Cω x)^(-(d : ℝ))
  bd_nonneg : 0 ≤ completeSaddleBD C x
  ad_positive : 0 < completeSaddleAD C x
  density_interval : completeSaddleAD C x < completeSaddleBD C x

 theorem eventually_completeSaddleEnergyGuards {d : ℕ} [NeZero d]
    (C : ModelConstants d) (hs : 1 < C.smoothness) (hd : 4*C.smoothness < (d : ℝ))
    {cf : ℝ} (hcf : 0 < cf) (Cω : ℝ) :
    ∀ᶠ n : ℕ in atTop, CompleteSaddleEnergyGuards C Cω cf n := by
  let m := highCompleteSourceSaddleCoefficient C
  let theta := highCompleteSourceSaddleTheta C
  let tau := densityIntervalExponent C.densityLower C.densityUpper
  have hab := C.densityLower_lt_one.trans C.one_lt_densityUpper
  have htau := densityIntervalExponent_pos C.densityLower_pos hab
  have hm := lowerSaddleCoefficient_pos hs hd htau
  have htheta := lowerSaddleTheta_pos hs hd htau
  obtain ⟨Ctau,_,hcontrol⟩ := exists_actual_lowerExponentControl C.densityLower_pos hab
  have hd0 : (0 : ℝ) < d := by linarith
  have hresp := lowerSaddleResponseQuantity_tends_zero hs hd hm htheta hcf hcontrol
    (lowerSaddleResponseOrder C.smoothness d) (lowerSaddleResponseOrder_bound) Cω
  have hscale := eventually_lowerSaddle_fine_field_energy_scale hs hd hm htheta hcontrol Cω (tau+1)
  have hparams := eventually_completeSourceSaddle_parameters C hs hd (cf := cf)
    (by norm_num : (0 : ℝ)<1) (by norm_num : (0 : ℝ)<1) Cω
  have hreal : ∀ᶠ x : ℝ in atTop, CompleteSaddleEnergyGuards C Cω cf x := by
    filter_upwards [actual_lowerAlias_guards hs hd C.densityLower_pos hab Cω, hscale, hparams,
      (lowerSaddleM_tendsto_atTop hm).eventually (eventually_ge_atTop (1 : ℝ)),
      eventually_gt_atTop (0 : ℝ), (lowerSaddleMu_tends_zero hd0 hm htheta Cω).eventually (gt_mem_nhds zero_lt_one),
      hresp.eventually (gt_mem_nhds zero_lt_one)] with n H hfield hpn hMone hn hmu1 hqt
    obtain ⟨had, hadb⟩ := high_source_interval_numeric C (completeSaddleM C n : ℝ) hpn.resolution_min
    have htn : 0 ≤ completeSaddleTau C n := by
      simpa only [completeSaddleTau, shrunkDensityExponent, one_div] using (densityIntervalExponent_pos had hadb).le
    have hell : 1 ≤ completeSaddleEll C Cω n := H.cutoff.le
    have hmu : 0 < completeSaddleMu C Cω n :=
      mul_pos hn (Real.rpow_pos_of_pos (lowerSaddleH_positive _ _ _ _ _) _)
    have hsquare : ((completeSaddleEll C Cω n)^(2-(d : ℝ)))^2 =
        (completeSaddleEll C Cω n)^(4-2*(d : ℝ)) := by
      rw [← Real.rpow_mul_natCast (by linarith only [hell] : 0 ≤ completeSaddleEll C Cω n)]
      congr 1
      ring
    refine ⟨hpn.resolution_min, hpn.degree_min, hell.trans hpn.cutoff_lt.le, hmu, hmu1.le, H.base_le,
      ?_, htn, H.exponent_le, lowerSaddleD_le_fixed_multiple (Nat.cast_nonneg _) hMone,
      hell, hpn.cutoff_lt, ?_, had.le.trans hadb.le, had, hadb⟩
    · simpa only [lowerSaddleResponseQuantity, Real.rpow_natCast, completeSaddleEta, completeSaddleN,
        highCompleteSourceSaddleCoefficient, highCompleteSourceSaddleTheta, m, theta] using hqt.le
    · rw [hsquare]
      exact hfield
  exact tendsto_natCast_atTop_atTop.eventually hreal

end NearlyMinimax
