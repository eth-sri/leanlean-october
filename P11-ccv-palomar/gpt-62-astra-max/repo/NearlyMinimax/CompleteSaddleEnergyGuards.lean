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

section
variable {d : ℕ} (C : ModelConstants d) (Cω cf x : ℝ)

abbrev completeSaddleM :=
  lowerSaddleM (highCompleteSourceSaddleCoefficient C) x
abbrev completeSaddleD :=
  lowerSaddleD d (highCompleteSourceSaddleCoefficient C) x
abbrev completeSaddleN :=
  lowerSaddleN C.smoothness d (highCompleteSourceSaddleCoefficient C)
    (highCompleteSourceSaddleTheta C) Cω (shrunkDensityExponent C.densityLower C.densityUpper) x
abbrev completeSaddleMu :=
  lowerSaddleMu d (highCompleteSourceSaddleCoefficient C) (highCompleteSourceSaddleTheta C) Cω x
abbrev completeSaddleEta :=
  lowerSaddleEta C.smoothness d (highCompleteSourceSaddleCoefficient C)
    (highCompleteSourceSaddleTheta C) Cω cf x
abbrev completeSaddleC0 :=
  densityIntervalExponent C.densityLower C.densityUpper+1
abbrev completeSaddleEll :=
  lowerAliasCutoff C.smoothness d (highCompleteSourceSaddleCoefficient C)
    (highCompleteSourceSaddleTheta C) Cω (completeSaddleC0 C)
    (shrunkDensityExponent C.densityLower C.densityUpper) x
abbrev completeSaddleTau :=
  shrunkDensityExponent C.densityLower C.densityUpper (completeSaddleM C x)
abbrev completeSaddleAD :=
  C.densityLower+1/(completeSaddleM C x)
abbrev completeSaddleBD :=
  C.densityUpper-1/(completeSaddleM C x)

end

structure CompleteSaddleEnergyGuards {d : ℕ} (C : ModelConstants d) (Cω cf x : ℝ) : Prop where
  resolution : highCenterResolutionThreshold C ≤ (completeSaddleM C x : ℝ)
  resolution_one : 1 ≤ (completeSaddleM C x : ℝ)
  N_one : 1 ≤ completeSaddleN C Cω x
  mu_positive : 0 < completeSaddleMu C Cω x
  mu_one : completeSaddleMu C Cω x ≤ 1
  mu_log : completeSaddleMu C Cω x*(1+Real.log (completeSaddleN C Cω x)) ≤ 1
  eta_positive : 0 < completeSaddleEta C Cω cf x
  response_taylor : (completeSaddleEta C Cω cf x)^(4*lowerSaddleResponseOrder C.smoothness d)*
    (completeSaddleN C Cω x)^d ≤ 1
  tau_nonneg : 0 ≤ completeSaddleTau C x
  tau_le : completeSaddleTau C x ≤ completeSaddleC0 C
  degree_multiple : (completeSaddleD C x : ℝ) ≤
    (((d : ℝ)+8)/4+1)*(completeSaddleM C x : ℝ)
  ell_one : 1 ≤ completeSaddleEll C Cω x
  ell_lt_N : completeSaddleEll C Cω x < completeSaddleN C Cω x
  field_scale : Real.exp (2*completeSaddleTau C x*(completeSaddleM C x : ℝ))*
    (completeSaddleMu C Cω x)^4*(completeSaddleEll C Cω x)^(4-2*(d : ℝ)) ≤
      (completeSaddleMu C Cω x)^2*(completeSaddleN C Cω x)^(-(d : ℝ))
  field_scale_square : Real.exp (2*completeSaddleTau C x*(completeSaddleM C x : ℝ))*
    (completeSaddleMu C Cω x)^4*((completeSaddleEll C Cω x)^(2-(d : ℝ)))^2 ≤
      (completeSaddleMu C Cω x)^2*(completeSaddleN C Cω x)^(-(d : ℝ))
  ad_ge : C.densityLower ≤ completeSaddleAD C x
  bd_nonneg : 0 ≤ completeSaddleBD C x
  bd_le : completeSaddleBD C x ≤ C.densityUpper
  ad_positive : 0 < completeSaddleAD C x
  density_interval : completeSaddleAD C x < completeSaddleBD C x

 theorem eventually_completeSaddleEnergyGuards {d : ℕ} [NeZero d]
    {C : ModelConstants d} (hs : 1 < C.smoothness) (hd : 4*C.smoothness < d)
    {cf : ℝ} (hcf : 0 < cf) (Cω : ℝ) :
    ∀ᶠ n : ℕ in atTop, CompleteSaddleEnergyGuards C Cω cf n := by
  have hab := C.densityLower_lt_one.trans C.one_lt_densityUpper
  have htau  := densityIntervalExponent_pos C.densityLower_pos hab
  have hm  := lowerSaddleCoefficient_pos hs hd htau
  obtain ⟨Ctau,_,hcontrol⟩ := exists_actual_lowerExponentControl C.densityLower_pos hab
  obtain ⟨K,_,hreg⟩ := completeSourceSaddle_fixed_regime_window hs hd hcf
  have hhier := actual_lowerAlias_hierarchy (Cact := 1) (Cs := 1) hs hd
    C.densityLower_pos hab (by norm_num) (by norm_num) Cω
  have hscale := eventually_lowerSaddle_fine_field_energy_scale hs hd hm (lowerSaddleTheta_pos hs hd htau) hcontrol Cω ((densityIntervalExponent C.densityLower C.densityUpper)+1)
  have hparams := eventually_completeSourceSaddle_parameters hs hd hcf
    (by norm_num : (0 : ℝ)<1) (by norm_num : (0 : ℝ)<1) Cω
  filter_upwards [hreg Cω 1 0 (by norm_num),tendsto_natCast_atTop_atTop.eventually hhier,
    tendsto_natCast_atTop_atTop.eventually hscale,
    tendsto_natCast_atTop_atTop.eventually hparams,
    tendsto_natCast_atTop_atTop.eventually
      ((lowerSaddleM_tendsto_atTop hm).eventually (eventually_ge_atTop 1))]
    with n hregn hhiern hscalen hpn hMone
  rcases hregn with ⟨_,_,hN,hmu,hmu1,_,_,_,_,heta,_,hqt⟩
  rcases hhiern with ⟨hell,htaule,hmulog,_,_,_,_,_,_,_,_,_⟩
  obtain ⟨had,hadb⟩ := high_source_interval_numeric hpn.2.2.1
  have htn : 0 ≤ completeSaddleTau C n := by
    exact (densityIntervalExponent_pos (by simpa using had) (by simpa using hadb)).le
  have hfield  := hscalen
  have hsquare : ((completeSaddleEll C Cω n)^(2-(d : ℝ)))^2 =
      (completeSaddleEll C Cω n)^(4-2*(d : ℝ)) := by
    rw [← Real.rpow_mul_natCast (by positivity)]
    ring
  refine ⟨hpn.2.2.1,hMone,hN,hmu,hmu1.le,hmulog,heta,?_,htn,htaule,
    lowerSaddleD_le_fixed_multiple (Nat.cast_nonneg _) hMone,hell.le,hpn.2.2.2.2.1,
    hfield,?_,?_,had.le.trans hadb.le,?_,had,hadb⟩
  · simpa only [lowerSaddleResponseQuantity,Real.rpow_natCast] using hqt
  · rw [hsquare]
    exact hfield
  · simp
  · simp

end NearlyMinimax
