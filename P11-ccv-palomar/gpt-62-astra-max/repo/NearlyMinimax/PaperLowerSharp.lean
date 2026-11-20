module

public import NearlyMinimax.CompleteSaddleEnergyWitness
public import NearlyMinimax.CompleteSaddleRiskReduction
public import NearlyMinimax.HighCompleteCostFlexible


@[expose] public section

/-! The original sharp lower bound. The actual complete singleton, pair,
and higher-band source supplies the raw spatial energy, legal normalized
model path and exceptional mass estimate. Every constant precedes the
extension domain and sample size. -/
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
attribute [local instance] Classical.propDecidable
attribute [local irreducible] sourceRowData highRowTotalMass
  highUnionSourceDensity highUnionSourceState historyMarkedAppend

theorem paper_lower_sharp {d : ℕ} (C : ModelConstants d) : LowerSharpClaim C := by
  classical
  intro hreg
  obtain ⟨hs,hd⟩ := hreg
  letI  := NeZero.of_pos C.dimension_pos
  obtain ⟨Q⟩ := lowSmoothnessTernaryConstants_exists C
  obtain ⟨Cfr0,etaG,hCfr0,hetaG,hgeometry⟩ := completeSaddleGeometry_witness Q hs hd
  obtain ⟨Cfr,eta0,ctr,hCfr,hmin,heta0,hctr,hcost⟩ :=
    highCompleteSource_cost_risk_uniform_above Q Cfr0
  obtain ⟨cf,cm,hcf,hHolder,hcm,hcmU⟩ := completeSourceSaddle_numeric_constants C
  let q := lowerSaddleResponseOrder C.smoothness d
  let lam := spatialInterpolationLambda d
  have hCB  := ((div_pos
      (sourceSaddleActivityConstant_positive _ q _ _ _ _ C.densityLower_pos (C.densityLower_lt_one.trans C.one_lt_densityUpper))
      (highCenterMix_mem C).1 : 0 < completeSourceSaddleActivityConstant C q Cfr lam)).le
  have hC5  := ((completeGeometryDefectConstant_pos .. : 0 < completeSaddleDefectConstant Q Cfr)).le
  have hC6  := (completeSaddleAliasConstant_pos Q Cfr).le
  apply completeSaddle_lower_rate_of_actual_cost_budget hs hd hcf hCB hC5 hC6 (((completeGeometryFieldConstant_pos .. : 0 < completeSaddleFieldConstant Q Cfr)).le) (((completeGeometryExteriorConstant_pos .. : 0 < completeSaddleExteriorConstant Q)).le) hctr hcm
  intro Cω
  filter_upwards [hgeometry Cfr cf hmin hcf Cω,
    tendsto_natCast_atTop_atTop.eventually
      (eventually_completeSourceSaddle_parameters hs hd hcf heta0 hcm Cω),
    tendsto_natCast_atTop_atTop.eventually
      (completeSourceSaddleActivity_eventually_bound hs hd q Cfr lam Cω)] with n hgeo hp hactivity
  let m := highCompleteSourceSaddleCoefficient C
  let k := lowerSaddleGrid d m (highCompleteSourceSaddleTheta C) Cω n
  let M := completeSaddleM C n
  let D := completeSaddleD C n
  let N := completeSaddleN C Cω n
  let ell := completeSaddleEll C Cω n
  let mu := completeSaddleMu C Cω n
  let eta := cf*k^(-C.smoothness)
  obtain ⟨hk,hD,hM,hell,hellN,heta,heps,hB⟩ := hp
  have hk' : 4 ≤ k := hk
  have hD'  := hD
  have hM'  := hM
  letI : NeZero k := ⟨by omega⟩
  letI  :=
    LinearOrder.lift' (Fintype.equivFin (HighWindowLabels d k))
      (Fintype.equivFin (HighWindowLabels d k)).injective
  let R := completeSourceRows C k D M q Cfr lam ell N mu
  obtain ⟨E,hE,hEcap,hHI,hH0,hdom,hseries⟩ := hgeo inferInstance inferInstance
  have hq : 1 ≤ q := by dsimp only [q,lowerSaddleResponseOrder]; omega
  let Bl := highRowTotalMass R.rowMass/highCenterMix C
  have hBl  := div_nonneg (completeSourceRows_guards k hD' hq hM' lam mu hCfr hell hellN).total_positive.le (highCenterMix_mem C).1.le
  refine ⟨Bl,E,hB,hBl,hE,hactivity,hEcap,?_⟩
  intro U
  let delta := localScorePathLength (highPathConstant (3^d) Q.ρ eta0) Bl (Real.sqrt ((3^d : ℕ)*k^d*E))
  have heta0' : 0 ≤ eta := by positivity
  have hV t (ht : t ∈ Icc 0 delta) : |(Q.v-eta^2*t)-Q.v| ≤ Q.ρ := by
    simp [sub_sub_cancel_left,abs_neg,abs_mul,abs_of_nonneg (sq_nonneg eta),abs_of_nonneg ht.1]
    exact (mul_le_mul_of_nonneg_left ht.2 (sq_nonneg eta)).trans (highPath_variance_budget _ Q.ρ_pos heta0 hBl (Real.sqrt_nonneg _) heta0' heta)
  have hout := hcost U k D M q inferInstance inferInstance hk' hD' hq hM' lam ell N mu hell hellN
    cf hcf.le hHolder heta cm hcm.le hcmU n E hE heps
    (fun _t _h _j r => completeSaddleGeometryEnvelope Q Cfr cf Cω n r)
    (fun _t _ht _h _j r => hHI r)
    (fun _t _ht _h _j r u => hH0 r u)
    (fun t ht h j r x hx => by
      simpa only [← (completeSourceSaddle_eta_eq C Cω cf n)] using hdom (Q.v-eta^2*t) (hV t ht) h j r x hx)
    (fun _t _ht _h => hseries)
  have htail : 2*Real.exp (-(cm/M)^2/
      (8*highHistoryMassParameter d k C.densityLower C.densityUpper)) =
      highCompleteSourceSaddleTail C Cω cm n :=
    highHistoryMass_saddle_tail_eq ..
  simpa only [htail] using hout

end NearlyMinimax
