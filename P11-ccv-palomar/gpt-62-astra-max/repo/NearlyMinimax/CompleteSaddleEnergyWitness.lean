module

public import NearlyMinimax.CompleteSaddleSpatialSeries


@[expose] public section

/-! The actual canonical H/E witness for the complete-source lower path.
Every geometric and factorial guard is derived at the rounded saddle. -/
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
attribute [local instance] Classical.propDecidable
attribute [local irreducible] highUnionSourceDensity highUnionSourceState historyMarkedAppend

 theorem completeSaddleGeometry_witness {d : ℕ} [NeZero d]
    {C : ModelConstants d} (Q : LowSmoothnessTernaryConstants C)
    (hs : 1 < C.smoothness) (hd : 4*C.smoothness < d) :
    ∃ Cfr0 eta0 : ℝ, 1 ≤ Cfr0 ∧ 0 < eta0 ∧
      ∀ Cfr cf, Cfr0 ≤ Cfr → 0 < cf → ∀ Cω,
      ∀ᶠ n : ℕ in atTop,
      let m := highCompleteSourceSaddleCoefficient C
      let theta := highCompleteSourceSaddleTheta C
      let k := lowerSaddleGrid d m theta Cω n
      let D := completeSaddleD C n
      let M := completeSaddleM C n
      let q := lowerSaddleResponseOrder C.smoothness d
      let ell := completeSaddleEll C Cω n
      let N := completeSaddleN C Cω n
      let mu := completeSaddleMu C Cω n
      let eta := completeSaddleEta C Cω cf n
      ∀ (_ : NeZero k) (_ : LinearOrder (HighWindowLabels d k)),
      let R := completeSourceRows C k D M q Cfr (spatialInterpolationLambda d) ell N mu
      ∃ E : ℝ, 0 ≤ E ∧
        E ≤ lowerSaddleRawEnergyBound C.smoothness d m theta Cω cf (completeSaddleDefectConstant Q Cfr)
          (completeSaddleAliasConstant Q Cfr) (completeSaddleFieldConstant Q Cfr) (completeSaddleExteriorConstant Q)
          (highRowTotalMass R.rowMass/highCenterMix C) (shrunkDensityExponent C.densityLower C.densityUpper) n ∧
        (∀ r, Integrable (completeSaddleGeometryEnvelope Q Cfr cf Cω n r) (fullSpatialPatchDesign d r)) ∧
        (∀ r U, 0 ≤ completeSaddleGeometryEnvelope Q Cfr cf Cω n r U) ∧
        (∀ V, |V-Q.v| ≤ Q.ρ →
          ∀ h,
          ∀ j r x, (∀ i, x i ∈ highTorusPatch j) →
          selectedRawSquareEnergy (highUnionSourceRawNumerator C R r Q.a V eta h j) x ≤
            completeSaddleGeometryEnvelope Q Cfr cf Cω n r (highPatchProductChart j x)) ∧
        highSourceSpatialSeries d k n C.densityLower Q.c (fun _j => completeSaddleGeometryEnvelope Q Cfr cf Cω n) ≤
          (3^d : ℕ)*k^d*E := by
  obtain ⟨Cfr0,eta0,hfr0,heta0,hcap⟩ := completeSource_original_all_geometry Q
  refine ⟨Cfr0,eta0,hfr0,heta0,?_⟩
  intro Cfr cf hfr hcf Cω
  have hd5 : 5 ≤ d := by
    have h : (4 : ℝ)<d := by bound
    have h' : 4<d := by exact_mod_cast h
    omega
  filter_upwards [eventually_completeSaddleGeometry_factorial Q hs hd hcf Cfr Cω,
    eventually_completeSaddleSpatialSeries_le Q hs hd hcf Cfr Cω,
    eventually_completeSaddleEnergyGuards hs hd hcf Cω,
    (tendsto_natCast_atTop_atTop.eventually (sourceSaddleHigherFamily_eventually_legal C.smoothness C.densityLower C.densityUpper Cω hs hd C.densityLower_pos (C.densityLower_lt_one.trans C.one_lt_densityUpper))),
    tendsto_natCast_atTop_atTop.eventually (eventually_ordinaryFineAlias_saddle_guards hs hd
      C.densityLower_pos (C.densityLower_lt_one.trans C.one_lt_densityUpper) Cω),
    tendsto_natCast_atTop_atTop.eventually (eventually_completeSourceSaddle_parameters hs hd hcf
      heta0 (by norm_num : (0 : ℝ)<1) Cω)] with n henergy hseries G hselection GO hphysical
  dsimp
  let k := lowerSaddleGrid d (highCompleteSourceSaddleCoefficient C) (highCompleteSourceSaddleTheta C) Cω n
  let D := completeSaddleD C n
  let M := completeSaddleM C n
  let q := lowerSaddleResponseOrder C.smoothness d
  let ell := completeSaddleEll C Cω n
  let N := completeSaddleN C Cω n
  let mu := completeSaddleMu C Cω n
  let eta := completeSaddleEta C Cω cf n
  let lam := spatialInterpolationLambda d
  let Rbound := ordinaryFineAliasSaddleTargetBound C.smoothness d C.densityLower C.densityUpper
  intro hk0 horder
  letI := hk0
  letI := horder
  have hk  := hphysical.1
  have hD  := hphysical.2.1
  have hq : 2 ≤ q := le_max_left _ _
  have GS := completeSourceRows_guards k (q := q) hD (by omega) G.resolution lam mu
    (hfr0.trans hfr) (lt_of_lt_of_le zero_lt_one G.ell_one) G.ell_lt_N
  refine ⟨(completeSaddleEnergyBudget Q Cfr cf Cω n),completeSaddleEnergyBudget_nonneg ..,le_rfl,?_,?_,?_,?_⟩
  · intro r
    exact completeSaddleGeometryEnvelope_integrable Q hd5 Cfr cf Cω n r G.ell_one G.ell_lt_N.le
  · exact completeSaddleGeometryEnvelope_nonneg Q Cfr cf Cω n
  · intro V hV h j r x hx
    have hI t ht : 1 ≤ t ∧ t ≤ Rbound :=
      ⟨by linarith [(GO.targets t ht).1],(GO.targets t ht).2⟩
    have hdom := hcap k D M q hk0 horder hk hD hq G.resolution Cfr _ ell N mu cf hfr G.ell_one G.ell_lt_N hcf.le (by bound) G.tau_le (fun j => by bound) (fun j => hselection.2.2 (j.val+3)) Rbound hI V hV j h r x hx
    have hmass  := GS.total_positive.le
    have hm := completeSourceGeometryEnvelope_mono_total D M Rbound q C.densityLower C.densityUpper
      (completeSaddleC0 C) ell N mu Cfr Q.a Q.ρ eta
      (highSeparatedScoreExponentialConstant Q.a Q.ρ C.densityUpper 1 1) hmass (by apply (le_div_iff₀ (highCenterMix_mem C).1).mpr; exact mul_le_of_le_one_right hmass (highCenterMix_mem C).2.le) (highPatchProductChart j x)
    rw [(completeSourceSaddle_eta_eq C Cω cf n)] at hdom
    exact hdom.trans hm
  · exact hseries hk0

end NearlyMinimax
