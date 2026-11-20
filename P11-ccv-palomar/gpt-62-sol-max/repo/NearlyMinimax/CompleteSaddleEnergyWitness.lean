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
    (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C)
    (hs : 1 < C.smoothness) (hd : 4*C.smoothness < (d : ℝ)) :
    ∃ Cfr0 eta0 : ℝ, 1 ≤ Cfr0 ∧ 0 < eta0 ∧
      ∀ Cfr cf : ℝ, Cfr0 ≤ Cfr → 0 < cf → ∀ Cω : ℝ,
      ∀ᶠ n : ℕ in atTop,
      let k := completeSaddleGrid C Cω n
      let D := completeSaddleD C n
      let M := completeSaddleM C n
      let q := lowerSaddleResponseOrder C.smoothness d
      let ell := completeSaddleEll C Cω n
      let N := completeSaddleN C Cω n
      let mu := completeSaddleMu C Cω n
      let eta := completeSaddleEta C Cω cf n
      ∀ (_ : NeZero k) (_ : LinearOrder (HighWindowLabels d k)),
      let R := completeSourceRows C k D M q Cfr (spatialInterpolationLambda d) ell N mu
      let E := completeSaddleEnergyBudget C Q Cfr cf Cω n
      0 ≤ E ∧
        (∀ r, Integrable (completeSaddleGeometryEnvelope C Q Cfr cf Cω n r) (fullSpatialPatchDesign d r)) ∧
        (∀ r U, 0 ≤ completeSaddleGeometryEnvelope C Q Cfr cf Cω n r U) ∧
        (∀ V : ℝ, |V-Q.v| ≤ Q.ρ →
          ∀ h : HighCompleteSourceHistory C k D M q Cfr (spatialInterpolationLambda d) ell N mu,
          ∀ j r x, (∀ i, x i ∈ highTorusPatch d k j) →
          selectedRawSquareEnergy (highUnionSourceRawNumerator C R r Q.a V eta h j) x ≤
            completeSaddleGeometryEnvelope C Q Cfr cf Cω n r (highPatchProductChart d k j x)) ∧
        highSourceSpatialSeries d k n C.densityLower Q.c (fun _j => completeSaddleGeometryEnvelope C Q Cfr cf Cω n) ≤
          (3^d : ℕ)*(k : ℝ)^d*E := by
  obtain ⟨Cfr0,eta0,hfr0,heta0,hcap⟩ := completeSource_original_all_geometry C Q
  refine ⟨Cfr0,eta0,hfr0,heta0,?_⟩
  intro Cfr cf hfr hcf Cω
  have hd5 : 5 ≤ d := by
    have h : (4 : ℝ)<d := by linarith
    have h' : 4<d := by exact_mod_cast h
    omega
  filter_upwards [eventually_completeSaddleSpatialSeries_le C Q hs hd hcf Cfr Cω,
    eventually_completeSaddleEnergyGuards C hs hd hcf Cω,
    completeSourceSaddle_higher_family_eventually_legal C hs hd Cω,
    tendsto_natCast_atTop_atTop.eventually (eventually_ordinaryFineAlias_saddle_guards hs hd
      C.densityLower_pos (C.densityLower_lt_one.trans C.one_lt_densityUpper) Cω),
    tendsto_natCast_atTop_atTop.eventually (eventually_completeSourceSaddle_parameters C hs hd (cf := cf)
      heta0 (by norm_num : (0 : ℝ)<1) Cω)] with n hseries G hselection GO hphysical
  dsimp only
  let k := completeSaddleGrid C Cω n
  let D := completeSaddleD C n
  let M := completeSaddleM C n
  let q := lowerSaddleResponseOrder C.smoothness d
  let ell := completeSaddleEll C Cω n
  let N := completeSaddleN C Cω n
  let mu := completeSaddleMu C Cω n
  let lam := spatialInterpolationLambda d
  let Rbound := ordinaryFineAliasSaddleTargetBound C.smoothness d C.densityLower C.densityUpper
  intro hk0 horder
  letI := hk0
  letI := horder
  let R := completeSourceRows C k D M q Cfr lam ell N mu
  have hk := hphysical.grid_min
  have hD := hphysical.degree_min
  have hq : 2 ≤ q := le_max_left _ _
  have hfr1 := hfr0.trans hfr
  have GS := (completeSourceRows_guards C k D M q hD (by omega) G.resolution Cfr lam ell N mu
    hfr1 (lt_of_lt_of_le zero_lt_one G.ell_one) G.ell_lt_N).1
  refine ⟨completeSaddleEnergyBudget_nonneg C Q Cfr cf Cω n,?_,?_,?_,?_⟩
  · intro r
    exact completeSaddleGeometryEnvelope_integrable C Q hd5 Cfr cf Cω n r G.ell_one G.ell_lt_N.le
  · apply completeSaddleGeometryEnvelope_nonneg <;> assumption
  · intro V hV h j r x hx
    have hI (t : ℕ) (ht : t ∈ ordinaryFineAliasTargetSet d D ell N mu) : 1 ≤ t ∧ t ≤ Rbound :=
      ⟨by have hh := (GO.targets t ht).1; omega,(GO.targets t ht).2⟩
    have hdom := hcap k D M q hk0 horder hk hD hq G.resolution Cfr (completeSaddleC0 C) ell N mu cf
      hfr G.ell_one G.ell_lt_N hcf.le hphysical.amplitude G.tau_le
      (fun j => hselection.2.1 (j.val+3)) (fun j => hselection.2.2 (j.val+3)) Rbound hI V hV j h r x hx
    have hmass := GS.total_positive.le
    have hB := rowMass_le_balanced_source_activity C R hmass
    let S := completeSaddleGeometryParameters C Q Cfr cf Cω n
    have hm := S.envelope_mono_total
      (highSeparatedScoreExponentialConstant Q.a Q.ρ C.densityUpper 1 1) hmass hB r (highPatchProductChart d k j x)
    have heta := completeSourceSaddle_eta_eq C Cω cf n
    dsimp only at hdom
    rw [heta] at hdom
    exact hdom.trans hm
  · exact hseries hk0

end NearlyMinimax
