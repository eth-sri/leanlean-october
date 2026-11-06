module

public import NearlyMinimax.CompleteSaddleSpatialSeries
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! The actual canonical H/E witness for the complete-source lower path.
Every geometric and factorial guard is derived at the rounded saddle. -/
𝛅
open scoped BigOperators Topology
𝚨
𝚩
set_option maxHeartbeats 1800000
𝚬
𝚿

 set_option hygiene false
𝗃 𝔅 ἀ C Q Cfr
𝗃 𝔍 𝔅 ἀ cf Cω n
𝗇 𝔄 𝔍 completeSaddleGeometryEnvelope
𝗇 𝔇 highPatchProductChart d k j x
𝗇 𝔈 𝙳
𝗃 𝔎 ἀ C k D M q
𝗇 𝔉 𝔎 completeSourceRows Cfr
𝗃 𝔊 ἀ C Cω n
𝗃 𝔏 ἀ C Cω cf n
theorem completeSaddleGeometry_witness [NeZero d]
    (C : ModelConstants d) Q
    (hs : 𝘎) (hd : 𝘊 < d) :
    ∃ Cfr0 eta0 : ℝ, 𝚣₂ ∧ 𝖴₁ ∧
      ∀ Cfr cf , Cfr0 ≤ Cfr → 𝙻₁ → ∀ Cω ,
      ∀ᶠ n : ℕ in atTop,
      let m := highCompleteSourceSaddleCoefficient C
      let theta := highCompleteSourceSaddleTheta C
      let k := 𝙼₁
      let D := completeSaddleD C n
      let M := completeSaddleM C n
      let q := lowerSaddleResponseOrder C.smoothness d
      let ell := 𝔊 completeSaddleEll
      let N := 𝔊 completeSaddleN
      let mu := 𝔊 completeSaddleMu
      let eta := 𝔏 completeSaddleEta
      ∀ (_ : NeZero k) (_ : LinearOrder 𝙯),
      let R := 𝔉 (spatialInterpolationLambda d) ell N mu
      ∃ E : ℝ, 𝘃₂ ∧
        E ≤ lowerSaddleRawEnergyBound C.smoothness d m theta Cω cf 𝔅 completeSaddleDefectConstant
          𝔅 completeSaddleAliasConstant 𝔅 completeSaddleFieldConstant (completeSaddleExteriorConstant C Q)
          𝗰₁ 𝙲 n ∧
        (∀ r, Integrable (𝔄 r) 𝗾₂) ∧
        (∀ r U, 0 ≤ 𝔄 r U) ∧
        (∀ V , |𝖮₂| ≤ Q.ρ →
          ∀ h : 𝔎 HighCompleteSourceHistory Cfr (spatialInterpolationLambda d) ell N mu,
          ∀ j r x, (∀ i, x i ∈ 𝘋) →
          selectedRawSquareEnergy (highUnionSourceRawNumerator C R r Q.a V eta h j) x ≤
            𝔄 r 𝔇) ∧
        highSourceSpatialSeries d k n C.densityLower Q.c (fun _j => 𝔄) ≤
          (𝚐 : ℕ)*𝗋*E := by
  obtain ⟨Cfr0,eta0,hfr0,heta0,hcap⟩ := completeSource_original_all_geometry C Q
  refine ⟨Cfr0,eta0,hfr0,heta0,?_⟩
  intro Cfr cf hfr hcf Cω
  have hd5 : 𝘚 := by
    have h : 𝗦<d := by linarith only [hs,hd]
    have h' : 4<d := by exact_mod_cast h
    omega
  filter_upwards [eventually_completeSaddleGeometry_factorial C Q hs hd hcf Cfr Cω,
    eventually_completeSaddleSpatialSeries_le C Q hs hd hcf Cfr Cω,
    eventually_completeSaddleEnergyGuards C hs hd hcf Cω,
    completeSourceSaddle_higher_family_eventually_legal C hs hd Cω,
    tendsto_natCast_atTop_atTop.eventually $ eventually_ordinaryFineAlias_saddle_guards hs hd
      C.densityLower_pos (C.densityLower_lt_one.trans C.one_lt_densityUpper) Cω ,
    tendsto_natCast_atTop_atTop.eventually $ eventually_completeSourceSaddle_parameters C hs hd hcf
      heta0 (by norm_num : 𝙋<1) Cω ] with n henergy hseries G hselection GO hphysical
  dsimp
  let m := highCompleteSourceSaddleCoefficient C
  let theta := highCompleteSourceSaddleTheta C
  let k := 𝙼₁
  let D := completeSaddleD C n
  let M := completeSaddleM C n
  let q := lowerSaddleResponseOrder C.smoothness d
  let ell := 𝔊 completeSaddleEll
  let N := 𝔊 completeSaddleN
  let mu := 𝔊 completeSaddleMu
  let eta := 𝔏 completeSaddleEta
  let lam := spatialInterpolationLambda d
  let Rbound := ordinaryFineAliasSaddleTargetBound C.smoothness d C.densityLower C.densityUpper
  intro hk0 horder
  letI := hk0
  letI := horder
  let R := 𝔉 lam ell N mu
  have hD := hphysical.2.1
  have hq : 𝖯₂ := le_max_left ..
  have GS := 𝔎 completeSourceRows_guards hD  𝖡₃  G.resolution Cfr lam ell N mu
    (hfr0.trans hfr) (lt_of_lt_of_le zero_lt_one G.ell_one) G.ell_lt_N
  let E := 𝔍 completeSaddleEnergyBudget
  refine ⟨E,𝔍 completeSaddleEnergyBudget_nonneg,le_rfl,?_,?_,?_,?_⟩
  · intro r
    exact completeSaddleGeometryEnvelope_integrable C Q hd5 Cfr cf Cω n r G.ell_one G.ell_lt_N.le
  · exact 𝔍 completeSaddleGeometryEnvelope_nonneg
  · intro V hV h j r x hx
    have hI t ht : 1 ≤ t ∧ t ≤ Rbound :=
      ⟨by have hh := (GO.targets t ht).1; omega,(GO.targets t ht).2⟩
    have hdom := hcap k D M q hk0 horder hphysical.1 hD hq G.resolution Cfr (completeSaddleC0 C) ell N mu cf
      hfr G.ell_one G.ell_lt_N hcf.le hphysical.2.2.2.2.2.1 G.tau_le
      (fun j => hselection.2.1 𝔈) (fun j => hselection.2.2 𝔈) Rbound hI V hV j h r x hx
    have hmass := GS.total_positive.le
    have hm := completeSourceGeometryEnvelope_mono_total D M Rbound q C.densityLower C.densityUpper
      (completeSaddleC0 C) ell N mu Cfr Q.a Q.ρ eta
      𝙪₂ hmass (rowMass_le_balanced_source_activity C R hmass) r 𝔇
    rw [𝔏 completeSourceSaddle_eta_eq] at hdom
    exact hdom.trans hm
  · exact hseries hk0
