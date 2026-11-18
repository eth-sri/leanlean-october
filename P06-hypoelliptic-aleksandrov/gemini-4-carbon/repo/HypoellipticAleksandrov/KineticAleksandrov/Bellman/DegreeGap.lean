module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.VagueCompactness
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.Tactic
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.PairSetting
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.RatioNormalizationMeasure
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.FundamentalMeasureFubini
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.VagueAdjointLimitDegree
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.Exponent
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.HighDegreeExclusion
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.FundamentalMeasureStationary
import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov
open Set MeasureTheory Filter Topology
open scoped CompactlySupported
section
open Set MeasureTheory Filter Topology
open scoped CompactlySupported ENNReal NNReal

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [MeasurableSpace X] [BorelSpace X]


/-- Inner regularity upgrades positive compact-test order to actual measure order. -/
theorem bellman_measure_le_of_positive_tests (mu nu : Measure X)
    [IsFiniteMeasureOnCompacts mu] [IsFiniteMeasureOnCompacts nu]
    [mu.InnerRegular] [nu.OuterRegular]
    (ht : ∀ f : C_c(X, ℝ), (∀ x, 0 ≤ f x) → ∫ x, f x ∂mu ≤ ∫ x, f x ∂nu) :
    mu ≤ nu  := by
  have bellman_compact_measure_le_of_positive_tests [IsFiniteMeasureOnCompacts mu] [IsFiniteMeasureOnCompacts nu] [nu.OuterRegular] (ht : ∀ f : C_c(X, ℝ), (∀ x, 0 ≤ f x) → ∫ x, f x ∂mu ≤ ∫ x, f x ∂nu) {K : Set X} (hK : IsCompact K) :
      mu K ≤ nu K := by
    refine ENNReal.le_of_forall_pos_le_add fun eps heps hnu => ?_
    have hmuK : mu K ≠ ⊤ := hK.measure_lt_top.ne
    obtain ⟨V, hKV, hV, hmass⟩ :=
      exists_isOpen_le_add K nu (ne_of_gt (ENNReal.coe_lt_coe.mpr heps))
    suffices mu.real K ≤ nu.real K + eps by
      rwa [← ENNReal.toReal_le_toReal, ENNReal.toReal_add, ENNReal.coe_toReal]
      all_goals finiteness
    have hVfinite := hmass.trans_lt (by finiteness)
    obtain ⟨f, hfone, hfc, hfs, hf01⟩ :=
      exists_continuousMap_one_of_isCompact_subset_isOpen hK hV hKV
    let g : C_c(X, ℝ) := ⟨f, hfc⟩
    have hgK (x : X) : K.indicator 1 x ≤ g x := by
      by_cases hx : x ∈ K
      · simp only [indicator_of_mem hx, Pi.one_apply]
        change 1 ≤ f x
        have he := hfone hx
        change f x = 1 at he
        rw [he]
      · simp only [indicator_of_notMem hx]; exact (hf01 x).1
    have hgV (x : X) : g x ≤ V.indicator 1 x := by
      by_cases hx : x ∈ tsupport g
      · simp only [indicator_of_mem (hfs hx), Pi.one_apply]; exact (hf01 x).2
      · rw [image_eq_zero_of_notMem_tsupport hx]
        exact indicator_nonneg (fun _ _ => zero_le_one) x
    calc mu.real K = ∫ x, K.indicator 1 x ∂mu :=
          (integral_indicator_one hK.measurableSet).symm
      _ ≤ ∫ x, g x ∂mu := integral_mono
        ((continuousOn_const.integrableOn_compact hK).integrable_indicator hK.measurableSet)
        g.integrable hgK
      _ ≤ ∫ x, g x ∂nu := ht g (fun x => (hf01 x).1)
      _ ≤ ∫ x, V.indicator 1 x ∂nu := integral_mono g.integrable
        (IntegrableOn.integrable_indicator integrableOn_const hV.measurableSet) hgV
      _ ≤ nu.real K + eps := by
        rw [integral_indicator_one hV.measurableSet]
        have hh := ENNReal.toReal_mono (by finiteness : nu K + (eps : ℝ≥0∞) ≠ ∞) hmass
        rwa [ENNReal.toReal_add hnu.ne ENNReal.coe_ne_top, ENNReal.coe_toReal] at hh
  apply Measure.le_iff.mpr
  intro E hE
  rw [hE.measure_eq_iSup_isCompact mu]
  refine iSup_le fun K => iSup_le fun hKE => iSup_le fun hK => ?_
  exact (bellman_compact_measure_le_of_positive_tests ht hK).trans (measure_mono hKE)

end

/-- Constant scalar multiplication preserves vague convergence. -/
theorem IsBellmanVagueLimit.smul {mu : ℕ → Measure BellmanPuncturedPlane}
    {nu : Measure BellmanPuncturedPlane} (h : IsBellmanVagueLimit mu nu) (c : ENNReal) :
    IsBellmanVagueLimit (fun n => c • mu n) (c • nu) := by
  intro f hf hfc
  simp
  exact (h f hf hfc).const_smul c.toReal

/-- Positive compact tests transfer an ordered sequence to ordered Radon limits. -/
theorem bellman_vague_limit_le (mu eta : ℕ → Measure BellmanPuncturedPlane)
    (muInf etaInf : Measure BellmanPuncturedPlane)
    (he : ∀ n, IsFiniteMeasureOnCompacts (eta n))
    (hmInf : IsBellmanRadon muInf) (heInf : IsBellmanRadon etaInf)
    (hmv : IsBellmanVagueLimit mu muInf) (hev : IsBellmanVagueLimit eta etaInf)
    (hle : ∀ n, mu n ≤ eta n) : muInf ≤ etaInf := by
  let : LocallyCompactSpace BellmanPuncturedPlane :=
    isOpen_compl_singleton.locallyCompactSpace
  let := hmInf.1
  let := hmInf.2
  let := heInf.1
  let (n : ℕ) : IsFiniteMeasureOnCompacts (eta n) := he n
  apply bellman_measure_le_of_positive_tests
  intro f hf
  exact le_of_tendsto_of_tendsto' (hmv f f.continuous f.hasCompactSupport)
    (hev f f.continuous f.hasCompactSupport) (fun n => integral_mono_measure (hle n)
      (Eventually.of_forall hf) f.integrable)


/-- Multiplying both measures preserves the literal weak equation. -/
theorem IsBellmanStationaryAdjointPair.smul {mu eta : Measure BellmanPuncturedPlane}
    (h : IsBellmanStationaryAdjointPair mu eta) (c : ENNReal) :
    IsBellmanStationaryAdjointPair (c • mu) (c • eta) := by
  intro phi hphi hc hs
  rw [integral_smul_measure, integral_smul_measure, ← smul_add, h phi hphi hc hs, smul_zero]

/-- Positive finite common scaling preserves every source condition of an admissible pair. -/
theorem IsBellmanAdjointPair.smul {lam Lam beta : ℝ}
    {mu eta : Measure BellmanPuncturedPlane} (h : IsBellmanAdjointPair lam Lam beta mu eta)
    (c : ℝ) (hc : 0 < c) :
    IsBellmanAdjointPair lam Lam beta (ENNReal.ofReal c • mu) (ENNReal.ofReal c • eta) := by
  rcases h with ⟨hm, he, hn, hlo, hhi, hstat, hdm, hde⟩
  refine ⟨hm.smul _ ENNReal.ofReal_ne_top, he.smul _ ENNReal.ofReal_ne_top, ?_, ?_, ?_,
    hstat.smul _, hdm.smul _, hde.smul _⟩
  · have hcn : ENNReal.ofReal c ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hc)
    rcases hn with hn | hn
    · exact Or.inl (fun hz => hn ((Measure.ennreal_smul_eq_zero.mp hz).resolve_left hcn))
    · exact Or.inr (fun hz => hn ((Measure.ennreal_smul_eq_zero.mp hz).resolve_left hcn))
  · simpa only [smul_smul, mul_comm] using smul_le_smul_left (ENNReal.ofReal c) hlo
  · simpa only [smul_smul, mul_comm] using smul_le_smul_left (ENNReal.ofReal c) hhi


/-- A fixed compact normalization survives the limit and prevents a zero adjoint pair. -/
theorem bellman_vague_limit_pair (R betaInf : ℝ) (_hR : 1 ≤ R)
    (beta : ℕ → ℝ) (mu eta : ℕ → Measure BellmanPuncturedPlane)
    (muInf etaInf : Measure BellmanPuncturedPlane)
    (hbeta : Tendsto beta atTop (𝓝 betaInf))
    (hp : ∀ n, IsBellmanAdjointPair 1 R (beta n) (mu n) (eta n))
    (hmInf : IsBellmanRadon muInf) (heInf : IsBellmanRadon etaInf)
    (hmv : IsBellmanVagueLimit mu muInf) (hev : IsBellmanVagueLimit eta etaInf)
    (chi : (ℝ × ℝ) → ℝ) (hchi : Continuous chi) (hc : HasCompactSupport chi)
    (hs : tsupport chi ⊆ {q | q ≠ (0, 0)})
    (hone : ∀ n, ∫ q, chi q.val ∂mu n = 1) :
    IsBellmanAdjointPair 1 R betaInf muInf etaInf ∧
      (∫ q, chi q.val ∂muInf) = 1  := by
  have bellman_vague_limit_stationary (hstat : ∀ n, IsBellmanStationaryAdjointPair (mu n) (eta n)) :
      IsBellmanStationaryAdjointPair muInf etaInf := by
    intro phi hphi hc hs
    have bellman_stationary_test_properties :
        (Continuous (fun q : BellmanPuncturedPlane =>
        q.val.2 * fderiv ℝ phi q.val (1, 0)) ∧
        HasCompactSupport (fun q : BellmanPuncturedPlane =>
          q.val.2 * fderiv ℝ phi q.val (1, 0))) ∧
      (Continuous (fun q : BellmanPuncturedPlane =>
        fderiv ℝ (fun z => fderiv ℝ phi z (0, 1)) q.val (0, 1)) ∧
        HasCompactSupport (fun q : BellmanPuncturedPlane =>
          fderiv ℝ (fun z => fderiv ℝ phi z (0, 1)) q.val (0, 1))) := by
      have hl := bellman_contDiff_direction hphi (1, 0)
      have hr := bellman_contDiff_direction (bellman_contDiff_direction hphi (0, 1)) (0, 1)
      have hls : tsupport (fun q => q.2 * fderiv ℝ phi q (1, 0)) ⊆ tsupport phi :=
        tsupport_mul_subset_right.trans (tsupport_fderiv_apply_subset ℝ (1, 0))
      have hrs : tsupport (fun q =>
          fderiv ℝ (fun z => fderiv ℝ phi z (0, 1)) q (0, 1)) ⊆ tsupport phi :=
        (tsupport_fderiv_apply_subset ℝ (0, 1)).trans
          (tsupport_fderiv_apply_subset ℝ (0, 1))
      exact ⟨⟨(continuous_snd.mul hl.continuous).comp continuous_subtype_val,
          bellman_test_compact_subtype (hc.of_isClosed_subset (isClosed_tsupport _) hls)
            (hls.trans hs)⟩,
        ⟨hr.continuous.comp continuous_subtype_val,
          bellman_test_compact_subtype (hc.of_isClosed_subset (isClosed_tsupport _) hrs)
            (hrs.trans hs)⟩⟩
    obtain ⟨⟨hl, hlc⟩, ⟨hr, hrc⟩⟩ := bellman_stationary_test_properties
    have ht := (hmv _ hl hlc).add (hev _ hr hrc)
    have he := funext (fun n => hstat n phi hphi hc hs)
    rw [he] at ht
    exact tendsto_nhds_unique ht tendsto_const_nhds
  have ht := hmv (fun q => chi q.val) (hchi.comp continuous_subtype_val)
    (bellman_test_compact_subtype hc hs)
  have hn : (∫ q, chi q.val ∂muInf) = 1 := by
    rw [(funext hone)] at ht
    exact tendsto_nhds_unique ht tendsto_const_nhds
  have hnonzero : muInf ≠ 0 := by
    intro hz
    rw [hz, integral_zero_measure] at hn
    norm_num at hn
  exact ⟨⟨hmInf, heInf, Or.inl hnonzero, by
    simpa using (bellman_vague_limit_le mu eta muInf etaInf (fun n => (hp n).2.1.1) hmInf heInf hmv hev (fun n => by simpa using (hp n).2.2.2.1)), (bellman_vague_limit_le eta (fun n => ENNReal.ofReal R • mu n) etaInf (ENNReal.ofReal R • muInf) (fun n => ((hp n).1.smul _ ENNReal.ofReal_ne_top).1) heInf (hmInf.smul _ ENNReal.ofReal_ne_top) hev (hmv.smul _) (fun n => (hp n).2.2.2.2.1)), (bellman_vague_limit_stationary (fun n => (hp n).2.2.2.2.2.1)), (bellman_vague_limit_degree beta betaInf mu muInf hbeta (fun n => (hp n).2.2.2.2.2.2.1) hmInf hmv), (bellman_vague_limit_degree beta betaInf eta etaInf hbeta (fun n => (hp n).2.2.2.2.2.2.2) heInf hev)⟩, hn⟩


/-- Degree two provides the lower bound for the chosen exponent. -/
theorem bellmanAdjointExponent_two_le (R : ℝ) (hR : 1 ≤ R) :
    2 ≤ bellmanAdjointExponent R hR :=
  (bellmanAdjointExponent_characterization R hR).1.1
    (two_mem_bellmanAdmissibleDegrees R hR)


/-- The normalized homogeneous adjoint exponent lies in the source's half-open interval. -/
theorem bellmanAdjointExponent_range (R : ℝ) (hR : 1 ≤ R) :
    2 ≤ bellmanAdjointExponent R hR ∧ bellmanAdjointExponent R hR < 3  := by
  have bellmanAdjointExponent_lt_three :
      bellmanAdjointExponent R hR < 3 := by
    have hlu := (bellmanAdjointExponent_characterization R hR).1
    by_contra hlt
    have heq := le_antisymm (hlu.2 (fun b hb => (admissible_degree_lt_three R hR b hb).le)) (le_of_not_gt hlt)
    have hex (n : ℕ) : ∃ b ∈ bellmanAdmissibleDegrees R,
        3 - 1 / ((n : ℝ) + 1) < b ∧ b ≤ 3 := by
      have hp : 0 < 1 / ((n : ℝ) + 1) := by positivity
      simpa only [heq] using hlu.exists_between (by rw [heq]; linarith)
    choose beta hb hlo hhi using hex
    have hpairs (n : ℕ) : ∃ mu eta : Measure BellmanPuncturedPlane,
        IsBellmanAdjointPair 1 R (beta n) mu eta :=
      (mem_bellmanAdmissibleDegrees_iff R (beta n)).mp (hb n)
    choose mu eta hp using hpairs
    have hbeta : Tendsto beta atTop (𝓝 3) := by
      have ht : Tendsto (fun n : ℕ => 3 - 1 / ((n : ℝ) + 1)) atTop (𝓝 3) := by
        simpa using (tendsto_const_nhds (x := 3)).sub
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le ht tendsto_const_nhds
        (fun n => (hlo n).le) hhi
    have hbounded : ∃ a b : ℝ, ∀ n, a ≤ beta n ∧ beta n ≤ b := by
      refine ⟨2, 3, fun n => ⟨?_, hhi n⟩⟩
      have hd : 1 ≤ (n : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
      have hi := (div_le_one (by positivity)).mpr hd
      linarith [hlo n]
    obtain ⟨chi, hchi, hc, hs, _, _, _, c, hcp, hcn, k, hk,
      muInf, etaInf, hmInf, heInf, hmv, hev⟩ :=
      homogeneous_pairs_subsequence R hR beta mu eta hp hbounded
    have hs0 : tsupport chi ⊆ {q | q ≠ (0, 0)} := by
      intro q hq hz
      have hg := (hs hq).1
      rw [hz] at hg
      norm_num [bellmanGauge, bellmanGaugePower] at hg
    have hmem :=
      (mem_bellmanAdmissibleDegrees_iff R 3).mpr ⟨muInf, etaInf, (bellman_vague_limit_pair R 3 hR (fun n => beta (k n)) (fun n => ENNReal.ofReal (c (k n)) • mu (k n)) (fun n => ENNReal.ofReal (c (k n)) • eta (k n)) muInf etaInf (hbeta.comp hk.tendsto_atTop) (fun n => (hp (k n)).smul (c (k n)) (hcp (k n))) hmInf heInf hmv hev chi hchi.continuous hc hs0 (fun n => hcn (k n))).1⟩
    exact (lt_irrefl 3) (admissible_degree_lt_three R hR 3 hmem)
  exact ⟨bellmanAdjointExponent_two_le R hR, bellmanAdjointExponent_lt_three⟩

end HypoellipticAleksandrov.KineticAleksandrov

