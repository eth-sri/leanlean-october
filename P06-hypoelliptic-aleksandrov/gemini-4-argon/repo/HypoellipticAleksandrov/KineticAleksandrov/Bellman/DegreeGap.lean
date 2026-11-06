module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.Exponent
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.VagueAdjointLimit
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.HighDegreeExclusion
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.FundamentalMeasureStationary
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.FundamentalMeasureFubini
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.VagueAdjointLimitComparison
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.VagueAdjointLimitDegree
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.VagueAdjointLimitScaling
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.VagueAdjointLimitStationary
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.VagueCompactness
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AnnularNormalization
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.VagueCompactnessExhaustion
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularDisintegrationHomogeneity
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AnnularNormalizationAnnuli
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AnnularNormalizationBounds
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AnnularNormalizationCutoff
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AnnularNormalizationGeometry
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AnnularNormalizationMass
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.PairSetting
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.RatioNormalizationMeasure
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.MeasureTheory.Integral.CompactlySupported
import Mathlib.Topology.Order.Compact

/-! # Strict upper gap for the homogeneous adjoint exponent -/

@[expose] public section
noncomputable section
open Set MeasureTheory Filter Topology
namespace HypoellipticAleksandrov.KineticAleksandrov
open scoped CompactlySupported ENNReal NNReal

/- Degree two provides the lower bound for the chosen exponent. -/
theorem bellmanAdjointExponent_two_le (R : ℝ) (hR : 1 ≤ R) :
    2 ≤ bellmanAdjointExponent R hR :=
  (bellmanAdjointExponent_characterization R hR).1.1
    (two_mem_bellmanAdmissibleDegrees R hR)

/- The excluded endpoint remains excluded after taking the supremum of admissible degrees. -/
theorem bellmanAdjointExponent_lt_three (R : ℝ) (hR : 1 ≤ R) :
    bellmanAdjointExponent R hR < 3 := by
  have hlu := (bellmanAdjointExponent_characterization R hR).1
  have hle :=
    hlu.2 (fun b hb => (admissible_degree_lt_three R hR b hb).le)
  by_contra hlt
  have heq := le_antisymm hle (le_of_not_gt hlt)
  have hex (n : ℕ) : ∃ b ∈ bellmanAdmissibleDegrees R,
      3 - 1 / ((n : ℝ) + 1) < b ∧ b ≤ 3 := by
    have hp : 0 < 1 / ((n : ℝ) + 1) := by positivity
    simpa only [heq] using hlu.exists_between (by rw [heq]; linarith)
  choose beta hb hlo hhi using hex
  have hpairs (n : ℕ) : ∃ mu eta : Measure BellmanPuncturedPlane,
      IsBellmanAdjointPair 1 R (beta n) mu eta :=
    (mem_bellmanAdmissibleDegrees_iff R (beta n)).mp (hb n)
  choose mu eta hp using hpairs
  have hbeta : Tendsto beta atTop (𝓝 (3 : ℝ)) := by
    have ht : Tendsto (fun n : ℕ => 3 - 1 / ((n : ℝ) + 1)) atTop (𝓝 3) := by
      simpa using (tendsto_const_nhds (x := (3 : ℝ))).sub
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le ht tendsto_const_nhds
      (fun n => (hlo n).le) hhi
  have hbounded : ∃ a b : ℝ, ∀ n, a ≤ beta n ∧ beta n ≤ b := by
    refine ⟨2, 3, fun n => ⟨?_, hhi n⟩⟩
    have hd : 1 ≤ (n : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
    have hi : 1 / ((n : ℝ) + 1) ≤ 1 := (div_le_one (by positivity)).mpr hd
    linarith [hlo n]
  obtain ⟨chi, hchi, hc, hs, _, _, _, c, hcp, hcn, k, hk,
    muInf, etaInf, hmInf, heInf, hmv, hev⟩ : ∃ chi : (ℝ × ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) chi ∧ HasCompactSupport chi ∧
      tsupport chi ⊆ {q | 1 / 2 < bellmanGauge q ∧ bellmanGauge q < 4} ∧
      (∀ q, 0 ≤ chi q ∧ chi q ≤ 1) ∧
      (∀ q, 1 ≤ bellmanGauge q → bellmanGauge q ≤ 2 → chi q = 1) ∧
      (∃ chi0 : ℝ → ℝ, ∀ q, chi q = chi0 (bellmanGauge q)) ∧
      ∃ c : ℕ → ℝ, (∀ n, 0 < c n) ∧
        (∀ n, ∫ q, chi q.val ∂(ENNReal.ofReal (c n) • mu n) = 1) ∧
        ∃ k : ℕ → ℕ, StrictMono k ∧ ∃ muinf etainf : Measure BellmanPuncturedPlane,
          IsBellmanRadon muinf ∧ IsBellmanRadon etainf ∧
          IsBellmanVagueLimit (fun n => ENNReal.ofReal (c (k n)) • mu (k n)) muinf ∧
          IsBellmanVagueLimit (fun n => ENNReal.ofReal (c (k n)) • eta (k n)) etainf := by
    obtain ⟨chi, hchi, hc, hs, hr, hone, hrad, c, hcp, hcn, hbound⟩ : ∃ chi : (ℝ × ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) chi ∧ HasCompactSupport chi ∧
      tsupport chi ⊆ {q | 1 / 2 < bellmanGauge q ∧ bellmanGauge q < 4} ∧
      (∀ q, 0 ≤ chi q ∧ chi q ≤ 1) ∧
      (∀ q, 1 ≤ bellmanGauge q → bellmanGauge q ≤ 2 → chi q = 1) ∧
      (∃ chi0 : ℝ → ℝ, ∀ q, chi q = chi0 (bellmanGauge q)) ∧
      ∃ c : ℕ → ℝ, (∀ n, 0 < c n) ∧
        (∀ n, ∫ q, chi q.val ∂(ENNReal.ofReal (c n) • mu n) = 1) ∧
        ∀ K : Set BellmanPuncturedPlane, IsCompact K → ∃ C : ℝ≥0,
          ∀ n, (ENNReal.ofReal (c n) • mu n) K ≤ C ∧
            (ENNReal.ofReal (c n) • eta n) K ≤ C := by
      obtain ⟨chi, hchi, hc, hs, hr, hone, hrad⟩ := exists_bellman_annular_cutoff
      have hpos (n : ℕ) : 0 < ∫ q, chi q.val ∂mu n :=
        bellman_annular_integral_pos _ _ (hp n).1 (hp n).left_ne_zero
          (hp n).2.2.2.2.2.2.1 chi hchi.continuous hc hs (fun q => (hr q).1) hone
      have hn (n : ℕ) : ∃ c : ℝ, 0 < c ∧ ∫ q, chi q.val ∂(ENNReal.ofReal c • (mu n)) = 1 := by
        let mu := (mu n)
        have hp := (hpos n)
        refine ⟨(∫ q, chi q.val ∂mu)⁻¹, inv_pos.mpr hp, ?_⟩
        rw [integral_smul_measure, ENNReal.toReal_ofReal (inv_nonneg.mpr hp.le), smul_eq_mul,
          inv_mul_cancel₀ hp.ne']
      choose c hcp hcn using hn
      let nu (n : ℕ) := ENNReal.ofReal (c n) • mu n
      have hradnu (n : ℕ) : IsBellmanRadon (nu n) :=
        (hp n).1.smul _ ENNReal.ofReal_ne_top
      let (n : ℕ) : IsFiniteMeasureOnCompacts (nu n) := (hradnu n).1
      have hdeg (n : ℕ) : HasBellmanDensityDegree (beta n) (nu n) :=
        (hp n).2.2.2.2.2.2.1.smul _
      have hunit (n : ℕ) : nu n bellmanUnitAnnulus ≤ 1 := by
        have hi : Integrable (fun q : BellmanPuncturedPlane => chi q.val) (nu n) :=
          (hchi.continuous.comp continuous_subtype_val).integrable_of_hasCompactSupport
            (bellman_annular_test_compact chi hc hs)
        have h := hi.measure_le_integral (Filter.Eventually.of_forall
          (fun q : BellmanPuncturedPlane => (hr q.val).1))
          (s := bellmanUnitAnnulus) (fun q hq => by rw [hone _ hq.1 hq.2])
        rw [hcn n, ENNReal.ofReal_one] at h
        exact h
      refine ⟨chi, hchi, hc, hs, hr, hone, hrad, c, hcp, hcn, ?_⟩
      intro K hK
      obtain ⟨C, hC⟩ : ∃ C : ℝ≥0, ∀ n, nu n K ≤ C := by
        obtain ⟨a, b, hbounded⟩ := hbounded
        have hf (j : ℤ) := bellman_degree_factor_bounded (2 ^ j)
          (zpow_pos (by norm_num) j) a b
        choose C hC using hf
        have hclosed (n : ℕ) (j : ℤ) : nu n (bellmanDyadicAnnulus j) ≤ C j := by
          rw [bellmanDyadicAnnulus, hdeg n _ _ _ bellmanUnitAnnulus_isCompact.measurableSet]
          calc ENNReal.ofReal ((2 ^ j) ^ (4 - beta n)) * nu n bellmanUnitAnnulus
              ≤ ENNReal.ofReal ((2 ^ j) ^ (4 - beta n)) * 1 := mul_le_mul_right (hunit n) _
            _ ≤ C j := by rw [mul_one]; exact hC j _ (hbounded n)
        have hopen (n : ℕ) (j : ℤ) :
            nu n (bellmanOpenDyadicAnnulus j) ≤ (C j : ℝ≥0∞) + C (j + 1) :=
          (measure_mono (bellmanOpenDyadicAnnulus_subset j)).trans
            ((measure_union_le _ _).trans (add_le_add (hclosed n j) (hclosed n (j + 1))))
        obtain ⟨s, hs⟩ := hK.elim_finite_subcover bellmanOpenDyadicAnnulus
          bellmanOpenDyadicAnnulus_isOpen (by rw [bellmanOpenDyadicAnnulus_iUnion]; exact subset_univ K)
        refine ⟨∑ j ∈ s, (C j + C (j + 1)), ?_⟩
        intro n
        calc nu n K ≤ nu n (⋃ j ∈ s, bellmanOpenDyadicAnnulus j) := measure_mono hs
          _ ≤ ∑ j ∈ s, nu n (bellmanOpenDyadicAnnulus j) := measure_biUnion_finset_le _ _
          _ ≤ ∑ j ∈ s, ((C j : ℝ≥0∞) + C (j + 1)) := Finset.sum_le_sum (fun j _ => hopen n j)
          _ = _ := by simp only [ENNReal.ofNNReal_finsetSum, ENNReal.coe_add]
      let M : ℝ≥0 := ⟨R, zero_le_one.trans hR⟩
      refine ⟨C + M * C, ?_⟩
      intro n
      have hm : nu n K ≤ (C : ℝ≥0∞) + M * C :=
        (hC n).trans (le_add_right le_rfl)
      have hh := smul_le_smul_left (ENNReal.ofReal (c n)) (hp n).2.2.2.2.1
      have he : (ENNReal.ofReal (c n) • eta n) ≤ ENNReal.ofReal R • nu n := by
        simpa only [nu, smul_smul, mul_comm] using hh
      have heK := Measure.le_iff.mp he K hK.measurableSet
      rw [Measure.smul_apply, smul_eq_mul] at heK
      have heM : ENNReal.ofReal R = (M : ℝ≥0∞) :=
        ENNReal.ofReal_eq_coe_nnreal (zero_le_one.trans hR)
      rw [heM] at heK
      constructor
      · simpa only [ENNReal.coe_add, ENNReal.coe_mul] using hm
      · calc (ENNReal.ofReal (c n) • eta n) K ≤ (M : ℝ≥0∞) * nu n K := heK
          _ ≤ (M : ℝ≥0∞) * C := mul_le_mul_right (hC n) _
          _ ≤ (C : ℝ≥0∞) + M * C := le_add_left le_rfl
          _ = _ := by simp only [ENNReal.coe_add, ENNReal.coe_mul]
    obtain ⟨k, hk, muinf, etainf, hmf, hef, hmt, het⟩ :=
      bellman_radon_pair_subsequence (fun n => ENNReal.ofReal (c n) • mu n)
        (fun n => ENNReal.ofReal (c n) • eta n)
        (fun n => (hp n).1.smul _ ENNReal.ofReal_ne_top)
        (fun n => (hp n).2.1.smul _ ENNReal.ofReal_ne_top) hbound
    exact ⟨chi, hchi, hc, hs, hr, hone, hrad, c, hcp, hcn, k, hk,
      muinf, etainf, hmf, hef, hmt, het⟩
  have hs0 : tsupport chi ⊆ {q | q ≠ (0, 0)} := by
    intro q hq hz
    have hg := (hs hq).1
    rw [hz] at hg
    norm_num [bellmanGauge, bellmanGaugePower] at hg
  have hlim : IsBellmanAdjointPair 1 R 3 muInf etaInf ∧
      (∫ q, chi q.val ∂muInf) = 1 := by
    let beta := (fun n => beta (k n))
    let mu := (fun n => ENNReal.ofReal (c (k n)) • mu (k n))
    let eta := (fun n => ENNReal.ofReal (c (k n)) • eta (k n))
    have hbeta := (hbeta.comp hk.tendsto_atTop)
    have hp := (fun n => (hp (k n)).smul (c (k n)) (hcp (k n)))
    have hchi := hchi.continuous
    have hone := (fun n => hcn (k n))
    have ht := hmv (fun q => chi q.val) (hchi.comp continuous_subtype_val)
      (bellman_test_compact_subtype hc hs0)
    have hn : (∫ q, chi q.val ∂muInf) = 1 := by
      have he := funext hone
      rw [he] at ht
      exact tendsto_nhds_unique ht tendsto_const_nhds
    have hnonzero : muInf ≠ 0 := by
      intro hz
      rw [hz, integral_zero_measure] at hn
      norm_num at hn
    have hlo := bellman_vague_limit_le mu eta muInf etaInf
      (fun n => (hp n).2.1.1) hmInf heInf hmv hev
      (fun n => by simpa only [ENNReal.ofReal_one, one_smul] using (hp n).2.2.2.1)
    have hhi : etaInf ≤ ENNReal.ofReal R • muInf := bellman_vague_limit_le eta
      (fun n => ENNReal.ofReal R • mu n) etaInf (ENNReal.ofReal R • muInf)
      (fun n => ((hp n).1.smul _ ENNReal.ofReal_ne_top).1)
      heInf (hmInf.smul _ ENNReal.ofReal_ne_top) hev (hmv.smul _) (fun n => (hp n).2.2.2.2.1)
    have hstat : IsBellmanStationaryAdjointPair muInf etaInf := by
      have hstat := (fun n => (hp n).2.2.2.2.2.1)
      intro phi hphi hc hs
      obtain ⟨⟨hl, hlc⟩, ⟨hr, hrc⟩⟩ : (Continuous (fun q : BellmanPuncturedPlane =>
          q.val.2 * fderiv ℝ phi q.val (1, 0)) ∧
          HasCompactSupport (fun q : BellmanPuncturedPlane =>
            q.val.2 * fderiv ℝ phi q.val (1, 0))) ∧
        (Continuous (fun q : BellmanPuncturedPlane =>
          fderiv ℝ (fun z => fderiv ℝ phi z (0, 1)) q.val (0, 1)) ∧
          HasCompactSupport (fun q : BellmanPuncturedPlane =>
            fderiv ℝ (fun z => fderiv ℝ phi z (0, 1)) q.val (0, 1))) := by
          have hl := bellman_contDiff_direction hphi (1, 0)
          have hv := bellman_contDiff_direction hphi (0, 1)
          have hr := bellman_contDiff_direction hv (0, 1)
          have hls : tsupport (fun q : ℝ × ℝ => q.2 * fderiv ℝ phi q (1, 0)) ⊆ tsupport phi :=
            tsupport_mul_subset_right.trans (tsupport_fderiv_apply_subset ℝ (1, 0))
          have hrs : tsupport (fun q : ℝ × ℝ =>
              fderiv ℝ (fun z => fderiv ℝ phi z (0, 1)) q (0, 1)) ⊆ tsupport phi :=
            (tsupport_fderiv_apply_subset ℝ (0, 1)).trans
              (tsupport_fderiv_apply_subset ℝ (0, 1))
          exact ⟨⟨(continuous_snd.mul hl.continuous).comp continuous_subtype_val,
              bellman_test_compact_subtype (hc.of_isClosed_subset (isClosed_tsupport _) hls)
                (hls.trans hs)⟩,
            ⟨hr.continuous.comp continuous_subtype_val,
              bellman_test_compact_subtype (hc.of_isClosed_subset (isClosed_tsupport _) hrs)
                (hrs.trans hs)⟩⟩

        /- The actual stationary identity passes to the common vague limit. -/
      have ht := (hmv _ hl hlc).add (hev _ hr hrc)
      have he : (fun n =>
          (∫ q, q.val.2 * fderiv ℝ phi q.val (1, 0) ∂mu n) +
          (∫ q, fderiv ℝ (fun z => fderiv ℝ phi z (0, 1)) q.val (0, 1) ∂eta n)) =
          fun _ : ℕ => (0 : ℝ) := funext (fun n => hstat n phi hphi hc hs)
      rw [he] at ht
      exact tendsto_nhds_unique ht tendsto_const_nhds
    have hdm := bellman_vague_limit_degree beta 3 mu muInf hbeta
      (fun n => (hp n).2.2.2.2.2.2.1) hmInf hmv
    have hde := bellman_vague_limit_degree beta 3 eta etaInf hbeta
      (fun n => (hp n).2.2.2.2.2.2.2) heInf hev
    exact ⟨⟨hmInf, heInf, Or.inl hnonzero, by
      simpa only [ENNReal.ofReal_one, one_smul] using hlo, hhi, hstat, hdm, hde⟩, hn⟩
  have hmem : 3 ∈ bellmanAdmissibleDegrees R :=
    (mem_bellmanAdmissibleDegrees_iff R 3).mpr ⟨muInf, etaInf, hlim.1⟩
  exact (lt_irrefl (3 : ℝ)) (admissible_degree_lt_three R hR 3 hmem)

/- The normalized homogeneous adjoint exponent lies in the source's half-open interval. -/
theorem bellmanAdjointExponent_range (R : ℝ) (hR : 1 ≤ R) :
    2 ≤ bellmanAdjointExponent R hR ∧ bellmanAdjointExponent R hR < 3 :=
  ⟨bellmanAdjointExponent_two_le R hR, bellmanAdjointExponent_lt_three R hR⟩

end HypoellipticAleksandrov.KineticAleksandrov
