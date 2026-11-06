/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.Brownian.Barrier.KilledMarkov
public import DOZZ.Brownian.WilliamsMaximumLaw
public import DOZZ.Statements.Brownian.BrownianPostMaximumPath
public import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
/-!
# The actual negative-drift maximum and its unique split

Summable endpoint and restarted-tail escape bounds imply escape to minus
infinity. Compact attainment then identifies the literal supremum. Its law is
the exact exponential reference measure, with no atoms.

At each deterministic rational cut, raw-past independence and the atomless
future maximum exclude a tie. Two distinct maximizing times would straddle
such a cut. This proves uniqueness on the original continuous Brownian paths.
The maximizing time and its literal pre/post path maps are almost surely
measurable. These are the geometric inputs for the thin-band proof; this
module does not assert the Williams disintegration itself.
-/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
namespace DOZZ.Proofs

private theorem exponential_series_finite c (hc : 0 < c) :
    (∑' n : ℕ, ENNReal.ofReal (Real.exp (-c*(n : ℝ)))) ≠ ∞ := by
  have he (n : ℕ) : ENNReal.ofReal (Real.exp (-c*(n : ℝ))) = (ENNReal.ofReal (Real.exp (-c)))^n := by
    rw [← ENNReal.ofReal_pow (Real.exp_pos _).le,← Real.exp_nat_mul]
    congr 2
    ring
  simp_rw [he]
  rw [ENNReal.tsum_geometric]
  apply ENNReal.inv_ne_top.mpr
  exact ne_of_gt (tsub_pos_iff_lt.mpr (by
    rw [ENNReal.ofReal_lt_one]
    exact Real.exp_lt_one_iff.mpr (neg_neg_of_pos hc)))




/-- The global negative-drift maximum is attained and its entire range is bounded above almost surely. -/
theorem brownianPath_negativeDrift_maximum_attained_ae (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (ν : ℝ) (hν : 0 < ν) :
    ∀ᵐ p ∂P, BddAbove (range (fun t : ℝ≥0 => p t-ν*(t : ℝ))) ∧
      ∃ σ : ℝ≥0, p σ-ν*(σ : ℝ) = driftedBrownianMaximum ν p := by
  have maximum_attained_of_escape (p : BrownianPath) (hp : Tendsto (fun t : ℝ≥0 => p t-ν*(t : ℝ)) atTop atBot) : ∃ σ : ℝ≥0, ∀ t : ℝ≥0, p t-ν*(t : ℝ) ≤ p σ-ν*(σ : ℝ) := by
    obtain ⟨T,hT⟩ := eventually_atTop.mp ((tendsto_atBot.mp hp) (p 0))
    let X := driftedBrownianPath (-ν) p
    obtain ⟨σ,hσ⟩ := brownianPath_runningMaximum_attained X T
    refine ⟨σ.1,fun t => ?_⟩
    by_cases ht : t ≤ T
    · have hh := le_ciSup (brownianPath_Iic_bddAbove X T) (⟨t,ht⟩ : Iic T)
      rw [hσ] at hh
      change p t+(-ν)*(t : ℝ) ≤ p σ.1+(-ν)*(σ.1 : ℝ) at hh
      simpa only [neg_mul,sub_eq_add_neg] using hh
    · have hh0 := le_ciSup (brownianPath_Iic_bddAbove X T) (⟨(0 : ℝ≥0),(zero_le : (0 : ℝ≥0) ≤ T)⟩ : Iic T)
      rw [hσ] at hh0
      rw [(show X 0 = p 0 by change p 0+(-ν)*(0 : ℝ) = p 0; rw [mul_zero,add_zero])] at hh0
      change p 0 ≤ p σ.1+(-ν)*(σ.1 : ℝ) at hh0
      exact (hT t (le_of_lt (lt_of_not_ge ht))).trans (by simpa only [neg_mul,sub_eq_add_neg] using hh0)
  have brownianPath_negativeDrift_tendsto_atBot : ∀ᵐ p ∂P, Tendsto (fun t : ℝ≥0 => p t-ν*(t : ℝ)) atTop atBot := by
    have endpoint_escape_bound (n : ℕ) : P {p : BrownianPath | ν*(n : ℝ)/4 < p (n : ℝ≥0)} ≤ ENNReal.ofReal (Real.exp (-(ν^2/32)*(n : ℝ))) := by
      have hb := brownian_terminal_event_bound hB.toIsPreBrownianReal (n : ℝ≥0) (-ν/4)
        (-ν^2*(n : ℝ)/16) {p : BrownianPath | ν*(n : ℝ)/4 < p (n : ℝ≥0)} (fun p hp => by
          nlinarith only [(mul_le_mul_of_nonpos_left hp.le (show -ν/4 ≤ 0 by linarith))])
      convert hb using 2
      congr 1
      rw [NNReal.coe_natCast]
      ring
    let C : ℕ → Set BrownianPath := fun n => {p | ∃ u : ℝ≥0,
      ν*(n : ℝ)/4 < p ((n : ℝ≥0)+u)-p (n : ℝ≥0)-ν*(u : ℝ)}
    have hC : (∑' n, P (C n)) ≠ ∞ := by
      have hc (n : ℕ) : P (C n) = ENNReal.ofReal (Real.exp (-(ν^2/2)*(n : ℝ))) := by
        convert (negativeDriftBrownian_maximum_tail P (fun u p => p ((n : ℝ≥0)+u)-p (n : ℝ≥0)) (hB.shift (n : ℝ≥0)) ν (ν*(n : ℝ)/4) hν (by positivity)) using 2
        congr 1
        ring
      simp_rw [hc]
      exact exponential_series_finite (ν^2/2) (by positivity)
    filter_upwards [ae_eventually_notMem (ne_top_of_le_ne_top (exponential_series_finite (ν^2/32) (by positivity)) (ENNReal.tsum_le_tsum (fun n => endpoint_escape_bound n))),ae_eventually_notMem hC] with p hpA hpC
    obtain ⟨N,hN⟩ := eventually_atTop.mp (hpA.and hpC)
    apply tendsto_atBot.mpr
    intro R
    obtain ⟨n,hn⟩ := exists_nat_gt (max (N : ℝ) (-2*R/ν))
    have hnN : N ≤ n := by exact_mod_cast (le_max_left _ _).trans hn.le
    have hR : -ν*(n : ℝ)/2 ≤ R := by
      have hh' := mul_le_mul_of_nonneg_right ((le_max_right _ _).trans hn.le) hν.le
      rw [(show (-2*R/ν)*ν = -2*R by field_simp)] at hh'
      linarith only [hh']
    refine eventually_atTop.mpr ⟨(n : ℝ≥0),fun t ht => ?_⟩
    have hy := not_lt.mp (fun h => (hN n hnN).2 ⟨t-(n : ℝ≥0),h⟩)
    rw [add_tsub_cancel_of_le ht,NNReal.coe_sub ht,NNReal.coe_natCast] at hy
    exact (show p t-ν*(t : ℝ) ≤ -ν*(n : ℝ)/2 by linarith only [(not_lt.mp (hN n hnN).1),hy]).trans hR
  filter_upwards [brownianPath_negativeDrift_tendsto_atBot] with p hp
  obtain ⟨σ,hσ⟩ := maximum_attained_of_escape p hp
  have hb : BddAbove (range (fun t : ℝ≥0 => p t-ν*(t : ℝ))) := ⟨p σ-ν*(σ : ℝ),by
    rintro y ⟨t,rfl⟩
    exact hσ t⟩
  refine ⟨hb,σ,?_⟩
  apply le_antisymm (le_csSup hb (mem_range_self σ))
  exact csSup_le (range_nonempty _) (by rintro y ⟨t,rfl⟩; exact hσ t)

/-- The maximum `DOZZ.driftedBrownianMaximum` is measurable under any positive-drift Brownian
law. -/
theorem aemeasurable_driftedBrownianMaximum (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) ν (hν : 0 < ν) :
    AEMeasurable (driftedBrownianMaximum ν) P := by
  obtain ⟨D,hDc,hDd⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
  let _ := hDc.to_subtype
  apply (Measurable.iSup (fun (u : D) => (ContinuousMap.measurable_eval u.1).sub measurable_const)).aemeasurable.congr
  filter_upwards [brownianPath_negativeDrift_maximum_attained_ae P hB ν hν] with p hp
  exact hDd.ciSup (p.continuous.sub (continuous_const.mul NNReal.continuous_coe)) hp.1

/-- On a bounded path the first hit of the global maximum equals its maximizing time. -/
theorem firstPassageTime_globalMaximum ν p
    (hb : BddAbove (range (fun t : ℝ≥0 => p t-ν*(t : ℝ)))) :
    firstPassageTime (driftedBrownianPath (-ν) p) (driftedBrownianMaximum ν p) =
      driftedBrownianMaximumTime ν p := by
  unfold firstPassageTime driftedBrownianMaximumTime
  congr 1
  ext t
  change driftedBrownianMaximum ν p ≤ p t+(-ν)*(t : ℝ) ↔
    p t-ν*(t : ℝ) = driftedBrownianMaximum ν p
  simp only [neg_mul,← sub_eq_add_neg]
  exact ⟨fun h => le_antisymm (le_csSup hb (mem_range_self t)) h,fun h => h.ge⟩

/-- The actual global maximizing time is measurable under the Brownian law. -/
theorem aemeasurable_driftedBrownianMaximumTime (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) ν (hν : 0 < ν) :
    AEMeasurable (driftedBrownianMaximumTime ν) P := by
  apply (measurable_firstPassageTime_joint.comp_aemeasurable ((aemeasurable_driftedBrownianMaximum P hB ν hν).prodMk (continuous_driftedBrownianPath.measurable.comp (measurable_const.prodMk measurable_id)).aemeasurable)).congr
  filter_upwards [brownianPath_negativeDrift_maximum_attained_ae P hB ν hν] with p hp
  exact firstPassageTime_globalMaximum ν p hp.1

/-- The literal lifetime-marked path preceding the maximum is measurable. -/
theorem aemeasurable_brownianPreMaximumSegment (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) ν (hν : 0 < ν) :
    AEMeasurable (brownianPreMaximumSegment ν) P := by
  have hσ := aemeasurable_driftedBrownianMaximumTime P hB ν hν
  convert hσ.prodMk (continuous_stopBrownianPath.measurable.comp_aemeasurable
    (hσ.prodMk (continuous_driftedBrownianPath.measurable.comp (measurable_const.prodMk measurable_id)).aemeasurable)) using 1
  funext p
  dsimp only [brownianPreMaximumSegment,Function.comp_def]
  congr 1
  congr 1
  apply ContinuousMap.ext
  intro t
  change p t-ν*(t : ℝ) = p t+(-ν)*(t : ℝ)
  ring

/-- The literal path following and recentered at the global maximum is measurable. -/
theorem aemeasurable_brownianPostMaximumPath (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) ν (hν : 0 < ν) :
    AEMeasurable (brownianPostMaximumPath ν) P := by
  have hc : Continuous (fun z : (ℝ≥0 × BrownianPath) × ℝ =>
      (⟨fun t => z.1.2 (z.1.1+t)-z.2,by fun_prop⟩ : BrownianPath)) := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun z : ((ℝ≥0 × BrownianPath) × ℝ) × ℝ≥0 =>
      z.1.1.2 (z.1.1.1+z.2)-z.1.2)
    exact (continuous_eval.comp (continuous_fst.fst.snd.prodMk
      (continuous_fst.fst.fst.add continuous_snd))).sub continuous_fst.snd
  convert hc.measurable.comp_aemeasurable (((aemeasurable_driftedBrownianMaximumTime P hB ν hν).prodMk (continuous_driftedBrownianPath.measurable.comp (measurable_const.prodMk measurable_id)).aemeasurable).prodMk (aemeasurable_driftedBrownianMaximum P hB ν hν)) using 1
  funext p
  apply ContinuousMap.ext
  intro t
  change p (driftedBrownianMaximumTime ν p+t)-ν*((driftedBrownianMaximumTime ν p+t : ℝ≥0) : ℝ)-
      driftedBrownianMaximum ν p =
    p (driftedBrownianMaximumTime ν p+t)+(-ν)*((driftedBrownianMaximumTime ν p+t : ℝ≥0) : ℝ)-
      driftedBrownianMaximum ν p
  ring

/-- The global maximum has the exact exponential upper tail. -/
theorem brownianPath_globalMaximum_Ioi (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) ν x (hν : 0 < ν) (hx : 0 ≤ x) :
    P.map (driftedBrownianMaximum ν) (Ioi x) = ENNReal.ofReal (Real.exp (-2*ν*x)) := by
  rw [Measure.map_apply_of_aemeasurable (aemeasurable_driftedBrownianMaximum P hB ν hν)
    measurableSet_Ioi]
  have he : (fun p => driftedBrownianMaximum ν p ∈ Ioi x) =ᵐ[P]
      (fun p => ∃ t : ℝ≥0, x < p t-ν*(t : ℝ)) := by
    filter_upwards [brownianPath_negativeDrift_maximum_attained_ae P hB ν hν] with p hp
    apply propext
    constructor
    · intro h
      obtain ⟨σ,hσ⟩ := hp.2
      exact ⟨σ,hσ ▸ h⟩
    · rintro ⟨t,ht⟩
      exact ht.trans_le (le_csSup hp.1 (mem_range_self t))
  exact (measure_congr he).trans (brownianPath_negativeDrift_maximum_tail P hB ν x hν hx)

/-- A Brownian path's maximum is nonnegative almost surely. -/
theorem brownianPath_globalMaximum_nonneg_ae (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) ν (hν : 0 < ν) :
    ∀ᵐ p ∂P, 0 ≤ driftedBrownianMaximum ν p := by
  filter_upwards [brownianPath_negativeDrift_maximum_attained_ae P hB ν hν,
    hB.eval_zero_ae_eq_zero] with p hp hp0
  have hh := le_csSup hp.1 (mem_range_self (0 : ℝ≥0))
  change p 0-ν*(0 : ℝ) ≤ driftedBrownianMaximum ν p at hh
  simpa only [mul_zero,sub_zero,hp0] using hh

/-- The literal maximum has the Williams reference law. -/
theorem brownianPath_globalMaximum_map (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) ν (hν : 0 < ν) :
    P.map (driftedBrownianMaximum ν) = brownianMaximumReferenceLaw ν := by
  let _ := (hB.hasLaw_eval 0).isProbabilityMeasure
  let _ := isProbabilityMeasure_expMeasure (show 0 < 2*ν by positivity)
  rw [brownianMaximumReferenceLaw_eq_expMeasure]
  apply Measure.ext_of_Iic
  intro x
  rw [← ofReal_cdf (expMeasure (2*ν)) x, cdf_expMeasure_eq (by positivity : 0 < 2*ν)]
  by_cases hx : 0 ≤ x
  · rw [ite_eq_left hx,← compl_Ioi,prob_compl_eq_one_sub measurableSet_Ioi,
      brownianPath_globalMaximum_Ioi P hB ν x hν hx]
    rw [ENNReal.ofReal_sub 1,ENNReal.ofReal_one]
    · exact congrArg (fun r : ℝ => (1 : ℝ≥0∞)-ENNReal.ofReal (Real.exp r)) (by ring)
    · exact (Real.exp_pos _).le
  · rw [ite_eq_right hx,ENNReal.ofReal_zero,Measure.map_apply_of_aemeasurable
      (aemeasurable_driftedBrownianMaximum P hB ν hν) measurableSet_Iic]
    apply measure_mono_null (t := {p | driftedBrownianMaximum ν p < 0})
    · intro p hp
      exact hp.trans_lt (lt_of_not_ge hx)
    · have hh : ∀ᵐ p ∂P, ¬driftedBrownianMaximum ν p < 0 :=
        (brownianPath_globalMaximum_nonneg_ae P hB ν hν).mono (fun p hp => not_lt.mpr hp)
      simpa only [ae_iff,Classical.not_not] using hh

/-- The maximum law has no atoms; ties against an independent past maximum have zero probability. -/
theorem noAtoms_brownianMaximumReferenceLaw ν : NullSingletonClass (brownianMaximumReferenceLaw ν) := by
  unfold brownianMaximumReferenceLaw
  infer_instance

/-- The past maximum relative to the endpoint of a deterministic interval. -/
noncomputable def brownianPastMaximumGap (ν : ℝ) (s : ℝ≥0) (p : BrownianPath) : ℝ :=
  (⨆ u : Iic s, p u-ν*(u : ℝ))-(p s-ν*(s : ℝ))



/-- Two attained global maxima on opposite sides of a cut force equal maximum gaps. -/
theorem brownianPath_maximum_tie_of_two_hits (ν : ℝ) (p : BrownianPath) (s u v : ℝ≥0)
    (hb : BddAbove (range (fun t : ℝ≥0 => p t-ν*(t : ℝ))))
    (hu : u ≤ s) (hv : s ≤ v)
    (hpu : p u-ν*(u : ℝ) = driftedBrownianMaximum ν p)
    (hpv : p v-ν*(v : ℝ) = driftedBrownianMaximum ν p) :
    brownianPastMaximumGap ν s p = driftedBrownianMaximum ν (brownianShiftPath s p) := by
  let M := driftedBrownianMaximum ν p
  have hmax (t : ℝ≥0) : p t-ν*(t : ℝ) ≤ M := le_csSup hb (mem_range_self t)
  have hb' : BddAbove (range (fun t : ℝ≥0 => brownianShiftPath s p t-ν*(t : ℝ))) := by
    refine ⟨M-(p s-ν*(s : ℝ)),?_⟩
    rintro y ⟨t,rfl⟩
    have hh := hmax (s+t)
    rw [NNReal.coe_add] at hh
    change p (s+t)-p s-ν*(t : ℝ) ≤ M-(p s-ν*(s : ℝ))
    linarith only [hh]
  have hpast : (⨆ t : Iic s, p t-ν*(t : ℝ)) = M := by
    apply le_antisymm (ciSup_le (fun t : Iic s => hmax t))
    change p u-ν*(u : ℝ) = M at hpu
    rw [← hpu]
    have hbI : BddAbove (range (fun u : Iic s => p u-ν*(u : ℝ))) := by
      have hh := brownianPath_Iic_bddAbove (driftedBrownianPath (-ν) p) s
      change BddAbove (range (fun u : Iic s => p u+(-ν)*(u : ℝ))) at hh
      simpa only [neg_mul,← sub_eq_add_neg] using hh
    exact le_ciSup hbI (⟨u,hu⟩ : Iic s)
  have hfuture : driftedBrownianMaximum ν (brownianShiftPath s p) = M-(p s-ν*(s : ℝ)) := by
    apply le_antisymm (csSup_le (range_nonempty _) (by
      rintro y ⟨t,rfl⟩
      have hh := hmax (s+t)
      rw [NNReal.coe_add] at hh
      change p (s+t)-p s-ν*(t : ℝ) ≤ M-(p s-ν*(s : ℝ))
      linarith only [hh]))
    have hh := le_csSup hb' (mem_range_self (v-s))
    change p (s+(v-s))-p s-ν*((v-s : ℝ≥0) : ℝ) ≤
      driftedBrownianMaximum ν (brownianShiftPath s p) at hh
    rw [add_tsub_cancel_of_le hv,NNReal.coe_sub hv] at hh
    change p v-ν*(v : ℝ) = M at hpv
    change M-(p s-ν*(s : ℝ)) ≤ driftedBrownianMaximum ν (brownianShiftPath s p)
    nlinarith only [hh,hpv]
  rw [brownianPastMaximumGap,hpast,hfuture]

/-- The maximizing time attains the global maximum almost surely. -/
theorem brownianPath_globalMaximumTime_attains_ae (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) ν (hν : 0 < ν) :
    ∀ᵐ p ∂P, p (driftedBrownianMaximumTime ν p)-ν*(driftedBrownianMaximumTime ν p : ℝ) =
      driftedBrownianMaximum ν p := by
  filter_upwards [brownianPath_negativeDrift_maximum_attained_ae P hB ν hν] with p hp
  have hh := firstPassageTime_mem (driftedBrownianPath (-ν) p) (driftedBrownianMaximum ν p)
    (by
      obtain ⟨t,ht⟩ := hp.2
      refine ⟨t,?_⟩
      change driftedBrownianMaximum ν p ≤ p t+(-ν)*(t : ℝ)
      simpa only [neg_mul,← sub_eq_add_neg] using ht.ge)
  rw [firstPassageTime_globalMaximum ν p hp.1] at hh
  have hl := le_csSup hp.1 (mem_range_self (driftedBrownianMaximumTime ν p))
  change p (driftedBrownianMaximumTime ν p)-ν*(driftedBrownianMaximumTime ν p : ℝ) ≤
    driftedBrownianMaximum ν p at hl
  apply le_antisymm hl
  change driftedBrownianMaximum ν p ≤ p (driftedBrownianMaximumTime ν p)+
    (-ν)*(driftedBrownianMaximumTime ν p : ℝ) at hh
  simpa only [neg_mul,← sub_eq_add_neg] using hh



/-- The first hits of levels approaching the actual maximum converge to its unique maximizing time. -/
theorem brownianPath_firstPassageTime_tendsto_globalMaximumTime_ae (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) ν (hν : 0 < ν) :
    ∀ᵐ p ∂P, ∀ cs : ℕ → ℝ, (∀ n, cs n ≤ driftedBrownianMaximum ν p) →
      Tendsto cs atTop (𝓝 (driftedBrownianMaximum ν p)) →
      Tendsto (fun n => firstPassageTime (driftedBrownianPath (-ν) p) (cs n))
        atTop (𝓝 (driftedBrownianMaximumTime ν p)) := by
  have firstPassageTime_tendsto_unique_maximum p M (σ : ℝ≥0) (hmax : ∀ t : ℝ≥0, p t ≤ M) (hσ : p σ = M) (hunique : ∀ t : ℝ≥0, p t = M → t = σ) (cs : ℕ → ℝ) (hcs : ∀ n, cs n ≤ M) (hlim : Tendsto cs atTop (𝓝 M)) : Tendsto (fun n => firstPassageTime p (cs n)) atTop (𝓝 σ) := by
    apply tendsto_order.mpr
    constructor
    · intro t ht
      obtain ⟨u,hu⟩ := brownianPath_runningMaximum_attained p t
      have hpast : (⨆ v : Iic t, p v) < M := by
        rw [hu]
        apply lt_of_le_of_ne (hmax u)
        intro he
        exact (not_le.mpr ht) ((hunique u he) ▸ u.2)
      filter_upwards [(tendsto_order.mp hlim).1 _ hpast] with n hn
      by_contra h
      exact (not_le.mpr hn) ((firstPassageTime_mem p (cs n) ⟨σ,hσ ▸ hcs n⟩).trans (le_ciSup (brownianPath_Iic_bddAbove p t) (⟨_,(le_of_not_gt h)⟩ : Iic t)))
    · intro t ht
      exact Filter.Eventually.of_forall (fun n => ((fun n => csInf_le (s := {u : ℝ≥0 | cs n ≤ p u}) (OrderBot.bddBelow _) (by change cs n ≤ p σ; rw [hσ]; exact hcs n)) n).trans_lt ht)
  have brownianPath_globalMaximum_unique_ae : ∀ᵐ p ∂P, ∀ t : ℝ≥0, p t-ν*(t : ℝ) = driftedBrownianMaximum ν p → t = driftedBrownianMaximumTime ν p := by
    have brownianPath_no_maximum_tie_at_cut (s : ℝ≥0) : ∀ᵐ p ∂P, brownianPastMaximumGap ν s p ≠ driftedBrownianMaximum ν (brownianShiftPath s p) := by
      have measurable_brownianPastMaximumGap_raw : Measurable[brownianRawFiltration (fun t (p : BrownianPath) => p t) (fun t => ContinuousMap.measurable_eval t) s] (brownianPastMaximumGap ν s) := by
        obtain ⟨D,hDc,hDd⟩ := TopologicalSpace.exists_countable_dense (Iic s)
        let _ := hDc.to_subtype
        convert ((Measurable.iSup (fun (u : D) => (measurable_brownianPath_eval_raw s u.1.1 u.1.2).sub measurable_const)).sub ((measurable_brownianPath_eval_raw s s le_rfl).sub (measurable_const (a := ν*(s : ℝ))))) using 1
        funext p
        change (⨆ u : Iic s, p u-ν*(u : ℝ))-(p s-ν*(s : ℝ)) =
          (⨆ u : D, p u.1.1-ν*(u.1.1 : ℝ))-(p s-ν*(s : ℝ))
        congr 1
        have hb : BddAbove (range (fun u : Iic s => p u-ν*(u : ℝ))) := by
          have hh := brownianPath_Iic_bddAbove (driftedBrownianPath (-ν) p) s
          change BddAbove (range (fun u : Iic s => p u+(-ν)*(u : ℝ))) at hh
          simpa only [neg_mul,← sub_eq_add_neg] using hh
        exact (hDd.ciSup ((p.continuous.sub (continuous_const.mul NNReal.continuous_coe)).comp
          continuous_subtype_val) hb).symm
      let _ := (hB.hasLaw_eval 0).isProbabilityMeasure
      have hM := aemeasurable_driftedBrownianMaximum P hB ν hν
      let M := hM.mk (driftedBrownianMaximum ν)
      have hmM := hM.measurable_mk
      let _ := noAtoms_brownianMaximumReferenceLaw ν
      have hsingle x : P {p | x = M p} = 0 := by
        have hh := congrArg (fun μ : Measure ℝ => μ {x}) ((Measure.map_congr hM.ae_eq_mk.symm).trans (brownianPath_globalMaximum_map P hB ν hν))
        rw [Measure.map_apply hmM (measurableSet_singleton x)] at hh
        simpa only [Set.preimage,mem_singleton_iff,eq_comm,measure_singleton] using hh
      let D := brownianPastMaximumGap ν s
      have hD := measurable_brownianPastMaximumGap_raw
      have hmS : Measurable (fun p => brownianShiftPath s p) :=
        continuous_brownianShiftPath.measurable.comp (measurable_const.prodMk measurable_id)
      let E : Set (ℝ × BrownianPath) := {z | z.1 = M z.2}
      have hE : MeasurableSet E := measurableSet_eq_fun measurable_fst (hmM.comp measurable_snd)
      have hz : P {p | D p = M (brownianShiftPath s p)} = 0 := by
        calc
          _ = P.map (fun p => (D p,brownianShiftPath s p)) E :=
            (Measure.map_apply ((hD.mono ((brownianRawFiltration _ _).le s) le_rfl).prodMk hmS) hE).symm
          _ = (P.map D).prod P E := by
            rw [brownianPath_deterministic_restart_joint_map P hB s D hD]
          _ = 0 := by
            rw [Measure.prod_apply hE]
            simp only [E,Set.preimage,mem_ofPred_eq,hsingle,lintegral_zero]
      have heq : ∀ᵐ p ∂P, driftedBrownianMaximum ν (brownianShiftPath s p) = M (brownianShiftPath s p) := by
        exact ae_eq_comp hmS.aemeasurable (show driftedBrownianMaximum ν =ᵐ[P.map (brownianShiftPath s)] M by rw [(brownianPath_bounded_restart_map P hB (fun _ => s) (isStoppingTime_const _ s) s (fun _ => le_rfl))]; exact hM.ae_eq_mk)
      filter_upwards [(show ∀ᵐ p ∂P, D p ≠ M (brownianShiftPath s p) by simpa only [ae_iff,Classical.not_not] using hz),heq] with p hp heq
      change ¬D p = M (brownianShiftPath s p) at hp
      rwa [heq]
    filter_upwards [(ae_all_iff.mpr (fun q => brownianPath_no_maximum_tie_at_cut _) : ∀ᵐ p ∂P, ∀ q : ℚ, brownianPastMaximumGap ν (Real.toNNReal (q : ℝ)) p ≠ driftedBrownianMaximum ν (brownianShiftPath (Real.toNNReal (q : ℝ)) p)),brownianPath_negativeDrift_maximum_attained_ae P hB ν hν,
      brownianPath_globalMaximumTime_attains_ae P hB ν hν] with p hp hb hσ
    intro t ht
    apply le_antisymm
    · by_contra h
      obtain ⟨q,hqσ,hqt⟩ := exists_rat_btwn (show
        (driftedBrownianMaximumTime ν p : ℝ) < (t : ℝ) from by exact_mod_cast lt_of_not_ge h)
      have hq0 := (driftedBrownianMaximumTime ν p).coe_nonneg.trans hqσ.le
      apply hp q
      apply brownianPath_maximum_tie_of_two_hits ν p _ _ _ hb.1
      · exact_mod_cast (by rw [Real.coe_toNNReal _ hq0]; exact hqσ.le :
          (driftedBrownianMaximumTime ν p : ℝ) ≤ (Real.toNNReal (q : ℝ) : ℝ))
      · exact_mod_cast (by rw [Real.coe_toNNReal _ hq0]; exact hqt.le :
          (Real.toNNReal (q : ℝ) : ℝ) ≤ (t : ℝ))
      · exact hσ
      · exact ht
    · by_contra h
      obtain ⟨q,hqt,hqσ⟩ := exists_rat_btwn (show
        (t : ℝ) < (driftedBrownianMaximumTime ν p : ℝ) from by exact_mod_cast lt_of_not_ge h)
      have hq0 := t.coe_nonneg.trans hqt.le
      apply hp q
      apply brownianPath_maximum_tie_of_two_hits ν p _ _ _ hb.1
      · exact_mod_cast (by rw [Real.coe_toNNReal _ hq0]; exact hqt.le :
          (t : ℝ) ≤ (Real.toNNReal (q : ℝ) : ℝ))
      · exact_mod_cast (by rw [Real.coe_toNNReal _ hq0]; exact hqσ.le :
          (Real.toNNReal (q : ℝ) : ℝ) ≤ (driftedBrownianMaximumTime ν p : ℝ))
      · exact ht
      · exact hσ
  filter_upwards [brownianPath_negativeDrift_maximum_attained_ae P hB ν hν,
    brownianPath_globalMaximumTime_attains_ae P hB ν hν,
    brownianPath_globalMaximum_unique_ae] with p hp hσ hu
  intro cs hcs hlim
  apply firstPassageTime_tendsto_unique_maximum (driftedBrownianPath (-ν) p)
    (driftedBrownianMaximum ν p) (driftedBrownianMaximumTime ν p) ?_ ?_ ?_ cs hcs hlim
  · intro t
    have hh := le_csSup hp.1 (mem_range_self t)
    change p t-ν*(t : ℝ) ≤ driftedBrownianMaximum ν p at hh
    change p t+(-ν)*(t : ℝ) ≤ driftedBrownianMaximum ν p
    simpa only [neg_mul,← sub_eq_add_neg] using hh
  · change p (driftedBrownianMaximumTime ν p)+(-ν)*(driftedBrownianMaximumTime ν p : ℝ) = _
    simpa only [neg_mul,← sub_eq_add_neg] using hσ
  · intro t ht
    apply hu t
    change p t+(-ν)*(t : ℝ) = driftedBrownianMaximum ν p at ht
    simpa only [neg_mul,← sub_eq_add_neg] using ht

/-- The actual lower-level lifetime-marked prefixes converge in the stopped-path topology. -/
theorem brownianPath_firstHitSegment_tendsto_preMaximum_ae (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) ν (hν : 0 < ν) :
    ∀ᵐ p ∂P, ∀ cs : ℕ → ℝ, (∀ n, cs n ≤ driftedBrownianMaximum ν p) →
      Tendsto cs atTop (𝓝 (driftedBrownianMaximum ν p)) →
      Tendsto (fun n => positiveDriftFirstHitSegment (-ν) (cs n) p) atTop
        (𝓝 (brownianPreMaximumSegment ν p)) := by
  filter_upwards [brownianPath_firstPassageTime_tendsto_globalMaximumTime_ae P hB ν hν] with p hp
  intro cs hcs hlim
  have hτ := hp cs hcs hlim
  have hh := hτ.prodMk_nhds (continuous_stopBrownianPath.continuousAt.tendsto.comp (hτ.prodMk_nhds (tendsto_const_nhds (x := driftedBrownianPath (-ν) p))))
  change Tendsto (fun n => positiveDriftFirstHitSegment (-ν) (cs n) p) atTop
    (𝓝 (driftedBrownianMaximumTime ν p,stopBrownianPath (driftedBrownianPath (-ν) p)
      (driftedBrownianMaximumTime ν p))) at hh
  convert hh using 1
  apply congrArg nhds
  apply Prod.ext
  · rfl
  apply ContinuousMap.ext
  intro t
  change p (min t (driftedBrownianMaximumTime ν p))-ν*((min t (driftedBrownianMaximumTime ν p) : ℝ≥0) : ℝ) =
    p (min t (driftedBrownianMaximumTime ν p))+(-ν)*((min t (driftedBrownianMaximumTime ν p) : ℝ≥0) : ℝ)
  ring

/-- The actual shifted first-hit futures converge to the post-maximum path. -/
theorem brownianPath_firstHitFuture_tendsto_postMaximum_ae (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) ν (hν : 0 < ν) :
    ∀ᵐ p ∂P, ∀ cs : ℕ → ℝ, (∀ n, cs n ≤ driftedBrownianMaximum ν p) →
      Tendsto cs atTop (𝓝 (driftedBrownianMaximum ν p)) →
      Tendsto (fun n => driftedBrownianPath (-ν)
        (brownianShiftPath (firstPassageTime (driftedBrownianPath (-ν) p) (cs n)) p))
        atTop (𝓝 (brownianPostMaximumPath ν p)) := by
  filter_upwards [brownianPath_firstPassageTime_tendsto_globalMaximumTime_ae P hB ν hν,
    brownianPath_globalMaximumTime_attains_ae P hB ν hν] with p hp hσ
  intro cs hcs hlim
  convert (by simpa only [Function.comp_def,brownianShiftPath_drift] using (continuous_brownianShiftPath.continuousAt.tendsto.comp ((hp cs hcs hlim).prodMk_nhds (tendsto_const_nhds (x := driftedBrownianPath (-ν) p))))) using 1
  apply congrArg nhds
  apply ContinuousMap.ext
  intro t
  change p (driftedBrownianMaximumTime ν p+t)-
      ν*((driftedBrownianMaximumTime ν p+t : ℝ≥0) : ℝ)-driftedBrownianMaximum ν p =
    (p (driftedBrownianMaximumTime ν p+t)-p (driftedBrownianMaximumTime ν p))+(-ν)*(t : ℝ)
  rw [NNReal.coe_add]
  linarith only [hσ]

end DOZZ.Proofs
