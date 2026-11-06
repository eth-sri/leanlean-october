/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.Brownian.Barrier.ZeroDrift
public import DOZZ.Statements.Brownian.BrownianPiecewiseDrift

/-!
# Gaussian endpoint estimates and drifted maximum upper bounds

Independent Gaussian increments give the exponential moment of any weighted
pair of ordered Brownian values. Applying this moment to the kink and terminal
constraints proves both piecewise-drift bounds directly.

A capped hit of a drifted continuous path is a genuine stopping time of the raw
Brownian history. Bounded optional stopping then bounds its crossing probability;
countable horizon exhaustion gives the sharp all-time exponential upper bound.
That bound is also valid at level zero and on arbitrary Brownian sample spaces.
The matching lower bound required by the maximum-tail estimate remains separate.
-/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
namespace DOZZ.Proofs




/-- A measurable exponential test bounds any event on which its exponent has a lower bound. -/
theorem brownian_exp_event_bound {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {X : Ω → ℝ} (hX : Integrable (fun ω => Real.exp (X ω)) P)
    A c (hA : ∀ ω ∈ A, c ≤ X ω) :
    P A ≤ ENNReal.ofReal (Real.exp (-c)*(∫ ω, Real.exp (X ω) ∂P)) := by
  calc
    P A ≤ P {ω | c ≤ X ω} := measure_mono hA
    _ = ENNReal.ofReal (P.real {ω | c ≤ X ω}) := (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      simpa only [mgf,one_mul,neg_mul] using (measure_ge_le_exp_mul_mgf (μ := P) (X := X) (t := 1) c (by norm_num) (by simpa only [one_mul] using hX))



/-- An endpoint alone gives the constant-drift Gaussian Chernoff estimate. -/
theorem brownian_terminal_event_bound {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (r : ℝ≥0) a c A (hA : ∀ ω ∈ A, a*B r ω ≤ c) :
    P A ≤ ENNReal.ofReal (Real.exp (c+a^2*(r : ℝ)/2)) := by
  have brownian_twoTime_linear_hasLaw (s : ℝ≥0) (d : ℝ≥0) a b : HasLaw (fun ω => a*B s ω+b*(B (s+d) ω-B s ω)) (gaussianReal 0 (NNReal.mk (a^2) (sq_nonneg _)*s+NNReal.mk (b^2) (sq_nonneg _)*d)) P := by
    have hx := gaussianReal_const_mul (hB.hasLaw_eval s) a
    have hy := gaussianReal_const_mul ((hB.shift s).hasLaw_eval d) b
    simp only [mul_zero] at hx hy
    refine ⟨hx.aemeasurable.add hy.aemeasurable,?_⟩
    simpa only [Pi.add_def,Pi.add_apply,zero_add] using (gaussianReal_add_gaussianReal_of_indepFun (by simpa only [Function.comp_def] using ((show IndepFun (fun ω => B (s+d) ω-B s ω) (B s) P by exact (hB.indepFun_shift s).comp (measurable_pi_apply d) (measurable_pi_apply (⟨s,le_rfl⟩ : Iic s)))).symm.comp (φ := fun x => a*x) (ψ := fun x => b*x) (by fun_prop) (by fun_prop)) hx hy)
  have brownian_weighted_twoTime_event_bound (s : ℝ≥0) (r : ℝ≥0) (hsr : s ≤ r) a b c A (hA : ∀ ω ∈ A, a*B s ω+b*B r ω ≤ c) : P A ≤ ENNReal.ofReal (Real.exp (c+((a+b)^2*(s : ℝ)+b^2*((r : ℝ)-(s : ℝ)))/2)) := by
    have brownian_weighted_twoTime_exp_integrable a b : Integrable (fun ω => Real.exp (a*B s ω+b*B r ω)) P := by
      have brownian_twoTime_exp_integrable (d : ℝ≥0) a b : Integrable (fun ω => Real.exp (a*B s ω+b*(B (s+d) ω-B s ω))) P := by
        simpa only [one_mul,Function.comp_def] using ((brownian_twoTime_linear_hasLaw s d a b).integrable_comp (integrable_exp_mul_gaussianReal (μ := 0) (v := NNReal.mk (a^2) (sq_nonneg _)*s+NNReal.mk (b^2) (sq_nonneg _)*d) 1))
      have he : (fun ω => Real.exp (a*B s ω+b*B r ω)) =
          (fun ω => Real.exp ((a+b)*B s ω+b*(B (s+(r-s)) ω-B s ω))) := by
        funext ω
        rw [add_tsub_cancel_of_le hsr]
        congr 1
        ring
      rw [he]
      exact brownian_twoTime_exp_integrable (r-s) (a+b) b
    have brownian_weighted_twoTime_exp_integral a b : (∫ ω, Real.exp (a*B s ω+b*B r ω) ∂P) = Real.exp (((a+b)^2*(s : ℝ)+b^2*((r : ℝ)-(s : ℝ)))/2) := by
      have brownian_twoTime_exp_integral (d : ℝ≥0) a b : (∫ ω, Real.exp (a*B s ω+b*(B (s+d) ω-B s ω)) ∂P) = Real.exp ((a^2*(s : ℝ)+b^2*(d : ℝ))/2) := by
        simpa only [mgf,one_mul,one_pow,mul_one,zero_mul,zero_add,
          NNReal.coe_add,NNReal.coe_mul,NNReal.coe_mk] using (mgf_gaussianReal (brownian_twoTime_linear_hasLaw s d a b) 1)
      have he ω : a*B s ω+b*B r ω =
          (a+b)*B s ω+b*(B (s+(r-s)) ω-B s ω) := by
        rw [add_tsub_cancel_of_le hsr]
        ring
      simp_rw [he]
      rw [brownian_twoTime_exp_integral (r-s) (a+b) b,NNReal.coe_sub hsr]
    let _ := (hB.hasLaw_eval 0).isProbabilityMeasure
    have he := brownian_exp_event_bound
      (brownian_weighted_twoTime_exp_integrable (-a) (-b)) A (-c)
      (fun ω hω => by have h := hA ω hω; linarith)
    rw [brownian_weighted_twoTime_exp_integral (-a) (-b),← Real.exp_add] at he
    convert he using 1
    congr 2
    ring
  simpa only [zero_add,NNReal.coe_zero,mul_zero,sub_zero,zero_div] using (brownian_weighted_twoTime_event_bound 0 r (zero_le) 0 a c A (by simpa only [zero_mul,zero_add] using hA))
/-! ## Drift translation and capped stopping times -/

/-- Add a deterministic linear drift to a literal continuous Brownian path. -/
noncomputable def brownianDriftPath (δ : ℝ) (p : BrownianPath) : BrownianPath :=
  ⟨fun t => p t+δ*(t : ℝ),p.continuous.add (continuous_const.mul NNReal.continuous_coe)⟩

/-- Drift translation is jointly continuous in the path and in its scalar drift. -/
theorem continuous_brownianDriftPath :
    Continuous (fun z : ℝ × BrownianPath => brownianDriftPath z.1 z.2) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun z : (ℝ × BrownianPath) × ℝ≥0 => z.1.2 z.2+z.1.1*(z.2 : ℝ))
  exact (continuous_eval.comp (continuous_fst.snd.prodMk continuous_snd)).add
    (continuous_fst.fst.mul (NNReal.continuous_coe.comp continuous_snd))



/-! ## Exhaustion to the entire-time maximum -/




/-- The entire-time crossing event is a countable increasing union of finite-horizon crossings. -/
theorem brownianPath_drift_crossing_eq_iUnion δ x :
    {p : BrownianPath | ∃ t : ℝ≥0, x < p t+δ*(t : ℝ)} =
      ⋃ n : ℕ, {p | ∃ t ≤ (n : ℝ≥0), x < p t+δ*(t : ℝ)} := by
  ext p
  simp only [mem_ofPred_eq,mem_iUnion]
  constructor
  · rintro ⟨t,ht⟩
    obtain ⟨n,hn⟩ := exists_nat_ge (t : ℝ)
    exact ⟨n,t,by exact_mod_cast hn,ht⟩
  · rintro ⟨n,t,_,ht⟩
    exact ⟨t,ht⟩

/-- Infinite-horizon drift crossing events are measurable on the continuous-path carrier. -/
theorem measurableSet_brownianPath_drift_crossing δ x :
    MeasurableSet {p : BrownianPath | ∃ t : ℝ≥0, x < p t+δ*(t : ℝ)} := by
  have measurableSet_brownianPath_drift_strict_crossing (T : ℝ≥0) : MeasurableSet {p : BrownianPath | ∃ u ≤ T, x < p u+δ*(u : ℝ)} := ((brownianRawFiltration _ (fun t => ContinuousMap.measurable_eval t)).le T _ (measurableSet_brownianPath_strict_crossing T x)).preimage (continuous_brownianDriftPath.measurable.comp (measurable_const.prodMk measurable_id))
  rw [brownianPath_drift_crossing_eq_iUnion]
  exact MeasurableSet.iUnion (fun n => measurableSet_brownianPath_drift_strict_crossing n)

/-- The all-time maximum of a negative-drift continuous Brownian path satisfies the sharp exponential upper bound. -/
theorem brownianPath_negativeDrift_maximum_le (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P)
    ν x (hx : 0 < x) :
    P {p | ∃ t : ℝ≥0, x < p t-ν*(t : ℝ)} ≤ ENNReal.ofReal (Real.exp (-2*ν*x)) := by
  have brownianPath_negativeDrift_finiteMaximum_le (T : ℝ≥0) : P {p | ∃ u ≤ T, x < p u-ν*(u : ℝ)} ≤ ENNReal.ofReal (Real.exp (-2*ν*x)) := by
    have cappedBrownianFirstPassage_lt_of_strict_crossing p (h0 : p 0 < x) (u : ℝ≥0) (hu : u ≤ T) (hx : x < p u) : cappedBrownianFirstPassage x T p < T := by
      obtain ⟨v,hv,hpv⟩ := intermediate_value_Icc (a := (0 : ℝ≥0)) (b := u)
        (f := fun t : ℝ≥0 => p t) zero_le p.continuous.continuousOn ⟨h0.le,hx.le⟩
      exact ((csInf_le (s := {t : ℝ≥0 | t ≤ T ∧ x ≤ p t} ∪ {T}) (OrderBot.bddBelow _) (Or.inl ⟨hv.2.trans hu,hpv ▸ le_rfl⟩)).trans_lt (lt_of_le_of_ne hv.2 (by intro he; exact hx.ne (he ▸ hpv).symm))).trans_le hu
    have brownianPath_negativeDrift_cappedHit_le : P {p | cappedBrownianFirstPassage x T (brownianDriftPath (-ν) p) < T} ≤ ENNReal.ofReal (Real.exp (-2*ν*x)) := by
      have cappedBrownianDriftFirstPassage_isStoppingTime δ β (T : ℝ≥0) : IsStoppingTime (brownianRawFiltration (fun t (p : BrownianPath) => p t) (fun t => ContinuousMap.measurable_eval t)) (fun p => (cappedBrownianFirstPassage β T (brownianDriftPath δ p) : WithTop ℝ≥0)) := by
        have measurable_brownianDriftPath_history (s : ℝ≥0) : Measurable[brownianRawFiltration (fun t (p : BrownianPath) => p t) (fun t => ContinuousMap.measurable_eval t) s, brownianRawFiltration (fun t (p : BrownianPath) => p t) (fun t => ContinuousMap.measurable_eval t) s] (brownianDriftPath δ) := by
          rw [measurable_iff_comap_le]
          change MeasurableSpace.comap (brownianDriftPath δ)
            (⨆ t : ℝ≥0, ⨆ (_ : t ≤ s), MeasurableSpace.comap (fun p => p t) inferInstance) ≤ _
          rw [MeasurableSpace.comap_iSup]
          apply iSup_le
          intro t
          rw [MeasurableSpace.comap_iSup]
          apply iSup_le
          intro ht
          rw [MeasurableSpace.comap_comp]
          exact ((show Measurable[brownianRawFiltration (fun t (p : BrownianPath) => p t) (fun t => ContinuousMap.measurable_eval t) s] (fun p => p t) by apply Measurable.of_comap_le; exact le_iSup_of_le t (le_iSup_of_le ht le_rfl)).add_const (δ*(t : ℝ))).comap_le
        intro s
        exact (cappedBrownianFirstPassage_isStoppingTime β T s).preimage
          (measurable_brownianDriftPath_history s)
      let _ := (hB.hasLaw_eval 0).isProbabilityMeasure
      let τ : BrownianPath → ℝ≥0 :=
        fun p => cappedBrownianFirstPassage x T (brownianDriftPath (-ν) p)
      have he := brownian_exponential_bounded_optional_stopping hB
        (fun t => ContinuousMap.measurable_eval t) (2*ν) T τ (cappedBrownianDriftFirstPassage_isStoppingTime (-ν) x T) (fun p => cappedBrownianFirstPassage_le x T _)
      let A := {p | τ p < T ∧ p 0 = 0}
      have hc : ∀ p ∈ A, 2*ν*x ≤ (2*ν)*p (τ p)-(2*ν)^2*((τ p : ℝ))/2 := by
        intro p hp
        have hv := cappedBrownianFirstPassage_value x T (brownianDriftPath (-ν) p) (by change p 0+(-ν)*(0 : ℝ) < x; simpa only [mul_zero,add_zero,hp.2] using hx) hp.1
        change p (τ p)+(-ν)*(τ p : ℝ) = x at hv
        exact (show (2*ν)*p (τ p)-(2*ν)^2*(τ p : ℝ)/2 = 2*ν*x by rw [← hv]; ring).ge
      have hb := brownian_exp_event_bound (integrable_of_integral_eq_one he) A (2*ν*x) hc
      rw [he,mul_one] at hb
      have hA : {p : BrownianPath | τ p < T} =ᵐ[P] A := by
        filter_upwards [hB.eval_zero_ae_eq_zero] with p hp
        apply propext
        simp only [A,mem_ofPred_eq,hp,and_true]
      rw [measure_congr hA]
      convert hb using 1
      congr 2
      ring
    have hsub : {p : BrownianPath | ∃ u ≤ T, x < p u-ν*(u : ℝ)} ≤ᵐ[P]
        {p | cappedBrownianFirstPassage x T (brownianDriftPath (-ν) p) < T} := by
      filter_upwards [hB.eval_zero_ae_eq_zero] with p hp
      rintro ⟨u,hu,hxu⟩
      apply cappedBrownianFirstPassage_lt_of_strict_crossing (brownianDriftPath (-ν) p) (by change p 0+(-ν)*(0 : ℝ) < x; simpa only [mul_zero,add_zero,hp] using hx) u hu
      change x < p u+(-ν)*(u : ℝ)
      simpa only [sub_eq_add_neg,neg_mul] using hxu
    exact (measure_mono_ae hsub).trans
      (brownianPath_negativeDrift_cappedHit_le)
  have hmono : Monotone (fun n : ℕ => {p : BrownianPath | ∃ t ≤ (n : ℝ≥0), x < p t-ν*(t : ℝ)}) := by
    intro n m hnm p
    rintro ⟨t,ht,hx⟩
    exact ⟨t,ht.trans (Nat.cast_le.mpr hnm),hx⟩
  rw [(show {p : BrownianPath | ∃ t : ℝ≥0, x < p t-ν*(t : ℝ)} = ⋃ n : ℕ, {p | ∃ t ≤ (n : ℝ≥0), x < p t-ν*(t : ℝ)} by simpa only [sub_eq_add_neg,neg_mul] using brownianPath_drift_crossing_eq_iUnion (-ν) x),hmono.measure_iUnion]
  exact iSup_le (fun n => brownianPath_negativeDrift_finiteMaximum_le n)

end DOZZ.Proofs
