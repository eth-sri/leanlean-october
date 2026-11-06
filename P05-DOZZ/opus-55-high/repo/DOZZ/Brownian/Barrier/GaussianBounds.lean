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
section
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
section
variable {B : ℝ≥0 → Ω → ℝ}
section
variable (hB : IsPreBrownianReal B P) (s d : ℝ≥0)
include hB
/-- A Brownian increment after a deterministic time is independent of the value at that time. -/
theorem brownian_increment_indep_value :
    IndepFun (fun ω => B (s+d) ω-B s ω) (B s) P := by
  exact (hB.indepFun_shift s).comp (measurable_pi_apply d)
    (measurable_pi_apply (⟨s,le_rfl⟩))
section
variable (a b : ℝ)

/-- Every linear combination of a Brownian value and a later independent increment has its Gaussian law. -/
theorem brownian_twoTime_linear_hasLaw :
    HasLaw (fun ω => a*B s ω+b*(B (s+d) ω-B s ω))
      (gaussianReal 0 (NNReal.mk (a^2) (sq_nonneg _)*s+NNReal.mk (b^2) (sq_nonneg _)*d)) P := by
  have hi : IndepFun (fun ω => a*B s ω) (fun ω => b*(B (s+d) ω-B s ω)) P := by
    simpa only [Function.comp_def] using
      (brownian_increment_indep_value hB s d).symm.comp
        (by fun_prop) (by fun_prop)
  have hx := gaussianReal_const_mul (hB.hasLaw_eval s) a
  have hy := gaussianReal_const_mul ((hB.shift s).hasLaw_eval d) b
  refine ⟨hx.aemeasurable.add hy.aemeasurable,?_⟩
  have he := gaussianReal_add_gaussianReal_of_indepFun hi hx hy
  aesop

/-- The two-time Gaussian exponential has a literal quadratic variance. -/
theorem brownian_twoTime_exp_integral :
    (∫ ω, Real.exp (a*B s ω+b*(B (s+d) ω-B s ω)) ∂P) =
      Real.exp ((a^2*(s : ℝ)+b^2*(d : ℝ))/2) := by
  simpa only [mgf,one_mul,one_pow,mul_one,zero_mul,zero_add,
    NNReal.coe_add,NNReal.coe_mul,NNReal.coe_mk] using (mgf_gaussianReal (brownian_twoTime_linear_hasLaw hB s d a b) 1)

/-- Two-time exponential tests of a Brownian motion are genuinely integrable. -/
theorem brownian_twoTime_exp_integrable :
    Integrable (fun ω => Real.exp (a*B s ω+b*(B (s+d) ω-B s ω))) P := by
  have hi := (brownian_twoTime_linear_hasLaw hB s d a b).integrable_comp
    (integrable_exp_mul_gaussianReal
      1)
  aesop

end

end

end

/-- A measurable exponential test bounds any event on which its exponent has a lower bound. -/
theorem brownian_exp_event_bound [IsFiniteMeasure P] {X : Ω → ℝ} (hX : Integrable (fun ω => Real.exp (X ω)) P)
    (A : Set Ω) (c : ℝ) (hA : ∀ ω ∈ A, c ≤ X ω) :
    P A ≤ ENNReal.ofReal (Real.exp (-c)*(∫ ω, Real.exp (X ω) ∂P)) := by
  have htail := measure_ge_le_exp_mul_mgf (μ := P) (t := 1) c (by norm_num)
    (by aesop)
  calc
    P A ≤ P {ω | c ≤ X ω} := measure_mono hA
    _ = ENNReal.ofReal (P.real {ω | c ≤ X ω}) := (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      simpa only [mgf,one_mul,neg_mul] using htail
section
variable {B : ℝ≥0 → Ω → ℝ}
section
variable (hB : IsPreBrownianReal B P) (s r : ℝ≥0) (hsr : s ≤ r)
include hB hsr
section
variable (a b : ℝ)
/-- The exponential moment of a weighted value at two ordered times. -/
theorem brownian_weighted_twoTime_exp_integral :
    (∫ ω, Real.exp (a*B s ω+b*B r ω) ∂P) =
      Real.exp (((a+b)^2*(s : ℝ)+b^2*((r : ℝ)-(s : ℝ)))/2) := by
  have he (ω : Ω) : a*B s ω+b*B r ω =
      (a+b)*B s ω+b*(B (s+(r-s)) ω-B s ω) := by
    rw [add_tsub_cancel_of_le hsr]
    ring
  simp_rw [he]
  rw [brownian_twoTime_exp_integral hB s _ _ b,NNReal.coe_sub hsr]

/-- Integrability of the weighted two-time exponential. -/
theorem brownian_weighted_twoTime_exp_integrable :
    Integrable (fun ω => Real.exp (a*B s ω+b*B r ω)) P := by
  have he : (fun ω => Real.exp (a*B s ω+b*B r ω)) =
      (fun ω => Real.exp ((a+b)*B s ω+b*(B (s+(r-s)) ω-B s ω))) := by
    funext ω
    rw [add_tsub_cancel_of_le hsr]
    ring
  rw [he]
  exact brownian_twoTime_exp_integrable hB s _ _ b

end

/-- Endpoint Chernoff bound for any event with a weighted two-time upper constraint. -/
theorem brownian_weighted_twoTime_event_bound (a b c : ℝ) (A : Set Ω)
    (hA : ∀ ω ∈ A, a*B s ω+b*B r ω ≤ c) :
    P A ≤ ENNReal.ofReal (Real.exp (c+((a+b)^2*(s : ℝ)+b^2*((r : ℝ)-(s : ℝ)))/2)) := by
  let _ := (hB.hasLaw_eval 0).isProbabilityMeasure
  have he := brownian_exp_event_bound
    (brownian_weighted_twoTime_exp_integrable hB s r hsr (-a) (-b)) A (-c)
    (fun ω hω => by grind)
  rw [brownian_weighted_twoTime_exp_integral hB s r hsr (-a) (-b),← Real.exp_add] at he
  grind

end

/-- An endpoint alone gives the constant-drift Gaussian Chernoff estimate. -/
theorem brownian_terminal_event_bound (hB : IsPreBrownianReal B P)
    (r : ℝ≥0) (a c : ℝ) (A : Set Ω) (hA : ∀ ω ∈ A, a*B r ω ≤ c) :
    P A ≤ ENNReal.ofReal (Real.exp (c+a^2*(r : ℝ)/2)) := by
  have he := brownian_weighted_twoTime_event_bound hB 0 r (zero_le) 0 a c A
    (by simp_all)
  simp_all

end

end
/-! ## Drift translation and capped stopping times -/

/-- Add a deterministic linear drift to a literal continuous Brownian path. -/
noncomputable def brownianDriftPath (δ : ℝ) (p : BrownianPath) : BrownianPath :=
  ⟨fun t => p t+δ*(t : ℝ),p.continuous.add (continuous_const.mul NNReal.continuous_coe)⟩

/-- Drift translation is jointly continuous in the path and in its scalar drift. -/
theorem continuous_brownianDriftPath :
    Continuous (fun z : ℝ × BrownianPath => brownianDriftPath z.1 z.2) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun z : (ℝ × BrownianPath) × ℝ≥0 => z.1.2 z.2+z.1.1*z.2)
  fun_prop

/-- Deterministic drift translation preserves measurability in each raw history sigma algebra. -/
theorem measurable_brownianDriftPath_history (δ : ℝ) (s : ℝ≥0) :
    Measurable[brownianRawFiltration (fun t (p : BrownianPath) => p t)
      (fun t => ContinuousMap.measurable_eval t) s,
      brownianRawFiltration (fun t (p : BrownianPath) => p t)
      (fun t => ContinuousMap.measurable_eval t) s] (brownianDriftPath δ) := by
  rw [measurable_iff_comap_le]
  change MeasurableSpace.comap (brownianDriftPath δ)
    (⨆ t : ℝ≥0, ⨆ _, MeasurableSpace.comap (fun p => p t) inferInstance) ≤ _
  rw [MeasurableSpace.comap_iSup]
  apply iSup_le
  intro t
  rw [MeasurableSpace.comap_iSup]
  apply iSup_le
  intro ht
  rw [MeasurableSpace.comap_comp]
  have hm : Measurable[brownianRawFiltration (fun t (p : BrownianPath) => p t)
      (fun t => ContinuousMap.measurable_eval t) s] (fun p : BrownianPath => p t) := by
    apply Measurable.of_comap_le
    exact le_iSup_of_le t (le_iSup_of_le ht le_rfl)
  exact (hm.add_const _).comap_le

/-- The capped hit of a linearly drifted path is a genuine raw Brownian stopping time. -/
theorem cappedBrownianDriftFirstPassage_isStoppingTime (δ β : ℝ) (T : ℝ≥0) :
    IsStoppingTime (brownianRawFiltration (fun t (p : BrownianPath) => p t)
      (fun t => ContinuousMap.measurable_eval t))
      (fun p => (cappedBrownianFirstPassage β T (brownianDriftPath δ p) : WithTop ℝ≥0)) := by
  intro s
  exact (cappedBrownianFirstPassage_isStoppingTime β T s).preimage
    (measurable_brownianDriftPath_history δ s)

/-- A bounded hit by the negative-drift path has the exponential-martingale upper tail bound. -/
theorem brownianPath_negativeDrift_cappedHit_le (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (ν x : ℝ) (hx : 0 < x)
    (T : ℝ≥0) :
    P {p | cappedBrownianFirstPassage x T (brownianDriftPath (-ν) p) < T} ≤
      ENNReal.ofReal (Real.exp (-2*ν*x)) := by
  let _ := (hB.hasLaw_eval 0).isProbabilityMeasure
  let τ : BrownianPath → ℝ≥0 :=
    fun p => cappedBrownianFirstPassage x T (brownianDriftPath (-ν) p)
  have hτ := cappedBrownianDriftFirstPassage_isStoppingTime (-ν) x T
  have hτT : ∀ p, τ p ≤ T := fun p => cappedBrownianFirstPassage_le x T _
  have he := brownian_exponential_bounded_optional_stopping hB
    (fun t => ContinuousMap.measurable_eval t) (2*ν) T τ hτ hτT
  let A := {p | τ p < T ∧ p 0 = 0}
  have hc : ∀ p ∈ A, 2*ν*x ≤ (2*ν)*p (τ p)-(2*ν)^2*((τ p))/2 := by
    intro p hp
    have h0 : brownianDriftPath (-ν) p 0 < x := by
      change p 0+(-ν)*0 < x
      aesop
    have hv := cappedBrownianFirstPassage_value x T _ h0 hp.1
    change p (τ p)+(-ν)*(τ p) = x at hv
    have hval : (2*ν)*p (τ p)-(2*ν)^2*(τ p)/2 = 2*ν*x := by
      rw [← hv]
      ring
    exact hval.ge
  have hb := brownian_exp_event_bound (integrable_of_integral_eq_one he) A _ hc
  rw [he,mul_one] at hb
  have hA : {p : BrownianPath | τ p < T} =ᵐ[P] A := by
    filter_upwards [hB.eval_zero_ae_eq_zero] with p hp
    apply propext
    simp only [A,mem_ofPred_eq,hp,and_true]
  rw [measure_congr hA]
  convert hb using 1
  congr 2
  ring
/-! ## Exhaustion to the entire-time maximum -/

/-- A strict crossing at any earlier time forces the capped first hit before the terminal horizon. -/
theorem cappedBrownianFirstPassage_lt_of_strict_crossing (x : ℝ) (T : ℝ≥0)
    (p : BrownianPath) (h0 : p 0 < x) (u : ℝ≥0) (hu : u ≤ T) (hx : x < p u) :
    cappedBrownianFirstPassage x T p < T := by
  obtain ⟨v,hv,hpv⟩ := intermediate_value_Icc
    zero_le p.continuous.continuousOn ⟨h0.le,hx.le⟩
  have hvu := lt_of_le_of_ne hv.2 (by aesop)
  have hτv :=
    csInf_le (s := {t : ℝ≥0 | t ≤ T ∧ x ≤ p t} ∪ {T}) (OrderBot.bddBelow _)
      (Or.inl ⟨hv.2.trans hu,hpv ▸ le_rfl⟩)
  exact (hτv.trans_lt hvu).trans_le hu

/-- Every finite-horizon strict crossing of a negative-drift path obeys the exponential upper bound. -/
theorem brownianPath_negativeDrift_finiteMaximum_le (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (ν x : ℝ) (hx : 0 < x)
    (T : ℝ≥0) :
    P {p | ∃ u ≤ T, x < p u-ν*(u : ℝ)} ≤ ENNReal.ofReal (Real.exp (-2*ν*x)) := by
  have hsub : {p : BrownianPath | ∃ u ≤ T, x < p u-ν*u} ≤ᵐ[P]
      {p | cappedBrownianFirstPassage x T (brownianDriftPath (-ν) p) < T} := by
    filter_upwards [hB.eval_zero_ae_eq_zero] with p hp
    rintro ⟨u,hu,hxu⟩
    have h0 : brownianDriftPath (-ν) p 0 < x := by
      change p 0+(-ν)*0 < x
      linarith
    apply cappedBrownianFirstPassage_lt_of_strict_crossing x T _ h0 u hu
    change x < p u+(-ν)*u
    linarith
  exact (measure_mono_ae hsub).trans
    (brownianPath_negativeDrift_cappedHit_le P hB ν x hx T)
section
variable (δ x : ℝ)

/-- Finite-horizon crossing events for a drifted continuous path are measurable. -/
theorem measurableSet_brownianPath_drift_strict_crossing (T : ℝ≥0) :
    MeasurableSet {p : BrownianPath | ∃ u ≤ T, x < p u+δ*(u : ℝ)} := by
  have hm : Measurable (brownianDriftPath δ) :=
    continuous_brownianDriftPath.measurable.comp (measurable_const.prodMk measurable_id)
  have hS := (brownianRawFiltration _ ContinuousMap.measurable_eval).le T _
    (measurableSet_brownianPath_strict_crossing T x)
  exact hS.preimage hm

/-- The entire-time crossing event is a countable increasing union of finite-horizon crossings. -/
theorem brownianPath_drift_crossing_eq_iUnion :
    {p : BrownianPath | ∃ t : ℝ≥0, x < p t+δ*(t : ℝ)} =
      ⋃ n : ℕ, {p | ∃ t ≤ (n : ℝ≥0), x < p t+δ*(t : ℝ)} := by
  ext p
  simp
  constructor
  · rintro ⟨t,ht⟩
    obtain ⟨n,hn⟩ := exists_nat_ge t
    tauto
  tauto

/-- Infinite-horizon drift crossing events are measurable on the continuous-path carrier. -/
theorem measurableSet_brownianPath_drift_crossing :
    MeasurableSet {p : BrownianPath | ∃ t : ℝ≥0, x < p t+δ*(t : ℝ)} := by
  rw [brownianPath_drift_crossing_eq_iUnion]
  exact MeasurableSet.iUnion (fun n => measurableSet_brownianPath_drift_strict_crossing δ x n)

end

/-- The all-time maximum of a negative-drift continuous Brownian path satisfies the sharp exponential upper bound. -/
theorem brownianPath_negativeDrift_maximum_le (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P)
    (ν x : ℝ) (hx : 0 < x) :
    P {p | ∃ t : ℝ≥0, x < p t-ν*(t : ℝ)} ≤ ENNReal.ofReal (Real.exp (-2*ν*x)) := by
  have hset : {p : BrownianPath | ∃ t : ℝ≥0, x < p t-ν*t} =
      ⋃ n : ℕ, {p | ∃ t ≤ (n : ℝ≥0), x < p t-ν*(t : ℝ)} := by
    simpa only [sub_eq_add_neg,neg_mul] using brownianPath_drift_crossing_eq_iUnion (-ν) x
  have hmono : Monotone (fun n : ℕ => {p : BrownianPath | ∃ t ≤ (n : ℝ≥0), x < p t-ν*(t : ℝ)}) := by
    intro n m hnm p
    rintro ⟨t,ht,hx⟩
    exact ⟨t,ht.trans (Nat.cast_le.mpr hnm),hx⟩
  rw [hset,hmono.measure_iUnion]
  exact iSup_le (fun n => brownianPath_negativeDrift_finiteMaximum_le P hB ν x hx n)

end DOZZ.Proofs
