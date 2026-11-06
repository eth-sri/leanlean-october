/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.Coupling.CountableLimit
public import DOZZ.Brownian.WienerExists
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Data.Rat.Denumerable
public import Mathlib.Topology.Instances.Rat
public import Mathlib.Topology.UniformSpace.UniformEmbedding
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

/-!
# Extension of an ordered rational-drift family

The drift-gap bounds give uniform continuity into the complete compact-open path carrier.
Extend the clipped rational family through its dense embedding into real drifts. Monotone
rational floor approximations transfer both order bounds and provide a jointly measurable
real-parameter family, with the zero family used outside the measurable order event.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology Uniformity Classical

namespace DOZZ.Proofs

/-- A monotone rational approximation from below, at mesh `1/(n+1)`. -/
noncomputable def couplingRationalApprox (n : ℕ) (a : ℝ) : ℚ :=
  (⌊((n : ℝ) + 1) * a⌋ : ℚ) / ((n : ℚ) + 1)


/-- The deterministic mesh error is bounded independently of the drift. -/
theorem couplingRationalApprox_error (n : ℕ) (a : ℝ) :
    0 ≤ a - (couplingRationalApprox n a : ℝ) ∧
      a - (couplingRationalApprox n a : ℝ) < 1 / ((n : ℝ) + 1) := by
  have couplingRationalApprox_cast (n : ℕ) (a : ℝ) : (couplingRationalApprox n a : ℝ) = (⌊((n : ℝ) + 1) * a⌋ : ℝ) / ((n : ℝ) + 1) := by
    simp only [couplingRationalApprox, Rat.cast_div, Rat.cast_intCast, Rat.cast_add,
      Rat.cast_natCast, Rat.cast_one]
  have hn : 0 < (n : ℝ) + 1 := by positivity
  rw [couplingRationalApprox_cast]
  have := Int.lt_floor_add_one (((n : ℝ) + 1) * a)
  constructor
  · exact sub_nonneg.mpr ((div_le_iff₀ hn).mpr (by simpa only [mul_comm] using (Int.floor_le (((n : ℝ) + 1) * a))))
  · apply (lt_div_iff₀ hn).mpr
    rw [(show (a - (⌊((n : ℝ) + 1) * a⌋ : ℝ) / ((n : ℝ) + 1)) * ((n : ℝ) + 1) = ((n : ℝ) + 1) * a - (⌊((n : ℝ) + 1) * a⌋ : ℝ) by field_simp)]
    nlinarith

theorem couplingRationalApprox_mono n : Monotone (couplingRationalApprox n) := by
  intro a b hab
  unfold couplingRationalApprox
  apply div_le_div_of_nonneg_right
  · exact_mod_cast Int.floor_mono (mul_le_mul_of_nonneg_left hab (by positivity))
  · positivity

/-- The floor approximation converges at every real drift. -/
theorem couplingRationalApprox_tendsto (a : ℝ) :
    Tendsto (fun n => (couplingRationalApprox n a : ℝ)) atTop (𝓝 a) := by
  simpa using ((tendsto_const_nhds (x := a)).sub (squeeze_zero (fun n => (couplingRationalApprox_error n a).1) (fun n => (couplingRationalApprox_error n a).2.le) tendsto_one_div_add_atTop_nhds_zero_nat))


/-- Compact-time pointwise Lipschitz bounds suffice for uniform continuity into paths. -/
theorem uniformContinuous_rationalPaths_of_drift_bound
    {F : ℚ → BrownianPath}
    (hF : ∀ q r : ℚ, ∀ t : ℝ≥0,
      |F q t - F r t| ≤ |(q : ℝ) - (r : ℝ)| * (t : ℝ)) : UniformContinuous F := by
  intro U hU
  obtain ⟨K, V, hK, hV, hVU⟩ :=
    (ContinuousMap.mem_compactConvergence_entourage_iff U).mp hU
  obtain ⟨ε, hε, hεV⟩ := Metric.mem_uniformity_dist.mp hV
  obtain ⟨T, hTpos, hT⟩ := compact_nonnegative_times_bounded K hK
  change {p : ℚ × ℚ | (F p.1, F p.2) ∈ U} ∈ 𝓤 ℚ
  filter_upwards [Metric.dist_mem_uniformity (div_pos hε hTpos)] with p hp
  apply hVU
  intro t ht
  apply hεV
  rw [Real.dist_eq]
  exact ((hF p.1 p.2 t).trans (mul_le_mul_of_nonneg_left (hT t ht) (abs_nonneg _))).trans_lt ((lt_div_iff₀ hTpos).mp (by simpa only [Rat.dist_eq] using hp))

/-- The uniform extension through the dense rational embedding. -/
noncomputable def rationalPathExtension (F : ℚ → BrownianPath) : ℝ → BrownianPath :=
  Rat.isDenseEmbedding_coe_real.isDenseInducing.extend F



/-- The extension is the compact-time limit along the explicit monotone mesh selectors. -/
theorem rationalPathExtension_approx_tendsto
    {F} (hF : UniformContinuous F) a :
    Tendsto (fun n => F (couplingRationalApprox n a)) atTop
      (𝓝 (rationalPathExtension F a)) := by
  have rationalPathExtension_rat (q : ℚ) : rationalPathExtension F q = F q := uniformly_extend_of_ind Rat.isUniformEmbedding_coe_real.isUniformInducing
      Rat.denseRange_cast hF q
  have uniformContinuous_rationalPathExtension : UniformContinuous (rationalPathExtension F) := uniformContinuous_uniformly_extend Rat.isUniformEmbedding_coe_real.isUniformInducing
      Rat.denseRange_cast hF
  simpa only [Function.comp_def, rationalPathExtension_rat] using ((uniformContinuous_rationalPathExtension).continuous.continuousAt.tendsto.comp (couplingRationalApprox_tendsto a))


/-- Extend a rational family constantly below zero before extending its parameter carrier. -/
def clippedRationalPathFamily (F : ℚ → BrownianPath) (q : ℚ) : BrownianPath := F (max q 0)

/-- The constant negative-drift part satisfies the same global drift-gap bounds. -/
theorem clippedRationalPathFamily_order
    {F}
    (hF : F ∈ negativeEntranceOrderSet ((↑) : ℚ → ℝ)) :
    ∀ q r : ℚ, q ≤ r → ∀ t : ℝ≥0,
      clippedRationalPathFamily F r t ≤ clippedRationalPathFamily F q t ∧
        clippedRationalPathFamily F q t ≤ clippedRationalPathFamily F r t +
          ((r : ℝ) - (q : ℝ)) * (t : ℝ) := by
  intro q r hqr t
  have hqrR : (q : ℝ) ≤ (r : ℝ) := by exact_mod_cast hqr
  have htn : 0 ≤ (t : ℝ) := t.2
  by_cases hr : r ≤ 0
  · have hq := hqr.trans hr
    simp only [clippedRationalPathFamily, max_eq_right hr, max_eq_right hq]
    exact ⟨le_rfl, le_add_of_nonneg_right (mul_nonneg (sub_nonneg.mpr hqrR) htn)⟩
  · have hr0 : 0 ≤ r := (lt_of_not_ge hr).le
    by_cases hq : q ≤ 0
    · have hqR : (q : ℝ) ≤ 0 := by exact_mod_cast hq
      have hrR : 0 ≤ (r : ℝ) := by exact_mod_cast hr0
      have h := hF 0 r (by norm_num) (by simpa only [Rat.cast_zero] using hrR) t
      simp only [clippedRationalPathFamily, max_eq_left hr0, max_eq_right hq]
      constructor
      · exact h.1
      · have hgap := h.2
        simp only [Rat.cast_zero, sub_zero] at hgap
        nlinarith
    · have hq0 : 0 ≤ q := (lt_of_not_ge hq).le
      simpa only [clippedRationalPathFamily, max_eq_left hr0, max_eq_left hq0]
        using hF q r (by exact_mod_cast hq0) hqrR t

/-- The clipped rational family's drift difference bounds its path difference. -/
theorem clippedRationalPathFamily_abs_sub_le
    {F}
    (hF : F ∈ negativeEntranceOrderSet ((↑) : ℚ → ℝ)) (q r : ℚ) (t : ℝ≥0) :
    |clippedRationalPathFamily F q t - clippedRationalPathFamily F r t| ≤
      |(q : ℝ) - (r : ℝ)| * (t : ℝ) := by
  rcases le_total q r with hqr | hrq
  · have h := clippedRationalPathFamily_order hF q r hqr t
    rw [abs_of_nonneg (sub_nonneg.mpr h.1), abs_of_nonpos (sub_nonpos.mpr (show (q : ℝ) ≤ (r : ℝ) by exact_mod_cast hqr))]
    nlinarith [h.2]
  · have h := clippedRationalPathFamily_order hF r q hrq t
    rw [abs_of_nonpos (sub_nonpos.mpr h.1), abs_of_nonneg (sub_nonneg.mpr (show (r : ℝ) ≤ (q : ℝ) by exact_mod_cast hrq))]
    nlinarith [h.2]

theorem uniformContinuous_clippedRationalPathFamily
    {F}
    (hF : F ∈ negativeEntranceOrderSet ((↑) : ℚ → ℝ)) :
    UniformContinuous (clippedRationalPathFamily F) :=
  uniformContinuous_rationalPaths_of_drift_bound (clippedRationalPathFamily_abs_sub_le hF)

/-- A real-parameter family defined on every sample. Off the closed order set use the zero path;
this choice permits a measurable extension without assuming order on exceptional samples. -/
noncomputable def orderedRationalPathExtension (F : ℚ → BrownianPath) (a : ℝ) : BrownianPath :=
  if F ∈ negativeEntranceOrderSet ((↑) : ℚ → ℝ) then
    rationalPathExtension (clippedRationalPathFamily F) a else 0

/-- Both all-real order bounds hold samplewise in the completed family. -/
theorem orderedRationalPathExtension_order (F : ℚ → BrownianPath) :
    NegativeEntranceFamilyOrder (orderedRationalPathExtension F) := by
  classical
  have rationalPathExtension_order {F : ℚ → BrownianPath} (hF : UniformContinuous F) (horder : ∀ q r : ℚ, q ≤ r → ∀ t : ℝ≥0, F r t ≤ F q t ∧ F q t ≤ F r t + ((r : ℝ) - (q : ℝ)) * (t : ℝ)) : ∀ a b : ℝ, a ≤ b → ∀ t : ℝ≥0, rationalPathExtension F b t ≤ rationalPathExtension F a t ∧ rationalPathExtension F a t ≤ rationalPathExtension F b t + (b - a) * (t : ℝ) := by
    intro a b hab t
    have ha := (continuous_eval_const t).continuousAt.tendsto.comp
      (rationalPathExtension_approx_tendsto hF a)
    have hb := (continuous_eval_const t).continuousAt.tendsto.comp
      (rationalPathExtension_approx_tendsto hF b)
    constructor
    · exact le_of_tendsto_of_tendsto hb ha (Eventually.of_forall fun n =>
        (horder _ _ (couplingRationalApprox_mono n hab) t).1)
    · exact le_of_tendsto_of_tendsto ha (hb.add (((couplingRationalApprox_tendsto b).sub (couplingRationalApprox_tendsto a)).mul_const (t : ℝ))) (Eventually.of_forall fun n =>
        (horder _ _ (couplingRationalApprox_mono n hab) t).2)
  by_cases hF : F ∈ negativeEntranceOrderSet ((↑) : ℚ → ℝ)
  · intro a b _ hab t
    simpa only [orderedRationalPathExtension, ite_eq_left hF] using
      rationalPathExtension_order (uniformContinuous_clippedRationalPathFamily hF)
        (clippedRationalPathFamily_order hF) a b hab t
  · intro a b _ hab t
    simp only [orderedRationalPathExtension, ite_eq_right hF, ContinuousMap.zero_apply, zero_add]
    exact ⟨le_rfl, mul_nonneg (sub_nonneg.mpr hab) t.2⟩

/-- The explicit selector sequence converges for all samples, including exceptional ones. -/
theorem orderedRationalPathExtension_approx_tendsto F a :
    Tendsto (fun n => if F ∈ negativeEntranceOrderSet ((↑) : ℚ → ℝ) then
      clippedRationalPathFamily F (couplingRationalApprox n a) else 0) atTop
      (𝓝 (orderedRationalPathExtension F a)) := by
  classical
  by_cases hF : F ∈ negativeEntranceOrderSet ((↑) : ℚ → ℝ)
  · simpa only [orderedRationalPathExtension, ite_eq_left hF] using
      rationalPathExtension_approx_tendsto (uniformContinuous_clippedRationalPathFamily hF) a
  · simp only [orderedRationalPathExtension, ite_eq_right hF]
    exact tendsto_const_nhds

/-- Joint measurability of one clipped mesh selector. Countability of the rational parameter
allows arbitrary dependence among the path coordinates. -/
theorem measurable_clipped_rational_selector n :
    Measurable (fun p : ℝ × (ℚ → BrownianPath) =>
      clippedRationalPathFamily p.2 (couplingRationalApprox n p.1)) := by
  exact (measurable_from_prod_countable_right (fun q => measurable_pi_apply (max q 0)) : Measurable (fun p : ℚ × (ℚ → BrownianPath) => p.2 (max p.1 0))).comp ((((show Measurable (couplingRationalApprox n) by exact (measurable_of_countable (fun k : ℤ => (k : ℚ) / ((n : ℚ) + 1))).comp (Int.measurable_floor.comp (measurable_const.mul measurable_id)))).comp measurable_fst).prodMk measurable_snd)

/-- The completed family is jointly measurable in drift and sample, not only separately
measurable at fixed drifts. -/
theorem measurable_orderedRationalPathExtension :
    Measurable (fun p : ℝ × (ℚ → BrownianPath) => orderedRationalPathExtension p.2 p.1) := by
  classical
  apply measurable_of_tendsto_metrizable
    (f := fun n p => if p.2 ∈ negativeEntranceOrderSet ((↑) : ℚ → ℝ) then
      clippedRationalPathFamily p.2 (couplingRationalApprox n p.1) else 0)
  · intro n
    exact (measurable_clipped_rational_selector n).ite ((isClosed_negativeEntranceOrderSet ((↑) : ℚ → ℝ)).measurableSet.preimage measurable_snd) measurable_const
  · apply tendsto_pi_nhds.mpr
    intro p
    exact orderedRationalPathExtension_approx_tendsto p.2 p.1

/-- Every fixed-drift evaluation is a measurable whole random path. -/
theorem measurable_orderedRationalPathExtension_at a :
    Measurable (fun F : ℚ → BrownianPath => orderedRationalPathExtension F a) :=
  measurable_orderedRationalPathExtension.comp
    ((show Measurable (fun _ : ℚ → BrownianPath => a) from measurable_const).prodMk measurable_id)

/-- The completed family has the exact compact-time zero-drift limit for every sample. -/
theorem orderedRationalPathExtension_tendsto_zero F :
    Tendsto (orderedRationalPathExtension F) (𝓝[>] 0)
      (𝓝 (orderedRationalPathExtension F 0)) :=
  negativeEntranceFamilyOrder_tendsto_zero (orderedRationalPathExtension_order F)

/-- The real-drift family on two independent copies of the rational-path carrier. -/
noncomputable def realDriftCouplingOfRationalPaths
    (a : ℝ) (F : (ℚ → BrownianPath) × (ℚ → BrownianPath)) :
    BrownianPath × BrownianPath :=
  (orderedRationalPathExtension F.1 a, orderedRationalPathExtension F.2 a)


/-- Only real-drift marginal identification remains in the final conditional assembly. The
simultaneous order event, path continuity, measurability and two-half independence are proved. -/
theorem realDriftCouplingOfRationalPaths_isOrdered_of_marginals
    (Q : Measure (ℚ → BrownianPath)) [IsProbabilityMeasure Q]
    (hlaw : ∀ a : ℝ, 0 ≤ a → IsNegativeConditionedBrownianLaw a
      (Q.map (fun F => orderedRationalPathExtension F a))) :
    IsOrderedTwoSidedConditionedCoupling (Q.prod Q) realDriftCouplingOfRationalPaths := by
  have realDriftCouplingOfRationalPaths_order_and_limit F : (∀ a b : ℝ, 0 ≤ a → a ≤ b → ∀ t : ℝ≥0, (realDriftCouplingOfRationalPaths b F).1 t ≤ (realDriftCouplingOfRationalPaths a F).1 t ∧ (realDriftCouplingOfRationalPaths a F).1 t ≤ (realDriftCouplingOfRationalPaths b F).1 t + (b - a) * (t : ℝ) ∧ (realDriftCouplingOfRationalPaths b F).2 t ≤ (realDriftCouplingOfRationalPaths a F).2 t ∧ (realDriftCouplingOfRationalPaths a F).2 t ≤ (realDriftCouplingOfRationalPaths b F).2 t + (b - a) * (t : ℝ)) ∧ Tendsto (fun a => realDriftCouplingOfRationalPaths a F) (𝓝[>] 0) (𝓝 (realDriftCouplingOfRationalPaths 0 F)) := by
    refine ⟨?_, (orderedRationalPathExtension_tendsto_zero F.1).prodMk_nhds
      (orderedRationalPathExtension_tendsto_zero F.2)⟩
    intro a b ha hab t
    have hfirst := orderedRationalPathExtension_order F.1 a b ha hab t
    have hsecond := orderedRationalPathExtension_order F.2 a b ha hab t
    exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩
  refine ⟨?_, ae_of_all _ realDriftCouplingOfRationalPaths_order_and_limit⟩
  intro a ha
  exact independentEntranceCopies_twoSided (F := fun a F => orderedRationalPathExtension F a) ⟨(measurable_orderedRationalPathExtension_at a).aemeasurable, hlaw a ha⟩

/-- Fix an enumeration of all rational drifts for the countable-product compactness argument. -/
noncomputable def couplingRationalEnumeration : ℚ ≃ ℕ := Denumerable.eqv ℚ

/-- Reindex the extracted countable path family by actual rational drifts. -/
noncomputable def couplingRationalReindex (x : ℕ → BrownianPath) : ℚ → BrownianPath :=
  fun q => x (couplingRationalEnumeration q)

theorem measurable_couplingRationalReindex : Measurable couplingRationalReindex :=
  measurable_pi_iff.mpr fun q => measurable_pi_apply (couplingRationalEnumeration q)

/-- Clipping negative drifts before enumeration provides nonnegative entrance marginals. -/
noncomputable def couplingEnumeratedDrift (n : ℕ) : ℝ :=
  max (couplingRationalEnumeration.symm n : ℝ) 0

/-- The reindexed limit retains the simultaneous rational order event. -/
theorem couplingRationalReindex_mem_orderSet x
    (hx : x ∈ negativeEntranceOrderSet couplingEnumeratedDrift) :
    couplingRationalReindex x ∈ negativeEntranceOrderSet ((↑) : ℚ → ℝ) := by
  intro q r hq hqr t
  have hq' : couplingEnumeratedDrift (couplingRationalEnumeration q) = (q : ℝ) := by
    simp [couplingEnumeratedDrift, max_eq_left hq]
  have hr' : couplingEnumeratedDrift (couplingRationalEnumeration r) = (r : ℝ) := by
    simp [couplingEnumeratedDrift, max_eq_left (hq.trans hqr)]
  simpa only [couplingRationalReindex, hq', hr'] using (hx (couplingRationalEnumeration q) (couplingRationalEnumeration r) (by rw [hq']; exact hq) (by rw [hq', hr']; exact hqr) t)

/-- Almost-sure convergence of measurable random paths gives convergence of their full path laws. -/
theorem coupling_probabilityMap_tendsto_of_ae
    {Ω E : Type*} [MeasurableSpace Ω] [TopologicalSpace E] [MeasurableSpace E]
    [BorelSpace E] (Q : ProbabilityMeasure Ω) (f : ℕ → Ω → E) g
    (hf : ∀ n, Measurable (f n)) (hg : Measurable g)
    (hlim : ∀ᵐ ω ∂(Q : Measure Ω), Tendsto (fun n => f n ω) atTop (𝓝 (g ω))) :
    Tendsto (fun n => Q.map (f n)) atTop (𝓝 (Q.map g)) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro test
  have hmap n : (∫ x, test x ∂(Q.map (f n) : Measure E)) =
      ∫ ω, test (f n ω) ∂(Q : Measure Ω) := integral_map (hf n).aemeasurable test.continuous.measurable.aestronglyMeasurable
  have hmapg : (∫ x, test x ∂(Q.map g : Measure E)) =
      ∫ ω, test (g ω) ∂(Q : Measure Ω) := integral_map hg.aemeasurable test.continuous.measurable.aestronglyMeasurable
  simp_rw [hmap, hmapg]
  apply tendsto_integral_of_dominated_convergence (fun _ => ‖test‖)
  · intro n
    exact (test.continuous.measurable.comp (hf n)).aestronglyMeasurable
  · exact integrable_const _
  · intro n
    exact ae_of_all _ fun ω => test.norm_coe_le_norm (f n ω)
  · exact hlim.mono fun ω hω => test.continuous.continuousAt.tendsto.comp hω



/-- A probability-measure version of the unconditional negative radial path candidate. -/
noncomputable def negativeRogersPitmanWienerProbability (a : ℝ) :
    ProbabilityMeasure BrownianPath :=
  ProbabilityMeasure.map
    (⟨wienerTripleMeasure, inferInstance⟩ : ProbabilityMeasure BrownianTriple)
    (negativeRogersPitmanPath a)




/-- Once the actual radial candidate is characterized, every real marginal of the completed
family has the literal conditioned law. -/
theorem orderedRationalPathExtension_real_law_of_radial
    (Q : ProbabilityMeasure (ℚ → BrownianPath))
    (hgood : ∀ᵐ F ∂(Q : Measure (ℚ → BrownianPath)),
      F ∈ negativeEntranceOrderSet ((↑) : ℚ → ℝ))
    (hrational : ∀ q : ℚ, 0 ≤ q →
      Q.map (fun F => F q) = negativeRogersPitmanWienerProbability q)
    (hradial : ∀ a : ℝ, 0 ≤ a → IsNegativeConditionedBrownianLaw a
      (negativeRogersPitmanWienerProbability a : Measure BrownianPath))
    a (ha : 0 ≤ a) :
    IsNegativeConditionedBrownianLaw a
      ((Q : Measure (ℚ → BrownianPath)).map (fun F => orderedRationalPathExtension F a)) := by
  have orderedRationalPathExtension_map_eq_radial : Q.map (fun F => orderedRationalPathExtension F a) = negativeRogersPitmanWienerProbability a := by
    have orderedRationalPathExtension_probability_tendsto : Tendsto (fun n => Q.map (fun F => if F ∈ negativeEntranceOrderSet ((↑) : ℚ → ℝ) then clippedRationalPathFamily F (couplingRationalApprox n a) else 0)) atTop (𝓝 (Q.map (fun F => orderedRationalPathExtension F a))) := by
      apply coupling_probabilityMap_tendsto_of_ae
      · intro n
        exact ((measurable_clipped_rational_selector n).comp
          (measurable_const.prodMk measurable_id)).ite
            (isClosed_negativeEntranceOrderSet ((↑) : ℚ → ℝ)).measurableSet measurable_const
      · exact measurable_orderedRationalPathExtension_at a
      · exact ae_of_all _ fun F => orderedRationalPathExtension_approx_tendsto F a
    have negativeRogersPitmanWienerProbability_tendsto {a : ℕ → ℝ} {b} (hab : Tendsto a atTop (𝓝 b)) : Tendsto (fun n => negativeRogersPitmanWienerProbability (a n)) atTop (𝓝 (negativeRogersPitmanWienerProbability b)) := by
      have continuous_rogersPitmanPath_parameter V : Continuous (fun a => rogersPitmanPath a V) := by
        apply ContinuousMap.continuous_of_continuous_uncurry
        change Continuous (fun p : ℝ × ℝ≥0 => ‖rogersPitmanVectorAt p.1 V p.2‖)
        apply Continuous.norm
        apply (PiLp.continuous_toLp 2 _).comp
        apply continuous_pi
        intro i
        change Continuous (fun p : ℝ × ℝ≥0 => V i p.2 +
          (if i = 0 then p.1 * (p.2 : ℝ) else 0))
        split_ifs <;> fun_prop
      apply coupling_probabilityMap_tendsto_of_ae
      · intro n
        exact measurable_negativeRogersPitmanPath (a n)
      · exact measurable_negativeRogersPitmanPath b
      · exact ae_of_all _ fun V =>
          ((fun V => (continuous_rogersPitmanPath_parameter V).neg) V).continuousAt.tendsto.comp hab
    have hmap n : Q.map (fun F =>
        if F ∈ negativeEntranceOrderSet ((↑) : ℚ → ℝ) then
          clippedRationalPathFamily F (couplingRationalApprox n a) else 0) =
        negativeRogersPitmanWienerProbability ((max (couplingRationalApprox n a) 0 : ℚ) : ℝ) := by
      calc
        _ = Q.map (fun F => F (max (couplingRationalApprox n a) 0)) := by
          apply Subtype.ext
          apply Measure.map_congr
          exact hgood.mono fun F hF => by
            dsimp only
            rw [ite_eq_left hF]
            rfl
        _ = _ := hrational _ (le_max_right _ _)
    have hradial := negativeRogersPitmanWienerProbability_tendsto (show Tendsto (fun n => ((max (couplingRationalApprox n a) 0 : ℚ) : ℝ)) atTop (𝓝 a) by simp only [Rat.cast_max, Rat.cast_zero]; simpa only [max_eq_left ha] using (couplingRationalApprox_tendsto a).max (tendsto_const_nhds (x := (0 : ℝ))))
    simp_rw [← hmap] at hradial
    exact tendsto_nhds_unique (orderedRationalPathExtension_probability_tendsto) hradial
  have h := congrArg (fun R : ProbabilityMeasure BrownianPath => (R : Measure BrownianPath))
    (orderedRationalPathExtension_map_eq_radial)
  change (Q : Measure (ℚ → BrownianPath)).map (fun F => orderedRationalPathExtension F a) =
    (negativeRogersPitmanWienerProbability a : Measure BrownianPath) at h
  rw [h]
  exact hradial a ha

end DOZZ.Proofs
