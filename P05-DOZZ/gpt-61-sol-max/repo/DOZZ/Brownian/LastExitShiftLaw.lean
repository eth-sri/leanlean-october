/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.LastExitDyadicMixture
public import DOZZ.Brownian.LastExitFinite
public import DOZZ.Brownian.LastExitPostPathMeasurability
public import DOZZ.Brownian.WienerExists
public import DOZZ.Brownian.ConditionedFDDUniqueness
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Tactic

/-!
# Finite rational projections of the post-last-exit path

The dyadic cell mixture converges on every measurable finite rational projection. The selected
continuous paths themselves converge pointwise in path space, so the limiting post-last-exit path
has the same finite rational projection law as the entrance density.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs

private theorem tendsto_map_of_ae_pointwise
    {Ω E : Type*} [MeasurableSpace Ω] [TopologicalSpace E] [MeasurableSpace E]
    [BorelSpace E] (Q : ProbabilityMeasure Ω) (f : ℕ → Ω → E) (g : Ω → E)
    (hf : ∀ n, Measurable (f n)) (hg : Measurable g)
    (hlim : ∀ᵐ ω ∂(Q : Measure Ω),
      Tendsto (fun n => f n ω) atTop (𝓝 (g ω))) :
    Tendsto (fun n => Q.map (f n)) atTop (𝓝 (Q.map g)) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro test
  have hmap (n : ℕ) :
      (∫ x, test x ∂(Q.map (f n) : Measure E)) =
        ∫ ω, test (f n ω) ∂(Q : Measure Ω) :=
    integral_map (hf n).aemeasurable test.continuous.measurable.aestronglyMeasurable
  have hmapg :
      (∫ x, test x ∂(Q.map g : Measure E)) =
        ∫ ω, test (g ω) ∂(Q : Measure Ω) :=
    integral_map hg.aemeasurable test.continuous.measurable.aestronglyMeasurable
  simp_rw [hmap, hmapg]
  apply tendsto_integral_of_dominated_convergence (fun _ => ‖test‖)
  · intro n
    exact (test.continuous.measurable.comp (hf n)).aestronglyMeasurable
  · exact integrable_const _
  · intro n
    exact ae_of_all _ fun ω => test.norm_coe_le_norm (f n ω)
  · exact hlim.mono fun ω hω => test.continuous.continuousAt.tendsto.comp hω

/-- The dyadic path approximation converges continuously to the literal recentered post-last-exit
path, for every input continuous path. -/
theorem dyadicLastExitPathApproximation_tendsto
    (p : BrownianPath) (c : ℝ) :
    Tendsto (fun n => dyadicLastExitPathApproximation n c p) atTop
      (𝓝 (negativeConditionedPostLastExitPath c p)) := by
  let τ := negativeLastExitTime p c
  have htimeReal : Tendsto
      (fun n : ℕ => (dyadicLastExitCeilingTime n τ : ℝ)) atTop (𝓝 (τ : ℝ)) := dyadicLastExitCeilingTime_coe_tendsto τ
  have htime  :=
    NNReal.tendsto_coe.mp htimeReal
  have hpair : Tendsto
      (fun n : ℕ => (dyadicLastExitCeilingTime n τ, p)) atTop (𝓝 (τ, p)) :=
    htime.prodMk_nhds tendsto_const_nhds
  have hcont  :=
    (continuous_shiftPathAddConstant c).continuousAt.tendsto.comp hpair
  aesop

/-- Every measurable finite projection at positive rational offsets of the post-last-exit path
has the conditioned entrance law. -/
theorem negativeConditionedPostLastExit_positiveRationalProjection
    {ν c : ℝ} {P B Q : Measure BrownianPath} [SFinite B]
    (hP : IsNegativeConditionedBrownianLaw ν P)
    (hB : IsBrownianReal (fun t p => p t) B)
    (hQ : IsNegativeConditionedBrownianLaw ν Q)
    (hν : 0 < ν) (hc : 0 < c)
    (n : ℕ) (offsets : Fin n → ℚ)
    (hoff : ∀ i, 0 < (offsets i : ℝ)) (hmono : StrictMono offsets) :
    (P.map (fun p i => -(negativeConditionedPostLastExitPath c p
        (Real.toNNReal (offsets i : ℝ))))) =
      volume.withDensity (brownianEntranceFinitePDF ν n
        (brownianFirstHitElapsed n (fun i => Real.toNNReal (offsets i)))) := by
  classical
  let := hP.2.1
  let ts  := fun i => Real.toNNReal (offsets i)
  let ds  := brownianFirstHitElapsed n ts
  have hts0  := fun i => Real.toNNReal_pos.mpr (hoff i)
  have htsmono : StrictMono ts := by
    intro i j hij
    aesop
  have hds  :=
    fun i => brownianFirstHitElapsed_pos n ts hts0 htsmono i
  have htime (i : Fin n) :
      (⟨(offsets i : ℝ), (hoff i).le⟩ : ℝ≥0) = ts i := by
    apply Subtype.ext
    simp [ts, Real.coe_toNNReal _ (hoff i).le]
  let M : Measure (Fin n → ℝ) := volume.withDensity (brownianEntranceFinitePDF ν n ds)
  have hMprob : IsProbabilityMeasure M := by
    refine ⟨?_⟩
    change (volume.withDensity (brownianEntranceFinitePDF ν n ds)) Set.univ = 1
    rw [withDensity_apply _ MeasurableSet.univ]
    simpa only [setLIntegral_univ] using
      lintegral_brownianEntranceFinitePDF_one Q ν hν hQ n ds hds
  let μ : ProbabilityMeasure (Fin n → ℝ) := ⟨M, hMprob⟩
  let f  := fun p i =>
    -(negativeConditionedPostLastExitPath c p (ts i))
  let fdyad  := fun k p i =>
    dyadicPositiveLastExitRationalEvals k c p (offsets i)
  have hfdyad : ∀ k, Measurable (fdyad k) := by
    intro k
    apply measurable_pi_iff.mpr
    intro i
    exact (measurable_pi_apply (offsets i)).comp
      (measurable_dyadicPositiveLastExitRationalEvals k c)
  have hf : Measurable f := by
    apply measurable_pi_iff.mpr
    intro i
    exact ((ContinuousMap.measurable_eval (ts i)).comp
      (measurable_negativeConditionedPostLastExitPath c)).neg
  let μdyad  := fun k =>
    ProbabilityMeasure.map (⟨P, hP.2.1⟩ : ProbabilityMeasure BrownianPath)
      (fdyad k)
  let μpost  :=
    ProbabilityMeasure.map (⟨P, hP.2.1⟩ : ProbabilityMeasure BrownianPath) f
  have hpoint : ∀ p, Tendsto (fun k => fdyad k p) atTop (𝓝 (f p)) := by
    intro p
    have hpath := dyadicLastExitPathApproximation_tendsto p c
    apply tendsto_pi_nhds.mpr
    intro i
    exact (continuous_eval_const (ts i)).neg.continuousAt.tendsto.comp hpath
  have hpathLaw  :=
    tendsto_map_of_ae_pointwise ⟨P, hP.2.1⟩ fdyad f hfdyad hf
      (Filter.Eventually.of_forall hpoint)
  have hmix := negativeConditionedDyadicLastExit_finiteProjection_tendsto_entrance
    hP hB hν hQ ⟨c, hc.le⟩ hc n offsets hoff hmono
  have hprobEvent (A : Set (Fin n → ℝ)) (hA : MeasurableSet A) :
      Tendsto (fun k => μdyad k A) atTop (𝓝 (μ A)) := by
    have hpre (k : ℕ) : fdyad k ⁻¹' A =
        dyadicPositiveLastExitRationalEvent k c
          {y | (fun i => y (offsets i)) ∈ A} := by
      ext p
      rfl
    have hreal : Tendsto
        (fun k => ((μdyad k : Measure (Fin n → ℝ)) A).toReal)
        atTop (𝓝 ((M A).toReal)) := by
      have heq (k : ℕ) :
          ((μdyad k : Measure (Fin n → ℝ)) A).toReal =
            P.real (dyadicPositiveLastExitRationalEvent k c
              {y | (fun i => y (offsets i)) ∈ A}) := by
        have happly : (μdyad k : Measure (Fin n → ℝ)) A = P (fdyad k ⁻¹' A) := by
          change (P.map (fdyad k)) A = _
          rw [Measure.map_apply (hfdyad k) hA]
        rw [happly, hpre]
        rfl
      exact Tendsto.congr'
        (Filter.Eventually.of_forall fun k => (heq k).symm) (hmix A hA)
    have hfinite : ∀ k, (μdyad k : Measure (Fin n → ℝ)) A ≠ ∞ :=
      fun k => measure_ne_top _ _
    have hmeasure  :=
      (ENNReal.tendsto_toReal_iff hfinite (measure_ne_top M A)).mp hreal
    have hnn := (ENNReal.tendsto_toNNReal_iff (measure_ne_top M A) hfinite).2 hmeasure
    assumption_mod_cast
  have hweak : Tendsto μdyad atTop (𝓝 μ) := by
    apply IsPiSystem.tendsto_probabilityMeasure_of_tendsto_of_mem
      (S := {U : Set (Fin n → ℝ) | @IsOpen (Fin n → ℝ) inferInstance U})
    · intro U hU V hV hne
      change IsOpen U at hU
      exact hU.inter hV
    · intro U hU
      change IsOpen U at hU
      exact hU.measurableSet
    · intro U hU x hx
      exact ⟨U, hU, hU.mem_nhds hx, Subset.rfl⟩
    · intro U hU
      change IsOpen U at hU
      exact hprobEvent U hU.measurableSet
  have hμeq  := tendsto_nhds_unique hpathLaw hweak
  have hdsEq : ds = brownianFirstHitElapsed n
      (fun i => Real.toNNReal (offsets i)) := rfl
  have hμeq'  :=
    congrArg (fun R : ProbabilityMeasure (Fin n → ℝ) => (R : Measure (Fin n → ℝ))) hμeq
  assumption_mod_cast

/-- The finite positive rational projections of any conditioned path law are the same
entrance-density measures used by the dyadic mixture. -/
theorem negativeConditionedLaw_positiveRationalProjection
    {ν : ℝ} {P : Measure BrownianPath}
    (hP : IsNegativeConditionedBrownianLaw ν P) (hν : 0 < ν)
    {n : ℕ} (hn : 0 < n) (offsets : Fin n → ℚ)
    (hoff : ∀ i, 0 < (offsets i : ℝ)) (hmono : StrictMono offsets) :
    (P.map (fun p i => -(p (Real.toNNReal (offsets i : ℝ))))) =
      volume.withDensity (brownianEntranceFinitePDF ν n
        (brownianFirstHitElapsed n (fun i => Real.toNNReal (offsets i : ℝ)))) := by
  classical
  let ts  := fun i => Real.toNNReal (offsets i : ℝ)
  let ds  := brownianFirstHitElapsed n ts
  have hts0  := fun i => Real.toNNReal_pos.mpr (hoff i)
  have htsmono : StrictMono ts := by
    intro i j hij
    aesop
  have hds  :=
    fun i => brownianFirstHitElapsed_pos n ts hts0 htsmono i
  have htimes : brownianFirstHitTimes n ds = ts := by
    cases n with
    | zero => simp at hn
    | succ m => exact brownianFirstHitTimes_elapsed m ts htsmono.monotone
  have hfd := negativeConditionedLaw_positiveFDD hP n hn ts hts0 htsmono
  have hpdf (x : Fin n → ℝ) :
      brownianEntranceFinitePDF ν n ds x =
        ENNReal.ofReal (max 0 (conditionedPositiveFDDDensity ν
          (List.ofFn fun i => (ts i : ℝ)) (List.ofFn fun i => x i))) := by
    rw [brownianEntranceFinitePDF_eq_conditionedPositiveFDDDensity ν hν n ds hds x, htimes]
    simp_all

  have hmeasure : volume.withDensity (brownianEntranceFinitePDF ν n ds) =
      volume.withDensity (fun x => ENNReal.ofReal (max 0
        (conditionedPositiveFDDDensity ν (List.ofFn fun i => (ts i : ℝ))
          (List.ofFn fun i => x i)))) := by
    ext <;> simp_all
  rw [hfd, hmeasure]

private def postLastExitPositiveRationalEvals (p : BrownianPath) :
    {q : ℚ // 0 < (q : ℝ)} → ℝ := fun q =>
  -(p ⟨(q.val : ℝ), q.property.le⟩)

private def postLastExitRationalEvalRect
    (I : Finset {q : ℚ // 0 < (q : ℝ)})
    (S : {q : ℚ // 0 < (q : ℝ)} → Set ℝ) : Set BrownianPath :=
  {p | ∀ q ∈ I, postLastExitPositiveRationalEvals p q ∈ S q}

private def postLastExitRationalEvalRectangles : Set (Set BrownianPath) :=
  {A | ∃ I S, (∀ q, MeasurableSet (S q)) ∧
    A = postLastExitRationalEvalRect I S}

private theorem measurable_postLastExitPositiveRationalEvals :
    Measurable postLastExitPositiveRationalEvals := by
  apply measurable_pi_iff.mpr
  intro q
  let t : ℝ≥0 := ⟨(q.val : ℝ), q.property.le⟩
  exact (ContinuousMap.measurable_eval t).neg

private theorem postLastExitRationalEvalRectangles_piSystem :
    IsPiSystem postLastExitRationalEvalRectangles := by
  intro A hA B hB hne
  rcases hA with ⟨I, S, hS, rfl⟩
  rcases hB with ⟨J, T, hT, rfl⟩
  let U  := fun q =>
    (if q ∈ I then S q else Set.univ) ∩ (if q ∈ J then T q else Set.univ)
  refine ⟨I ∪ J, U, ?_, ?_⟩
  · intro q
    dsimp [U]
    split_ifs <;> simp [hS, hT]
  · ext p
    simp only [postLastExitRationalEvalRect, Set.mem_ofPred_eq, Set.mem_inter_iff]
    grind

/-- Rational evaluations on positive times generate the Borel sigma algebra of continuous path
space. Every real evaluation is a pointwise limit of evaluations at rational times from above. -/
private theorem postLastExitRationalEvalRectangles_generate_measurableSpace :
    (inferInstance : MeasurableSpace BrownianPath) =
      MeasurableSpace.generateFrom postLastExitRationalEvalRectangles := by
  let mRat := MeasurableSpace.generateFrom postLastExitRationalEvalRectangles
  have hcoord (q : {q : ℚ // 0 < (q : ℝ)}) : Measurable[mRat]
      (fun p : BrownianPath => postLastExitPositiveRationalEvals p q) := by
    intro s hs
    let S  := fun r =>
      if r = q then s else Set.univ
    have hS : ∀ r, MeasurableSet (S r) := by
      continuity
    have hrect : postLastExitRationalEvalRect {q} S =
        {p | postLastExitPositiveRationalEvals p q ∈ s} := by
      ext p
      simp [postLastExitRationalEvalRect, S]
    have hbasic : postLastExitRationalEvalRect {q} S ∈
        postLastExitRationalEvalRectangles := ⟨{q}, S, hS, rfl⟩
    change MeasurableSet {p | postLastExitPositiveRationalEvals p q ∈ s}
    rw [← hrect]
    exact MeasurableSpace.measurableSet_generateFrom hbasic
  have hEval (t : ℝ≥0) : Measurable[mRat] (fun p : BrownianPath => p t) := by
    let qfun  := (Real.exists_seq_rat_strictAnti_tendsto (t : ℝ)).choose
    have hqfun  :=
      (Real.exists_seq_rat_strictAnti_tendsto (t : ℝ)).choose_spec
    have hzeroLe : (0 : ℝ) ≤ (t : ℝ) := by exact_mod_cast t.property
    let rfun : ℕ → ℝ≥0 := fun n => ⟨(qfun n : ℝ),
      (lt_of_le_of_lt hzeroLe (hqfun.2.1 n)).le⟩
    have hrfunReal  := hqfun.2.2
    have hrfun : Tendsto rfun atTop (𝓝 t) := NNReal.tendsto_coe.mp hrfunReal
    let rfunQ : ℕ → {q : ℚ // 0 < (q : ℝ)} := fun n =>
      ⟨qfun n, lt_of_le_of_lt hzeroLe (hqfun.2.1 n)⟩
    have happrox : ∀ n, Measurable[mRat] (fun p : BrownianPath => p (rfun n)) := by
      intro n
      have hcoord' := hcoord (rfunQ n)
      have heq : (fun p : BrownianPath => p (rfun n)) =
          fun p => -postLastExitPositiveRationalEvals p (rfunQ n) := by
        funext p
        simp [postLastExitPositiveRationalEvals, rfun, rfunQ]
      rw [heq]
      exact hcoord'.neg
    have hlimit : ∀ p : BrownianPath,
        Tendsto (fun n => p (rfun n)) atTop (𝓝 (p t)) := by
      intro p
      exact p.continuous.continuousAt.tendsto.comp hrfun
    have hlimitFun  := tendsto_pi_nhds.mpr hlimit
    exact measurable_of_tendsto_metrizable happrox hlimitFun
  have hfull_le : ContinuousMap.measurableSpace ≤ mRat := by
    rw [ContinuousMap.measurableSpace_eq_iSup_comap_eval]
    exact iSup_le fun t => (hEval t).comap_le
  have hRat_le : mRat ≤ ContinuousMap.measurableSpace := by
    apply MeasurableSpace.generateFrom_le
    intro A hA
    rcases hA with ⟨I, S, hS, rfl⟩
    change MeasurableSet[ContinuousMap.measurableSpace] (postLastExitRationalEvalRect I S)
    have hset : {p | ∀ q ∈ I, postLastExitPositiveRationalEvals p q ∈ S q} =
        ⋂ q, ⋂ (_ : q ∈ I), {p | postLastExitPositiveRationalEvals p q ∈ S q} := by
      ext p
      simp
    change MeasurableSet[ContinuousMap.measurableSpace]
      {p | ∀ q ∈ I, postLastExitPositiveRationalEvals p q ∈ S q}
    rw [hset]
    apply MeasurableSet.iInter
    intro q
    apply MeasurableSet.iInter
    intro hq
    exact (hS q).preimage
      ((measurable_pi_apply q).comp measurable_postLastExitPositiveRationalEvals)
  exact le_antisymm hfull_le hRat_le

private theorem postLastExitRationalEvalRect_measure_eq
    {ν c : ℝ} {P : Measure BrownianPath}
    (hP : IsNegativeConditionedBrownianLaw ν P)
    (hν : 0 < ν) (hc : 0 < c)
    (I : Finset {q : ℚ // 0 < (q : ℝ)}) (hI : I.Nonempty)
    (S : {q : ℚ // 0 < (q : ℝ)} → Set ℝ) (hS : ∀ q, MeasurableSet (S q)) :
    (P.map (negativeConditionedPostLastExitPath c))
        (postLastExitRationalEvalRect I S) = P (postLastExitRationalEvalRect I S) := by
  classical
  let n := I.card
  have hn  := Finset.card_pos.mpr hI
  let e : Fin n ≃o I := I.orderIsoOfFin rfl
  let qidx  := fun i => (e i).val
  let offsets  := fun i => (qidx i).val
  have hoff  := fun i => (qidx i).property
  have hmono : StrictMono offsets := by
    intro i j hij
    exact_mod_cast e.strictMono hij
  let fpost  := fun p i =>
    -(negativeConditionedPostLastExitPath c p
      (Real.toNNReal (offsets i : ℝ)))
  let forig : BrownianPath → Fin n → ℝ := fun p i =>
    -(p (Real.toNNReal (offsets i : ℝ)))
  let rpost  := fun p i =>
    postLastExitPositiveRationalEvals
      (negativeConditionedPostLastExitPath c p) (qidx i)
  let rorig  := fun p i =>
    postLastExitPositiveRationalEvals p (qidx i)
  have hB := wienerPathMeasure_isBrownian
  let  := isProbabilityMeasure_wienerPathMeasure
  let : IsFiniteMeasure wienerPathMeasure := ⟨by
    simp_all⟩
  let : SFinite wienerPathMeasure := instSFiniteOfSigmaFinite
  have hpost := negativeConditionedPostLastExit_positiveRationalProjection
    hP hB hP hν hc n offsets hoff hmono
  have horig := negativeConditionedLaw_positiveRationalProjection
    hP hν hn offsets hoff hmono
  have htime (i : Fin n) :
      Real.toNNReal (offsets i : ℝ) =
        (⟨((qidx i).val : ℚ), (qidx i).property.le⟩ : ℝ≥0) := by
    apply Subtype.ext
    simp [offsets, Real.coe_toNNReal _ (hoff i).le]
  have hfunpost : fpost = rpost := by
    funext p i
    dsimp [fpost, rpost, postLastExitPositiveRationalEvals]
    simp_all
  have hfunorig : forig = rorig := by
    funext p i
    dsimp [forig, rorig, postLastExitPositiveRationalEvals]
    simp_all
  have hpost' : P.map rpost =
      volume.withDensity (brownianEntranceFinitePDF ν n
        (brownianFirstHitElapsed n (fun i => Real.toNNReal (offsets i)))) := by
    rw [← hfunpost]
    exact hpost
  have horig' : P.map rorig =
      volume.withDensity (brownianEntranceFinitePDF ν n
        (brownianFirstHitElapsed n (fun i => Real.toNNReal (offsets i)))) := by
    rw [← hfunorig]
    exact horig
  have hproj  := hpost'.trans horig'.symm
  let A : Set (Fin n → ℝ) := {x | ∀ i, x i ∈ S (qidx i)}
  have hA : MeasurableSet A := by
    change MeasurableSet {x : Fin n → ℝ | ∀ i, x i ∈ S (qidx i)}
    rw [show {x : Fin n → ℝ | ∀ i, x i ∈ S (qidx i)} =
        ⋂ i, {x : Fin n → ℝ | x i ∈ S (qidx i)} by ext x; simp]
    exact MeasurableSet.iInter fun i =>
      (hS (qidx i)).preimage (measurable_pi_apply i)
  have hrpost : Measurable rpost := by
    apply measurable_pi_iff.mpr
    intro i
    exact ((ContinuousMap.measurable_eval _).comp
      (measurable_negativeConditionedPostLastExitPath c)).neg
  have hrorig : Measurable rorig := by
    apply measurable_pi_iff.mpr
    intro i
    exact (ContinuousMap.measurable_eval _).neg
  have hprepost : rpost ⁻¹' A =
      (negativeConditionedPostLastExitPath c) ⁻¹' postLastExitRationalEvalRect I S := by
    ext p
    simp only [Set.mem_preimage, A, rpost, postLastExitRationalEvalRect,
      Set.mem_ofPred_eq]
    constructor
    · intro hp q hq
      let i  := e.symm ⟨q, hq⟩
      have hqi : qidx i = q := congrArg Subtype.val (e.apply_symm_apply ⟨q, hq⟩)
      simpa [hqi] using hp i
    grind
  have hpreorig : rorig ⁻¹' A = postLastExitRationalEvalRect I S := by
    ext p
    simp only [Set.mem_preimage, A, rorig, postLastExitRationalEvalRect,
      Set.mem_ofPred_eq]
    constructor
    · intro hp q hq
      let i  := e.symm ⟨q, hq⟩
      have hqi : qidx i = q := congrArg Subtype.val (e.apply_symm_apply ⟨q, hq⟩)
      simpa [hqi] using hp i
    grind
  have hRect  := MeasurableSet.congr (hrorig hA) hpreorig
  calc
    (P.map (negativeConditionedPostLastExitPath c))
        (postLastExitRationalEvalRect I S) = P
          ((negativeConditionedPostLastExitPath c) ⁻¹' postLastExitRationalEvalRect I S) :=
            Measure.map_apply (measurable_negativeConditionedPostLastExitPath c) hRect
    _ = P (rpost ⁻¹' A) := by rw [← hprepost]
    _ = (P.map rpost) A := (Measure.map_apply hrpost hA).symm
    _ = (P.map rorig) A := by rw [hproj]
    _ = P (postLastExitRationalEvalRect I S) := by
          rw [Measure.map_apply hrorig hA, hpreorig]

/-- The post-last-exit recentering preserves the full conditioned path law. This proves
`DOZZ.negativeConditioned_postLastExit_law` by equality on positive rational evaluation
rectangles. -/
theorem negativeConditioned_postLastExit_law
    (ν c : ℝ) (hν : 0 < ν) (hc : 0 < c)
    (P : Measure BrownianPath) (hP : IsNegativeConditionedBrownianLaw ν P) :
    AEMeasurable (negativeConditionedPostLastExitPath c) P ∧
      P.map (negativeConditionedPostLastExitPath c) = P := by
  classical
  have hmap  :=
    aemeasurable_negativeConditionedPostLastExitPath c P
  refine ⟨hmap, ?_⟩
  let  :=
    (Measure.isProbabilityMeasure_map_iff hmap).mpr hP.2.1
  let  := hP.2.1
  have hrect : ∀ A ∈ postLastExitRationalEvalRectangles,
      (P.map (negativeConditionedPostLastExitPath c)) A = P A := by
    intro A hA
    rcases hA with ⟨I, S, hS, rfl⟩
    by_cases hI : I = ∅
    · simp [postLastExitRationalEvalRect, hI]
    · exact postLastExitRationalEvalRect_measure_eq hP hν hc I
        (Finset.nonempty_iff_ne_empty.mpr hI) S hS
  have hgen := postLastExitRationalEvalRectangles_generate_measurableSpace
  have hpi := postLastExitRationalEvalRectangles_piSystem
  have huniv :
      (P.map (negativeConditionedPostLastExitPath c)) Set.univ = P Set.univ := by
    simp
  refine MeasureTheory.ext_of_generate_finite postLastExitRationalEvalRectangles
    hgen hpi hrect huniv

end DOZZ.Proofs

end
