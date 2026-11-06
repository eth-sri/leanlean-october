/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.Brownian.Barrier.FirstHitTilting
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The actual Gaussian first-hit lifetime density

The zero-drift lifetime tail is the half-normal survival integral. The
fundamental theorem of calculus differentiates it at every positive horizon
and integrates the resulting Gaussian first-hit density on compact intervals.

The actual lifetime measure agrees with that density on every positive
compact interval. A measure-identification lemma exhausts the positive axis
by intervals bounded away from zero. Both measures have zero mass on the
nonpositive axis, so this yields their full equality, including the boundary.

The previously proved stopped likelihood then gives the positive-drift
lifetime density as an equality of actual measures. Every nonnegative lifetime
test integrates against the density. Its total mass and genuine Lebesgue
integrability follow from this actual probability-law identification.

The explicit density is jointly measurable in drift, level and time. Its
heat-kernel and horizon-power forms are identified algebraically. Finally,
the positive conditioned entrance density equals the hitting density
multiplied by the Doob harmonic factor and divided by the positive drift.
This is the scalar entrance cancellation in the first-hit reversal proof.

These statements establish the first-hit density input.
They do not identify any multi-time killed-path law or lifetime-marked
reversed segment; those remain the probabilistic assembly steps.
-/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
namespace DOZZ.Proofs

/-- The real half-normal lifetime survival function on positive horizons. -/
noncomputable def brownianFirstHitSurvival (β t : ℝ) : ℝ :=
  Real.sqrt (2/Real.pi)*∫ x in (0 : ℝ)..(β/Real.sqrt t), Real.exp (-x^2/2)

/-- The scalar first-hit density, with its literal zero value off the positive time axis. -/
noncomputable def brownianFirstHitDensity (a β t : ℝ) : ℝ :=
  if 0 < t then β/t*(Real.sqrt (2*Real.pi*t))⁻¹*
    Real.exp (-β^2/(2*t)+a*β-a^2*t/2) else 0



/-- The first-hit density is nonnegative at every time for a nonnegative level. -/
theorem brownianFirstHitDensity_nonneg a β t (hβ : 0 ≤ β) : 0 ≤ brownianFirstHitDensity a β t := by
  classical
  by_cases ht : 0 < t
  · simp only [brownianFirstHitDensity,ite_eq_left ht]
    positivity
  · simp only [brownianFirstHitDensity,ite_eq_right ht,le_refl]






/-- Every nonnegative positive-drift first-hit lifetime test integrates against the literal hitting density. -/
theorem brownianPath_positiveDrift_firstHit_density_lintegral (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (a β : ℝ) (ha : 0 < a) (hβ : 0 < β)
    (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ p, F (firstPassageTime (driftedBrownianPath a p) β : ℝ) ∂P) =
      ∫⁻ t, ENNReal.ofReal (brownianFirstHitDensity a β t)*F t := by
  have brownianPath_zeroDrift_firstHit_real_tail t (ht : 0 < t) : (P.map (fun p => (firstPassageTime p β : ℝ))).real (Ioi t) = brownianFirstHitSurvival β t := by
    let T : ℝ≥0 := NNReal.mk t ht.le
    have hm : Measurable (fun p => (firstPassageTime p β : ℝ)) :=
      NNReal.continuous_coe.measurable.comp (measurable_firstPassageTime β)
    rw [Measure.real,Measure.map_apply hm measurableSet_Ioi, (show (fun p : BrownianPath => (firstPassageTime p β : ℝ)) ⁻¹' Ioi t = {p : BrownianPath | T < firstPassageTime p β} by ext p; rfl),brownianPath_zeroDrift_firstHit_tail_integral P hB β hβ T (show T ≠ 0 by intro he; exact ht.ne' (congrArg (fun u : ℝ≥0 => (u : ℝ)) he))]
    change (ENNReal.ofReal (Real.sqrt (2/Real.pi)*∫ x in Icc (0 : ℝ) (β/Real.sqrt t), Real.exp (-x^2/2))).toReal = _
    rw [ENNReal.toReal_ofReal (mul_nonneg (Real.sqrt_nonneg _) (integral_nonneg (fun x => (Real.exp_pos _).le)))]
    unfold brownianFirstHitSurvival
    rw [intervalIntegral.integral_of_le (by positivity : 0 ≤ β/Real.sqrt t),integral_Icc_eq_integral_Ioc]
  have continuousAt_brownianFirstHitDensity a β t (ht : 0 < t) : ContinuousAt (brownianFirstHitDensity a β) t := (show ContinuousAt (fun u => β/u*(Real.sqrt (2*Real.pi*u))⁻¹* Real.exp (-β^2/(2*u)+a*β-a^2*u/2)) t by fun_prop (disch := positivity)).congr_of_eventuallyEq (by filter_upwards [Ioi_mem_nhds ht] with u hu; change 0 < u at hu; simp only [brownianFirstHitDensity,ite_eq_left hu])
  have measurable_brownianFirstHitDensity a β : Measurable (brownianFirstHitDensity a β) := by
    classical
    unfold brownianFirstHitDensity
    apply Measurable.ite (measurableSet_lt measurable_const measurable_id) _ measurable_const
    fun_prop
  have brownianPath_positiveDrift_firstHit_density_map : P.map (fun p => (firstPassageTime (driftedBrownianPath a p) β : ℝ)) = volume.withDensity (fun t => ENNReal.ofReal (brownianFirstHitDensity a β t)) := by
    have brownianPath_zeroDrift_firstHit_density_map : P.map (fun p => (firstPassageTime p β : ℝ)) = volume.withDensity (fun t => ENNReal.ofReal (brownianFirstHitDensity 0 β t)) := by
      have brownian_measure_eq_of_positive_Ioc (μ : Measure ℝ) (ν : Measure ℝ) [IsFiniteMeasure μ] (hμ0 : μ (Iic 0) = 0) (hν0 : ν (Iic 0) = 0) (hI : ∀ s t : ℝ, 0 < s → s < t → μ (Ioc s t) = ν (Ioc s t)) : μ = ν := by
        have hδ δ (hδ : 0 < δ) : μ.restrict (Ioi δ) = ν.restrict (Ioi δ) := by
          apply Measure.ext_of_Ioc'
            (μ.restrict (Ioi δ)) (ν.restrict (Ioi δ)) (fun _ _ _ => measure_ne_top _ _)
          intro a b hab
          rw [Measure.restrict_apply measurableSet_Ioc,Measure.restrict_apply measurableSet_Ioc]
          by_cases hb : δ < b
          · have he : Ioc a b ∩ Ioi δ = Ioc (max a δ) b := by
              ext t
              simp only [mem_inter_iff,mem_Ioc,mem_Ioi,max_lt_iff]
              tauto
            rw [he]
            exact hI (max a δ) b (hδ.trans_le (le_max_right _ _)) (max_lt hab hb)
          · have he : Ioc a b ∩ Ioi δ = ∅ := by
              apply Set.eq_empty_iff_forall_notMem.mpr
              rintro t ⟨ht,hδt⟩
              exact (lt_of_lt_of_le hδt ht.2).not_ge (le_of_not_gt hb)
            rw [he,measure_empty,measure_empty]
        have hm := Measure.restrict_eq_self_of_ae_mem (by
          rw [ae_iff]
          rw [(show {a : ℝ | a ∉ Ioi 0} = Iic 0 by ext a; simp only [mem_ofPred_eq,mem_Ioi,mem_Iic,not_lt])]
          exact hμ0)
        have hn := Measure.restrict_eq_self_of_ae_mem (by
          rw [ae_iff]
          rw [(show {a : ℝ | a ∉ Ioi 0} = Iic 0 by ext a; simp only [mem_ofPred_eq,mem_Ioi,mem_Iic,not_lt])]
          exact hν0)
        rw [← hm,← hn]
        apply Measure.ext
        intro S hS
        rw [Measure.restrict_apply hS,Measure.restrict_apply hS]
        have hmono : Monotone (fun n : ℕ => S ∩ Ioi (1/((n : ℝ)+1))) := by
          intro n m hnm
          exact inter_subset_inter_right S (Ioi_subset_Ioi (one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hnm 1)))
        have hu : (⋃ n : ℕ, S ∩ Ioi (1/((n : ℝ)+1))) = S ∩ Ioi 0 := by
          ext t
          simp only [mem_iUnion,mem_inter_iff,mem_Ioi]
          constructor
          · rintro ⟨n,ht,hε⟩
            exact ⟨ht,(by positivity : 0 < 1/((n : ℝ)+1)).trans hε⟩
          · rintro ⟨ht,hpos⟩
            obtain ⟨n,hn⟩ := (tendsto_one_div_add_atTop_nhds_zero_nat.eventually (Iio_mem_nhds hpos)).exists
            exact ⟨n,ht,hn⟩
        rw [← hu,hmono.measure_iUnion,hmono.measure_iUnion]
        congr 1
        funext n
        simpa only [Measure.restrict_apply hS] using (congrArg (fun π : Measure ℝ => π S) (hδ (1/((n : ℝ)+1)) (by positivity)))
      have brownianPath_zeroDrift_firstHit_density_Ioc s t (hs : 0 < s) (hst : s < t) : P.map (fun p => (firstPassageTime p β : ℝ)) (Ioc s t) = volume.withDensity (fun u => ENNReal.ofReal (brownianFirstHitDensity 0 β u)) (Ioc s t) := by
        have integral_brownianFirstHitDensity_zero (hst : s ≤ t) : (∫ u in Ioc s t, brownianFirstHitDensity 0 β u) = brownianFirstHitSurvival β s-brownianFirstHitSurvival β t := by
          have hasDerivAt_brownianFirstHitSurvival t (ht : 0 < t) : HasDerivAt (brownianFirstHitSurvival β) (-brownianFirstHitDensity 0 β t) t := by
            have hs0 : Real.sqrt t ≠ 0 := by positivity
            have hi := (((show Continuous (fun x => Real.exp (-x^2/2)) by fun_prop).integral_hasStrictDerivAt (0 : ℝ) (β/Real.sqrt t)).hasDerivAt.comp t ((hasDerivAt_const t β).div (Real.hasDerivAt_sqrt ht.ne') hs0)).const_mul
              (Real.sqrt (2/Real.pi))
            simp only [Function.comp_def,Pi.div_def] at hi
            change HasDerivAt (fun u => Real.sqrt (2/Real.pi)*∫ x in (0 : ℝ)..(β/Real.sqrt u), Real.exp (-x^2/2)) _ t
            convert hi using 1
            simp only [brownianFirstHitDensity,ite_eq_left ht,zero_mul,zero_pow (by norm_num : 2 ≠ 0),zero_div,add_zero,sub_zero]
            rw [(show -(β/Real.sqrt t)^2/2 = -β^2/(2*t) by rw [(show (β/Real.sqrt t)^2 = β^2/t by rw [div_pow,Real.sq_sqrt ht.le])]; field_simp),Real.sqrt_mul (by positivity : 0 ≤ 2*Real.pi),← brownian_gaussian_normalization]
            field_simp [hs0,ht.ne']
            rw [Real.sq_sqrt ht.le]
            ring_nf
          have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (by intro u hu; simpa only [Pi.neg_def,Pi.neg_apply,neg_neg] using (hasDerivAt_brownianFirstHitSurvival u (hs.trans_le (show u ∈ Icc s t by simpa only [uIcc_of_le hst] using hu).1)).neg) ((show ContinuousOn (brownianFirstHitDensity 0 β) (Icc s t) by intro u hu; exact (continuousAt_brownianFirstHitDensity 0 β u (hs.trans_le hu.1)).continuousWithinAt).intervalIntegrable_of_Icc hst)
          rw [intervalIntegral.integral_of_le hst] at he
          exact he.trans (by ring_nf)
        let _ := (hB.hasLaw_eval 0).isProbabilityMeasure
        let μ := P.map (fun p => (firstPassageTime p β : ℝ))
        calc
          _ = ENNReal.ofReal (μ.real (Ioc s t)) := (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
          _ = ENNReal.ofReal (∫ u in Ioc s t, brownianFirstHitDensity 0 β u) := by
            rw [(show μ.real (Ioc s t) = brownianFirstHitSurvival β s-brownianFirstHitSurvival β t by rw [← Ioi_sdiff_Ioi,measureReal_sdiff (Ioi_subset_Ioi hst.le) measurableSet_Ioi (measure_ne_top _ _), brownianPath_zeroDrift_firstHit_real_tail s hs, brownianPath_zeroDrift_firstHit_real_tail t (hs.trans hst)]),integral_brownianFirstHitDensity_zero hst.le]
          _ = _ := by
            rw [withDensity_apply _ measurableSet_Ioc,ofReal_integral_eq_lintegral_ofReal (((show ContinuousOn (brownianFirstHitDensity 0 β) (Icc s t) by intro u hu; exact (continuousAt_brownianFirstHitDensity 0 β u (hs.trans_le hu.1)).continuousWithinAt).integrableOn_Icc).mono_set Ioc_subset_Icc_self)
              (ae_of_all _ (fun u => brownianFirstHitDensity_nonneg 0 β u hβ.le))]
      let _ := (hB.hasLaw_eval 0).isProbabilityMeasure
      have hm : Measurable (fun p => (firstPassageTime p β : ℝ)) :=
        NNReal.continuous_coe.measurable.comp (measurable_firstPassageTime β)
      apply brownian_measure_eq_of_positive_Ioc
      · rw [Measure.map_apply hm measurableSet_Iic]
        apply measure_eq_zero_iff_ae_notMem.mpr
        filter_upwards [brownianPath_zeroDrift_firstHit_ae P hB β hβ] with p hp
        change ¬(firstPassageTime p β : ℝ) ≤ 0
        exact not_le.mpr (NNReal.coe_pos.mpr hp.1)
      · rw [withDensity_apply _ measurableSet_Iic]
        apply (lintegral_eq_zero_iff (measurable_brownianFirstHitDensity 0 β).ennreal_ofReal).mpr
        filter_upwards [ae_restrict_mem measurableSet_Iic] with t ht
        simp only [brownianFirstHitDensity,ite_eq_right (not_lt.mpr ht),ENNReal.ofReal_zero,Pi.zero_apply]
      · intro s t hs hst
        exact brownianPath_zeroDrift_firstHit_density_Ioc s t hs hst
    have brownianFirstHitDensity_tilt a β t : brownianFirstHitDensity a β t = brownianFirstHitDensity 0 β t*Real.exp (a*β-a^2*t/2) := by
      classical
      by_cases ht : 0 < t
      · have he : -β^2/(2*t)+a*β-a^2*t/2 = -β^2/(2*t)+(a*β-a^2*t/2) := by ring_nf
        simp only [brownianFirstHitDensity,ite_eq_left ht,zero_mul,zero_pow (by norm_num : 2 ≠ 0),zero_div,add_zero,sub_zero,
          he,Real.exp_add,mul_assoc]
      · simp only [brownianFirstHitDensity,ite_eq_right ht,zero_mul]
    let σ := fun p => firstPassageTime (driftedBrownianPath a p) β
    let τ := fun p => firstPassageTime p β
    let w : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (Real.exp (a*β-a^2*t/2))
    have hmσ : Measurable σ := (measurable_firstPassageTime β).comp
      (continuous_driftedBrownianPath.measurable.comp (measurable_const.prodMk measurable_id))
    have hmτ : Measurable τ := measurable_firstPassageTime β
    have hc : Measurable (fun t : ℝ≥0 => (t : ℝ)) := NNReal.continuous_coe.measurable
    have hw : Measurable w := by dsimp [w]; fun_prop
    rw [← (show (P.map σ).map (fun t : ℝ≥0 => (t : ℝ)) = P.map (fun p => (σ p : ℝ)) by rw [Measure.map_map hc hmσ]; simp only [Function.comp_def]),brownianPath_firstHit_lifetime_map_tilt P hB a β ha hβ]
    rw [(show (fun t : ℝ≥0 => brownianGaussianLikelihood a t β) = fun t : ℝ≥0 => w (t : ℝ) by funext t; rfl),brownian_map_withDensity_comp (P.map τ) _ hc w hw,(show (P.map τ).map (fun t : ℝ≥0 => (t : ℝ)) = P.map (fun p => (τ p : ℝ)) by rw [Measure.map_map hc hmτ]; simp only [Function.comp_def]),
      brownianPath_zeroDrift_firstHit_density_map,
      ← withDensity_mul volume (measurable_brownianFirstHitDensity 0 β).ennreal_ofReal hw]
    congr 1
    funext t
    change ENNReal.ofReal (brownianFirstHitDensity 0 β t)*ENNReal.ofReal (Real.exp (a*β-a^2*t/2)) = _
    rw [← ENNReal.ofReal_mul (brownianFirstHitDensity_nonneg 0 β t hβ.le),← brownianFirstHitDensity_tilt]
  calc
    _ = ∫⁻ t, F t ∂P.map (fun p => (firstPassageTime (driftedBrownianPath a p) β : ℝ)) :=
      (lintegral_map hF (NNReal.continuous_coe.measurable.comp ((measurable_firstPassageTime β).comp (continuous_driftedBrownianPath.measurable.comp (measurable_const.prodMk measurable_id))))).symm
    _ = ∫⁻ t, F t ∂volume.withDensity (fun t => ENNReal.ofReal (brownianFirstHitDensity a β t)) := by
      rw [brownianPath_positiveDrift_firstHit_density_map]
    _ = _ := lintegral_withDensity_eq_lintegral_mul volume (measurable_brownianFirstHitDensity a β).ennreal_ofReal hF
/-- The hitting density has the literal heat-kernel form. -/
theorem brownianFirstHitDensity_heat a β t (ht : 0 < t) :
    brownianFirstHitDensity a β t = β/t*brownianHeatDensity t β*Real.exp (a*β-a^2*t/2) := by
  simp only [brownianFirstHitDensity,brownianHeatDensity,ite_eq_left ht]
  rw [(show -β^2/(2*t)+a*β-a^2*t/2 = -β^2/(2*t)+(a*β-a^2*t/2) by ring_nf),Real.exp_add]
  ring_nf




/-- The entrance density equals the hitting density times its Doob harmonic factor. -/
theorem conditionedPositiveEntranceDensity_eq_firstHit a t β
    (ha : 0 < a) (ht : 0 < t) (hβ : 0 < β) :
    conditionedPositiveEntranceDensity a t β = conditionedH a β*brownianFirstHitDensity a β t/a := by
  have conditionedH_mul_exp_firstHit : conditionedH a β*Real.exp (a*β) = 2*Real.sinh (a*β) := by
    rw [conditionedH,ite_eq_right ha.ne',Real.sinh_eq,sub_mul,one_mul]
    have he : Real.exp (-2*a*β)*Real.exp (a*β) = Real.exp (-(a*β)) := by
      rw [← Real.exp_add]
      congr 1
      ring_nf
    rw [he]
    ring_nf
  rw [conditionedPositiveEntranceDensity,ite_eq_left (show 0 ≤ a ∧ 0 < t ∧ 0 < β from ⟨ha.le,ht,hβ⟩),
    ite_eq_right ha.ne',(show brownianFirstHitDensity a β t = Real.sqrt (2/Real.pi)*t^(-(3/2 : ℝ))*β/2* Real.exp (-β^2/(2*t)+a*β-a^2*t/2) by rw [brownianFirstHitDensity,ite_eq_left ht, (show β/t*(Real.sqrt (2*Real.pi*t))⁻¹ = β*((Real.sqrt (2*Real.pi*t))⁻¹/t) by ring_nf),(show (Real.sqrt (2*Real.pi*t))⁻¹/t = Real.sqrt (2/Real.pi)/2*t^(-(3/2 : ℝ)) by rw [Real.rpow_neg ht.le,(show t^(3/2 : ℝ) = t*Real.sqrt t by rw [show (3/2 : ℝ) = 1+1/2 by norm_num,Real.rpow_add ht,Real.rpow_one,← Real.sqrt_eq_rpow]),Real.sqrt_mul (by positivity : 0 ≤ 2*Real.pi),← brownian_gaussian_normalization]; field_simp [(show Real.sqrt (2*Real.pi) ≠ 0 by positivity),(show Real.sqrt t ≠ 0 by positivity),ht.ne'])]; ring_nf)]
  rw [(show -β^2/(2*t)+a*β-a^2*t/2 = (-β^2/(2*t)-a^2*t/2)+a*β by ring_nf),Real.exp_add]
  symm
  calc
    _ = (conditionedH a β*Real.exp (a*β))*Real.sqrt (2/Real.pi)*t^(-(3/2 : ℝ))*β/2*
        Real.exp (-β^2/(2*t)-a^2*t/2)/a := by ring_nf
    _ = _ := by rw [conditionedH_mul_exp_firstHit]; ring_nf
/-- The hitting density is jointly measurable in drift, level and time. -/
theorem measurable_brownianFirstHitDensity_joint :
    Measurable (fun z : ℝ × ℝ × ℝ => brownianFirstHitDensity z.1 z.2.1 z.2.2) := by
  classical
  unfold brownianFirstHitDensity
  apply Measurable.ite (measurableSet_lt measurable_const (measurable_snd.comp measurable_snd)) _ measurable_const
  fun_prop

end DOZZ.Proofs
