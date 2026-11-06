module
public import NearlyMinimax.HighObservationLaw
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace NearlyMinimax
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

variable {d : ℕ}
section
section
variable {Ω : Type*} [MeasurableSpace Ω]
theorem highRawDensityMass_joint_measurable  (p : Ω → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) :
    Measurable (fun ω => highRawDensityMass (p ω)) := by
  let _ := cubeVolume_isProbability d
  exact hp.stronglyMeasurable.integral_prod_right.measurable
theorem ternaryMass_joint_measurable  [MeasurableSpace α]
    (a V F) (hF : Measurable F) :
    Measurable (fun z : α × Fin 3 => ternaryMass a (F z.1) V z.2) := by
  exact measurable_from_prod_countable_left fun y =>
    ternaryMass_measurable_comp a V F hF y
theorem highSampleLikelihood_joint_measurable  (n a V p F) (hp : Measurable (Function.uncurry p))
    (hF : Measurable (Function.uncurry F)) :
    Measurable (fun z : Ω × ((Fin n → Covariate d) × (Fin n → Fin 3)) =>
      highSampleLikelihood n a V (p z.1) (F z.1) z.2) := by
  have hx (i : Fin n) : Measurable
      (fun z : Ω × ((Fin n → Covariate d) × (Fin n → Fin 3)) => (z.1, z.2.1 i)) :=
    measurable_fst.prodMk ((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd))
  have hy (i : Fin n) : Measurable
      (fun z : Ω × ((Fin n → Covariate d) × (Fin n → Fin 3)) => z.2.2 i) :=
    (measurable_pi_apply i).comp (measurable_snd.comp measurable_snd)
  exact ((Finset.measurable_prod _ (fun i _ => hp.comp (hx i))).div
    (((highRawDensityMass_joint_measurable p hp).comp measurable_fst).pow_const n)).mul
    (Finset.measurable_prod _ (fun i _ =>
      (ternaryMass_joint_measurable a V (Function.uncurry F) hF).comp
        ((hx i).prodMk (hy i))))
def highSampleReference (d n ) : Measure ((Fin n → Covariate d) × (Fin n → Fin 3)) :=
  (Measure.pi (fun _ => cubeVolume d)).prod Measure.count
instance highSampleReference_isFinite (d n : ℕ) : IsFiniteMeasure (highSampleReference d n) := by
  let _ := cubeVolume_isProbability d
  unfold highSampleReference
  infer_instance
def highSampleIndexKernel  (n ) (a V : ℝ)
    (p F : Ω → Covariate d → ℝ) (hp : Measurable (Function.uncurry p))
    (hF : Measurable (Function.uncurry F)) :
    Kernel Ω ((Fin n → Covariate d) × (Fin n → Fin 3)) := by
  exact (Kernel.const Ω (highSampleReference d n)).withDensity
    (fun ω z => ENNReal.ofReal (highSampleLikelihood n a V (p ω) (F ω) z))
theorem highSampleIndexKernel_apply  (n a V p F hp)
    (hF : Measurable (Function.uncurry F)) (ω : Ω) :
    highSampleIndexKernel n a V p F hp hF ω =
      (highSampleReference d n).withDensity
        (fun z => ENNReal.ofReal (highSampleLikelihood n a V (p ω) (F ω) z)) := by
  let _ := cubeVolume_isProbability d
  have hl : Measurable (Function.uncurry (fun ω z =>
      ENNReal.ofReal (highSampleLikelihood n a V (p ω) (F ω) z))) :=
    ENNReal.measurable_ofReal.comp (highSampleLikelihood_joint_measurable n a V p F hp hF)
  change ((Kernel.const Ω (highSampleReference d n)).withDensity
    (fun ω z => ENNReal.ofReal (highSampleLikelihood n a V (p ω) (F ω) z))) ω = _
  exact Kernel.withDensity_apply _ hl ω
theorem highSampleIndexKernel_markov  (n : ℕ) (a V : ℝ)
    (p F : Ω → Covariate d → ℝ) (hp : Measurable (Function.uncurry p))
    (hF : Measurable (Function.uncurry F)) (aRaw bRaw : ℝ) (haRaw : 0 < aRaw)
    (hraw : ∀ ω x, aRaw ≤ p ω x ∧ p ω x ≤ bRaw) (ha : a ≠ 0)
    (hq : ∀ ω x y, 0 ≤ ternaryMass a (F ω x) V y) :
    IsMarkovKernel (highSampleIndexKernel n a V p F hp hF) := by
  constructor
  intro ω
  have hpω : Measurable (p ω) := hp.of_uncurry_left
  have hFω : Measurable (F ω) := hF.of_uncurry_left
  let hd := normalizedDensityTernaryParameter_design_probability (p ω) hpω aRaw bRaw haRaw
    (Filter.Eventually.of_forall (hraw ω))
  let _ := hd
  let _ := responseSampleIndexKernel_markov n a V (F ω) hFω ha (hq ω)
  have hm : 0 < highRawDensityMass (p ω) := haRaw.trans_le
    (highRawDensityMass_mem_Icc (p ω) hpω aRaw bRaw haRaw
      (Filter.Eventually.of_forall (hraw ω))).1
  rw [highSampleIndexKernel_apply, highSampleReference, ← highSample_index_density n (p ω) (F ω) hpω hFω a V hd
    (fun x => haRaw.le.trans (hraw ω x).1) hm (hq ω)]
  infer_instance
end
variable {Ω : Type*} [MeasurableSpace Ω]
def highRealSampleKernel  (n ) (a V : ℝ)
    (p F : Ω → Covariate d → ℝ) (hp : Measurable (Function.uncurry p))
    (hF : Measurable (Function.uncurry F)) : Kernel Ω (Fin n → Observation d) :=
  (highSampleIndexKernel n a V p F hp hF).map (encodeDesignResponse a)
theorem highRealSampleKernel_apply  (n a V)
    (p F : Ω → Covariate d → ℝ) (hp : Measurable (Function.uncurry p))
    (hF : Measurable (Function.uncurry F)) (ω : Ω) :
    highRealSampleKernel n a V p F hp hF ω =
      (highSampleIndexKernel n a V p F hp hF ω).map (encodeDesignResponse a) :=
  Kernel.map_apply _ (encodeDesignResponse_measurable a) ω
theorem highRealSampleKernel_markov  (n a V)
    (p F : Ω → Covariate d → ℝ) (hp : Measurable (Function.uncurry p))
    (hF : Measurable (Function.uncurry F)) (aRaw bRaw : ℝ) (haRaw : 0 < aRaw)
    (hraw : ∀ ω x, aRaw ≤ p ω x ∧ p ω x ≤ bRaw) (ha : a ≠ 0)
    (hq : ∀ ω x y, 0 ≤ ternaryMass a (F ω x) V y) :
    IsMarkovKernel (highRealSampleKernel n a V p F hp hF) := by
  let _ := highSampleIndexKernel_markov n a V p F hp hF aRaw bRaw haRaw hraw ha hq
  exact Kernel.IsMarkovKernel.map _ (encodeDesignResponse_measurable a)
theorem highRealSampleKernel_eq_sampleLaw  (n : ℕ) (a V : ℝ)
    (p F : Ω → Covariate d → ℝ) (hp : Measurable (Function.uncurry p))
    (hF : Measurable (Function.uncurry F)) (aRaw bRaw : ℝ) (haRaw : 0 < aRaw)
    (hraw : ∀ ω x, aRaw ≤ p ω x ∧ p ω x ≤ bRaw) (ha : a ≠ 0)
    (hq : ∀ ω x y, 0 ≤ ternaryMass a (F ω x) V y) (ω : Ω) :
    highRealSampleKernel n a V p F hp hF ω =
      sampleLaw (normalizedDensityTernaryParameter (p ω) (F ω) a V hF.of_uncurry_left ha (hq ω)) n := by
  rw [highRealSampleKernel_apply]
  have hpω : Measurable (p ω) := hp.of_uncurry_left
  have hFω : Measurable (F ω) := hF.of_uncurry_left
  have hd := normalizedDensityTernaryParameter_design_probability (p ω) hpω aRaw bRaw haRaw
    (Filter.Eventually.of_forall (hraw ω))
  have hm : 0 < highRawDensityMass (p ω) := haRaw.trans_le
    (highRawDensityMass_mem_Icc (p ω) hpω aRaw bRaw haRaw
      (Filter.Eventually.of_forall (hraw ω))).1
  rw [highSampleIndexKernel_apply, highSampleReference, ← highSample_index_density n (p ω) (F ω) hpω hFω a V hd
    (fun x => haRaw.le.trans (hraw ω x).1) hm (hq ω)]
  let _ := cubeVolume_isProbability d
  let _ := hd
  let _ := responseIndexKernel_markov a V (F ω) hFω ha (hq ω)
  let _ := responseSampleIndexKernel_markov n a V (F ω) hFω ha (hq ω)
  have h_normalizedDensityTernaryParameter_observation_index_map : (((cubeVolume d).withDensity (fun x => ENNReal.ofReal (highNormalizedDensity (p ω) x))).compProd (responseIndexKernel a V (F ω) hFω)).map
      (fun z : Covariate d × Fin 3 => (z.1, ternaryValue a z.2)) =
      observationLaw (normalizedDensityTernaryParameter (p ω) (F ω) a V hFω ha (hq ω)) := by
    let _ := cubeVolume_isProbability d
    let _ := hd
    let _ := responseIndexKernel_markov a V (F ω) hFω ha (hq ω)
    let _ := ternaryErrorKernel_markov a V (F ω) hFω ha (hq ω)
    have hencode : Measurable (fun z : Covariate d × Fin 3 => (z.1, ternaryValue a z.2)) :=
      measurable_fst.prodMk ((measurable_of_countable _).comp measurable_snd)
    have hreal : Measurable (fun z : Covariate d × ℝ => (z.1, (F ω) z.1 + z.2)) :=
      measurable_fst.prodMk ((hFω.comp measurable_fst).add measurable_snd)
    ext s hs
    rw [Measure.map_apply hencode hs, observationLaw]
    change _ = (((designLaw (normalizedDensityTernaryParameter (p ω) (F ω) a V hFω ha (hq ω))).compProd
      (ternaryErrorKernel a V (F ω) hFω)).map (fun z : Covariate d × ℝ => (z.1, (F ω) z.1 + z.2))) s
    rw [Measure.map_apply hreal hs]
    change _ = (((cubeVolume d).withDensity (fun x => ENNReal.ofReal (highNormalizedDensity (p ω) x))).compProd (ternaryErrorKernel a V (F ω) hFω)) ((fun z : Covariate d × ℝ => (z.1, (F ω) z.1 + z.2)) ⁻¹' s)
    rw [Measure.compProd_apply (hs.preimage hencode), Measure.compProd_apply (hs.preimage hreal)]
    apply lintegral_congr
    intro x
    have hSreal : MeasurableSet {u : ℝ | (x, (F ω) x + u) ∈ s} :=
      hs.preimage (measurable_const.prodMk (measurable_const.add measurable_id))
    have hSindex : MeasurableSet {y : Fin 3 | (x, ternaryValue a y) ∈ s} :=
      hs.preimage (measurable_const.prodMk (measurable_of_countable _))
    simp only [responseIndexKernel_apply, ternaryErrorKernel_apply, Measure.finsetSum_apply,
      Measure.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro y _
    congr 1
    change Measure.dirac y {y | (x, ternaryValue a y) ∈ s} =
      Measure.dirac (ternaryValue a y - (F ω) x) {u | (x, (F ω) x + u) ∈ s}
    rw [Measure.dirac_apply' _ hSindex, Measure.dirac_apply' _ hSreal]
    have he : (F ω) x + ternaryValue a y - (F ω) x = ternaryValue a y := by ring
    by_cases h : (x, ternaryValue a y) ∈ s <;> simp [Set.indicator, h]
  have hsingle : MeasurePreserving
      (fun z : Covariate d × Fin 3 => (z.1, ternaryValue a z.2))
      (((cubeVolume d).withDensity (fun x => ENNReal.ofReal (highNormalizedDensity (p ω) x))).compProd (responseIndexKernel a V (F ω) hFω))
      (observationLaw (normalizedDensityTernaryParameter (p ω) (F ω) a V hFω ha (hq ω))) :=
    ⟨measurable_fst.prodMk ((measurable_of_countable _).comp measurable_snd),
      h_normalizedDensityTernaryParameter_observation_index_map⟩
  let _ : IsProbabilityMeasure (observationLaw (normalizedDensityTernaryParameter (p ω) (F ω) a V hFω ha (hq ω))) := by
    rw [← hsingle.map_eq]
    infer_instance
  have h := (measurePreserving_pi _ _ (fun _ : Fin n => hsingle)).map_eq
  rw [← responseSampleIndexKernel_joint_map ((cubeVolume d).withDensity (fun x => ENNReal.ofReal (highNormalizedDensity (p ω) x))) n a V (F ω) hFω ha (hq ω),
    Measure.map_map] at h
  · exact h
  · apply Measurable.of_eval
    intro i
    exact (measurable_fst.prodMk ((measurable_of_countable _).comp measurable_snd)).comp
      (measurable_pi_apply i)
  · fun_prop
end
variable {Ω : Type*} [MeasurableSpace Ω]
def massPowerNormalizer (μ : Measure Ω) (m : Ω → ℝ) (n : ℕ) : ℝ :=
  ∫ ω, m ω ^ n ∂μ
def massPowerTilt (μ : Measure Ω) (m : Ω → ℝ) (n : ℕ) : Measure Ω :=
  μ.withDensity (fun ω => ENNReal.ofReal (m ω ^ n / massPowerNormalizer μ m n))
theorem massPower_integrable (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m : Ω → ℝ) (hm : Measurable m) (n : ℕ) (a b : ℝ) (ha : 0 < a)
    (hbound : ∀ ω, a ≤ m ω ∧ m ω ≤ b) : Integrable (fun ω => m ω ^ n) μ := by
  apply (integrable_const (b ^ n)).mono' (hm.pow_const n).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro ω
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (ha.le.trans (hbound ω).1) n)]
  exact pow_le_pow_left₀ (ha.le.trans (hbound ω).1) (hbound ω).2 n
theorem massPowerNormalizer_mem_Icc (μ ) [IsProbabilityMeasure μ]
    (m : Ω → ℝ) (hm : Measurable m) (n : ℕ) (a b : ℝ) (ha : 0 < a)
    (hbound : ∀ ω, a ≤ m ω ∧ m ω ≤ b) :
    massPowerNormalizer μ m n ∈ Icc (a ^ n) (b ^ n) := by
  have hi := massPower_integrable μ m hm n a b ha hbound
  constructor
  · simpa [massPowerNormalizer] using integral_mono_ae (integrable_const (a ^ n)) hi
      (Filter.Eventually.of_forall (fun ω => pow_le_pow_left₀ ha.le (hbound ω).1 n))
  · simpa [massPowerNormalizer] using integral_mono_ae hi (integrable_const (b ^ n))
      (Filter.Eventually.of_forall (fun ω =>
        pow_le_pow_left₀ (ha.le.trans (hbound ω).1) (hbound ω).2 n))
theorem massPowerNormalizer_pos (μ ) [IsProbabilityMeasure μ]
    (m : Ω → ℝ) (hm : Measurable m) (n : ℕ) (a b : ℝ) (ha : 0 < a)
    (hbound : ∀ ω, a ≤ m ω ∧ m ω ≤ b) : 0 < massPowerNormalizer μ m n :=
  (pow_pos ha n).trans_le (massPowerNormalizer_mem_Icc μ m hm n a b ha hbound).1
theorem massPowerTilt_isProbability (μ ) [IsProbabilityMeasure μ]
    (m : Ω → ℝ) (hm : Measurable m) (n : ℕ) (a b : ℝ) (ha : 0 < a)
    (hbound : ∀ ω, a ≤ m ω ∧ m ω ≤ b) : IsProbabilityMeasure (massPowerTilt μ m n) := by
  have hG := massPowerNormalizer_pos μ m hm n a b ha hbound
  constructor
  rw [massPowerTilt, withDensity_apply _ MeasurableSet.univ]
  simp only [Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal ((massPower_integrable μ m hm n a b ha hbound).div_const _)
    (Filter.Eventually.of_forall (fun ω =>
      div_nonneg (pow_nonneg (ha.le.trans (hbound ω).1) n) hG.le)), integral_div]
  change ENNReal.ofReal (massPowerNormalizer μ m n / massPowerNormalizer μ m n) = 1
  rw [div_self hG.ne', ENNReal.ofReal_one]
theorem massPowerNormalizer_eq_of_massLaw (μ ν : Measure Ω) (m )
    (hm : Measurable m) (n ) (hlaw : μ.map m = ν.map m) :
    massPowerNormalizer μ m n = massPowerNormalizer ν m n := by
  have hμ := integral_map_of_stronglyMeasurable (μ := μ) hm
    ((measurable_id.pow_const n : Measurable (fun x => x ^ n)).stronglyMeasurable)
  have hν := integral_map_of_stronglyMeasurable (μ := ν) hm
    ((measurable_id.pow_const n : Measurable (fun x => x ^ n)).stronglyMeasurable)
  rw [hlaw] at hμ
  exact hμ.symm.trans hν
theorem map_withDensity_pullback  [MeasurableSpace Α]
    (μ : Measure Ω) (m ) (hm : Measurable m)
    (f : Α → ℝ≥0∞) (hf : Measurable f) :
    (μ.withDensity (fun ω => f (m ω))).map m = (μ.map m).withDensity f := by
  apply Measure.ext_of_lintegral
  intro G hG
  have hfm : Measurable (fun ω => f (m ω)) := hf.comp hm
  have hGm : Measurable (fun ω => G (m ω)) := hG.comp hm
  rw [lintegral_map hG hm,
    lintegral_withDensity_eq_lintegral_mul _ hfm hGm,
    lintegral_withDensity_eq_lintegral_mul _ hf hG,
    lintegral_map (hf.mul hG) hm]
  rfl
def highRawSampleLikelihood  (n ) (a V : ℝ)
    (p F : Covariate d → ℝ) (z : (Fin n → Covariate d) × (Fin n → Fin 3)) : ℝ :=
  ∏ i, p (z.1 i) * ternaryMass a (F (z.1 i)) V (z.2 i)
theorem highRawSampleLikelihood_joint_measurable  (n a V p F) (hp : Measurable (Function.uncurry p))
    (hF : Measurable (Function.uncurry F)) :
    Measurable (fun z : Ω × ((Fin n → Covariate d) × (Fin n → Fin 3)) =>
      highRawSampleLikelihood n a V (p z.1) (F z.1) z.2) := by
  have hx (i : Fin n) : Measurable
      (fun z : Ω × ((Fin n → Covariate d) × (Fin n → Fin 3)) => (z.1, z.2.1 i)) :=
    measurable_fst.prodMk ((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd))
  have hy (i : Fin n) : Measurable
      (fun z : Ω × ((Fin n → Covariate d) × (Fin n → Fin 3)) => z.2.2 i) :=
    (measurable_pi_apply i).comp (measurable_snd.comp measurable_snd)
  exact Finset.measurable_prod _ (fun i _ => (hp.comp (hx i)).mul
    ((ternaryMass_joint_measurable a V (Function.uncurry F) hF).comp ((hx i).prodMk (hy i))))
theorem highSampleLikelihood_mass_cancellation  (n a V)
    (p F : Covariate d → ℝ) (hm : highRawDensityMass p ≠ 0)
    (z : (Fin n → Covariate d) × (Fin n → Fin 3)) :
    highRawDensityMass p ^ n * highSampleLikelihood n a V p F z =
      highRawSampleLikelihood n a V p F z := by
  simp only [highSampleLikelihood, highRawSampleLikelihood, Finset.prod_mul_distrib]
  field_simp
instance highSampleIndexKernel_isSFinite {d : ℕ} (n : ℕ) (a V : ℝ)
    (p F : Ω → Covariate d → ℝ) (hp : Measurable (Function.uncurry p))
    (hF : Measurable (Function.uncurry F)) : IsSFiniteKernel (highSampleIndexKernel n a V p F hp hF) := by
  change IsSFiniteKernel ((Kernel.const Ω (highSampleReference d n)).withDensity
    (fun ω z => ENNReal.ofReal (highSampleLikelihood n a V (p ω) (F ω) z)))
  exact Kernel.isSFiniteKernel_withDensity_of_isFiniteKernel _ (fun _ _ => ENNReal.ofReal_ne_top)
theorem massPowerTilt_highSample_compProd  (ν : Measure Ω) [IsProbabilityMeasure ν]
    (n a V p F)
    (hp : Measurable (Function.uncurry p)) (hF )
    (aRaw bRaw : ℝ) (haRaw : 0 < aRaw)
    (hraw : ∀ ω x, aRaw ≤ p ω x ∧ p ω x ≤ bRaw) :
    (massPowerTilt ν (fun ω => highRawDensityMass (p ω)) n).compProd
      (highSampleIndexKernel n a V p F hp hF) =
      (ν.prod (highSampleReference d n)).withDensity (fun z =>
        ENNReal.ofReal (highRawSampleLikelihood n a V (p z.1) (F z.1) z.2 /
          massPowerNormalizer ν (fun ω => highRawDensityMass (p ω)) n)) := by
  let m : Ω → ℝ := fun ω => highRawDensityMass (p ω)
  have hm  := highRawDensityMass_joint_measurable p hp
  have hbound (ω : Ω) : aRaw ≤ m ω ∧ m ω ≤ bRaw :=
    highRawDensityMass_mem_Icc (p ω) hp.of_uncurry_left aRaw bRaw haRaw
      (Filter.Eventually.of_forall (hraw ω))
  let _ := Kernel.isSFiniteKernel_withDensity_of_isFiniteKernel
    (f := fun ω z => ENNReal.ofReal (highSampleLikelihood n a V (p ω) (F ω) z))
    (Kernel.const Ω (highSampleReference d n)) (fun _ _ => ENNReal.ofReal_ne_top)
  change (ν.withDensity (fun ω => ENNReal.ofReal (m ω ^ n / massPowerNormalizer ν m n))).compProd
    ((Kernel.const Ω (highSampleReference d n)).withDensity
      (fun ω z => ENNReal.ofReal (highSampleLikelihood n a V (p ω) (F ω) z))) = _
  rw [Measure.withDensity_compProd_withDensity
    (f := fun ω => ENNReal.ofReal (m ω ^ n / massPowerNormalizer ν m n))
    (g := fun ω z => ENNReal.ofReal (highSampleLikelihood n a V (p ω) (F ω) z)) (ENNReal.measurable_ofReal.comp ((hm.pow_const n).div_const _)) (ENNReal.measurable_ofReal.comp (highSampleLikelihood_joint_measurable n a V p F hp hF)),
    Measure.compProd_const]
  congr 1
  funext z
  rw [← ENNReal.ofReal_mul (div_nonneg (pow_nonneg (haRaw.le.trans (hbound z.1).1) n) (massPowerNormalizer_pos ν m hm n aRaw bRaw haRaw hbound).le)]
  congr 1
  calc
    (m z.1 ^ n / massPowerNormalizer ν m n) * highSampleLikelihood n a V (p z.1) (F z.1) z.2 =
        m z.1 ^ n * highSampleLikelihood n a V (p z.1) (F z.1) z.2 / massPowerNormalizer ν m n := by ring
    _ = _ := by rw [highSampleLikelihood_mass_cancellation n a V (p z.1) (F z.1)
      (haRaw.trans_le (hbound z.1).1).ne']
end NearlyMinimax
