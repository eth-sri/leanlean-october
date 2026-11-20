module

public import NearlyMinimax.HighObservationLaw

@[expose] public section

/-! Jointly measurable, normalized high-prior experiments over arbitrary raw states. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace NearlyMinimax
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [MeasurableSpace Ω]

theorem highRawDensityMass_joint_measurable {d : ℕ} (p : Ω → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) :
    Measurable (fun ω => highRawDensityMass (p ω)) := by
  let _ := cubeVolume_isProbability d
  exact hp.stronglyMeasurable.integral_prod_right.measurable

section
variable {X : Type*} [MeasurableSpace X] {d n : ℕ}
    {ω : X → Ω} {z : X → TernarySample d n} {V : X → ℝ}

/-- Evaluate a jointly measurable field at a sample coordinate. -/
theorem highSample_design_measurable {p : Ω → Covariate d → ℝ}
    (hp : Measurable (Function.uncurry p)) (hω : Measurable ω) (hz : Measurable z) (i : Fin n) :
    Measurable (fun x => p (ω x) ((z x).1 i)) :=
  hp.comp (hω.prodMk ((measurable_pi_apply i).comp hz.fst))

theorem highSample_response_measurable (a : ℝ) {F : Ω → Covariate d → ℝ}
    (hF : Measurable (Function.uncurry F)) (hω : Measurable ω) (hz : Measurable z) (hV : Measurable V) (i : Fin n) :
    Measurable (fun x => ternaryMass a (F (ω x) ((z x).1 i)) (V x) ((z x).2 i)) :=
  ternaryMass_measurable a (highSample_design_measurable hF hω hz i) hV ((measurable_pi_apply i).comp hz.snd)

theorem highRawSampleLikelihood_params_measurable (a : ℝ) {p F : Ω → Covariate d → ℝ}
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F))
    (hω : Measurable ω) (hz : Measurable z) (hV : Measurable V) :
    Measurable (fun x => highRawSampleLikelihood n a (V x) (p (ω x)) (F (ω x)) (z x)) :=
  Finset.measurable_prod _ fun i _ =>
    (highSample_design_measurable hp hω hz i).mul (highSample_response_measurable a hF hω hz hV i)

end

section
variable {d : ℕ} (n : ℕ) (a V : ℝ)
    (p F : Ω → Covariate d → ℝ) (hp : Measurable (Function.uncurry p))
    (hF : Measurable (Function.uncurry F))
include hp hF

theorem highRawSampleLikelihood_joint_measurable :
    Measurable (fun z : Ω × TernarySample d n =>
      highRawSampleLikelihood n a V (p z.1) (F z.1) z.2) :=
  highRawSampleLikelihood_params_measurable a hp hF measurable_fst measurable_snd measurable_const

theorem highSampleLikelihood_joint_measurable :
    Measurable (fun z : Ω × TernarySample d n =>
      highSampleLikelihood n a V (p z.1) (F z.1) z.2) :=
  (highRawSampleLikelihood_joint_measurable n a V p F hp hF).div
    (((highRawDensityMass_joint_measurable p hp).comp measurable_fst).pow_const n)

end

/-- Fixed reference measure for the full design/finite-response experiment. -/
def highSampleReference (d n : ℕ) : Measure (TernarySample d n) :=
  (Measure.pi (fun _ : Fin n => cubeVolume d)).prod Measure.count

instance highSampleReference_isFinite (d n : ℕ) : IsFiniteMeasure (highSampleReference d n) := by
  let _ := cubeVolume_isProbability d
  unfold highSampleReference
  infer_instance

/-- The joint sample kernel carries exactly the normalized raw likelihood. -/
def highSampleIndexKernel {d : ℕ} (n : ℕ) (a V : ℝ)
    (p F : Ω → Covariate d → ℝ) (hp : Measurable (Function.uncurry p))
    (hF : Measurable (Function.uncurry F)) :
    Kernel Ω (TernarySample d n) :=
  (Kernel.const Ω (highSampleReference d n)).withDensity
    (fun ω z => ENNReal.ofReal (highSampleLikelihood n a V (p ω) (F ω) z))

section
variable {d : ℕ} (n : ℕ) (a V : ℝ)
    (p F : Ω → Covariate d → ℝ) (hp : Measurable (Function.uncurry p))
    (hF : Measurable (Function.uncurry F))

theorem highSampleIndexKernel_apply (ω : Ω) :
    highSampleIndexKernel n a V p F hp hF ω =
      (highSampleReference d n).withDensity
        (fun z => ENNReal.ofReal (highSampleLikelihood n a V (p ω) (F ω) z)) := by
  have hl : Measurable (Function.uncurry (fun ω z =>
      ENNReal.ofReal (highSampleLikelihood n a V (p ω) (F ω) z))) :=
    ENNReal.measurable_ofReal.comp (highSampleLikelihood_joint_measurable n a V p F hp hF)
  exact Kernel.withDensity_apply (Kernel.const Ω (highSampleReference d n)) hl ω

section
variable (aRaw bRaw : ℝ) (haRaw : 0 < aRaw)
    (hraw : ∀ ω x, aRaw ≤ p ω x ∧ p ω x ≤ bRaw) (ha : a ≠ 0)
    (hq : ∀ ω x y, 0 ≤ ternaryMass a (F ω x) V y)
include haRaw hraw hq

/-- The kernel's fibers are exactly the product design and conditional response experiment. -/
theorem highSampleIndexKernel_eq_compProd (ω : Ω) :
    highSampleIndexKernel n a V p F hp hF ω =
      (Measure.pi (fun _ : Fin n => highNormalizedDesignLaw (p ω))).compProd
        (responseSampleIndexKernel n a V (F ω) hF.of_uncurry_left) := by
  rw [highSampleIndexKernel_apply]
  exact (highSample_index_density n (p ω) (F ω) hp.of_uncurry_left hF.of_uncurry_left a V
    (high_normalized_design_probability (p ω) hp.of_uncurry_left aRaw bRaw haRaw (.of_forall (hraw ω)))
    (fun x => haRaw.le.trans (hraw ω x).1)
    (haRaw.trans_le (highRawDensityMass_joint_mem_Icc hp haRaw hraw ω).1)).symm

include ha

/-- This family is a probability kernel on every raw state, including states
outside the original-model density interval after normalization. -/
theorem highSampleIndexKernel_markov :
    IsMarkovKernel (highSampleIndexKernel n a V p F hp hF) := by
  refine ⟨fun ω => ?_⟩
  rw [highSampleIndexKernel_eq_compProd n a V p F hp hF aRaw bRaw haRaw hraw hq]
  let _ := high_normalized_design_probability (p ω) hp.of_uncurry_left aRaw bRaw haRaw (.of_forall (hraw ω))
  let _ := responseSampleIndexKernel_markov n a V (F ω) hF.of_uncurry_left ha (hq ω)
  infer_instance

/-- Exact transfer of the normalized experiment to the original real-valued sample law. -/
theorem highSampleIndexKernel_encode (ω : Ω) :
    (highSampleIndexKernel n a V p F hp hF ω).map (encodeDesignResponse a) =
      sampleLaw (normalizedDensityTernaryParameter (p ω) (F ω) a V
        hF.of_uncurry_left ha (hq ω)) n := by
  rw [highSampleIndexKernel_eq_compProd n a V p F hp hF aRaw bRaw haRaw hraw hq]
  exact normalizedDensityTernaryParameter_sample_index_map (p ω)
    (high_normalized_design_probability (p ω) hp.of_uncurry_left aRaw bRaw haRaw (.of_forall (hraw ω)))
    n a V (F ω) hF.of_uncurry_left ha (hq ω)

end

end

end NearlyMinimax
