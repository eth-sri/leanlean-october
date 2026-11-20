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

@[fun_prop] theorem highRawDensityMass_joint_measurable {d : ℕ} {p : Ω → Covariate d → ℝ}
    (hp : Measurable (Function.uncurry p)) :
    Measurable (fun ω => highRawDensityMass (p ω)) := by
  let _ := cubeVolume_isProbability d
  exact hp.stronglyMeasurable.integral_prod_right.measurable

theorem highSampleLikelihood_joint_measurable {d : ℕ} (n : ℕ) (a V : ℝ)
    {p F : Ω → Covariate d → ℝ} (hp : Measurable (Function.uncurry p))
    (hF : Measurable (Function.uncurry F)) :
    Measurable (fun z : Ω × (IndexedSample d n) =>
      highSampleLikelihood a V (p z.1) (F z.1) z.2) := by
  fun_prop [highSampleLikelihood]

/-- Fixed reference measure for the full design/finite-response experiment. -/
def highSampleReference (d n : ℕ) : Measure (IndexedSample d n) :=
  (Measure.pi (fun _ => cubeVolume d)).prod Measure.count

instance highSampleReference_isFinite (d n : ℕ) : IsFiniteMeasure (highSampleReference d n) := by
  let _ := cubeVolume_isProbability d
  unfold highSampleReference
  infer_instance

section
variable {d : ℕ} (n : ℕ) (a V : ℝ)

/-- The joint sample kernel carries exactly the normalized raw likelihood. -/
def highSampleIndexKernel
    {p F : Ω → Covariate d → ℝ} (hp : Measurable (Function.uncurry p))
    (hF : Measurable (Function.uncurry F)) :
    Kernel Ω (IndexedSample d n) := by
  let _ := cubeVolume_isProbability d
  exact (Kernel.const Ω (highSampleReference d n)).withDensity
    (fun ω z => ENNReal.ofReal (highSampleLikelihood a V (p ω) (F ω) z))

theorem highSampleIndexKernel_apply
    (p F : Ω → Covariate d → ℝ) (hp : Measurable (Function.uncurry p))
    (hF : Measurable (Function.uncurry F)) (ω : Ω) :
    highSampleIndexKernel n a V hp hF ω =
      (highSampleReference d n).withDensity
        (fun z => ENNReal.ofReal (highSampleLikelihood a V (p ω) (F ω) z)) := by
  let _ := cubeVolume_isProbability d
  have hl : Measurable (Function.uncurry (fun ω z =>
      ENNReal.ofReal (highSampleLikelihood a V (p ω) (F ω) z))) :=
    ENNReal.measurable_ofReal.comp (highSampleLikelihood_joint_measurable n a V hp hF)
  exact Kernel.withDensity_apply _ hl ω

end

variable {d : ℕ} (n : ℕ) {a V : ℝ} {p F : Ω → Covariate d → ℝ} (hp : Measurable (Function.uncurry p))
    (hF : Measurable (Function.uncurry F)) {aRaw bRaw : ℝ} (haRaw : 0 < aRaw)
    (hraw : ∀ ω x, aRaw ≤ p ω x ∧ p ω x ≤ bRaw) (ha : a ≠ 0)
    (hq : ∀ ω x y, 0 ≤ ternaryMass a (F ω x) V y)
include ha haRaw hq hraw

/-- This family is a probability kernel on every raw state, including states
outside the original-model density interval after normalization. -/
theorem highSampleIndexKernel_markov :
    IsMarkovKernel (highSampleIndexKernel n a V hp hF) := by
  constructor
  intro ω
  have hpω : Measurable (p ω) := hp.of_uncurry_left
  have hFω : Measurable (F ω) := hF.of_uncurry_left
  let hd := normalizedDensityTernaryParameter_design_probability hpω haRaw
    (Filter.Eventually.of_forall (hraw ω))
  let _ := hd
  let _ := responseSampleIndexKernel_markov n hFω ha (hq ω)
  have hm  := haRaw.trans_le
    (highRawDensityMass_mem_Icc hpω haRaw
      (Filter.Eventually.of_forall (hraw ω))).1
  rw [highSampleIndexKernel_apply, highSampleReference, ← highSample_index_density n hpω hFω a V hd
    (fun x => haRaw.le.trans (hraw ω x).1) hm (hq ω)]
  infer_instance

/-- Exact transfer of the normalized experiment to the original real-valued sample law. -/
theorem highSampleIndexKernel_encode (ω : Ω) :
    (highSampleIndexKernel n a V hp hF ω).map (encodeDesignResponse a) =
      sampleLaw (normalizedDensityTernaryParameter (p ω)
        hF.of_uncurry_left ha (hq ω)) n := by
  have hpω : Measurable (p ω) := hp.of_uncurry_left
  have hFω : Measurable (F ω) := hF.of_uncurry_left
  have hd := normalizedDensityTernaryParameter_design_probability hpω haRaw
    (Filter.Eventually.of_forall (hraw ω))
  have hm  := haRaw.trans_le
    (highRawDensityMass_mem_Icc hpω haRaw
      (Filter.Eventually.of_forall (hraw ω))).1
  rw [highSampleIndexKernel_apply, highSampleReference, ← highSample_index_density n hpω hFω a V hd
    (fun x => haRaw.le.trans (hraw ω x).1) hm (hq ω)]
  solve_by_elim [ternaryParameter_sample_index_map]

end NearlyMinimax
