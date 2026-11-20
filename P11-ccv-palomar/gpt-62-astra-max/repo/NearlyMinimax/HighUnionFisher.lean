module

public import NearlyMinimax.HighUnionScorePrimitives
public import NearlyMinimax.HighFrameDesignEnergy


@[expose] public section

/-! Genuine canonical-source Fisher integrability and spatial factorial
energy from actual local numerator envelopes under the original sample law. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency true
attribute [local instance] Classical.propDecidable
attribute [local irreducible] highUnionSourceDensity highUnionSourceState historyMarkedAppend
  highUnionSourceRegression highHistoryLikelihoodScore highSampleIndexKernel

variable {d k D : ℕ} {I : Type*} [Fintype I] {E : I → Type*}
    [∀ i, MeasurableSpace (E i)] [∀ i, StandardBorelSpace (E i)]
    [NeZero k] [LinearOrder (HighWindowLabels d k)]
    (C : ModelConstants d) (R : HighUnionRowData d k D I E)
    {M Cfr : ℝ} (G : HighUnionSourceGuards C M Cfr R)
    (hpos : ∀ i, 0 < R.rowMass i)

def highUnionSourceRawNumerator (r : ℕ) (a V η : ℝ)
    (h : WindowHistory d k E)
    (j : HighWindowLabels d k) (x : DesignSample d r) (y : TernaryVector r) : ℝ :=
  highMarkedSampleNumerator r (highUnionLaw R (highCenterMix C))
    (highUnionActivation R (highCenterMix C)) a V η (highUnionSourceDensity C R h)
    (highUnionSourceResetDensity C R j h) (highUnionSourceResetCoefficient C R j h)
    (highLocalFieldWithout η (highUnionSourceState C R h).2 j)
    (highPeriodicTensor j) (fun x => highLocalFrameFeature j x)
    ((highUnionSourceState C R h).2 j) x y

include G hpos in
/-- The genuine sample-kernel score has square integrability and the
original factorial spatial budget, derived from local raw numerators. -/
theorem highUnionSource_sample_fisher_bound (n : ℕ) (hk : 4 ≤ k)
    (a V η cMass : ℝ) (ha : a ≠ 0) (hcMass : 0 < cMass)
    (hq : ∀ h x y, cMass ≤ ternaryMass a (highUnionSourceRegression C R η h x) V y)
    (hDensity : ∀ j h (x : DesignSample d n),
      (∫ e, highUnionActivation R (highCenterMix C) e *
        ∏ i, highUnionSourceResetDensity C R j h e (x i) ∂highUnionLaw R (highCenterMix C)) = 0)
    (h : WindowHistory d k E)
    (H : HighWindowLabels d k → (r : ℕ) → (DesignSample d r) → ℝ)
    (hH : ∀ j r, Integrable (H j r) (Measure.pi (fun _ => volume.restrict (spatialPatchBox d))))
    (hH0 : ∀ j r u, 0 ≤ H j r u)
    (hdom : ∀ j r x, (∀ i, x i ∈ highTorusPatch j) →
      selectedRawSquareEnergy (highUnionSourceRawNumerator C R r a V η h j) x ≤
        H j r (highPatchProductChart j x)) :
    let hp := highUnionSourceDensity_joint_measurable C R G
    let hF := highUnionSourceRegression_joint_measurable C R G η
    let S := highHistoryLikelihoodScore
      (highUnionLaw R (highCenterMix C)) (highUnionActivation R (highCenterMix C))
      n a V η (highUnionSourceDensity C R) (highUnionSourceRegression C R η) h
    Integrable (fun z => S z ^ 2)
      (highSampleIndexKernel n a V hp hF h) ∧
    (∫ z, S z ^ 2 ∂highSampleIndexKernel n a V hp hF h) ≤
      (3 ^ d : ℕ) * ∑ j, ∑ r ∈ Finset.range (n + 1),
        (n * highFixedScoreDenominator C.densityLower cMass * (2 / k) ^ d) ^ r /
          r.factorial * ∫ u, H j r u
            ∂Measure.pi (fun _ => volume.restrict (spatialPatchBox d)) := by
  letI : StandardBorelSpace (HighUnionMark E) := highUnionMark_standardBorel
  letI := highUnionSourceLaw_probability C R G
  let π := highUnionLaw R (highCenterMix C)
  let act := highUnionActivation R (highCenterMix C)
  let p := highUnionSourceDensity C R
  let F := highUnionSourceRegression C R η
  have hp : Measurable (Function.uncurry p) := highUnionSourceDensity_joint_measurable C R G
  have hF : Measurable (Function.uncurry F) := highUnionSourceRegression_joint_measurable C R G η
  have ham := highUnionActivation_measurable R G.activation_measurable (highCenterMix C)
  have hai : Integrable act π := Integrable.of_bound ham.aestronglyMeasurable
    (highRowTotalMass R.rowMass / highCenterMix C)
    (Filter.Eventually.of_forall (fun e => by solve_by_elim [highUnionSourceActivation_bound]))
  let c := (highUnionSourceState C R h).2
  let Fh := highFrameField k η (highFramePolynomial ∘ c)
  have hFh_eq : F h = Fh := by
    simp [F,Fh,c]
    funext x
    unfold highUnionSourceRegression
    rfl
  have hFh : Measurable Fh := (highFrameField_contDiff d k η _).continuous.measurable
  have hreg j e x y :
      highMarkedResponseMass a V η (highLocalFieldWithout η c j)
        (highPeriodicTensor j) (fun x => highLocalFrameFeature j x)
        (highUnionSourceResetCoefficient C R j h e) x y =
      ternaryMass a (F (historyMarkedAppend j (h,e)) x) V y := by
    have hr := congrFun (highUnionSourceRegression_append C R 1 hk η j h e (fun _ => x)) 0
    exact congrArg (fun t => ternaryMass a t V y) hr
  have hs := high_frame_complete_design_spatial_series d k D n hk (fun _ => ham) (fun _ => hai) ha C.densityLower_pos
    (by linarith [C.one_lt_densityUpper]) hcMass hp.of_uncurry_left
    (highUnionSourceDensity_coarse_interval C R G h)
    (fun j => highUnionSourceResetDensity_measurable C R G j h)
    (fun j => highUnionSourceResetDensity_abs_le C R G j h)
    (fun j => highUnionSourceResetDensity_outside C R j h)
    (fun j => highUnionSourceResetCoefficient_measurable C R G j h)
    (by
      change ∀ x y, cMass ≤ ternaryMass a (Fh x) V y
      intro x y
      rw [← hFh_eq]
      exact hq h x y) (by
      grind) (fun j x => hDensity ..) hH hH0 hdom
  have he : highSampleIndexKernel n a V hp hF h =
      (Measure.pi (fun _ => highNormalizedDesignLaw (p h))).compProd
        (responseSampleIndexKernel n a V hFh) := by
    have hm  := C.densityLower_pos.trans_le
      (highRawDensityMass_mem_Icc hp.of_uncurry_left C.densityLower_pos
        (Filter.Eventually.of_forall (highUnionSourceDensity_coarse_interval C R G h))).1
    rw [highSampleIndexKernel_apply]
    have hed := (highSample_index_density n hp.of_uncurry_left hF.of_uncurry_left a V (high_normalized_design_probability hp.of_uncurry_left C.densityLower_pos (Filter.Eventually.of_forall (highUnionSourceDensity_coarse_interval C R G h)))
      (fun x => C.densityLower_pos.le.trans (highUnionSourceDensity_coarse_interval C R G h x).1)
      hm (fun x y => hcMass.le.trans (hq h x y))).symm
    simpa only [hFh_eq,highSampleReference,highNormalizedDesignLaw] using hed
  have hS : highHistoryLikelihoodScore π act n a V η p F h =
      highFrameFullMarkedScore n (fun _ => π) (fun _ => act) a V η (p h)
        (fun j => highUnionSourceResetDensity C R j h)
        (fun j => highUnionSourceResetCoefficient C R j h) c := by
    funext z
    solve_by_elim [highUnionSourceLikelihoodScore_eq_sum]
  dsimp
  rw [hS,he]
  exact hs

end NearlyMinimax
