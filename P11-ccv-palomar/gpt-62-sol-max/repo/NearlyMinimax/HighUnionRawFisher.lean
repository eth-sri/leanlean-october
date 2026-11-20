module

public import NearlyMinimax.HighUnionFisher
public import NearlyMinimax.HighRawScoreEnergy


@[expose] public section

/-! The genuine spatial factorial budget yields joint raw Fisher
integrability and the mass-normalized energy for the actual source prior. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency true
attribute [local instance] Classical.propDecidable
attribute [local irreducible] highUnionSourceDensity highUnionSourceRegression highUnionSourceState
  historyMarkedAppend highRawSampleLikelihood massPowerNormalizer highSampleIndexKernel

variable {d k D : ℕ} {I : Type*} [Fintype I] {E : I → Type*}
    [∀ i, MeasurableSpace (E i)] [∀ i, StandardBorelSpace (E i)]
    [NeZero k] [LinearOrder (HighWindowLabels d k)]
    (C : ModelConstants d) (R : HighUnionRowData d k D I E)
    {M Cfr : ℝ} (G : HighUnionSourceGuards C M Cfr R)
    (hpos : ∀ i, 0 < R.rowMass i)

include G hpos in
 theorem highUnionSource_raw_fisher_bound
    (ν : Measure (HighUnionHistory d k E))
    [IsProbabilityMeasure ν] (n : ℕ) (hk : 4 ≤ k)
    (a V η cMass : ℝ) (ha : a ≠ 0) (hcMass : 0 < cMass)
    (hq : ∀ h x y, cMass ≤ ternaryMass a (highUnionSourceRegression C R η h x) V y)
    (hDensity : ∀ j h (x : Fin n → Covariate d),
      (∫ e, highUnionActivation R (highCenterMix C) e *
        ∏ i, highUnionSourceResetDensity C R j h e (x i) ∂highUnionLaw R (highCenterMix C)) = 0)
    (H : HighUnionHistory d k E →
      HighWindowLabels d k → (r : ℕ) → (Fin r → Covariate d) → ℝ)
    (hH : ∀ h j r, Integrable (H h j r)
      (Measure.pi (fun _ : Fin r => volume.restrict (spatialPatchBox d))))
    (hH0 : ∀ h j r u, 0 ≤ H h j r u)
    (hdom : ∀ h j r x, (∀ i, x i ∈ highTorusPatch d k j) →
      selectedRawSquareEnergy (highUnionSourceRawNumerator C R r a V η h j) x ≤
        H h j r (highPatchProductChart d k j x))
    (B : ℝ)
    (hbudget : ∀ h, highSourceSpatialSeries d k n C.densityLower cMass (H h) ≤ B) :
    let D := highHistoryLikelihoodDerivative (highNeighbors d k)
      (highNeighbors_symm d k)
      (highUnionLaw R (highCenterMix C)) (highUnionActivation R (highCenterMix C))
      n a V η (highUnionSourceDensity C R) (highUnionSourceRegression C R η)
    HighRawFisherBudget ν n a V (highUnionSourceDensity C R) (highUnionSourceRegression C R η) D B := by
  letI : StandardBorelSpace (HighUnionMark E) := highUnionMark_standardBorel
  letI := highUnionSourceLaw_probability C R G
  let π := highUnionLaw R (highCenterMix C)
  let act := highUnionActivation R (highCenterMix C)
  let p := highUnionSourceDensity C R
  let F := highUnionSourceRegression C R η
  have hp := highUnionSourceDensity_joint_measurable C R G
  have hF := highUnionSourceRegression_joint_measurable C R G η
  have ham := highUnionActivation_measurable R G.activation_measurable (highCenterMix C)
  let Dscore := highHistoryLikelihoodDerivative (highNeighbors d k)
    (highNeighbors_symm d k) π act n a V η p F
  have hDm := highHistoryLikelihoodDerivative_measurable
    (highNeighbors d k) (highNeighbors_symm d k) π act ham n a V η p F hp hF
  have hai : Integrable act π := Integrable.of_bound ham.aestronglyMeasurable
    (highRowTotalMass R.rowMass / highCenterMix C)
    (Filter.Eventually.of_forall (fun e => by simpa only [Real.norm_eq_abs] using (highUnionSourceActivation_bound C R G hpos e)))
  apply high_raw_joint_fisher_integrable_bound ν n a V p F hp hF
    C.densityLower C.densityUpper C.densityLower_pos
    (highUnionSourceDensity_coarse_interval C R G) (fun h x y => hcMass.trans_le (hq h x y))
    Dscore hDm B
  intro h
  let c := (highUnionSourceState C R h).2
  let Fh := highFrameField d k η (fun l => highFramePolynomial (c l))
  have hFh_eq : F h = Fh := by
    simp only [F,Fh,c]
    funext x
    unfold highUnionSourceRegression
    rfl
  have hFh : Measurable Fh := (highFrameField_contDiff d k η _).continuous.measurable
  have hreg (j : HighWindowLabels d k) (e : HighUnionMark E) (x : Covariate d) (y : Fin 3) :
      highMarkedResponseMass a V η (highLocalFieldWithout d k D η c j)
        (highPeriodicTensor d k j) (fun x => highLocalFrameFeature k j x)
        (highUnionSourceResetCoefficient C R j h e) x y =
      ternaryMass a (F (historyMarkedAppend
        (highNeighbors d k)
        (highNeighbors_symm d k) j (h,e)) x) V y := by
    unfold highMarkedResponseMass
    have hr := congrFun (highUnionSourceRegression_append C R 1 hk η j h e (fun _ => x)) 0
    exact congrArg (fun t : ℝ => ternaryMass a t V y) hr
  have hs := high_frame_complete_design_spatial_series d k D n hk
    (fun _ => π) (fun _ => act) (fun _ => ham) (fun _ => hai)
    a V η C.densityLower C.densityUpper cMass ha C.densityLower_pos
    (by linarith [C.one_lt_densityUpper]) hcMass (p h) hp.of_uncurry_left
    (highUnionSourceDensity_coarse_interval C R G h)
    (fun j => highUnionSourceResetDensity C R j h)
    (fun j => highUnionSourceResetDensity_measurable C R G j h)
    (fun j => highUnionSourceResetDensity_abs_le C R G j h)
    (fun j => highUnionSourceResetDensity_outside C R j h)
    (fun j => highUnionSourceResetCoefficient C R j h)
    (fun j => highUnionSourceResetCoefficient_measurable C R G j h) c
    (by
      change ∀ x y, cMass ≤ ternaryMass a (Fh x) V y
      intro x y
      rw [← hFh_eq] <;> solve_by_elim) (by
      intro j e x y
      rw [hreg]
      solve_by_elim [hcMass.le.trans]) (fun j x => hDensity j h x) (H h) (hH h) (hH0 h) (hdom h)
  have he : highSampleIndexKernel n a V p F hp hF h =
      (Measure.pi (fun _ : Fin n => highNormalizedDesignLaw (p h))).compProd
        (responseSampleIndexKernel n a V Fh hFh) := by
    simpa only [hFh_eq] using
      highSampleIndexKernel_eq_compProd n a V p F hp hF C.densityLower C.densityUpper
        C.densityLower_pos (highUnionSourceDensity_coarse_interval C R G)
        (fun h x y => hcMass.le.trans (hq h x y)) h
  have hS : highHistoryLikelihoodScore (highNeighbors d k)
      (highNeighbors_symm d k) π act n a V η p F h =
      highFrameFullMarkedScore d k D n (fun _ => π) (fun _ => act) a V η (p h)
        (fun j => highUnionSourceResetDensity C R j h)
        (fun j => highUnionSourceResetCoefficient C R j h) c := by
    funext z
    solve_by_elim [highUnionSourceLikelihoodScore_eq_sum]
  dsimp only at hs
  rw [← he, ← hS] at hs
  exact ⟨hs.1, hs.2.trans (hbudget h)⟩

end NearlyMinimax
