module

public import NearlyMinimax.HighUnionInvariantMass

@[expose] public section

/-! The actual complete-row mass-power tilt is a probability measure;
the source bounded-differences MGF gives its exceptional mass probability. -/
noncomputable section
open MeasureTheory Set
namespace NearlyMinimax
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

section Generic
variable {d k F : ℕ} {I : Type*} [Fintype I] {E : I → Type*}
    [∀ i, MeasurableSpace (E i)] [∀ i, StandardBorelSpace (E i)]
    [NeZero k] [LinearOrder (HighWindowLabels d k)]
    (C : ModelConstants d) (R : HighUnionRowData d k F I E)
    {M Cfr : ℝ} (G : HighUnionSourceGuards C M Cfr R)
include G

theorem highUnionSourceMass_coarse_interval
    h :
    highUnionSourceMass C R h ∈ Icc C.densityLower C.densityUpper := by
  have hg := highCenterResolution_guards C M G.resolution
  have hM0 : 0 < M := by linarith [hg.1]
  have hb := highUnionSourceMass_interval C R G h
  constructor
  · exact (le_add_of_nonneg_right (one_div_pos.mpr hM0).le).trans hb.1
  · exact hb.2.trans (sub_le_self _ (one_div_pos.mpr hM0).le)

/-- Actual complete-union reference fiber means and true torus block
oscillation yield the mass-tilted exceptional probability. -/
theorem highUnionSourceMass_reference_tilted_tail (hk : 2 ≤ k) (n : ℕ) ε
    (hε : 8*highHistoryMassParameter d k C.densityLower C.densityUpper*n ≤ ε) :
    (massPowerTilt
      (historyMarkedReference (fun i j => j ∈ highNeighborLabels d k i) (3^d)
        (highUnionLaw R (highCenterMix C))) (highUnionSourceMass C R) n).real
      {h | ε < |highUnionSourceMass C R h-1|} ≤
      2*Real.exp (-ε^2/(8*highHistoryMassParameter d k C.densityLower C.densityUpper)) := by
  letI := highUnionSourceLaw_probability C R G
  letI := historyMarkedReference_probability _ (highNeighborLabels_self_mem d k)
    (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h) (3^d)
    (one_le_pow₀ (by norm_num : (1:ℕ) ≤ 3)) (highNeighbor_dependency_card d k)
    (highUnionLaw R (highCenterMix C))
  exact massPowerTilt_abs_tail _ _ (highUnionSourceMass_measurable C R G) n
    C.densityLower C.densityUpper C.densityLower_pos (highUnionSourceMass_coarse_interval C R G)
    (highUnionSourceMass_reference_mean_one C R G) _ ε
    (highHistoryMassParameter_pos d k _ _ (by omega)
      (C.densityLower_lt_one.trans C.one_lt_densityUpper))
    (highUnionSourceMass_reference_mgf C R G hk) hε

end Generic

section ActualFinePair
variable {d k D M q : ℕ} [NeZero d] [NeZero k] [LinearOrder (HighWindowLabels d k)]
    (C : ModelConstants d) (Cfr T₀ N : ℝ)
    (hD : 3 ≤ D) (hq : 1 ≤ q) (hM : highCenterResolutionThreshold C ≤ (M : ℝ))
    (hCfr : 1 ≤ Cfr) (hT₀ : 0 < T₀) (hTN : T₀ < N)
include hD hq hM hCfr hT₀ hTN

end ActualFinePair
end NearlyMinimax
