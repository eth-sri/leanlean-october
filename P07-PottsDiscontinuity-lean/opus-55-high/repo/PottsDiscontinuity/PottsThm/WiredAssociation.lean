module

public import PottsDiscontinuity.FK.WiredBoxLaw
public import PottsDiscontinuity.FK.IncreasingEvents

public section

open MeasureTheory Filter Topology

namespace PottsDiscontinuity.PottsThm

open PottsDiscontinuity
open PottsDiscontinuity.FK

noncomputable section

attribute [local instance] configurationMeasurableSpace

theorem wiredBoxConfiguration_mono (c : LatticeVertex) (r : ℕ)
    {A B : Configuration (boxGraph c r)} (hAB : A ≤ B) :
    wiredBoxConfiguration c r A ≤ wiredBoxConfiguration c r B := by
  intro e
  by_cases hA : wiredBoxConfiguration c r A e = true
  · have hpropB : ∀ f, boxEdgeEmbedding c r f = e → f ∈ B := by
      intro f hf
      exact hAB (((wiredBoxConfiguration_open_iff c r A e).mp hA) f hf)
    simp [hA, ((wiredBoxConfiguration_open_iff c r B e).mpr hpropB)]
  simp_all

section
variable (θ : Parameters) (c : LatticeVertex) (r : ℕ)
theorem wiredBoxProbabilityMeasure_apply_preimage
    (s : Set LatticeConfiguration)
    (hs : MeasurableSet s) :
    (wiredBoxProbabilityMeasure θ c r : Measure LatticeConfiguration) s =
      measure (boxGraph c r) θ (BoundaryCondition.wired (boxVertexBoundary c r))
        {A | wiredBoxConfiguration c r A ∈ s} := by
  change ((law (boxGraph c r) θ (BoundaryCondition.wired (boxVertexBoundary c r))).map
    (wiredBoxConfiguration c r)).toMeasure s = _
  rw [PMF.toMeasure_map_apply _ _ _ measurable_from_top hs]
  rfl

theorem wiredBoxProbabilityMeasure_finite_positive_association
    (s t : Set LatticeConfiguration) (hsUpper : IsUpperSet s)
    (htUpper : IsUpperSet t) (hsMeas : MeasurableSet s) (htMeas : MeasurableSet t) :
    (wiredBoxProbabilityMeasure θ c r : Measure LatticeConfiguration).real s *
      (wiredBoxProbabilityMeasure θ c r : Measure LatticeConfiguration).real t ≤
        (wiredBoxProbabilityMeasure θ c r : Measure LatticeConfiguration).real (s ∩ t) := by
  let sbox :=
    {A | wiredBoxConfiguration c r A ∈ s}
  let tbox :=
    {A | wiredBoxConfiguration c r A ∈ t}
  have hsbox : IsUpperSet sbox := by
    intro A B hAB hA
    exact hsUpper (wiredBoxConfiguration_mono c r hAB) hA
  have htbox : IsUpperSet tbox := by
    intro A B hAB hA
    exact htUpper (wiredBoxConfiguration_mono c r hAB) hA
  have h := measure_positive_association θ
    (BoundaryCondition.wired (boxVertexBoundary c r)) sbox tbox hsbox htbox
  have hS := wiredBoxProbabilityMeasure_apply_preimage θ c r s hsMeas
  have hT := wiredBoxProbabilityMeasure_apply_preimage θ c r t htMeas
  have hST := wiredBoxProbabilityMeasure_apply_preimage θ c r (s ∩ t)
    (hsMeas.inter htMeas)
  have hsets : sbox ∩ tbox =
      {A | wiredBoxConfiguration c r A ∈ s ∩ t} := by
    rfl
  rw [Measure.real_def, Measure.real_def, Measure.real_def]
  grind
end

/-- Positive association for increasing clopen events under every actual wired
infinite-volume limit. -/
theorem wired_clopen_positive_association (θ : Parameters)
    (φ : ProbabilityMeasure LatticeConfiguration)
    (hφ : Tendsto (fun n => wiredBoxProbabilityMeasure θ (0, 0) n) atTop (𝓝 φ))
    (s t : Set LatticeConfiguration) (hsClopen : IsClopen s)
    (htClopen : IsClopen t) (hsUpper : IsUpperSet s) (htUpper : IsUpperSet t) :
    φ.toMeasure.real s * φ.toMeasure.real t ≤ φ.toMeasure.real (s ∩ t) := by
  have hS := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hφ hsClopen
  have hT := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hφ htClopen
  have hST := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hφ
        (hsClopen.inter htClopen)
  have hSreal : Tendsto (fun n =>
      (((wiredBoxProbabilityMeasure θ (0, 0) n s : NNReal) : ℝ))) atTop
      (𝓝 ((φ s : NNReal) : ℝ)) :=
    by simp_all
  have hTreal : Tendsto (fun n =>
      (((wiredBoxProbabilityMeasure θ (0, 0) n t : NNReal) : ℝ))) atTop
      (𝓝 ((φ t : NNReal) : ℝ)) :=
    by simp_all
  have hSTreal : Tendsto (fun n =>
      (((wiredBoxProbabilityMeasure θ (0, 0) n (s ∩ t) : NNReal) : ℝ))) atTop
      (𝓝 ((φ (s ∩ t) : NNReal) : ℝ)) :=
    by simp_all
  have hfinite (n : ℕ) :
      (((wiredBoxProbabilityMeasure θ (0, 0) n s : NNReal) : ℝ) *
        ((wiredBoxProbabilityMeasure θ (0, 0) n t : NNReal) : ℝ)) ≤
        ((wiredBoxProbabilityMeasure θ (0, 0) n (s ∩ t) : NNReal) : ℝ) := by
    have h := wiredBoxProbabilityMeasure_finite_positive_association θ (0, 0) n s t
      hsUpper htUpper hsClopen.2.measurableSet htClopen.2.measurableSet
    simp_all
  have hlim := le_of_tendsto_of_tendsto' (hSreal.mul hTreal) hSTreal hfinite
  simp_all

end
end PottsDiscontinuity.PottsThm
