module

public import PottsDiscontinuity.FK.WiredBoxLaw
public import PottsDiscontinuity.FK.IncreasingEvents

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsDiscontinuity.PottsThm

open PottsDiscontinuity
open PottsDiscontinuity.FK

noncomputable section

attribute [local instance] configurationMeasurableSpace

private theorem wiredBoxConfiguration_mono (c : LatticeVertex) (r : ℕ)
    {A B : Configuration (boxGraph c r)} (hAB : A ≤ B) :
    wiredBoxConfiguration c r A ≤ wiredBoxConfiguration c r B := fun e => by
  by_cases hA : wiredBoxConfiguration c r A e = true
  · simp [hA, (wiredBoxConfiguration_open_iff c r B e).mpr fun f hf =>
      hAB ((wiredBoxConfiguration_open_iff c r A e).mp hA f hf)]
  · simp [Bool.eq_false_of_ne_true hA]

private theorem wiredBoxProbabilityMeasure_apply_preimage
    (θ : Parameters) (c : LatticeVertex) (r : ℕ) (s : Set LatticeConfiguration)
    (hs : MeasurableSet s) :
    (wiredBoxProbabilityMeasure θ c r : Measure LatticeConfiguration) s =
      measure (boxGraph c r) θ (BoundaryCondition.wired (boxVertexBoundary c r))
        {A | wiredBoxConfiguration c r A ∈ s} := by
  change ((law (boxGraph c r) θ (BoundaryCondition.wired (boxVertexBoundary c r))).map
    (wiredBoxConfiguration c r)).toMeasure s = _
  rw [PMF.toMeasure_map_apply _ _ _ measurable_from_top hs]
  rfl

private theorem wiredBoxProbabilityMeasure_finite_positive_association
    (θ : Parameters) (c : LatticeVertex) (r : ℕ)
    (s t : Set LatticeConfiguration) (hsUpper : IsUpperSet s)
    (htUpper : IsUpperSet t) (hsMeas : MeasurableSet s) (htMeas : MeasurableSet t) :
    (wiredBoxProbabilityMeasure θ c r : Measure LatticeConfiguration).real s *
      (wiredBoxProbabilityMeasure θ c r : Measure LatticeConfiguration).real t ≤
        (wiredBoxProbabilityMeasure θ c r : Measure LatticeConfiguration).real (s ∩ t) := by
  rw [Measure.real_def, Measure.real_def, Measure.real_def,
    wiredBoxProbabilityMeasure_apply_preimage θ c r s hsMeas,
    wiredBoxProbabilityMeasure_apply_preimage θ c r t htMeas,
    wiredBoxProbabilityMeasure_apply_preimage θ c r (s ∩ t) (hsMeas.inter htMeas)]
  exact measure_positive_association θ
    (BoundaryCondition.wired (boxVertexBoundary c r))
    {A | wiredBoxConfiguration c r A ∈ s} {A | wiredBoxConfiguration c r A ∈ t}
    (fun _ _ hAB hA => hsUpper (wiredBoxConfiguration_mono c r hAB) hA)
    (fun _ _ hAB hA => htUpper (wiredBoxConfiguration_mono c r hAB) hA)

theorem wired_clopen_positive_association (θ : Parameters)
    (φ : ProbabilityMeasure LatticeConfiguration)
    (hφ : Tendsto (fun n => wiredBoxProbabilityMeasure θ (0, 0) n) atTop (𝓝 φ))
    (s t : Set LatticeConfiguration) (hsClopen : IsClopen s)
    (htClopen : IsClopen t) (hsUpper : IsUpperSet s) (htUpper : IsUpperSet t) :
    φ.toMeasure.real s * φ.toMeasure.real t ≤ φ.toMeasure.real (s ∩ t) := by
  have hreal (u : Set LatticeConfiguration) (hu : IsClopen u) :
      Tendsto (fun n => (wiredBoxProbabilityMeasure θ (0, 0) n : Measure LatticeConfiguration).real u)
        atTop (𝓝 (φ.toMeasure.real u)) := by
    simp_rw [ProbabilityMeasure.measureReal_eq_coe_coeFn]
    exact NNReal.continuous_coe.continuousAt.tendsto.comp
      (ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hφ hu)
  exact le_of_tendsto_of_tendsto' ((hreal s hsClopen).mul (hreal t htClopen))
    (hreal (s ∩ t) (hsClopen.inter htClopen)) fun n =>
      wiredBoxProbabilityMeasure_finite_positive_association θ (0, 0) n s t
        hsUpper htUpper hsClopen.2.measurableSet htClopen.2.measurableSet

end
end PottsDiscontinuity.PottsThm
