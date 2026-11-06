module
public import Mathlib

public import PottsDiscontinuity.FK.WiredBoxLaw
public import PottsDiscontinuity.FK.IncreasingEvents

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsDiscontinuity.PottsThm


open PottsDiscontinuity.FK

noncomputable section



private theorem wiredBoxConfiguration_mono (c : LatticeVertex) (r : ℕ)
    {A B : Configuration (boxGraph c r)} (hAB : A ≤ B) :
    wiredBoxConfiguration c r A ≤ wiredBoxConfiguration c r B := by
  intro e
  by_cases hA : wiredBoxConfiguration c r A e = true
  · 
    
    have hB  :=
      (wiredBoxConfiguration_open_iff c r B e).mpr  fun f hf => hAB (((wiredBoxConfiguration_open_iff c r A e).mp hA) f hf) 
    simp [hB]
  · simp_all

section

variable (θ : Parameters) (c : LatticeVertex) (r : ℕ)


private theorem wiredBoxProbabilityMeasure_apply_preimage
     (s : Set LatticeConfiguration)
    (hs : MeasurableSet s) :
    (wiredBoxProbabilityMeasure θ c r : Measure LatticeConfiguration) s =
      measure (boxGraph c r) θ (BoundaryCondition.wired (boxVertexBoundary c r))
        {A | wiredBoxConfiguration c r A ∈ s} := by
  change ((law (boxGraph c r) θ (BoundaryCondition.wired (boxVertexBoundary c r))).map
    (wiredBoxConfiguration c r)).toMeasure s = _
  rw [PMF.toMeasure_map_apply _ _ _ measurable_from_top hs]
  rfl

private theorem wiredBoxProbabilityMeasure_finite_positive_association
    
    (s t : Set LatticeConfiguration) (hsUpper : IsUpperSet s)
    (htUpper : IsUpperSet t) (hsMeas : MeasurableSet s) (htMeas : MeasurableSet t) :
    (wiredBoxProbabilityMeasure θ c r : Measure LatticeConfiguration).real s *
      (wiredBoxProbabilityMeasure θ c r : Measure LatticeConfiguration).real t ≤
        (wiredBoxProbabilityMeasure θ c r : Measure LatticeConfiguration).real (s ∩ t) := by
  let sbox  :=
    {A | wiredBoxConfiguration c r A ∈ s}
  let tbox  :=
    {A | wiredBoxConfiguration c r A ∈ t}
  
  
  have h := measure_positive_association θ
    (BoundaryCondition.wired (boxVertexBoundary c r)) sbox tbox (fun ⦃A B⦄ hAB => hsUpper (wiredBoxConfiguration_mono c r hAB))  fun ⦃A B⦄ hAB => htUpper (wiredBoxConfiguration_mono c r hAB) 
  
  
  
  
  rw [Measure.real_def, Measure.real_def, Measure.real_def]
  rw [ wiredBoxProbabilityMeasure_apply_preimage θ c r s hsMeas ,  wiredBoxProbabilityMeasure_apply_preimage θ c r t htMeas ,  wiredBoxProbabilityMeasure_apply_preimage θ c r (s ∩ t)
                 (hsMeas.inter htMeas) ]
  
  exact h

end

/-- Positive association for increasing clopen events under every actual wired
infinite-volume limit. -/
theorem wired_clopen_positive_association (θ : Parameters)
    (φ : ProbabilityMeasure LatticeConfiguration)
    (hφ : Tendsto  (wiredBoxProbabilityMeasure θ (0, 0))  atTop (𝓝 φ))
    (s t : Set LatticeConfiguration) (hsClopen : IsClopen s)
    (htClopen : IsClopen t) (hsUpper : IsUpperSet s) (htUpper : IsUpperSet t) :
    φ.toMeasure.real s * φ.toMeasure.real t ≤ φ.toMeasure.real (s ∩ t) := by
  
  
  
  
  
  
  
  
  have hlim := le_of_tendsto_of_tendsto' (((NNReal.continuous_coe.continuousAt.tendsto).comp (ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hφ hsClopen)).mul ((NNReal.continuous_coe.continuousAt.tendsto).comp (ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hφ htClopen))) ((NNReal.continuous_coe.continuousAt.tendsto).comp (ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hφ
                                                                                                                         (hsClopen.inter htClopen)))  fun n => by
                                                          have h := wiredBoxProbabilityMeasure_finite_positive_association θ (0, 0) n s t
                                                            hsUpper htUpper hsClopen.2.measurableSet htClopen.2.measurableSet
                                                          simp_all 
  simp_all

end
end PottsDiscontinuity.PottsThm
