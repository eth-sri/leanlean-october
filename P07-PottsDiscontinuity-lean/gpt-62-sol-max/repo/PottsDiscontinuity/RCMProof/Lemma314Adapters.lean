module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Homotopy.Path
public import PottsDiscontinuity.Duality.Decay
public import PottsDiscontinuity.Duality.FiniteDuality
public import PottsDiscontinuity.TorusLoops.Lemma314Corrected

@[expose] public section

namespace PottsDiscontinuity.RCMProof

open PottsDiscontinuity
open MeasureTheory

/-- The square-box premise required by the corrected Lemma 3.14 follows from the absence of
percolation for the critical free measure, which is derived in `RCMProof/Item3.lean` from the
positive lower bound on the inverse correlation length. The rectangle and critical parameter
records are the same record, and the free-box limit is unique. -/
theorem lemma314_square_boundary_decay_of_nonpercolation
    (q : Set.Ici (1 : ℝ)) (μ : MeasureTheory.Measure FK.LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit (FK.criticalParameters q).toP
      (FK.criticalParameters q).toQ 0 μ)
    (hno : μ (Duality.infiniteClusterAt (0, 0)) = 0) :
    Filter.Tendsto
      (fun n => (((Classical.choose (FK.freeBoxLimit_existsUnique
        (TorusLoops.rectangleFKParameters q)))
          (Zhang.boundaryConnectionEvent n) : NNReal) : ℝ))
      Filter.atTop (nhds 0) := by
  have := hμ.1
  have he := CorrLength.free_limit_eq_selected (TorusLoops.rectangleFKParameters q) μ hμ
  simp only [← ProbabilityMeasure.measureReal_eq_coe_coeFn, Measure.real_def, ← he]
  simpa only [Function.comp_def, ENNReal.toReal_zero] using
    (ENNReal.continuousAt_toReal (show (0 : ENNReal) ≠ ⊤ by simp)).tendsto.comp
      ((Zhang.tendsto_boundaryConnection_zero_iff μ).2 hno)

end PottsDiscontinuity.RCMProof
