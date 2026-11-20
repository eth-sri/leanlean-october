module

public import Mathlib
public import PottsDiscontinuity.Duality.FiniteDuality
public import PottsDiscontinuity.TorusRC.CorrelationRate
public import PottsDiscontinuity.TorusRC.CrossingContracts
public import PottsDiscontinuity.TorusRC.ElementaryTail

@[expose] public section

open Finset

namespace PottsDiscontinuity.RCMProof

open PottsDiscontinuity
def contract_h319 : Prop :=
  ∀ (q : Set.Ici (1 : ℝ)), TorusRC.h319 q

/- Provider statement for (3.16), proved as `TorusExploration.contract_eq316` in
`TorusExploration/Contract.lean`, with the same free-limit rate convention as (3.15). -/
def contract_eq316 : Prop :=
  ∀ (q : Set.Ici (1 : ℝ))
    (μ : MeasureTheory.Measure PottsDiscontinuity.FK.LatticeConfiguration)
    (_hμ : PottsDiscontinuity.IsRCInfiniteVolumeLimit
      (FK.criticalParameters q).toP (FK.criticalParameters q).toQ 0 μ)
    (ξinv : ℝ)
    (_hRate : Filter.Tendsto (fun n : ℕ =>
      -Real.log (μ.real (CorrLength.connectionEvent (0, 0)
        (PottsDiscontinuity.diagonalSite n))) / (n : ℝ))
      Filter.atTop (nhds ξinv))
    (r : ℕ) (_hr : 1 ≤ r),
      Filter.limsup
        (fun n : ℕ => Filter.limsup
          (fun m : ℕ => TorusRC.positiveEvenVerticalTailRateE q r n m) Filter.atTop)
        Filter.atTop ≤ (-((r - 1 : ℕ) : ℝ) * ξinv : ℝ)

end PottsDiscontinuity.RCMProof
