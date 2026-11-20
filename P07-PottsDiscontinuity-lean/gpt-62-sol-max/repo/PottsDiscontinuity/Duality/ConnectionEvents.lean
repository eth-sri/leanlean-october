module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Homotopy.Path
public import PottsDiscontinuity.Duality.Decay
public import PottsDiscontinuity.CorrLength.ConnectionEvents
public import PottsDiscontinuity.FK.BoxCylinders
public import PottsDiscontinuity.FK.Wiring

/-! Finite actual-path witnesses for whole-plane connectivity. -/

@[expose] public section

open MeasureTheory

namespace PottsDiscontinuity.Duality

open FK FK.Medial

theorem mem_connectionEvent_iff_finite_witness (ω : LatticeConfiguration) (u v : LatticeVertex) :
    ω ∈ connectionEvent u v ↔ ∃ F : Finset squareLattice.edgeSet,
      ActualConnected squareLattice F u v ∧ ω ∈ LatticeConfiguration.allOpen F :=
  (CorrLength.connectionEvent_iff_rcInfiniteReachable u v ω).symm

theorem connectionEvent_eq_finite (u v : LatticeVertex) :
    connectionEvent u v = CorrLength.connectionEvent u v :=
  Set.ext fun ω => mem_connectionEvent_iff_finite_witness ω u v

lemma connectionEvent_measurableSet (u v : LatticeVertex) : MeasurableSet (connectionEvent u v) :=
  connectionEvent_eq_finite u v ▸ CorrLength.connectionEvent_isMeasurableSet u v

end PottsDiscontinuity.Duality
