module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Homotopy.Path
public import PottsDiscontinuity.Duality.Decay
public import PottsDiscontinuity.Duality.ScreenBridge
public import PottsDiscontinuity.FK.BoxCylinders
public import PottsDiscontinuity.FK.Wiring

/-! Finite actual-path witnesses for whole-plane connectivity. -/

@[expose] public section

open MeasureTheory

namespace PottsDiscontinuity.Duality

open FK FK.Medial

section
variable (ω : LatticeConfiguration)
theorem finite_openGraph_le (F : Finset squareLattice.edgeSet) (hF : ω ∈ LatticeConfiguration.allOpen F) :
    openGraph squareLattice F ≤ wholePlaneOpenPrimalGraph ω := by
  intro u v huv
  have hG := openGraph_le squareLattice F huv
  obtain ⟨e, he, heval⟩ := (openGraph_adj squareLattice F u v).1 huv
  refine ⟨hG, ?_⟩
  aesop

/-- Every actual whole-plane connection is witnessed by finitely many open
original lattice edges, and conversely. -/
theorem mem_connectionEvent_iff_finite_witness
    (u v : LatticeVertex) :
    ω ∈ connectionEvent u v ↔ ∃ F : Finset squareLattice.edgeSet,
      ActualConnected squareLattice F u v ∧ ω ∈ LatticeConfiguration.allOpen F := by
  change (rcInfiniteOpenGraph ω).Reachable u v ↔ _
  rw [← wholePlaneOpenPrimalGraph_eq_rcInfiniteOpenGraph]
  constructor
  · rintro ⟨p⟩
    induction p with
    | nil => exact ⟨∅, SimpleGraph.Reachable.refl _, fun _ h => False.elim (Finset.notMem_empty _ h)⟩
    | @cons a b c hab p ih =>
      obtain ⟨F, hconn, hF⟩ := ih
      obtain ⟨hG, hopen⟩ := hab
      let e : squareLattice.edgeSet := ⟨s(a, b), squareLattice.mem_edgeSet.mpr hG⟩
      have hadj : (openGraph squareLattice (insert e F)).Adj a b := by
        rw [openGraph_adj]
        exact ⟨e, Finset.mem_insert_self _ _, rfl⟩
      refine ⟨insert e F, hadj.reachable.trans
        (actualConnected_mono (Finset.subset_insert _ _) hconn), ?_⟩
      aesop
  · rintro ⟨F, hconn, hF⟩
    exact hconn.mono (finite_openGraph_le ω F hF)
end

/-- A finite original-edge configuration connecting the prescribed vertices. -/
abbrev ConnectionWitness (u v : LatticeVertex) :=
  {F : Finset squareLattice.edgeSet // ActualConnected squareLattice F u v}

section
variable (u v : LatticeVertex) (S : Finset (ConnectionWitness u v))
/-- A finite union of finite path cylinders. -/
def finiteConnectionUnion  :
    Set LatticeConfiguration :=
  ⋃ F ∈ S, LatticeConfiguration.allOpen F.val

theorem finiteConnectionUnion_isClopen  : IsClopen (finiteConnectionUnion u v S) :=
  isClopen_biUnion_finset (fun F _ => LatticeConfiguration.allOpen_isClopen F.val)
end

theorem allOpen_isUpperSet (F : Finset squareLattice.edgeSet) :
    IsUpperSet (LatticeConfiguration.allOpen F) := by
  tauto

section
variable (u v : LatticeVertex)
theorem finiteConnectionUnion_isUpperSet (S : Finset (ConnectionWitness u v)) : IsUpperSet (finiteConnectionUnion u v S) := by
  intro ω η hle hω
  obtain ⟨F, hF, hω⟩ := Set.mem_iUnion₂.1 hω
  exact Set.mem_iUnion₂.2 ⟨F, hF, allOpen_isUpperSet F.val hle hω⟩

theorem finiteConnectionUnion_mono  :
    Monotone (finiteConnectionUnion u v) := by
  intro S T hST ω hω
  obtain ⟨F, hF, hω⟩ := Set.mem_iUnion₂.1 hω
  exact Set.mem_iUnion₂.2 ⟨F, hST hF, hω⟩

theorem connectionEvent_eq_iUnion  :
    connectionEvent u v = ⋃ S : Finset (ConnectionWitness u v), finiteConnectionUnion u v S := by
  ext ω
  rw [mem_connectionEvent_iff_finite_witness]
  constructor
  · rintro ⟨F, hconn, hF⟩
    exact Set.mem_iUnion.2 ⟨{⟨F, hconn⟩},
      Set.mem_iUnion₂.2 ⟨⟨F, hconn⟩, Finset.mem_singleton_self _, hF⟩⟩
  · intro h
    obtain ⟨S, hS⟩ := Set.mem_iUnion.1 h
    obtain ⟨F, _, hF⟩ := Set.mem_iUnion₂.1 hS
    grind

theorem connectionEvent_isOpen  : IsOpen (connectionEvent u v) := by
  rw [connectionEvent_eq_iUnion]
  exact isOpen_iUnion (fun S => (finiteConnectionUnion_isClopen u v S).isOpen)

theorem connectionEvent_measurableSet  :
    MeasurableSet (connectionEvent u v) := (connectionEvent_isOpen u v).measurableSet
end

theorem measure_connectionEvent_eq_iSup (μ : Measure LatticeConfiguration) (u v : LatticeVertex) :
    μ (connectionEvent u v) =
      ⨆ S : Finset (ConnectionWitness u v), μ (finiteConnectionUnion u v S) := by
  rw [connectionEvent_eq_iUnion]
  exact (finiteConnectionUnion_mono u v).directed_le.measure_iUnion

end PottsDiscontinuity.Duality
