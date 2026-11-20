module

public import PottsDiscontinuity.Duality.ScreenBridge
public import PottsDiscontinuity.FK.FreeBoxPositiveAssociation
public import PottsDiscontinuity.FK.LimitTranslation

/-!
# Finite witnesses for infinite-lattice connection events

Connection is expressed as the existence of a finite set of open edges that
connects the marked vertices. The countable finite-witness union is measurable
and is approximated from below by clopen increasing events.
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsDiscontinuity.CorrLength

open PottsDiscontinuity.FK

noncomputable section

local instance connectionEdgeCountable : Countable squareLattice.edgeSet := inferInstance
local instance connectionFinsetCountable : Countable (Finset squareLattice.edgeSet) := inferInstance

/-- A surjective enumeration of all finite sets of square-lattice edges. -/
noncomputable def finiteEdgeSetEnumeration : ℕ → Finset squareLattice.edgeSet :=
  (exists_surjective_nat _).choose

theorem finiteEdgeSetEnumeration_surjective :
    Function.Surjective finiteEdgeSetEnumeration :=
  (exists_surjective_nat _).choose_spec

/-- The event that a fixed finite edge set is open and connects the endpoints. -/
def finiteConnectionEvent (u v : LatticeVertex) (F : Finset squareLattice.edgeSet) :
    Set LatticeConfiguration :=
  {ω | ActualConnected F u v ∧ ω ∈ LatticeConfiguration.allOpen F}

/-- Finite approximations to connection, enumerated by finite edge sets. -/
def connectionApprox (u v : LatticeVertex) (n : ℕ) : Set LatticeConfiguration :=
  ⋃ i : {i : ℕ // i ≤ n}, finiteConnectionEvent u v (finiteEdgeSetEnumeration i)

/-- Connection by some finite set of open edges. -/
def connectionEvent (u v : LatticeVertex) : Set LatticeConfiguration :=
  {ω | ∃ F,
    ActualConnected F u v ∧ ω ∈ LatticeConfiguration.allOpen F}

theorem mem_connectionApprox_iff (u v : LatticeVertex) (n : ℕ)
    (ω : LatticeConfiguration) :
    ω ∈ connectionApprox u v n ↔
      ∃ i ≤ n, ActualConnected (finiteEdgeSetEnumeration i) u v ∧
        ω ∈ LatticeConfiguration.allOpen (finiteEdgeSetEnumeration i) := by
  rw [connectionApprox]
  aesop

theorem connectionApprox_mono (u v : LatticeVertex) :
    Monotone (connectionApprox u v) := by
  intro n m hnm ω hω
  rcases (mem_connectionApprox_iff u v n ω).mp hω with ⟨i, hi, hconn, hopen⟩
  exact (mem_connectionApprox_iff u v m ω).mpr
    (by grind)

theorem connectionEvent_eq_iUnion_connectionApprox (u v : LatticeVertex) :
    connectionEvent u v = ⋃ n, connectionApprox u v n := by
  ext ω
  constructor
  · rintro ⟨F, hconn, hopen⟩
    obtain ⟨i, hi⟩ := finiteEdgeSetEnumeration_surjective F
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    exact (mem_connectionApprox_iff u v i ω).mpr ⟨i, le_rfl, (by grind), (by grind)⟩
  · intro h
    rcases Set.mem_iUnion.mp h with ⟨n, hn⟩
    rcases (mem_connectionApprox_iff u v n ω).mp hn with ⟨i, hi, hconn, hopen⟩
    exact ⟨finiteEdgeSetEnumeration i, hconn, hopen⟩

theorem connectionApprox_isClopen (u v : LatticeVertex) (n : ℕ) :
    IsClopen (connectionApprox u v n) := by
  apply isClopen_iUnion_of_finite
  intro i
  by_cases hconn : ActualConnected (finiteEdgeSetEnumeration i) u v
  · simpa [connectionApprox, finiteConnectionEvent, hconn] using
      LatticeConfiguration.allOpen_isClopen _
  · simpa [connectionApprox, finiteConnectionEvent, hconn] using
      isClopen_empty

theorem connectionApprox_isUpperSet (u v : LatticeVertex) (n : ℕ) :
    IsUpperSet (connectionApprox u v n) := by
  intro ω η hωη hω
  rcases (mem_connectionApprox_iff u v n ω).mp hω with ⟨i, hi, hconn, hopen⟩
  refine (mem_connectionApprox_iff u v n η).mpr ⟨i, hi, hconn, ?_⟩
  solve_by_elim [hωη, hopen, False.elim]

theorem connectionEvent_isMeasurableSet (u v : LatticeVertex) :
    MeasurableSet (connectionEvent u v) := by
  rw [connectionEvent_eq_iUnion_connectionApprox]
  exact MeasurableSet.iUnion fun n => (connectionApprox_isClopen u v n).2.measurableSet

theorem tendsto_connectionApprox_probability (ν : ProbabilityMeasure LatticeConfiguration)
    (u v : LatticeVertex) :
    Tendsto (fun n : ℕ => ν.toFiniteMeasure (connectionApprox u v n)) atTop
      (𝓝 (ν.toFiniteMeasure (connectionEvent u v))) := by
  have hacc (n : ℕ) : Set.accumulate (connectionApprox u v) n = connectionApprox u v n := by
    ext ω
    rw [Set.mem_accumulate]
    constructor
    · rintro ⟨m, hmn, hm⟩
      exact (connectionApprox_mono u v hmn) hm
    · grind
  have h := ν.toFiniteMeasure.tendsto_measure_iUnion_accumulate
    (f := connectionApprox u v)
  have h' : Tendsto (fun n => ν.toFiniteMeasure (connectionApprox u v n)) atTop
      (𝓝 (ν.toFiniteMeasure (⋃ n, connectionApprox u v n))) := by
    grind
  simpa [ProbabilityMeasure.toFiniteMeasure_apply,
    connectionEvent_eq_iUnion_connectionApprox] using h'

theorem finiteConnection_union (u v w : LatticeVertex)
    {F G : Finset squareLattice.edgeSet}
    (hF : ActualConnected F u v)
    (hG : ActualConnected G v w)
    (ω : LatticeConfiguration)
    (hopenF : ω ∈ LatticeConfiguration.allOpen F)
    (hopenG : ω ∈ LatticeConfiguration.allOpen G) :
    ω ∈ connectionEvent u w := by
  refine ⟨F ∪ G, ?_, ?_⟩
  · exact (actualConnected_mono Finset.subset_union_left hF).trans (actualConnected_mono Finset.subset_union_right hG)
  · intro e he
    aesop

private theorem openGraph_subset_rcInfiniteOpenGraph (ω : LatticeConfiguration)
    (F : Finset squareLattice.edgeSet)
    (hopen : ω ∈ LatticeConfiguration.allOpen F) :
    openGraph F ≤ PottsDiscontinuity.rcInfiniteOpenGraph ω := by
  intro u v huv
  obtain ⟨e, heF, heq⟩ := (openGraph_adj F u v).mp huv
  have hEdge : s(u, v) ∈ squareLattice.edgeSet := by
    grind
  have he : ⟨s(u, v), hEdge⟩ = e := by
    grind
  have hω : ω ⟨s(u, v), hEdge⟩ = true := by
    rw [he]
    exact hopen e heF
  grind [PottsDiscontinuity.rcInfiniteOpenGraph, SimpleGraph.fromEdgeSet_adj]

private theorem reachable_to_finiteConnectionEvent (ω : LatticeConfiguration)
    {u v : LatticeVertex}
    (h : (PottsDiscontinuity.rcInfiniteOpenGraph ω).Reachable u v) :
    ω ∈ connectionEvent u v := by
  rcases h with ⟨p⟩
  induction p with
  | nil =>
      refine ⟨∅, ?_, ?_⟩
      · simp
      · simp
  | @cons u v w huv p ih =>
      obtain ⟨he, hω⟩ := huv.1
      obtain ⟨F, hF, hopen⟩ := ih
      let e : squareLattice.edgeSet := ⟨s(u, v), he⟩
      refine ⟨insert e F, ?_, ?_⟩
      · have hfirst :
            ActualConnected (insert e F) u v := by
          have hAdj : (openGraph (insert e F)).Adj u v := by
            apply (openGraph_adj _ u v).mpr
            exact ⟨e, by simp, rfl⟩
          exact hAdj.reachable
        exact hfirst.trans (actualConnected_mono (Finset.subset_insert e F) hF)
      · aesop

/-- The finite-witness event is exactly reachability in the frozen infinite open graph. -/
theorem connectionEvent_iff_rcInfiniteReachable (u v : LatticeVertex)
    (ω : LatticeConfiguration) :
    ω ∈ connectionEvent u v ↔
      (PottsDiscontinuity.rcInfiniteOpenGraph ω).Reachable u v := by
  constructor
  · rintro ⟨F, hF, hopen⟩
    exact SimpleGraph.Reachable.mono
      (openGraph_subset_rcInfiniteOpenGraph ω F hopen) hF
  · exact reachable_to_finiteConnectionEvent ω

def rcInfiniteOpenGraphTranslationIso (a : LatticeVertex)
    (ω : LatticeConfiguration) :
    PottsDiscontinuity.rcInfiniteOpenGraph ω ≃g
      PottsDiscontinuity.rcInfiniteOpenGraph
        (latticeConfigurationTranslate a ω) where
  toEquiv := latticeTranslationIso a
  map_rel_iff' := by
    intro u v
    rw [PottsDiscontinuity.rcInfiniteOpenGraph,
      PottsDiscontinuity.rcInfiniteOpenGraph, SimpleGraph.fromEdgeSet_adj,
      SimpleGraph.fromEdgeSet_adj]
    constructor
    · rintro ⟨hmem, hne⟩
      change ∃ he : s(latticeTranslate a u, latticeTranslate a v) ∈ squareLattice.edgeSet,
        latticeConfigurationTranslate a ω
          ⟨s(latticeTranslate a u, latticeTranslate a v), he⟩ = true at hmem
      obtain ⟨hEdge, hOpen⟩ := hmem
      have hAdj : squareLattice.Adj (latticeTranslate a u) (latticeTranslate a v) :=
        squareLattice.mem_edgeSet.mp hEdge
      have hAdj' : squareLattice.Adj u v :=
        (squareLattice_adj_translate_iff a u v).mp hAdj
      have hBack : s(u, v) ∈ squareLattice.edgeSet := squareLattice.mem_edgeSet.mpr hAdj'
      let e' : squareLattice.edgeSet := ⟨s(latticeTranslate a u, latticeTranslate a v), hEdge⟩
      let e : squareLattice.edgeSet := ⟨s(u, v), hBack⟩
      have he : SimpleGraph.Iso.mapEdgeSet (latticeTranslationIso (-a)) e' = e := by
        apply Subtype.ext
        simp [e', e, latticeTranslationIso, latticeTranslate]
      have hOpen' : latticeConfigurationTranslate a ω e' = ω e := by
        rw [latticeConfigurationTranslate_apply, he]
      refine ⟨⟨hBack, ?_⟩, fun heq => hne (congrArg (latticeTranslate a) heq)⟩
      simpa [e', e] using hOpen'.symm.trans hOpen
    · rintro ⟨hmem, hne⟩
      change ∃ he : s(u, v) ∈ squareLattice.edgeSet,
        ω ⟨s(u, v), he⟩ = true at hmem
      obtain ⟨hEdge, hOpen⟩ := hmem
      have hAdj : squareLattice.Adj u v := squareLattice.mem_edgeSet.mp hEdge
      have hAdj' : squareLattice.Adj (latticeTranslate a u) (latticeTranslate a v) :=
        (squareLattice_adj_translate_iff a u v).mpr hAdj
      have hFwd : s(latticeTranslate a u, latticeTranslate a v) ∈ squareLattice.edgeSet :=
        squareLattice.mem_edgeSet.mpr hAdj'
      let e' : squareLattice.edgeSet := ⟨s(latticeTranslate a u, latticeTranslate a v), hFwd⟩
      let e : squareLattice.edgeSet := ⟨s(u, v), hEdge⟩
      have he : SimpleGraph.Iso.mapEdgeSet (latticeTranslationIso (-a)) e' = e := by
        apply Subtype.ext
        simp [e', e, latticeTranslationIso, latticeTranslate]
      have hOpen' : latticeConfigurationTranslate a ω e' = ω e := by
        rw [latticeConfigurationTranslate_apply, he]
      refine ⟨⟨hFwd, ?_⟩, fun heq => hne ((latticeTranslationIso a).injective heq)⟩
      simpa [e', e, latticeTranslationIso, latticeTranslate] using hOpen'.trans hOpen

theorem connectionEvent_translation (a u v : LatticeVertex) (ω : LatticeConfiguration) :
    latticeConfigurationTranslate a ω ∈
        connectionEvent (latticeTranslate a u) (latticeTranslate a v) ↔
      ω ∈ connectionEvent u v := by
  rw [connectionEvent_iff_rcInfiniteReachable, connectionEvent_iff_rcInfiniteReachable]
  exact SimpleGraph.Iso.reachable_iff
    (φ := rcInfiniteOpenGraphTranslationIso a ω)

/-- Every frozen limit has translation-invariant connection probabilities. -/
theorem isRCInfiniteVolumeLimit_connection_translation_invariant
    (θ : Parameters)
    (μ : Measure LatticeConfiguration)
    (hμ : PottsDiscontinuity.IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ)
    (a u v : LatticeVertex) :
    μ.real (connectionEvent (latticeTranslate a u) (latticeTranslate a v)) =
      μ.real (connectionEvent u v) := by
  have hmap := congrArg (fun ν : Measure LatticeConfiguration =>
    ν (connectionEvent (latticeTranslate a u) (latticeTranslate a v))) (PottsDiscontinuity.FK.isRCInfiniteVolumeLimit_interior_translation_invariant hμ a)
  rw [Measure.map_apply (latticeConfigurationTranslate_measurable a) (connectionEvent_isMeasurableSet (latticeTranslate a u) (latticeTranslate a v))] at hmap
  have hpre :
      (latticeConfigurationTranslate a) ⁻¹'
        connectionEvent (latticeTranslate a u) (latticeTranslate a v) =
        connectionEvent u v := by
    grind [connectionEvent_translation]
  rw [hpre] at hmap
  exact (congrArg ENNReal.toReal hmap).symm

/-- Connection probabilities in the canonical free limit are supermultiplicative. -/
theorem freeLimit_connection_supermultiplicative (q : Parameters)
    (x y : LatticeVertex) :
    Classical.choose (freeBoxLimit_existsUnique q)
      (connectionEvent (0, 0) (x.1 + y.1, x.2 + y.2)) ≥
      Classical.choose (freeBoxLimit_existsUnique q)
        (connectionEvent (0, 0) x) *
      Classical.choose (freeBoxLimit_existsUnique q)
        (connectionEvent x (x.1 + y.1, x.2 + y.2)) := by
  let ν :=
    Classical.choose (freeBoxLimit_existsUnique q)
  let approx := connectionApprox x (x.1 + y.1, x.2 + y.2)
  let approx' := connectionApprox (0, 0) x
  have hbound (n : ℕ) :
      ν.toFiniteMeasure (approx' n) *
        ν.toFiniteMeasure (approx n) ≤
          ν.toFiniteMeasure (connectionEvent (0, 0) (x.1 + y.1, x.2 + y.2)) := by
    have hfk := PottsDiscontinuity.FK.Internal.freeBoxLimit_clopen_positive_association
      q
      (connectionApprox_isClopen _ x n)
      (connectionApprox_isClopen x _ n)
      (connectionApprox_isUpperSet (0, 0) x n)
      (connectionApprox_isUpperSet x (x.1 + y.1, x.2 + y.2) n)
    have hsubset :
        approx' n ∩
          approx n ⊆
            connectionEvent (0, 0) (x.1 + y.1, x.2 + y.2) := by
      intro ω hω
      rcases (mem_connectionApprox_iff _ x n ω).mp hω.1 with
        ⟨i, hi, hconn₁, hopen₁⟩
      rcases (mem_connectionApprox_iff x _ n ω).mp hω.2 with
        ⟨j, hj, hconn₂, hopen₂⟩
      solve_by_elim [finiteConnection_union]
    have hmono := ν.toFiniteMeasure.apply_mono hsubset
    have hfk' :
        ν.toFiniteMeasure (approx' n) *
          ν.toFiniteMeasure (approx n) ≤
            ν.toFiniteMeasure (approx' n ∩
              approx n) := by
      assumption
    grind
  exact le_of_tendsto_of_tendsto' ((tendsto_connectionApprox_probability ν (0, 0) x).mul (tendsto_connectionApprox_probability ν x (x.1 + y.1, x.2 + y.2))) tendsto_const_nhds hbound

/-- The same supermultiplicativity holds for every measure satisfying the
frozen free infinite-volume limit characterization. -/
theorem isRCInfiniteVolumeLimit_connection_supermultiplicative
    (θ : Parameters) (μ : Measure LatticeConfiguration)
    (hμ : PottsDiscontinuity.IsRCInfiniteVolumeLimit
      θ.toP θ.toQ 0 μ) (x y : LatticeVertex) :
    μ.real (connectionEvent (0, 0) (x.1 + y.1, x.2 + y.2)) ≥
      μ.real (connectionEvent (0, 0) x) *
        μ.real (connectionEvent x (x.1 + y.1, x.2 + y.2)) := by
  have hν :=
    isRCInfiniteVolumeLimit_of_freeBox_tendsto ((Classical.choose_spec (freeBoxLimit_existsUnique θ)).1 (fun _ => (0, 0)) (fun n => n) origin_latticeBox_nested origin_latticeBox_exhaustive)
  rw [(PottsDiscontinuity.rc_limit_unique hμ hν)]
  exact freeLimit_connection_supermultiplicative θ x y

/-- In the free limit, translation invariance turns the FKG inequality into
supermultiplicativity of probabilities based at the origin. -/
theorem isRCInfiniteVolumeLimit_origin_connection_supermultiplicative
    (θ : Parameters) (μ : Measure LatticeConfiguration)
    (hμ : PottsDiscontinuity.IsRCInfiniteVolumeLimit
      θ.toP θ.toQ 0 μ) (x y : LatticeVertex) :
    μ.real (connectionEvent (0, 0) (x.1 + y.1, x.2 + y.2)) ≥
      μ.real (connectionEvent (0, 0) x) *
        μ.real (connectionEvent (0, 0) y) := by
  have hmul := isRCInfiniteVolumeLimit_connection_supermultiplicative θ μ hμ x y
  have hxy :
      μ.real (connectionEvent x (x.1 + y.1, x.2 + y.2)) =
        μ.real (connectionEvent (0, 0) y) := by
    simpa [latticeTranslate] using (isRCInfiniteVolumeLimit_connection_translation_invariant θ μ hμ (-x) x (x.1 + y.1, x.2 + y.2)).symm
  grind

end

end PottsDiscontinuity.CorrLength
