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
  (exists_surjective_nat (Finset squareLattice.edgeSet)).choose

theorem finiteEdgeSetEnumeration_surjective :
    Function.Surjective finiteEdgeSetEnumeration :=
  (exists_surjective_nat (Finset squareLattice.edgeSet)).choose_spec

/-- The event that a fixed finite edge set is open and connects the endpoints. -/
def finiteConnectionEvent (u v : LatticeVertex) (F : Finset squareLattice.edgeSet) :
    Set LatticeConfiguration :=
  {ω | ActualConnected squareLattice F u v ∧ ω ∈ LatticeConfiguration.allOpen F}

/-- Finite approximations to connection, enumerated by finite edge sets. -/
def connectionApprox (u v : LatticeVertex) (n : ℕ) : Set LatticeConfiguration :=
  ⋃ i : {i : ℕ // i ≤ n}, finiteConnectionEvent u v (finiteEdgeSetEnumeration i)

/-- Connection by some finite set of open edges. -/
def connectionEvent (u v : LatticeVertex) : Set LatticeConfiguration :=
  {ω | ∃ F : Finset squareLattice.edgeSet,
    ActualConnected squareLattice F u v ∧ ω ∈ LatticeConfiguration.allOpen F}

theorem mem_connectionApprox_iff (u v : LatticeVertex) (n : ℕ)
    (ω : LatticeConfiguration) :
    ω ∈ connectionApprox u v n ↔
      ∃ i ≤ n, ActualConnected squareLattice (finiteEdgeSetEnumeration i) u v ∧
        ω ∈ LatticeConfiguration.allOpen (finiteEdgeSetEnumeration i) := by
  simp [connectionApprox, finiteConnectionEvent, Subtype.exists, and_left_comm]

theorem connectionApprox_mono (u v : LatticeVertex) :
    Monotone (connectionApprox u v) := by
  intro n m hnm ω hω
  rcases (mem_connectionApprox_iff u v n ω).mp hω with ⟨i, hi, hconn, hopen⟩
  exact (mem_connectionApprox_iff u v m ω).mpr ⟨i, hi.trans hnm, hconn, hopen⟩

theorem connectionEvent_eq_iUnion_connectionApprox (u v : LatticeVertex) :
    connectionEvent u v = ⋃ n, connectionApprox u v n := by
  ext ω
  simp only [connectionEvent, Set.mem_ofPred, Set.mem_iUnion, mem_connectionApprox_iff]
  exact ⟨fun ⟨F, hconn, hopen⟩ => by
      obtain ⟨i, rfl⟩ := finiteEdgeSetEnumeration_surjective F
      exact ⟨i, i, le_rfl, hconn, hopen⟩,
    fun ⟨_, i, _, hconn, hopen⟩ => ⟨finiteEdgeSetEnumeration i, hconn, hopen⟩⟩

theorem connectionApprox_isClopen (u v : LatticeVertex) (n : ℕ) :
    IsClopen (connectionApprox u v n) := by
  refine isClopen_iUnion_of_finite fun i => ?_
  by_cases hconn : ActualConnected squareLattice (finiteEdgeSetEnumeration i) u v
  · simpa [connectionApprox, finiteConnectionEvent, hconn] using
      LatticeConfiguration.allOpen_isClopen (finiteEdgeSetEnumeration i)
  · simpa [connectionApprox, finiteConnectionEvent, hconn] using
      (isClopen_empty : IsClopen (∅ : Set LatticeConfiguration))

theorem finiteConnectionEvent_isUpperSet (u v : LatticeVertex)
    (F : Finset squareLattice.edgeSet) :
    IsUpperSet (finiteConnectionEvent u v F) := by
  intro ω η hωη hω
  refine ⟨hω.1, fun e he => ?_⟩
  have h := hωη e
  rw [hω.2 e he] at h
  exact eq_top_iff.mpr h

theorem connectionApprox_isUpperSet (u v : LatticeVertex) (n : ℕ) :
    IsUpperSet (connectionApprox u v n) := by
  intro ω η hωη hω
  rcases (mem_connectionApprox_iff u v n ω).mp hω with ⟨i, hi, hconn, hopen⟩
  exact (mem_connectionApprox_iff u v n η).mpr
    ⟨i, hi, hconn, (finiteConnectionEvent_isUpperSet u v _ hωη ⟨hconn, hopen⟩).2⟩

theorem connectionEvent_isMeasurableSet (u v : LatticeVertex) :
    MeasurableSet (connectionEvent u v) := by
  rw [connectionEvent_eq_iUnion_connectionApprox]
  exact MeasurableSet.iUnion fun n => (connectionApprox_isClopen u v n).2.measurableSet

theorem tendsto_connectionApprox_probability (ν : ProbabilityMeasure LatticeConfiguration)
    (u v : LatticeVertex) :
    Tendsto (fun n : ℕ => ν.toFiniteMeasure (connectionApprox u v n)) atTop
      (𝓝 (ν.toFiniteMeasure (connectionEvent u v))) := by
  have h := (ν.toFiniteMeasure.tendsto_measure_iUnion_accumulate (f := connectionApprox u v)).congr'
    (Filter.Eventually.of_forall fun n => congrArg ν.toFiniteMeasure <| Set.ext fun ω => by
      simp only [Set.mem_accumulate]
      exact ⟨fun ⟨m, hmn, hm⟩ => connectionApprox_mono u v hmn hm, fun hn => ⟨n, le_rfl, hn⟩⟩)
  simpa [ProbabilityMeasure.toFiniteMeasure_apply,
    connectionEvent_eq_iUnion_connectionApprox] using h

theorem finiteConnection_union (u v w : LatticeVertex)
    (F G : Finset squareLattice.edgeSet)
    (hF : ActualConnected squareLattice F u v)
    (hG : ActualConnected squareLattice G v w)
    (ω : LatticeConfiguration)
    (hopenF : ω ∈ LatticeConfiguration.allOpen F)
    (hopenG : ω ∈ LatticeConfiguration.allOpen G) :
    ω ∈ connectionEvent u w :=
  ⟨F ∪ G, (actualConnected_mono Finset.subset_union_left hF).trans
    (actualConnected_mono Finset.subset_union_right hG),
    fun e he => (Finset.mem_union.mp he).elim (hopenF e) (hopenG e)⟩

private theorem openGraph_subset_rcInfiniteOpenGraph (ω : LatticeConfiguration)
    (F : Finset squareLattice.edgeSet)
    (hopen : ω ∈ LatticeConfiguration.allOpen F) :
    openGraph squareLattice F ≤ PottsDiscontinuity.rcInfiniteOpenGraph ω := by
  intro u v huv
  obtain ⟨e, heF, heq⟩ := (openGraph_adj squareLattice F u v).mp huv
  have hEdge : s(u, v) ∈ squareLattice.edgeSet := heq ▸ e.property
  rw [PottsDiscontinuity.rcInfiniteOpenGraph, SimpleGraph.fromEdgeSet_adj]
  exact ⟨⟨hEdge, by rw [show (⟨s(u, v), hEdge⟩ : squareLattice.edgeSet) = e from Subtype.ext heq.symm]; exact hopen e heF⟩,
    squareLattice.not_isDiag_of_mem_edgeSet hEdge⟩

private theorem reachable_to_finiteConnectionEvent (ω : LatticeConfiguration)
    {u v : LatticeVertex}
    (h : (PottsDiscontinuity.rcInfiniteOpenGraph ω).Reachable u v) :
    ω ∈ connectionEvent u v := by
  rcases h with ⟨p⟩
  induction p with
  | nil => exact ⟨∅, by simp, by simp [LatticeConfiguration.allOpen]⟩
  | @cons u v w huv _ ih =>
      obtain ⟨he, hω⟩ : ∃ he : s(u, v) ∈ squareLattice.edgeSet, ω ⟨s(u, v), he⟩ = true := huv.1
      obtain ⟨F, hF, hopen⟩ := ih
      let e : squareLattice.edgeSet := ⟨s(u, v), he⟩
      refine ⟨insert e F, SimpleGraph.Adj.reachable ((openGraph_adj squareLattice (insert e F) u v).mpr
          ⟨e, by simp [e], rfl⟩) |>.trans (actualConnected_mono (Finset.subset_insert e F) hF),
        fun f hf => (Finset.mem_insert.mp hf).elim (fun h => h ▸ hω) (hopen f)⟩

/-- The finite-witness event is exactly reachability in the frozen infinite open graph. -/
theorem connectionEvent_iff_rcInfiniteReachable (u v : LatticeVertex)
    (ω : LatticeConfiguration) :
    ω ∈ connectionEvent u v ↔
      (PottsDiscontinuity.rcInfiniteOpenGraph ω).Reachable u v :=
  ⟨fun ⟨F, hF, hopen⟩ => SimpleGraph.Reachable.mono (openGraph_subset_rcInfiniteOpenGraph ω F hopen) hF,
    reachable_to_finiteConnectionEvent ω⟩

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
    · rintro ⟨⟨hEdge, hOpen⟩, hne⟩
      have hBack : s(u, v) ∈ squareLattice.edgeSet :=
        squareLattice.mem_edgeSet.mpr ((squareLattice_adj_translate_iff a u v).mp
          (squareLattice.mem_edgeSet.mp hEdge))
      refine ⟨⟨hBack, ?_⟩, fun heq => hne (congrArg (latticeTranslate a) heq)⟩
      rw [← hOpen, latticeConfigurationTranslate_apply]
      congr 1; apply Subtype.ext; simp [latticeTranslationIso, latticeTranslate]
    · rintro ⟨⟨hEdge, hOpen⟩, hne⟩
      have hFwd : s(latticeTranslate a u, latticeTranslate a v) ∈ squareLattice.edgeSet :=
        squareLattice.mem_edgeSet.mpr ((squareLattice_adj_translate_iff a u v).mpr
          (squareLattice.mem_edgeSet.mp hEdge))
      refine ⟨⟨hFwd, ?_⟩, fun heq => hne ((latticeTranslationIso a).injective heq)⟩
      rw [← hOpen, latticeConfigurationTranslate_apply]
      congr 1; apply Subtype.ext; simp [latticeTranslationIso, latticeTranslate]

theorem connectionEvent_translation (a u v : LatticeVertex) (ω : LatticeConfiguration) :
    latticeConfigurationTranslate a ω ∈
        connectionEvent (latticeTranslate a u) (latticeTranslate a v) ↔
      ω ∈ connectionEvent u v := by
  rw [connectionEvent_iff_rcInfiniteReachable, connectionEvent_iff_rcInfiniteReachable]
  exact SimpleGraph.Iso.reachable_iff
    (φ := rcInfiniteOpenGraphTranslationIso a ω) (u := u) (v := v)

/-- Every frozen limit has translation-invariant connection probabilities. -/
theorem isRCInfiniteVolumeLimit_connection_translation_invariant
    (p : Set.Icc (0 : ℝ) 1) (q : Set.Ioi (0 : ℝ)) (hq : 1 ≤ (q : ℝ))
    (μ : Measure LatticeConfiguration)
    (hμ : PottsDiscontinuity.IsRCInfiniteVolumeLimit p q 0 μ)
    (a u v : LatticeVertex) :
    μ.real (connectionEvent (latticeTranslate a u) (latticeTranslate a v)) =
      μ.real (connectionEvent u v) := by
  have hmap := congrArg (fun ν : Measure LatticeConfiguration =>
    ν (connectionEvent (latticeTranslate a u) (latticeTranslate a v)))
    (PottsDiscontinuity.FK.isRCInfiniteVolumeLimit_translation_invariant p q hq 0 μ hμ a)
  rw [Measure.map_apply (latticeConfigurationTranslate_measurable a)
      (connectionEvent_isMeasurableSet _ _),
    show latticeConfigurationTranslate a ⁻¹'
      connectionEvent (latticeTranslate a u) (latticeTranslate a v) = connectionEvent u v from
      Set.ext (connectionEvent_translation a u v)] at hmap
  simpa [Measure.real_def] using (congrArg ENNReal.toReal hmap).symm

/-- Connection probabilities in the canonical free limit are supermultiplicative. -/
theorem freeLimit_connection_supermultiplicative (q : Parameters)
    (x y : LatticeVertex) :
    Classical.choose (freeBoxLimit_existsUnique q)
      (connectionEvent (0, 0) (x.1 + y.1, x.2 + y.2)) ≥
      Classical.choose (freeBoxLimit_existsUnique q)
        (connectionEvent (0, 0) x) *
      Classical.choose (freeBoxLimit_existsUnique q)
        (connectionEvent x (x.1 + y.1, x.2 + y.2)) := by
  let ν : ProbabilityMeasure LatticeConfiguration := Classical.choose (freeBoxLimit_existsUnique q)
  have hprod := (tendsto_connectionApprox_probability ν (0, 0) x).mul
    (tendsto_connectionApprox_probability ν x (x.1 + y.1, x.2 + y.2))
  have hbound (n : ℕ) :
      ν.toFiniteMeasure (connectionApprox (0, 0) x n) *
        ν.toFiniteMeasure (connectionApprox x (x.1 + y.1, x.2 + y.2) n) ≤
          ν.toFiniteMeasure (connectionEvent (0, 0) (x.1 + y.1, x.2 + y.2)) := by
    have hfk :
        ν.toFiniteMeasure (connectionApprox (0, 0) x n) *
          ν.toFiniteMeasure (connectionApprox x (x.1 + y.1, x.2 + y.2) n) ≤
            ν.toFiniteMeasure (connectionApprox (0, 0) x n ∩
              connectionApprox x (x.1 + y.1, x.2 + y.2) n) := by
      apply NNReal.coe_le_coe.mp
      simpa only [Prod.forall, FiniteMeasure.self_eq_mass_mul_normalize,
        ProbabilityMeasure.mass_toFiniteMeasure,
        ProbabilityMeasure.toFiniteMeasure_normalize_eq_self, one_mul, NNReal.coe_mul, ν] using
        PottsDiscontinuity.FK.Internal.freeBoxLimit_clopen_positive_association
          q (connectionApprox (0, 0) x n) (connectionApprox x (x.1 + y.1, x.2 + y.2) n)
          (connectionApprox_isClopen (0, 0) x n)
          (connectionApprox_isClopen x (x.1 + y.1, x.2 + y.2) n)
          (connectionApprox_isUpperSet (0, 0) x n)
          (connectionApprox_isUpperSet x (x.1 + y.1, x.2 + y.2) n)
    refine hfk.trans (ν.toFiniteMeasure.apply_mono fun ω hω => ?_)
    rcases (mem_connectionApprox_iff (0, 0) x n ω).mp hω.1 with ⟨i, _, hconn₁, hopen₁⟩
    rcases (mem_connectionApprox_iff x (x.1 + y.1, x.2 + y.2) n ω).mp hω.2 with ⟨j, _, hconn₂, hopen₂⟩
    exact finiteConnection_union (0, 0) x (x.1 + y.1, x.2 + y.2)
      (finiteEdgeSetEnumeration i) (finiteEdgeSetEnumeration j) hconn₁ hconn₂ ω hopen₁ hopen₂
  simpa only [Prod.forall, ge_iff_le, FiniteMeasure.self_eq_mass_mul_normalize,
    ProbabilityMeasure.mass_toFiniteMeasure, ProbabilityMeasure.toFiniteMeasure_normalize_eq_self,
    one_mul, ν] using le_of_tendsto_of_tendsto' hprod tendsto_const_nhds hbound

/-- The same supermultiplicativity holds for every measure satisfying the
frozen free infinite-volume limit characterization. -/
theorem isRCInfiniteVolumeLimit_connection_supermultiplicative
    (θ : Parameters) (μ : Measure LatticeConfiguration)
    (hμ : PottsDiscontinuity.IsRCInfiniteVolumeLimit
      θ.toP θ.toQ 0 μ) (x y : LatticeVertex) :
    μ.real (connectionEvent (0, 0) (x.1 + y.1, x.2 + y.2)) ≥
      μ.real (connectionEvent (0, 0) x) *
        μ.real (connectionEvent x (x.1 + y.1, x.2 + y.2)) := by
  let ν : ProbabilityMeasure LatticeConfiguration := Classical.choose (freeBoxLimit_existsUnique θ)
  have hν : PottsDiscontinuity.IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 ν.toMeasure :=
    isRCInfiniteVolumeLimit_of_freeBox_tendsto θ ν
      ((Classical.choose_spec (freeBoxLimit_existsUnique θ)).1 (fun _ => (0, 0)) (fun n => n)
        origin_latticeBox_nested origin_latticeBox_exhaustive)
  rw [PottsDiscontinuity.rc_limit_unique θ.toP θ.toQ 0 μ ν.toMeasure hμ hν]
  have hNN :
      ν.toFiniteMeasure (connectionEvent (0, 0) x) *
        ν.toFiniteMeasure (connectionEvent x (x.1 + y.1, x.2 + y.2)) ≤
          ν.toFiniteMeasure (connectionEvent (0, 0) (x.1 + y.1, x.2 + y.2)) := by
    simpa only [Prod.forall, FiniteMeasure.self_eq_mass_mul_normalize,
      ProbabilityMeasure.mass_toFiniteMeasure,
      ProbabilityMeasure.toFiniteMeasure_normalize_eq_self, one_mul, ge_iff_le, ν] using
      freeLimit_connection_supermultiplicative θ x y
  simpa [ProbabilityMeasure.measureReal_eq_coe_coeFn] using (by exact_mod_cast hNN :
    ((ν.toFiniteMeasure (connectionEvent (0, 0) x) : NNReal) : ℝ) *
      ((ν.toFiniteMeasure (connectionEvent x (x.1 + y.1, x.2 + y.2)) : NNReal) : ℝ) ≤
        ((ν.toFiniteMeasure (connectionEvent (0, 0) (x.1 + y.1, x.2 + y.2)) : NNReal) : ℝ))

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
  rwa [show μ.real (connectionEvent x (x.1 + y.1, x.2 + y.2)) = μ.real (connectionEvent (0, 0) y) by
    simpa [latticeTranslate] using (isRCInfiniteVolumeLimit_connection_translation_invariant
      θ.toP θ.toQ θ.property μ hμ (-x) x (x.1 + y.1, x.2 + y.2)).symm] at hmul

end

end PottsDiscontinuity.CorrLength
