module
public import Mathlib

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
noncomputable def finiteEdgeSetEnumeration  :=
  (exists_surjective_nat (Finset squareLattice.edgeSet)).choose

theorem finiteEdgeSetEnumeration_surjective :
    Function.Surjective finiteEdgeSetEnumeration :=
  (exists_surjective_nat (Finset squareLattice.edgeSet)).choose_spec

/-- The event that a fixed finite edge set is open and connects the endpoints. -/
def finiteConnectionEvent (u v : LatticeVertex) (F : Finset squareLattice.edgeSet)  :=
  {ω | ActualConnected squareLattice F u v ∧ ω ∈ LatticeConfiguration.allOpen F}

/-- Finite approximations to connection, enumerated by finite edge sets. -/
def connectionApprox (u v : LatticeVertex) (n : ℕ)  :=
  ⋃ i : {i : ℕ // i ≤ n}, finiteConnectionEvent u v (finiteEdgeSetEnumeration i)

/-- Connection by some finite set of open edges. -/
def connectionEvent (u v : LatticeVertex)  :=
  {ω | ∃ F : Finset squareLattice.edgeSet,
    ActualConnected squareLattice F u v ∧ ω ∈ LatticeConfiguration.allOpen F}

section

variable (u v : LatticeVertex)


theorem mem_connectionApprox_iff  (n : ℕ)
    (ω : LatticeConfiguration) :
    ω ∈ connectionApprox u v n ↔
      ∃ i ≤ n, ActualConnected squareLattice (finiteEdgeSetEnumeration i) u v ∧
        ω ∈ LatticeConfiguration.allOpen (finiteEdgeSetEnumeration i) := by
  rw [connectionApprox]
  aesop

theorem connectionApprox_mono  :
    Monotone (connectionApprox u v) := by
  intro n m hnm ω hω
  rcases (mem_connectionApprox_iff u v n ω).mp hω with ⟨i, hi, hconn, hopen⟩
  exact (mem_connectionApprox_iff u v m ω).mpr
    ⟨i, hi.trans hnm, hconn, hopen⟩

theorem connectionEvent_eq_iUnion_connectionApprox  :
    connectionEvent u v = ⋃ n, connectionApprox u v n := by
  ext ω
  constructor
  · rintro ⟨F, hconn, hopen⟩
    obtain ⟨i, hi⟩ := finiteEdgeSetEnumeration_surjective F
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    
    
    exact (mem_connectionApprox_iff u v i ω).mpr ⟨i, le_rfl,  by
                                                                simpa [hi] using hconn ,  by
                                                                        simpa [hi] using hopen ⟩
  · intro h
    rcases Set.mem_iUnion.mp h with ⟨n, hn⟩
    rcases (mem_connectionApprox_iff u v n ω).mp hn with ⟨i, hi, hconn, hopen⟩
    exact ⟨finiteEdgeSetEnumeration i, hconn, hopen⟩

theorem connectionApprox_isClopen  (n : ℕ) :
    IsClopen (connectionApprox u v n) := by
  apply isClopen_iUnion_of_finite
  intro i
  by_cases hconn : ActualConnected squareLattice (finiteEdgeSetEnumeration i) u v
  · simpa [finiteConnectionEvent, hconn] using
      LatticeConfiguration.allOpen_isClopen (finiteEdgeSetEnumeration i)
  · simpa [finiteConnectionEvent, hconn] using
       isClopen_empty 

theorem finiteConnectionEvent_isUpperSet 
    (F : Finset squareLattice.edgeSet) :
    IsUpperSet (finiteConnectionEvent u v F) := by
  intro ω η hωη hω
  refine ⟨hω.1, ?_⟩
  intro e he
  
  have hopen := hω.2 e he
  aesop

theorem connectionApprox_isUpperSet  (n : ℕ) :
    IsUpperSet (connectionApprox u v n) := by
  intro ω η hωη hω
  rcases (mem_connectionApprox_iff u v n ω).mp hω with ⟨i, hi, hconn, hopen⟩
  refine (mem_connectionApprox_iff u v n η).mpr ⟨i, hi, hconn, ?_⟩
  intro e he
  aesop

theorem connectionEvent_isMeasurableSet  :
    MeasurableSet (connectionEvent u v) := by
  rw [connectionEvent_eq_iUnion_connectionApprox]
  exact MeasurableSet.iUnion fun n => (connectionApprox_isClopen u v n).2.measurableSet

end

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
    · aesop
  have h := ν.toFiniteMeasure.tendsto_measure_iUnion_accumulate
    (f := connectionApprox u v)
  
  simpa [connectionEvent_eq_iUnion_connectionApprox] using  by
                                                         simp_all 

theorem finiteConnection_union (u v w : LatticeVertex)
    (F G : Finset squareLattice.edgeSet)
    (hF : ActualConnected squareLattice F u v)
    (hG : ActualConnected squareLattice G v w)
    (ω : LatticeConfiguration)
    (hopenF : ω ∈ LatticeConfiguration.allOpen F)
    (hopenG : ω ∈ LatticeConfiguration.allOpen G) :
    ω ∈ connectionEvent u w := Exists.intro (F ∪ G)
                                 ⟨SimpleGraph.Reachable.trans (actualConnected_mono Finset.subset_union_left hF)
                                     (actualConnected_mono Finset.subset_union_right hG),
                                   fun e he => Or.casesOn (Finset.mem_union.mp he) (hopenF e) (hopenG e)⟩

private theorem openGraph_subset_rcInfiniteOpenGraph (ω : LatticeConfiguration)
    (F : Finset squareLattice.edgeSet)
    (hopen : ω ∈ LatticeConfiguration.allOpen F) :
    openGraph squareLattice F ≤ PottsDiscontinuity.rcInfiniteOpenGraph ω := by
  intro u v huv
  obtain ⟨e, heF, heq⟩ := (openGraph_adj squareLattice F u v).mp huv
  
  
  have hω : ω ⟨s(u, v),  by
                           rw [← heq]
                           exact e.property ⟩ = true := by
    rw [(Subtype.ext heq.symm : (⟨s(u, v),  by
                          rw [← heq]
                          exact e.property ⟩ ) = e)]
    exact hopen e heF
  rw [PottsDiscontinuity.rcInfiniteOpenGraph, SimpleGraph.fromEdgeSet_adj]
  grind

private theorem reachable_to_finiteConnectionEvent (ω : LatticeConfiguration)
    {u v : LatticeVertex}
    (h : (PottsDiscontinuity.rcInfiniteOpenGraph ω).Reachable u v) :
    ω ∈ connectionEvent u v := by
  rcases h with ⟨p⟩
  induction p with
  | nil =>
      refine ⟨∅, ?_, ?_⟩
      all_goals simp_all
  | @cons u v w huv p ih =>
      
      have hEdge := huv.1
      
      obtain ⟨he, hω⟩ := hEdge
      obtain ⟨F, hF, hopen⟩ := ih
      let e : squareLattice.edgeSet := ⟨s(u, v), he⟩
      refine ⟨insert e F, ?_, ?_⟩
      · have hfirst :
            ActualConnected squareLattice (insert e F) u v := by
          have hAdj : (openGraph squareLattice (insert e F)).Adj u v := by
            apply (openGraph_adj squareLattice (insert e F) u v).mpr
            
            exact ⟨e, by simp , rfl⟩
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
    rw [PottsDiscontinuity.rcInfiniteOpenGraph, PottsDiscontinuity.rcInfiniteOpenGraph]
    constructor
    · rintro ⟨hmem, hne⟩
      change ∃ he : s(latticeTranslate a u, latticeTranslate a v) ∈ squareLattice.edgeSet,
        latticeConfigurationTranslate a ω
          ⟨s(latticeTranslate a u, latticeTranslate a v), he⟩ = true at hmem
      obtain ⟨hEdge, hOpen⟩ := hmem
      
      have hAdj'  :=
        (squareLattice_adj_translate_iff a u v).mp (squareLattice.mem_edgeSet.mp hEdge)
      
      let e' : squareLattice.edgeSet := ⟨s(latticeTranslate a u, latticeTranslate a v), hEdge⟩
      let e : squareLattice.edgeSet := ⟨s(u, v),  squareLattice.mem_edgeSet.mpr hAdj' ⟩
      have he : SimpleGraph.Iso.mapEdgeSet (latticeTranslationIso (-a)) e' = e := by
        apply Subtype.ext
        simp [e', e, latticeTranslationIso, latticeTranslate]
      all_goals aesop
    · rintro ⟨hmem, hne⟩
      change ∃ he : s(u, v) ∈ squareLattice.edgeSet,
        ω ⟨s(u, v), he⟩ = true at hmem
      obtain ⟨hEdge, hOpen⟩ := hmem
      
      
      have hFwd  :=
        squareLattice.mem_edgeSet.mpr ((squareLattice_adj_translate_iff a u v).mpr (squareLattice.mem_edgeSet.mp hEdge))
      let e' : squareLattice.edgeSet := ⟨s(latticeTranslate a u, latticeTranslate a v), hFwd⟩
      let e : squareLattice.edgeSet := ⟨s(u, v), hEdge⟩
      have he : SimpleGraph.Iso.mapEdgeSet (latticeTranslationIso (-a)) e' = e := by
        apply Subtype.ext
        simp [e', e, latticeTranslationIso, latticeTranslate]
      have hOpen' : latticeConfigurationTranslate a ω e' = ω e := by
        rw [latticeConfigurationTranslate_apply, he]
      refine ⟨⟨hFwd, ?_⟩, fun heq => hne ((latticeTranslationIso a).injective heq)⟩
      simpa [latticeTranslationIso] using hOpen'.trans hOpen

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
  
  
  have hmap := congrArg (fun ν  =>
    ν (connectionEvent (latticeTranslate a u) (latticeTranslate a v))) (PottsDiscontinuity.FK.isRCInfiniteVolumeLimit_translation_invariant
                                                                          p q hq 0 μ hμ a)
  rw [Measure.map_apply (latticeConfigurationTranslate_measurable a) (connectionEvent_isMeasurableSet (latticeTranslate a u) (latticeTranslate a v))] at hmap
  have hpre :
       latticeConfigurationTranslate a  ⁻¹'
        connectionEvent (latticeTranslate a u) (latticeTranslate a v) =
        connectionEvent u v := by
    grind [connectionEvent_translation]
  rw [hpre] at hmap
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
  let ν  :=
    Classical.choose (freeBoxLimit_existsUnique q)
  
  
  
  have hbound (n : ℕ) :
      ν.toFiniteMeasure (connectionApprox (0, 0) x n) *
        ν.toFiniteMeasure (connectionApprox x (x.1 + y.1, x.2 + y.2) n) ≤
          ν.toFiniteMeasure (connectionEvent (0, 0) (x.1 + y.1, x.2 + y.2)) := by
    have hfk := PottsDiscontinuity.FK.Internal.freeBoxLimit_clopen_positive_association
      q (connectionApprox (0, 0) x n)
      (connectionApprox x (x.1 + y.1, x.2 + y.2) n)
      (connectionApprox_isClopen (0, 0) x n)
      (connectionApprox_isClopen x (x.1 + y.1, x.2 + y.2) n)
      (connectionApprox_isUpperSet (0, 0) x n)
      (connectionApprox_isUpperSet x (x.1 + y.1, x.2 + y.2) n)
    have hsubset :
        connectionApprox (0, 0) x n ∩
          connectionApprox x (x.1 + y.1, x.2 + y.2) n ⊆
            connectionEvent (0, 0) (x.1 + y.1, x.2 + y.2) := by
      intro ω hω
      rcases (mem_connectionApprox_iff (0, 0) x n ω).mp hω.1 with
        ⟨i, hi, hconn₁, hopen₁⟩
      rcases (mem_connectionApprox_iff x (x.1 + y.1, x.2 + y.2) n ω).mp hω.2 with
        ⟨j, hj, hconn₂, hopen₂⟩
      exact finiteConnection_union (0, 0) x (x.1 + y.1, x.2 + y.2)
        (finiteEdgeSetEnumeration i) (finiteEdgeSetEnumeration j)
        hconn₁ hconn₂ ω hopen₁ hopen₂
    have hmono := ν.toFiniteMeasure.apply_mono hsubset
    have hfk' :
        ν.toFiniteMeasure (connectionApprox (0, 0) x n) *
          ν.toFiniteMeasure (connectionApprox x (x.1 + y.1, x.2 + y.2) n) ≤
            ν.toFiniteMeasure (connectionApprox (0, 0) x n ∩
              connectionApprox x (x.1 + y.1, x.2 + y.2) n) := by
      assumption
    have hmono'  := hmono
    exact hfk'.trans hmono'
  
  simpa only [FiniteMeasure.self_eq_mass_mul_normalize, ProbabilityMeasure.mass_toFiniteMeasure, ProbabilityMeasure.toFiniteMeasure_normalize_eq_self, one_mul, ν] using  le_of_tendsto_of_tendsto' ((tendsto_connectionApprox_probability ν (0, 0) x).mul (tendsto_connectionApprox_probability ν x (x.1 + y.1, x.2 + y.2)))  tendsto_const_nhds  hbound 

section

variable (θ : Parameters) (μ : Measure LatticeConfiguration) (hμ : PottsDiscontinuity.IsRCInfiniteVolumeLimit
      θ.toP θ.toQ 0 μ) (x y : LatticeVertex)
include hμ

/-- The same supermultiplicativity holds for every measure satisfying the
frozen free infinite-volume limit characterization. -/
theorem isRCInfiniteVolumeLimit_connection_supermultiplicative
     :
    μ.real (connectionEvent (0, 0) (x.1 + y.1, x.2 + y.2)) ≥
      μ.real (connectionEvent (0, 0) x) *
        μ.real (connectionEvent x (x.1 + y.1, x.2 + y.2)) := by
  let ν  :=
    Classical.choose (freeBoxLimit_existsUnique θ)
  
  
  
  rw [ PottsDiscontinuity.rc_limit_unique θ.toP θ.toQ 0 μ ν.toMeasure hμ (isRCInfiniteVolumeLimit_of_freeBox_tendsto θ ν ((Classical.choose_spec (freeBoxLimit_existsUnique θ)).1
                                                                                                                              (fun _ => (0, 0)) (fun n => n)
                                                                                                                              origin_latticeBox_nested origin_latticeBox_exhaustive)) ]
  have h := freeLimit_connection_supermultiplicative θ x y
  
  
  simpa  using  by
                                                               exact_mod_cast  by
                                                                                 assumption  

/-- In the free limit, translation invariance turns the FKG inequality into
supermultiplicativity of probabilities based at the origin. -/
theorem isRCInfiniteVolumeLimit_origin_connection_supermultiplicative
     :
    μ.real (connectionEvent (0, 0) (x.1 + y.1, x.2 + y.2)) ≥
      μ.real (connectionEvent (0, 0) x) *
        μ.real (connectionEvent (0, 0) y) := by
  have hmul := isRCInfiniteVolumeLimit_connection_supermultiplicative θ μ hμ x y
  
  
  rw [(by
         simpa [latticeTranslate] using (isRCInfiniteVolumeLimit_connection_translation_invariant
                                           θ.toP θ.toQ θ.property μ hμ (-x) x (x.1 + y.1, x.2 + y.2)).symm :
      μ.real (connectionEvent x (x.1 + y.1, x.2 + y.2)) =
        μ.real (connectionEvent (0, 0) y))] at hmul
  exact hmul

end

end

end PottsDiscontinuity.CorrLength
