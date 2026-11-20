module

public import PottsDiscontinuity.Duality.BondStates
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

section

variable (u v : LatticeVertex)

/-- The event that a fixed finite edge set is open and connects the endpoints. -/
def finiteConnectionEvent (F : Finset squareLattice.edgeSet) :
    Set LatticeConfiguration :=
  {ω | ActualConnected squareLattice F u v ∧ ω ∈ LatticeConfiguration.allOpen F}

/-- Finite approximations to connection, enumerated by finite edge sets. -/
def connectionApprox (n : ℕ) : Set LatticeConfiguration :=
  ⋃ i : {i : ℕ // i ≤ n}, finiteConnectionEvent u v (finiteEdgeSetEnumeration i)

/-- Connection by some finite set of open edges. -/
def connectionEvent : Set LatticeConfiguration :=
  {ω | ∃ F : Finset squareLattice.edgeSet,
    ActualConnected squareLattice F u v ∧ ω ∈ LatticeConfiguration.allOpen F}

theorem mem_connectionApprox_iff (n : ℕ)
    (ω : LatticeConfiguration) :
    ω ∈ connectionApprox u v n ↔
      ∃ i ≤ n, ActualConnected squareLattice (finiteEdgeSetEnumeration i) u v ∧
        ω ∈ LatticeConfiguration.allOpen (finiteEdgeSetEnumeration i) := by
  rw [connectionApprox]
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨i, hconn, hopen⟩
    grind
  · rintro ⟨i, hi, hconn, hopen⟩
    exact ⟨⟨i, hi⟩, hconn, hopen⟩

theorem connectionApprox_mono :
    Monotone (connectionApprox u v) := by
  intro n m hnm ω hω
  grind [mem_connectionApprox_iff]

theorem connectionEvent_eq_iUnion_connectionApprox :
    connectionEvent u v = ⋃ n, connectionApprox u v n := by
  ext ω
  constructor
  · rintro ⟨F, hconn, hopen⟩
    obtain ⟨i, hi⟩ := finiteEdgeSetEnumeration_surjective F
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    grind only [mem_connectionApprox_iff]
  · intro h
    rcases Set.mem_iUnion.mp h with ⟨n, hn⟩
    rcases (mem_connectionApprox_iff u v n ω).mp hn with ⟨i, hi, hconn, hopen⟩
    exact ⟨finiteEdgeSetEnumeration i, hconn, hopen⟩

theorem connectionApprox_isClopen (n : ℕ) :
    IsClopen (connectionApprox u v n) := by
  apply isClopen_iUnion_of_finite
  intro i
  by_cases hconn : ActualConnected squareLattice (finiteEdgeSetEnumeration i) u v
  · simpa [finiteConnectionEvent, hconn] using
          LatticeConfiguration.allOpen_isClopen (finiteEdgeSetEnumeration i)
  · simpa [finiteConnectionEvent, hconn] using
          (isClopen_empty : IsClopen (∅ : Set LatticeConfiguration))

theorem finiteConnectionEvent_isUpperSet
    (F : Finset squareLattice.edgeSet) :
    IsUpperSet (finiteConnectionEvent u v F) := by
  intro ω η hωη hω
  refine ⟨hω.1, ?_⟩
  intro e he
  have h := hωη e
  have hopen := hω.2 e he
  rw [hopen] at h
  aesop

theorem connectionApprox_isUpperSet (n : ℕ) :
    IsUpperSet (connectionApprox u v n) := by
  intro ω η hωη hω
  rcases (mem_connectionApprox_iff u v n ω).mp hω with ⟨i, hi, hconn, hopen⟩
  refine (mem_connectionApprox_iff u v n η).mpr ⟨i, hi, hconn, ?_⟩
  intro e he
  aesop

theorem connectionEvent_isOpen : IsOpen (connectionEvent u v) := by
  rw [connectionEvent_eq_iUnion_connectionApprox]
  exact isOpen_iUnion fun n => (connectionApprox_isClopen u v n).isOpen

theorem connectionEvent_isMeasurableSet : MeasurableSet (connectionEvent u v) :=
  (connectionEvent_isOpen u v).measurableSet

end

private theorem openGraph_subset_rcInfiniteOpenGraph (ω : LatticeConfiguration)
    (F : Finset squareLattice.edgeSet)
    (hopen : ω ∈ LatticeConfiguration.allOpen F) :
    openGraph squareLattice F ≤ PottsDiscontinuity.rcInfiniteOpenGraph ω := by
  intro u v huv
  obtain ⟨e, heF, heq⟩ := (openGraph_adj squareLattice F u v).mp huv
  have h := openGraph_le _ _ huv
  refine (FK.Medial.rcInfiniteOpenGraph_adj_iff ω u v).2 ⟨h, ?_⟩
  rw [← (Subtype.ext heq : e = ⟨s(u, v), squareLattice.mem_edgeSet.mpr h⟩)]
  exact hopen e heF

private theorem reachable_to_finiteConnectionEvent (ω : LatticeConfiguration)
    {u v : LatticeVertex} (h : (rcInfiniteOpenGraph ω).Reachable u v) :
    ω ∈ connectionEvent u v := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact ⟨∅, SimpleGraph.Reachable.refl _, by simp⟩
  | @cons a b c hab p ih =>
    obtain ⟨F, hconn, hF⟩ := ih
    obtain ⟨hG, hopen⟩ := (FK.Medial.rcInfiniteOpenGraph_adj_iff _ _ _).1 hab
    let e : squareLattice.edgeSet := ⟨s(a, b), squareLattice.mem_edgeSet.mpr hG⟩
    have hadj : (openGraph squareLattice (insert e F)).Adj a b :=
      (openGraph_adj _ _ _ _).2 ⟨e, Finset.mem_insert_self _ _, rfl⟩
    refine ⟨insert e F, hadj.reachable.trans (actualConnected_mono (Finset.subset_insert _ _) hconn), ?_⟩
    intro d hd
    rcases Finset.mem_insert.1 hd with rfl | hd
    · exact hopen
    · exact hF d hd

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

/-- A lattice isomorphism transports the actual open graph edge by edge. -/
def rcInfiniteOpenGraphIso (e : squareLattice ≃g squareLattice) (ω : LatticeConfiguration) :
    rcInfiniteOpenGraph ω ≃g
      rcInfiniteOpenGraph (latticeConfigurationIsoHomeomorph e ω) where
  toEquiv := e.toEquiv
  map_rel_iff' := by
    intro u v
    have hidx (h : squareLattice.Adj (e.toEquiv u) (e.toEquiv v)) :
        SimpleGraph.Iso.mapEdgeSet e.symm ⟨s(e.toEquiv u, e.toEquiv v), squareLattice.mem_edgeSet.mpr h⟩ =
          ⟨s(u, v), squareLattice.mem_edgeSet.mpr (e.map_rel_iff'.1 h)⟩ := by
      aesop
    simp only [FK.Medial.rcInfiniteOpenGraph_adj_iff]
    constructor
    · rintro ⟨hadj, hopen⟩
      refine ⟨e.map_rel_iff'.1 hadj, ?_⟩
      rw [latticeConfigurationIsoHomeomorph_apply, hidx hadj] at hopen
      exact hopen
    · rintro ⟨hadj, hopen⟩
      refine ⟨e.map_rel_iff'.2 hadj, ?_⟩
      rw [latticeConfigurationIsoHomeomorph_apply, hidx (e.map_rel_iff'.2 hadj)]
      exact hopen

theorem connectionEvent_translation (a u v : LatticeVertex) (ω : LatticeConfiguration) :
    latticeConfigurationTranslate a ω ∈
        connectionEvent (latticeTranslate a u) (latticeTranslate a v) ↔
      ω ∈ connectionEvent u v := by
  rw [connectionEvent_iff_rcInfiniteReachable, connectionEvent_iff_rcInfiniteReachable]
  exact SimpleGraph.Iso.reachable_iff
    (φ := rcInfiniteOpenGraphIso (latticeTranslationIso a) ω) (u := u) (v := v)

/-- The frozen free limit has translation-invariant connection probabilities. -/
theorem isRCInfiniteVolumeLimit_connection_translation_invariant
    (θ : Parameters) (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ)
    (a u v : LatticeVertex) :
    μ.real (connectionEvent (latticeTranslate a u) (latticeTranslate a v)) =
      μ.real (connectionEvent u v) := by
  have hinv := isRCInfiniteVolumeLimit_interior_translation_invariant θ 0 μ hμ a
  have hmeas := connectionEvent_isMeasurableSet (latticeTranslate a u) (latticeTranslate a v)
  have hmap := congrArg (fun ν : Measure LatticeConfiguration =>
    ν (connectionEvent (latticeTranslate a u) (latticeTranslate a v))) hinv
  rw [Measure.map_apply (latticeConfigurationTranslate_measurable a) hmeas] at hmap
  have hpre :
      (latticeConfigurationTranslate a) ⁻¹'
        connectionEvent (latticeTranslate a u) (latticeTranslate a v) =
        connectionEvent u v := by
    ext ω
    exact connectionEvent_translation a u v ω
  rw [hpre] at hmap
  simpa [Measure.real_def] using (congrArg ENNReal.toReal hmap).symm

/-- The canonical free box limit along the origin-centered exhaustion. -/
theorem selected_freeBox_tendsto (θ : Parameters) :
    Tendsto (fun n => boxProbabilityMeasure θ (0, 0) n) atTop
      (𝓝 (Classical.choose (freeBoxLimit_existsUnique θ))) :=
  (Classical.choose_spec (freeBoxLimit_existsUnique θ)).1 _ _
    origin_latticeBox_nested origin_latticeBox_exhaustive

/-- The frozen free limit coincides with the canonical box limit. -/
theorem free_limit_eq_selected (θ : Parameters) (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ) :
    μ = (Classical.choose (freeBoxLimit_existsUnique θ)).toMeasure :=
  rc_limit_unique θ.toP θ.toQ 0 μ _ hμ
    (isRCInfiniteVolumeLimit_of_freeBox_tendsto θ _ (selected_freeBox_tendsto θ))

/-- Extend clopen FKG to connections by approximation from below. -/
theorem free_connection_positive_association (θ : Parameters) (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ) (u v x y : LatticeVertex) :
    μ (connectionEvent u v) * μ (connectionEvent x y) ≤ μ (connectionEvent u v ∩ connectionEvent x y) := by
  have := hμ.1
  have hFK (s t : Set LatticeConfiguration) (hs : IsClopen s) (ht : IsClopen t)
      (hsu : IsUpperSet s) (htu : IsUpperSet t) : μ s * μ t ≤ μ (s ∩ t) := by
    apply (ENNReal.toReal_le_toReal
      (ENNReal.mul_ne_top (measure_ne_top μ s) (measure_ne_top μ t)) (measure_ne_top μ _)).1
    rw [ENNReal.toReal_mul, free_limit_eq_selected θ μ hμ]
    simpa [← ProbabilityMeasure.measureReal_eq_coe_coeFn, Measure.real_def] using
          Internal.freeBoxLimit_clopen_positive_association θ s t hs ht hsu htu
  calc
    _ = (⨆ n, μ (connectionApprox u v n)) * (⨆ n, μ (connectionApprox x y n)) := by
      congr 1 <;> rw [connectionEvent_eq_iUnion_connectionApprox,
        (connectionApprox_mono _ _).directed_le.measure_iUnion]
    _ ≤ _ := by
      rw [ENNReal.iSup_mul]
      refine iSup_le fun n => ?_
      rw [ENNReal.mul_iSup]
      refine iSup_le fun m => (hFK _ _ (connectionApprox_isClopen u v n)
        (connectionApprox_isClopen x y m) (connectionApprox_isUpperSet u v n)
        (connectionApprox_isUpperSet x y m)).trans (measure_mono (Set.inter_subset_inter ?_ ?_))
      all_goals rw [connectionEvent_eq_iUnion_connectionApprox]; exact Set.subset_iUnion _ _

theorem free_connection_mul_le (θ : Parameters) (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ) (u v w : LatticeVertex) :
    μ (connectionEvent u v) * μ (connectionEvent v w) ≤ μ (connectionEvent u w) := by
  refine (free_connection_positive_association θ μ hμ u v v w).trans (measure_mono ?_)
  simp only [Set.subset_def, Set.mem_inter_iff, connectionEvent_iff_rcInfiniteReachable]
  exact fun _ h => h.1.trans h.2

/-- In the free limit, translation invariance turns the FKG inequality into
supermultiplicativity of probabilities based at the origin. -/
theorem isRCInfiniteVolumeLimit_origin_connection_supermultiplicative
    (θ : Parameters) (μ : Measure LatticeConfiguration)
    (hμ : PottsDiscontinuity.IsRCInfiniteVolumeLimit
      θ.toP θ.toQ 0 μ) (x y : LatticeVertex) :
    μ.real (connectionEvent (0, 0) (x.1 + y.1, x.2 + y.2)) ≥
      μ.real (connectionEvent (0, 0) x) *
        μ.real (connectionEvent (0, 0) y) := by
  have := hμ.1
  have hmul := ENNReal.toReal_mono (measure_ne_top μ _)
    (free_connection_mul_le θ μ hμ (0,0) x (x.1 + y.1, x.2 + y.2))
  simp only [ENNReal.toReal_mul, ← Measure.real_def] at hmul
  have htrans := isRCInfiniteVolumeLimit_connection_translation_invariant
    θ μ hμ (-x) x (x.1 + y.1, x.2 + y.2)
  have hxy :
      μ.real (connectionEvent x (x.1 + y.1, x.2 + y.2)) =
        μ.real (connectionEvent (0, 0) y) := by
    simpa [latticeTranslate] using htrans.symm
  simp_all

end

end PottsDiscontinuity.CorrLength
