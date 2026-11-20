module

public import PottsDiscontinuity.FK.SubgraphComparison
public import PottsDiscontinuity.TorusRC.LiftedBoxes
public import PottsDiscontinuity.TorusRC.RightHalf

/-! # Lifted boxes wholly inside the right-half interior -/

@[expose] public section

namespace PottsDiscontinuity.TorusRC

open Torus CorrLength

variable {N M : ℕ}

section
variable (hN : Even N) (hM : Even M) (hN4 : 4 ≤ N) (hM4 : 4 ≤ M) (hNp : 0 < N) (hMp : 0 < M)
    (c : RotatedVertex) (R : ℕ) (hRN : 2 * R < N) (hRM : 2 * R < M)
    (hleft : (N / 2) ≤ c.val.1 - R) (hright : c.val.1 + R ≤ N) (hbottom : 0 < c.val.2 - R)
    (htop : c.val.2 + R < M)
include hleft hright hbottom htop

/-- A box away from the horizontal seam uses only right-half interior edges.
The box may touch either vertical boundary of the right half. -/
theorem liftedBox_edge_rightHalfInterior
    {u v : LiftedBoxVertex c R} (huv : (liftedBoxGraph c R).Adj u v) :
    rightHalfInteriorSite (liftedEdgeIndex hNp hMp u.val v.val) := by
  have hux := abs_le.mp u.property.1
  have hvx := abs_le.mp v.property.1
  have huy := abs_le.mp u.property.2
  have hvy := abs_le.mp v.property.2
  have hdist := huv.1
  have hne : u.val.val.1 ≠ v.val.val.1 := by
    intro heq
    simp_all
  have hyval : (liftedEdgeIndex hNp hMp u.val v.val).2.val =
      max u.val.val.2 v.val.val.2 := by
    change ((periodicCoordinate hMp _).val : ℤ) = _
    rw [periodicCoordinate_val, Int.emod_eq_of_lt (by omega) (by omega)]
  refine ⟨?_, by omega⟩
  by_cases hxN : max u.val.val.1 v.val.val.1 = N
  · left
    have hxval := periodicCoordinate_val hNp (max u.val.val.1 v.val.val.1)
    rw [hxN, Int.emod_self] at hxval
    change (periodicCoordinate hNp _).val = 0
    grind
  · right
    have hxval := periodicCoordinate_val hNp (max u.val.val.1 v.val.val.1)
    rw [Int.emod_eq_of_lt (by omega) (by omega)] at hxval
    change _ < (periodicCoordinate hNp _).val
    omega

/-- The actual embedded native box graph is contained in the graph sampled by
a right-half fiber. No frozen edge is used by this interior box. -/
theorem liftedBoxGraph_map_projection_le_rightHalf :
    (liftedBoxGraph c R).map (liftedBoxProjection hN hM hNp hMp c hRN hRM) ≤
      FK.edgeRestriction (fullDiamondGraph hN hM)
        (rightHalfFrozenEdges hN hM hN4 hM4) := by
  intro x y hxy
  have hfull := liftedBoxGraph_map_projection_le hN hM hNp hMp c R hRN hRM hxy
  rw [SimpleGraph.map_adj] at hxy
  rcases hxy with ⟨u, v, huv, rfl, rfl⟩
  change ((fullDiamondGraph hN hM).deleteEdges
    (FK.openEdges (rightHalfFrozenEdges hN hM hN4 hM4))).Adj _ _
  rw [SimpleGraph.deleteEdges_adj]
  refine ⟨hfull, ?_⟩
  let idx := liftedEdgeIndex hNp hMp u.val v.val
  let e := torusIndexedEdgeEquiv hN hM hN4 hM4 idx
  have hnot := fun he => (mem_rightHalfFrozenEdges hN hM hN4 hM4 idx).mp he (liftedBox_edge_rightHalfInterior hNp hMp c R hleft hright hbottom htop huv)
  have hpair : e.val = s(liftedFaceVertex hN hM hNp hMp u.val,
      liftedFaceVertex hN hM hNp hMp v.val) := (liftedFaceEndpoints_eq hN hM hNp hMp huv).symm
  intro hopen
  apply hnot
  apply (FK.coe_mem_openEdges_iff _
    _ e).mp
  rw [hpair]
  exact hopen

end

noncomputable section

variable (hN : Even N) (hM : Even M) (hN4 : 4 ≤ N) (hM4 : 4 ≤ M) (hNp : 0 < N) (hMp : 0 < M)

local instance interiorDeletedFintype :
    Fintype (FK.edgeRestriction (fullDiamondGraph hN hM)
      (rightHalfFrozenEdges hN hM hN4 hM4)).edgeSet := Fintype.ofFinite _

local instance interiorRemainingFintype :
    Fintype (FK.RemainingConfiguration (fullDiamondGraph hN hM)
      (rightHalfFrozenEdges hN hM hN4 hM4)) := Fintype.ofFinite _

/-- An actual connection in the embedded box restriction lifts back to the
prescribed box connection after the exterior state is restored. -/
theorem embeddedBox_connection_lifts
    (c : RotatedVertex) (R : ℕ) (hRN : 2 * R < N) (hRM : 2 * R < M)
    (hleft : (N / 2) ≤ c.val.1 - R) (hright : c.val.1 + R ≤ N)
    (hGH : (liftedBoxGraph c R).map
      (liftedBoxProjection hN hM hNp hMp c hRN hRM) ≤
      FK.edgeRestriction (fullDiamondGraph hN hM) (rightHalfFrozenEdges hN hM hN4 hM4))
    (H : FK.RemovedConfiguration (fullDiamondGraph hN hM)
      (rightHalfFrozenEdges hN hM hN4 hM4))
    (C : FK.Configuration (FK.edgeRestriction (fullDiamondGraph hN hM)
      (rightHalfFrozenEdges hN hM hN4 hM4))) (v : RotatedVertex)
    (hconn : FK.embeddedConfigurationRestriction (liftedBoxGraph c R)
      (FK.edgeRestriction (fullDiamondGraph hN hM) (rightHalfFrozenEdges hN hM hN4 hM4))
      (liftedBoxProjection hN hM hNp hMp c hRN hRM) hGH C ∈
        liftedBoxFreeConnectionEvent c R c v) :
    liftedBoxConnection hNp hMp
      (rightHalfRestore H
        (FK.edgeRestrictionConfigurationEquiv (fullDiamondGraph hN hM)
          (rightHalfFrozenEdges hN hM hN4 hM4) C))
      (N / 2) N R c v := by
  classical
  let D := FK.edgeRestriction _ (rightHalfFrozenEdges hN hM hN4 hM4)
  let f := liftedBoxProjection hN hM hNp hMp c hRN hRM
  let A := FK.edgeRestrictionConfigurationEquiv _
    _ C
  let Cbox := FK.embeddedConfigurationRestriction _ D f hGH C
  let F : FK.openGraph Cbox →g
      liftedStripGraph hNp hMp (rightHalfRestore H A)
        (N / 2) N :=
    { toFun := fun z => z.val
      map_rel' := by
        intro u w huw
        have hlat :=
          FK.openGraph_le Cbox huw
        rw [FK.openGraph_adj] at huw
        obtain ⟨e, he, heuw⟩ := huw
        let idx := liftedEdgeIndex hNp hMp u.val w.val
        have heA : torusIndexedEdgeEquiv hN hM hN4 hM4 idx ∈ A.val := by
          rw [FK.edgeRestrictionConfigurationEquiv_val]
          exact Finset.mem_map.mpr ⟨_, ((FK.mem_embeddedConfigurationRestriction _ D f hGH C e).mp he), (by
            apply Subtype.ext
            rw [FK.edgeRestrictionEdgeEmbedding_coe, FK.embeddedEdgeEmbedding_coe, heuw]
            exact liftedFaceEndpoints_eq hN hM hNp hMp hlat)⟩
        have hu := abs_le.mp u.property.1
        have hw := abs_le.mp w.property.1
        exact ⟨hlat, (rightHalfRestore_true_iff H A idx).mpr (Or.inl heA),
          ⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩ }
  obtain ⟨hc, hv, p⟩ := hconn
  obtain ⟨p⟩ := p
  refine ⟨p.map F, ?_⟩
  intro z hz
  rw [SimpleGraph.Walk.support_map] at hz
  obtain ⟨z', _, rfl⟩ := List.mem_map.mp hz
  exact z'.property

/-- On every right-half fiber, a local box away from the seam has connection
probability at least its native free-box probability. The exterior state is
arbitrary, including every exterior state compatible with B. -/
theorem liftedBoxFreeConnectionProbability_le_free_remaining
    (q : Set.Ici 1) {c : RotatedVertex} (R : ℕ) (v : RotatedVertex)
    (hRN : 2 * R < N) (hRM : 2 * R < M)
    (hleft : (N / 2) ≤ c.val.1 - R) (hright : c.val.1 + R ≤ N)
    (hbottom : 0 < c.val.2 - R) (htop : c.val.2 + R < M)
    (H : FK.RemovedConfiguration (fullDiamondGraph hN hM)
      (rightHalfFrozenEdges hN hM hN4 hM4)) :
    liftedBoxFreeConnectionProbability (torusRCBridgeParameters q) c R c v ≤
      torusRCFiberEventProbability
        (FK.remainingLaw (fullDiamondGraph hN hM) (torusRCBridgeParameters q)
          (FK.BoundaryCondition.free ∅) (rightHalfFrozenEdges hN hM hN4 hM4))
        {A | liftedBoxConnection hNp hMp (rightHalfRestore H A)
          (N / 2) N R c v} := by
  classical
  let G := fullDiamondGraph hN hM
  let R₀ := rightHalfFrozenEdges hN hM hN4 hM4
  let D := FK.edgeRestriction G R₀
  let f := liftedBoxProjection hN hM hNp hMp c hRN hRM
  have hGH := liftedBoxGraph_map_projection_le_rightHalf hN hM hN4 hM4 hNp hMp
    c R hRN hRM hleft hright hbottom htop
  let E :=
    {A | liftedBoxConnection hNp hMp (rightHalfRestore H A)
      (N / 2) N R c v}
  let S := liftedBoxFreeConnectionEvent c R c v
  let ind : FK.Configuration (liftedBoxGraph c R) → ℝ := S.indicator (fun _ => 1)
  have hind0 : ∀ A, 0 ≤ ind A := by
    intro A
    by_cases hA : A ∈ S <;> simp [ind, hA]
  have hind : Monotone ind := by
    intro A B hAB
    by_cases hA : A ∈ S
    · have hB : B ∈ S := liftedBoxFreeConnectionEvent_upper c R c v hAB hA
      simp [ind, *]
    · simpa [ind, Set.indicator, hA] using hind0 B
  have hdom : FK.FiniteProbability.expectation (FK.law D (torusRCBridgeParameters q)
      (FK.BoundaryCondition.free ∅))
      (fun C => ind (FK.embeddedConfigurationRestriction _ D f hGH C)) ≤
      FK.FiniteProbability.expectation (FK.remainingLaw G (torusRCBridgeParameters q)
        (FK.BoundaryCondition.free ∅) R₀) (E.indicator (fun _ => 1)) := by
    rw [← FK.law_edgeRestriction_map, FK.FiniteProbability.expectation_map]
    apply FK.FiniteProbability.expectation_mono
    intro C
    by_cases hc : FK.embeddedConfigurationRestriction _ D f hGH C ∈ S
    · have heE : FK.edgeRestrictionConfigurationEquiv G R₀ C ∈ E := (by apply embeddedBox_connection_lifts <;> assumption)
      simp [ind, Set.indicator_of_mem hc, Set.indicator_of_mem heE, le_refl]
    · simp only [ind, Set.indicator_of_notMem hc]
      by_cases he : FK.edgeRestrictionConfigurationEquiv G R₀ C ∈ E <;>
        simp [Set.indicator, he]
  exact (FK.embedded_free_expectation_le _ D f hGH (torusRCBridgeParameters q) ∅ ∅ hind0 hind).trans hdom

end

end PottsDiscontinuity.TorusRC
