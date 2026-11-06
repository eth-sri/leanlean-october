module

public import PottsDiscontinuity.FK.SubgraphComparison
public import PottsDiscontinuity.TorusRC.LiftedBoxes
public import PottsDiscontinuity.TorusRC.RightHalf

/-! # Lifted boxes wholly inside the right-half interior -/

@[expose] public section

namespace PottsDiscontinuity.TorusRC

open Torus CorrLength

variable {N M : ℕ}

/-- A box away from the horizontal seam uses only right-half interior edges.
The box may touch either vertical boundary of the right half. -/
theorem liftedBox_edge_rightHalfInterior (hNp : 0 < N) (hMp : 0 < M)
    (c : RotatedVertex) (R : ℕ)
    (hleft : (N / 2 : ℤ) ≤ c.val.1 - R) (hright : c.val.1 + R ≤ (N : ℤ))
    (hbottom : 0 < c.val.2 - R) (htop : c.val.2 + R < (M : ℤ))
    {u v : LiftedBoxVertex c R} (huv : (liftedBoxGraph c R).Adj u v) :
    rightHalfInteriorSite (liftedEdgeIndex hNp hMp u.val v.val) := by
  have hux := abs_le.mp u.property.1
  have hvx := abs_le.mp v.property.1
  have huy := abs_le.mp u.property.2
  have hvy := abs_le.mp v.property.2
  have hne : u.val.val.1 ≠ v.val.val.1 := fun heq => by
    have hdist : |u.val.val.1 - v.val.val.1| = 1 := huv.1
    simp [heq] at hdist
  have hxlo : (N / 2 : ℤ) < max u.val.val.1 v.val.val.1 := by omega
  have hxhi : max u.val.val.1 v.val.val.1 ≤ (N : ℤ) := by omega
  have hylo : 0 < max u.val.val.2 v.val.val.2 := by omega
  have hyhi : max u.val.val.2 v.val.val.2 < (M : ℤ) := by omega
  have hyval : ((liftedEdgeIndex hNp hMp u.val v.val).2.val : ℤ) =
      max u.val.val.2 v.val.val.2 := by
    change ((periodicCoordinate hMp _).val : ℤ) = _
    rw [periodicCoordinate_val, Int.emod_eq_of_lt (by omega) hyhi]
  refine ⟨?_, by omega⟩
  by_cases hxN : max u.val.val.1 v.val.val.1 = (N : ℤ)
  · left
    have hxval := periodicCoordinate_val hNp (max u.val.val.1 v.val.val.1)
    rw [hxN, Int.emod_self] at hxval
    change (periodicCoordinate hNp _).val = 0
    rw [hxN]; exact_mod_cast hxval
  · right
    have hxval := periodicCoordinate_val hNp (max u.val.val.1 v.val.val.1)
    rw [Int.emod_eq_of_lt (by omega) (by omega)] at hxval
    change N / 2 < (periodicCoordinate hNp _).val
    omega

/-- The actual embedded native box graph is contained in the graph sampled by
a right-half fiber. No frozen edge is used by this interior box. -/
theorem liftedBoxGraph_map_projection_le_rightHalf (hN : Even N) (hM : Even M)
    (hN4 : 4 ≤ N) (hM4 : 4 ≤ M) (hNp : 0 < N) (hMp : 0 < M)
    (c : RotatedVertex) (R : ℕ) (hRN : 2 * R < N) (hRM : 2 * R < M)
    (hleft : (N / 2 : ℤ) ≤ c.val.1 - R) (hright : c.val.1 + R ≤ (N : ℤ))
    (hbottom : 0 < c.val.2 - R) (htop : c.val.2 + R < (M : ℤ)) :
    (liftedBoxGraph c R).map (liftedBoxProjection hN hM hNp hMp c R hRN hRM) ≤
      FK.edgeRestriction (fullDiamondGraph hN hM)
        (rightHalfFrozenEdges hN hM hN4 hM4) := by
  intro x y hxy
  have hfull := liftedBoxGraph_map_projection_le hN hM hNp hMp c R hRN hRM hxy
  rw [SimpleGraph.map_adj] at hxy
  rcases hxy with ⟨u, v, huv, rfl, rfl⟩
  change ((fullDiamondGraph hN hM).deleteEdges
    (FK.openEdges (fullDiamondGraph hN hM) (rightHalfFrozenEdges hN hM hN4 hM4))).Adj _ _
  rw [SimpleGraph.deleteEdges_adj]
  refine ⟨hfull, fun hopen => ?_⟩
  let idx := liftedEdgeIndex hNp hMp u.val v.val
  let e := torusIndexedEdgeEquiv hN hM hN4 hM4 idx
  have hpair : e.val = s(liftedFaceVertex hN hM hNp hMp u.val,
      liftedFaceVertex hN hM hNp hMp v.val) :=
    (liftedFaceEndpoints_eq hN hM hNp hMp u.val v.val huv).symm
  exact (mem_rightHalfFrozenEdges hN hM hN4 hM4 idx).mp
    ((FK.coe_mem_openEdges_iff (fullDiamondGraph hN hM) (rightHalfFrozenEdges hN hM hN4 hM4) e).mp
      (hpair.symm ▸ hopen))
    (liftedBox_edge_rightHalfInterior hNp hMp c R hleft hright hbottom htop huv)

noncomputable section

local instance interiorGraphFintype (hN : Even N) (hM : Even M) :
    Fintype (fullDiamondGraph hN hM).edgeSet := Fintype.ofFinite _

local instance interiorGraphDecidableEq (hN : Even N) (hM : Even M) :
    DecidableEq (fullDiamondGraph hN hM).edgeSet := Classical.decEq _

local instance interiorBoxFintype (c : RotatedVertex) (R : ℕ) :
    Fintype (liftedBoxGraph c R).edgeSet := Fintype.ofFinite _

local instance interiorDeletedFintype (hN : Even N) (hM : Even M)
    (hN4 : 4 ≤ N) (hM4 : 4 ≤ M) :
    Fintype (FK.edgeRestriction (fullDiamondGraph hN hM)
      (rightHalfFrozenEdges hN hM hN4 hM4)).edgeSet := Fintype.ofFinite _

local instance interiorRemainingFintype (hN : Even N) (hM : Even M)
    (hN4 : 4 ≤ N) (hM4 : 4 ≤ M) :
    Fintype (FK.RemainingConfiguration (fullDiamondGraph hN hM)
      (rightHalfFrozenEdges hN hM hN4 hM4)) := Fintype.ofFinite _

/-- An actual connection in the embedded box restriction lifts back to the
prescribed box connection after the exterior state is restored. -/
theorem embeddedBox_connection_lifts (hN : Even N) (hM : Even M)
    (hN4 : 4 ≤ N) (hM4 : 4 ≤ M) (hNp : 0 < N) (hMp : 0 < M)
    (c : RotatedVertex) (R : ℕ) (hRN : 2 * R < N) (hRM : 2 * R < M)
    (hleft : (N / 2 : ℤ) ≤ c.val.1 - R) (hright : c.val.1 + R ≤ (N : ℤ))
    (hGH : (liftedBoxGraph c R).map
      (liftedBoxProjection hN hM hNp hMp c R hRN hRM) ≤
      FK.edgeRestriction (fullDiamondGraph hN hM) (rightHalfFrozenEdges hN hM hN4 hM4))
    (H : FK.RemovedConfiguration (fullDiamondGraph hN hM)
      (rightHalfFrozenEdges hN hM hN4 hM4))
    (C : FK.Configuration (FK.edgeRestriction (fullDiamondGraph hN hM)
      (rightHalfFrozenEdges hN hM hN4 hM4))) (v : RotatedVertex)
    (hconn : FK.embeddedConfigurationRestriction (liftedBoxGraph c R)
      (FK.edgeRestriction (fullDiamondGraph hN hM) (rightHalfFrozenEdges hN hM hN4 hM4))
      (liftedBoxProjection hN hM hNp hMp c R hRN hRM) hGH C ∈
        liftedBoxFreeConnectionEvent c R c v) :
    liftedBoxConnection hNp hMp
      (rightHalfRestore hN hM hN4 hM4 H
        (FK.edgeRestrictionConfigurationEquiv (fullDiamondGraph hN hM)
          (rightHalfFrozenEdges hN hM hN4 hM4) C))
      (N / 2 : ℤ) (N : ℤ) R c v := by
  classical
  let D := FK.edgeRestriction (fullDiamondGraph hN hM) (rightHalfFrozenEdges hN hM hN4 hM4)
  let f := liftedBoxProjection hN hM hNp hMp c R hRN hRM
  let A := FK.edgeRestrictionConfigurationEquiv (fullDiamondGraph hN hM)
    (rightHalfFrozenEdges hN hM hN4 hM4) C
  let Cbox := FK.embeddedConfigurationRestriction (liftedBoxGraph c R) D f hGH C
  let F : FK.openGraph (liftedBoxGraph c R) Cbox →g
      liftedStripGraph hNp hMp (rightHalfRestore hN hM hN4 hM4 H A)
        (N / 2 : ℤ) (N : ℤ) :=
    { toFun z := z.val
      map_rel' := by
        intro u w huw
        have hlat : rotatedLattice.Adj u.val w.val :=
          FK.openGraph_le (liftedBoxGraph c R) Cbox huw
        obtain ⟨e, he, heuw⟩ := (FK.openGraph_adj (liftedBoxGraph c R) Cbox u w).mp huw
        let idx := liftedEdgeIndex hNp hMp u.val w.val
        have heA : torusIndexedEdgeEquiv hN hM hN4 hM4 idx ∈ A.val := by
          rw [FK.edgeRestrictionConfigurationEquiv_val]
          refine Finset.mem_map.mpr ⟨_, (FK.mem_embeddedConfigurationRestriction (liftedBoxGraph c R) D f hGH C e).mp he, ?_⟩
          apply Subtype.ext
          rw [FK.edgeRestrictionEdgeEmbedding_coe, FK.embeddedEdgeEmbedding_coe, heuw]
          exact liftedFaceEndpoints_eq hN hM hNp hMp u.val w.val hlat
        have hu := abs_le.mp u.property.1
        have hw := abs_le.mp w.property.1
        exact ⟨hlat, (rightHalfRestore_true_iff hN hM hN4 hM4 H A idx).mpr (Or.inl heA),
          ⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩ }
  obtain ⟨_, _, ⟨p⟩⟩ := hconn
  refine ⟨p.map F, fun z hz => ?_⟩
  obtain ⟨z', _, rfl⟩ := List.mem_map.mp (SimpleGraph.Walk.support_map F p ▸ hz)
  exact z'.property

/-- On every right-half fiber, a local box away from the seam has connection
probability at least its native free-box probability. The exterior state is
arbitrary, including every exterior state compatible with B. -/
theorem liftedBoxFreeConnectionProbability_le_free_remaining (hN : Even N) (hM : Even M)
    (hN4 : 4 ≤ N) (hM4 : 4 ≤ M) (hNp : 0 < N) (hMp : 0 < M)
    (q : Set.Ici (1 : ℝ)) (c : RotatedVertex) (R : ℕ) (v : RotatedVertex)
    (hRN : 2 * R < N) (hRM : 2 * R < M)
    (hleft : (N / 2 : ℤ) ≤ c.val.1 - R) (hright : c.val.1 + R ≤ (N : ℤ))
    (hbottom : 0 < c.val.2 - R) (htop : c.val.2 + R < (M : ℤ))
    (H : FK.RemovedConfiguration (fullDiamondGraph hN hM)
      (rightHalfFrozenEdges hN hM hN4 hM4)) :
    liftedBoxFreeConnectionProbability (torusRCBridgeParameters q) c R c v ≤
      torusRCFiberEventProbability
        (FK.remainingLaw (fullDiamondGraph hN hM) (torusRCBridgeParameters q)
          (FK.BoundaryCondition.free ∅) (rightHalfFrozenEdges hN hM hN4 hM4))
        {A | liftedBoxConnection hNp hMp (rightHalfRestore hN hM hN4 hM4 H A)
          (N / 2 : ℤ) (N : ℤ) R c v} := by
  classical
  let G := fullDiamondGraph hN hM
  let R₀ := rightHalfFrozenEdges hN hM hN4 hM4
  let D := FK.edgeRestriction G R₀
  let f := liftedBoxProjection hN hM hNp hMp c R hRN hRM
  have hGH := liftedBoxGraph_map_projection_le_rightHalf hN hM hN4 hM4 hNp hMp
    c R hRN hRM hleft hright hbottom htop
  let S := liftedBoxFreeConnectionEvent c R c v
  let ind : FK.Configuration (liftedBoxGraph c R) → ℝ := S.indicator (fun _ => 1)
  have hind0 (A) : 0 ≤ ind A := by by_cases hA : A ∈ S <;> simp [ind, hA]
  have hind : Monotone ind := fun A B hAB => by
    by_cases hA : A ∈ S
    · have hB : B ∈ S := liftedBoxFreeConnectionEvent_upper c R c v hAB hA
      simp [ind, hA, hB]
    · simpa [ind, Set.indicator, hA] using hind0 B
  refine (FK.embedded_free_expectation_le (liftedBoxGraph c R) D f hGH
    (torusRCBridgeParameters q) ∅ ∅ ind hind0 hind).trans ?_
  unfold torusRCFiberEventProbability
  rw [← FK.law_edgeRestriction_map, FK.FiniteProbability.expectation_map]
  apply FK.FiniteProbability.expectation_mono; intro C
  dsimp only [ind]
  by_cases hc : FK.embeddedConfigurationRestriction (liftedBoxGraph c R) D f hGH C ∈ S
  · rw [Set.indicator_of_mem hc, Set.indicator_of_mem
      (s := {A | liftedBoxConnection hNp hMp (rightHalfRestore hN hM hN4 hM4 H A) (N / 2 : ℤ) (N : ℤ) R c v})
      (embeddedBox_connection_lifts hN hM hN4 hM4 hNp hMp c R hRN hRM hleft hright hGH H C v hc)]
  · rw [Set.indicator_of_notMem hc]
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) _

end

end PottsDiscontinuity.TorusRC
