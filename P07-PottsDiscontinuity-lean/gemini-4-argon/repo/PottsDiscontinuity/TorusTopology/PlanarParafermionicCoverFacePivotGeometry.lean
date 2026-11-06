module

public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFaceTopEdges

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open PottsDiscontinuity.TorusTopology.Planar

abbrev ParafermionicCoverFiniteFaceTopIndex (n : ℕ) :=
  {f : ParafermionicCoverVertex // f ∈ parafermionicCoverFiniteOrdinaryFaces n}

def parafermionicCoverFiniteFaceTopPivot (n : ℕ)
    (f : ParafermionicCoverFiniteFaceTopIndex n) :
    Sym2 (ParafermionicCoverBoxVertex n) :=
  s(⟨parafermionicCoverFaceRightUpLift f.1.1.1 f.1.1.2 f.1.2,
      (parafermionicCoverFiniteFaceTopEdge_endpoints_mem n f.1 f.2).1⟩,
    ⟨parafermionicCoverFaceRightUpLeftLift f.1.1.1 f.1.1.2 f.1.2,
      (parafermionicCoverFiniteFaceTopEdge_endpoints_mem n f.1 f.2).2⟩)

theorem parafermionicCoverFiniteFaceTopPivot_map (n : ℕ)
    (f : ParafermionicCoverFiniteFaceTopIndex n) :
    Sym2.map Subtype.val (parafermionicCoverFiniteFaceTopPivot n f) =
      parafermionicCoverFiniteFaceTopEdge f.1 := by
  simp [parafermionicCoverFiniteFaceTopPivot, parafermionicCoverFiniteFaceTopEdge, Sym2.map_mk]

theorem parafermionicCoverFiniteFaceTopPivot_injective (n : ℕ) :
    Function.Injective (parafermionicCoverFiniteFaceTopPivot n) := by
  intro f g h
  apply Subtype.ext
  apply parafermionicCoverFiniteFaceTopEdge_injective n f.2 g.2
  have hm := congrArg (Sym2.map Subtype.val) h
  rwa [parafermionicCoverFiniteFaceTopPivot_map, parafermionicCoverFiniteFaceTopPivot_map] at hm

theorem parafermionicCoverFiniteFaceTopPivot_mem_edgeSet (n : ℕ)
    (f : ParafermionicCoverFiniteFaceTopIndex n) :
    parafermionicCoverFiniteFaceTopPivot n f ∈
      (parafermionicCoverBoxGraph n).edgeSet :=
  parafermionicCoverFiniteFaceTopEdge_adjacent n f.1 f.2

def parafermionicCoverFiniteFaceTopRank (n : ℕ)
    (f : ParafermionicCoverFiniteFaceTopIndex n) : ℕ :=
  (f.1.1.2 + (n : ℤ)).toNat

theorem parafermionicCoverFiniteFaceTopRank_strict_height (n : ℕ)
    {f g : ParafermionicCoverFiniteFaceTopIndex n}
    (hheight : f.1.1.2 < g.1.1.2) :
    parafermionicCoverFiniteFaceTopRank n f <
      parafermionicCoverFiniteFaceTopRank n g := by
  have hf := (parafermionicCoverFiniteOrdinaryFaces_mem_iff n f.1).mp f.2
  have hg := (parafermionicCoverFiniteOrdinaryFaces_mem_iff n g.1).mp g.2
  unfold parafermionicCoverFiniteFaceTopRank
  omega

private def treeParent (n : ℕ) (v : ParafermionicCoverVertex) : ParafermionicCoverVertex :=
  if v.1.2 = -(n : ℤ) then ((v.1.1 - 1, -(n : ℤ)), v.2) else ((v.1.1, v.1.2 - 1), v.2)

private def treeRank (v : ParafermionicCoverVertex) : ℤ := v.1.1 + v.1.2

private lemma deleteTopPivots_horiz_bottom {n : ℕ}
    {u v : ParafermionicCoverBoxVertex n}
    (hadj : ((parafermionicCoverBoxGraph n).deleteEdges
      (Set.range (parafermionicCoverFiniteFaceTopPivot n))).Adj u v)
    (hx : u.1.1.1 + 1 = v.1.1.1) (hy : u.1.1.2 = v.1.1.2) :
    u.1.1.2 = -(n : ℤ) := by
  rcases u with ⟨⟨⟨x, y⟩, k⟩, hu⟩
  rcases v with ⟨⟨⟨x', y'⟩, k'⟩, hv⟩
  dsimp at hx hy ⊢
  subst hx hy
  rw [SimpleGraph.deleteEdges_adj] at hadj
  rcases hadj with ⟨hcov, hnot⟩
  have hk' : k = k' := by have := hcov.2; simp [parafermionicCoverSheetShift] at this; omega
  subst hk'
  by_contra hyn
  have hu' := (parafermionicCoverBoxVertices_mem n ((x, y), k)).1 hu
  have hv' := (parafermionicCoverBoxVertices_mem n ((x + 1, y), k)).1 hv
  dsimp at hu' hv'
  have hf : ((x, y - 1), k) ∈ parafermionicCoverFiniteOrdinaryFaces n := by
    rw [parafermionicCoverFiniteOrdinaryFaces_mem_iff]; dsimp; omega
  apply hnot ⟨⟨((x, y - 1), k), hf⟩, ?_⟩
  rw [Sym2.eq_swap]
  apply Sym2.map.injective Subtype.val_injective
  rw [parafermionicCoverFiniteFaceTopPivot_map]
  simp [parafermionicCoverFiniteFaceTopEdge, Sym2.map_mk]

private lemma deleteTopPivots_parent_rank {n : ℕ}
    {u v : ParafermionicCoverBoxVertex n}
    (hadj : ((parafermionicCoverBoxGraph n).deleteEdges
      (Set.range (parafermionicCoverFiniteFaceTopPivot n))).Adj u v) :
    (u.1 = treeParent n v.1 ∧ treeRank u.1 < treeRank v.1) ∨
      (v.1 = treeParent n u.1 ∧ treeRank v.1 < treeRank u.1) := by
  have hcov : parafermionicCoverGraph.Adj u.1 v.1 := (SimpleGraph.deleteEdges_adj.1 hadj).1
  have hu := (parafermionicCoverBoxVertices_mem n u.1).1 u.2
  have hv := (parafermionicCoverBoxVertices_mem n v.1).1 v.2
  rcases u with ⟨⟨⟨x, y⟩, k⟩, hu_mem⟩
  rcases v with ⟨⟨⟨x', y'⟩, k'⟩, hv_mem⟩
  rcases hcov with ⟨hbase, hsheet⟩
  rw [squareLattice_adj_iff] at hbase
  dsimp [parafermionicCoverSheetShift] at hbase hsheet hu hv
  subst hsheet
  rcases hbase with ⟨hx | hx, rfl⟩ | ⟨rfl, hy | hy⟩
  · have hy_bot := deleteTopPivots_horiz_bottom hadj hx rfl
    dsimp at hy_bot
    subst hx hy_bot
    left; simp [treeParent, treeRank]
  · have hy_bot := deleteTopPivots_horiz_bottom hadj.symm hx rfl
    dsimp at hy_bot
    subst hx hy_bot
    right; simp [treeParent, treeRank]
  · subst hy
    left; simp [treeParent, treeRank, show y + 1 ≠ -(n : ℤ) by omega]
  · subst hy
    right; simp [treeParent, treeRank, show y' + 1 ≠ -(n : ℤ) by omega]

theorem parafermionicCoverBoxGraph_deleteTopPivots_isAcyclic
    (n : ℕ) (_hn : 1 ≤ n) :
    ((parafermionicCoverBoxGraph n).deleteEdges
      (Set.range (parafermionicCoverFiniteFaceTopPivot n))).IsAcyclic := by
  classical
  let G := (parafermionicCoverBoxGraph n).deleteEdges
    (Set.range (parafermionicCoverFiniteFaceTopPivot n))
  intro w p hp
  obtain ⟨u, hu_mem, hu_max⟩ := Finset.exists_max_image p.support.toFinset
    (fun z : ParafermionicCoverBoxVertex n => treeRank z.1)
    ⟨w, List.mem_toFinset.2 p.start_mem_support⟩
  have hu : u ∈ p.support := List.mem_toFinset.1 hu_mem
  have hmax (z : ParafermionicCoverBoxVertex n) (hz : z ∈ p.support) :
      treeRank z.1 ≤ treeRank u.1 := hu_max z (List.mem_toFinset.2 hz)
  let q := p.rotate u hu
  have hq : q.IsCycle := hp.rotate hu
  have hq_not_nil : ¬ q.Nil := hq.not_nil
  have hq_sub {z : ParafermionicCoverBoxVertex n} (hz : z ∈ q.support) : z ∈ p.support := by
    dsimp [q, SimpleGraph.Walk.rotate] at hz
    rcases (SimpleGraph.Walk.mem_support_append_iff _ _).1 hz with h | h
    · exact p.support_dropUntil_subset hu h
    · exact p.support_takeUntil_subset hu h
  have hparent {z : ParafermionicCoverBoxVertex n} (hadj : G.Adj u z) (hz : z ∈ q.support) :
      z.1 = treeParent n u.1 := by
    rcases deleteTopPivots_parent_rank hadj with ⟨_, hlt⟩ | ⟨heq, _⟩
    · linarith [hmax z (hq_sub hz)]
    · exact heq
  have hsnd_mem : q.snd ∈ q.support := by
    have := SimpleGraph.Walk.dart_snd_mem_support_of_mem_darts q (SimpleGraph.Walk.firstDart_mem_darts hq_not_nil)
    simpa [SimpleGraph.Walk.firstDart] using this
  have hpen_mem : q.penultimate ∈ q.support := by
    have := SimpleGraph.Walk.dart_fst_mem_support_of_mem_darts q (SimpleGraph.Walk.lastDart_mem_darts hq_not_nil)
    simpa [SimpleGraph.Walk.lastDart] using this
  have hsnd_eq := hparent (q.adj_snd hq_not_nil) hsnd_mem
  have hpen_eq := hparent (q.adj_penultimate hq_not_nil).symm hpen_mem
  exact hq.snd_ne_penultimate (Subtype.ext (hsnd_eq.trans hpen_eq.symm))

end PottsDiscontinuity.TorusTopology.Planar.Medial
