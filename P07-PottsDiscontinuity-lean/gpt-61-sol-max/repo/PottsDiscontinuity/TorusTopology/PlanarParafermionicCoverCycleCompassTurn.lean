/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: namespace/import relocation; generic walk API only.
Generic compass definitions are copied from the same source. -/
module
public import Mathlib

public import Mathlib.Combinatorics.SimpleGraph.Walk.Operations
public import Mathlib.Tactic
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverSimpleCycleTurning
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverWalkFiniteBox

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open PottsDiscontinuity.TorusTopology.Planar
open SimpleGraph
open Classical

/-- The ordered compass labels of the actual directed darts of a full-cover walk. -/
noncomputable def parafermionicCoverWalkCompassDirections {u v : ParafermionicCoverVertex}
    (p : parafermionicCoverGraph.Walk u v) : List (Fin 4) :=
  p.darts.map fun d => parafermionicCoverCompassDirection d.fst d.snd d.adj



@[simp] theorem parafermionicCoverWalkCompassDirections_cons
    {u v w : ParafermionicCoverVertex}
    (h : parafermionicCoverGraph.Adj u v)
    (p : parafermionicCoverGraph.Walk v w) :
    parafermionicCoverWalkCompassDirections (Walk.cons h p) =
      parafermionicCoverCompassDirection u v h ::
        parafermionicCoverWalkCompassDirections p := rfl



theorem parafermionicCoverCompassDirection_eq_of_neighbor
    {u v : ParafermionicCoverVertex}
    (h : parafermionicCoverGraph.Adj u v) (d : Fin 4)
    (hd : parafermionicCoverCompassNeighbor u d = v) :
    parafermionicCoverCompassDirection u v h = d := parafermionicCoverCompassNeighbor_injective u
                                                      (Trans.trans (parafermionicCoverCompassDirection_neighbor u v h) (Eq.symm hd))

/-- The cyclic compass turn of an actual full-cover closed walk, including the
last-to-first dart pair. -/
noncomputable def parafermionicCoverWalkCyclicCompassTurn
    {u : ParafermionicCoverVertex}
    (p : parafermionicCoverGraph.Walk u u)  :=
  ((parafermionicCoverWalkCompassDirections p).zipWith
    primalCompassQuarterTurn
    ((parafermionicCoverWalkCompassDirections p).rotate 1)).sum



/-- Mapping an actual finite-box walk into the full cover preserves the exact
ordered compass label of every dart. -/

private theorem parafermionicCoverWalk_rotate_dart_fst_eq_snd
    {V : Type*} {G : SimpleGraph V} {u : V} (p : G.Walk u u) :
    (p.darts.map fun d => d.toProd.1).rotate 1 =
      p.darts.map fun d => d.toProd.2 := by
  cases p with
  | nil => simp
  | @cons a b c h q =>
      simp only [Walk.darts_cons, List.map_cons]
      rw [List.rotate_cons_succ]
      simp only [List.rotate_zero]
      
      
      rw [ Walk.map_fst_darts_append q ,  Walk.cons_map_snd_darts q ]

private theorem parafermionicCover_mem_zip_endpoint_eq
    {α β : Type*} (L R : List α) (fst snd : α → β)
    (hrot : R.map fst = L.map snd)
    {d e : α} (hmem : (d, e) ∈ L.zip R) : snd d = fst e := by
  induction L generalizing R with
  | nil => simp at hmem
  | cons a L ih =>
      cases R with
      | nil => simp at hmem
      | cons b R =>
          grind

section

variable {V : Type*} {G : SimpleGraph V} {u : V} (p : G.Walk u u) (hp : p.IsCycle) {d e : G.Dart} (hd : d ∈ p.darts) (he : e ∈ p.darts)
include hp hd he

private theorem parafermionicCoverDart_snd_injective_of_isCycle
    
    (h : d.snd = e.snd) : d = e := have hmap := Eq.mpr (congrArg List.Nodup (Walk.map_snd_darts p)) hp.support_nodup;
                                   (List.nodup_map_iff_inj_on (List.Nodup.of_map (fun x => x.toProd.2) hmap)).mp hmap d hd e he h

private theorem parafermionicCoverDart_fst_injective_of_isCycle
    
    (h : d.fst = e.fst) : d = e := by
  
  have hd' : d.symm ∈ p.reverse.darts := by simpa using hd
  have he' : e.symm ∈ p.reverse.darts := by simpa using he
  have h'  := h
  have := parafermionicCoverDart_snd_injective_of_isCycle p.reverse  hp.reverse  hd' he' h'
  simpa using congrArg Dart.symm this

end

private theorem parafermionicCoverPrimalCycle_pair_turn_eq_local
    {n : ℕ} {u : ParafermionicCoverBoxVertex n}
    (p : (parafermionicCoverBoxGraph n).Walk u u) (hp : p.IsCycle)
    {d e : (parafermionicCoverBoxGraph n).Dart}
    (hd : d ∈ p.darts) (he : e ∈ p.darts) (hde : d.snd = e.fst) :
    primalCompassQuarterTurn
      (parafermionicCoverCompassDirection d.fst.1 d.snd.1 d.adj)
      (parafermionicCoverCompassDirection e.fst.1 e.snd.1 e.adj) =
      parafermionicCoverPrimalCycleQuarterTurn p hp d.snd
        (Walk.dart_snd_mem_support_of_mem_darts p hd) := by
  let v := d.snd
  have hv  := Walk.dart_snd_mem_support_of_mem_darts p hd
  let q := p.rotate v hv
  have hqcycle : q.IsCycle := by
    simpa [q] using hp.rotate hv
  have hqnotnil  := hqcycle.not_nil
  
  
  have hlast : q.lastDart hqnotnil = d := by
    apply parafermionicCoverDart_snd_injective_of_isCycle p hp (by
                                                                  apply (p.rotate_darts v hv).mem_iff.mp
                                                                  exact Walk.lastDart_mem_darts hqnotnil) hd
    rfl
  have hfirst  := parafermionicCoverDart_fst_injective_of_isCycle p hp (by
                                                                                                    apply (p.rotate_darts v hv).mem_iff.mp
                                                                                                    exact Walk.firstDart_mem_darts hqnotnil) he hde
  
  have hout := parafermionicCoverPrimalCycleOutgoingDirection_neighbor p hp v hv
  
  have hqnext : q.snd = e.toProd.2 := congrArg (fun z => z.toProd.2) hfirst
  
  have hinQ : parafermionicCoverCompassNeighbor q.penultimate.1
      (parafermionicCoverPrimalCycleIncomingDirection p hp v hv) = v.1 :=  parafermionicCoverPrimalCycleIncomingDirection_neighbor p hp v hv 
  
  have houtQ : parafermionicCoverCompassNeighbor v.1
      (parafermionicCoverPrimalCycleOutgoingDirection p hp v hv) = q.snd.1 := hout
  have hout' : parafermionicCoverCompassNeighbor e.fst.1
      (parafermionicCoverPrimalCycleOutgoingDirection p hp v hv) = e.snd.1 := by
    grind
  
  
  simp [parafermionicCoverPrimalCycleQuarterTurn, v,  parafermionicCoverCompassDirection_eq_of_neighbor
                                                        (show parafermionicCoverGraph.Adj d.fst.1 d.snd.1 from d.adj)
                                                        (parafermionicCoverPrimalCycleIncomingDirection p hp v hv) (by
                                                                                                                      rw [← (congrArg (fun z => z.toProd.1) hlast)]
                                                                                                                      simpa [v] using hinQ) ,  parafermionicCoverCompassDirection_eq_of_neighbor
                                                              (show parafermionicCoverGraph.Adj e.fst.1 e.snd.1 from e.adj)
                                                              (parafermionicCoverPrimalCycleOutgoingDirection p hp v hv) hout' ]

theorem parafermionicCoverWalkCompassDirections_map_induce
    {S : Set ParafermionicCoverVertex} {u v : S}
    (p : (parafermionicCoverGraph.induce S).Walk u v) :
    parafermionicCoverWalkCompassDirections
      (p.map (SimpleGraph.Embedding.induce S).toHom) =
    p.darts.map  fun d => parafermionicCoverCompassDirection
      d.fst.1 d.snd.1 d.adj  := by
  
  induction p with
  | nil => rfl
  | @cons a b c h q ih =>
      simp only [parafermionicCoverWalkCompassDirections_cons, Walk.map_cons]
      rw [ih]
      rfl

section

variable {n : ℕ} {u : ParafermionicCoverBoxVertex n} (p : (parafermionicCoverBoxGraph n).Walk u u) (hp : p.IsCycle)
include hp

private theorem parafermionicCoverPrimalCycle_cyclicCompassTurn_eq_tail_sum
     :
    parafermionicCoverWalkCyclicCompassTurn
      (p.map (SimpleGraph.Embedding.induce
        (parafermionicCoverBoxVertices n)).toHom) =
      (p.support.tail.map fun v =>
        if hv : v ∈ p.support then
          parafermionicCoverPrimalCycleQuarterTurn p hp v hv else 0).sum := by
  
  let dir : (parafermionicCoverBoxGraph n).Dart → Fin 4 := fun d =>
    parafermionicCoverCompassDirection d.fst.1 d.snd.1  d.adj 
  
  let f  := fun v =>
    if hv : v ∈ p.support then parafermionicCoverPrimalCycleQuarterTurn p hp v hv else 0
  unfold parafermionicCoverWalkCyclicCompassTurn
  rw [ parafermionicCoverWalkCompassDirections_map_induce p , ← List.map_rotate]
  rw [List.zipWith_map]
  rw [← List.map_uncurry_zip_eq_zipWith]
  have hrot : (p.darts.rotate 1).map (fun d => d.toProd.1) =
      p.darts.map  fun d => d.toProd.2  :=
    by
      simp_all [parafermionicCoverWalk_rotate_dart_fst_eq_snd]
  have hmapfst : (p.darts.zip (p.darts.rotate 1)).map
      Prod.fst = p.darts := List.map_fst_zip (by simp)
  have hlist : (p.darts.zip (p.darts.rotate 1)).map
      (fun z => primalCompassQuarterTurn (dir z.1) (dir z.2)) =
      (p.darts.zip (p.darts.rotate 1)).map  fun z => f z.1.snd  := by
    apply List.map_congr_left
    intro z hz
    
    have hmem := List.of_mem_zip hz
    have hadj := parafermionicCover_mem_zip_endpoint_eq
      p.darts (p.darts.rotate 1) (fun d => d.toProd.1)
      (fun d => d.toProd.2) hrot hz
    have he  := List.mem_rotate.mp hmem.2
    have hturn := parafermionicCoverPrimalCycle_pair_turn_eq_local
      p hp hmem.1 he hadj
    simpa [f, Walk.dart_snd_mem_support_of_mem_darts p hmem.1] using hturn
  have hzipmap : (p.darts.zip (p.darts.rotate 1)).map
      (fun z => f z.1.snd) = p.darts.map  fun d => f d.snd  := by
    calc
      (p.darts.zip (p.darts.rotate 1)).map (fun z => f z.1.snd) =
          ((p.darts.zip (p.darts.rotate 1)).map Prod.fst).map
             fun d => f d.snd  := by simp 
      _ = p.darts.map  fun d => f d.snd  := by rw [hmapfst]
  have htail : p.darts.map (fun d => f d.snd) = p.support.tail.map f := by
    calc
      p.darts.map (fun d => f d.snd) =
          (p.darts.map  fun d => d.snd ).map f := by
        simp 
      _ = p.support.tail.map f := by rw [Walk.map_snd_darts]
  calc
    (List.map (fun z => primalCompassQuarterTurn (dir z.1) (dir z.2))
        (p.darts.zip (p.darts.rotate 1))).sum =
      ((p.darts.zip (p.darts.rotate 1)).map  fun z => f z.1.snd ).sum := by
        rw [hlist]
    _ = (p.darts.map  fun d => f d.snd ).sum := by
      rw [hzipmap]
    _ = (p.support.tail.map f).sum := by rw [htail]
    _ = (p.support.tail.map fun v =>
        if hv : v ∈ p.support then
          parafermionicCoverPrimalCycleQuarterTurn p hp v hv else 0).sum := by
      simp [f]

/-- For an actual finite-box simple cycle, the cyclic turn of its mapped full-cover
walk is exactly the already defined primal cycle turn sum. The zip includes the
last-to-first dart pair. -/
theorem parafermionicCoverWalkCyclicCompassTurn_map_boxCycle_eq_primalTurnSum
     :
    parafermionicCoverWalkCyclicCompassTurn
      (p.map (SimpleGraph.Embedding.induce
        (parafermionicCoverBoxVertices n)).toHom) =
      parafermionicCoverPrimalCycleTurnSum p hp := by
  
  let f  := fun v =>
    if hv : v ∈ p.support then parafermionicCoverPrimalCycleQuarterTurn p hp v hv else 0
  calc
    parafermionicCoverWalkCyclicCompassTurn
        (p.map (SimpleGraph.Embedding.induce
          (parafermionicCoverBoxVertices n)).toHom) =
      (p.support.tail.map f).sum := by
        grind [parafermionicCoverPrimalCycle_cyclicCompassTurn_eq_tail_sum]
    _ = Finset.sum p.support.toFinset f :=
      (parafermionicCoverPrimalCycle_support_sum_eq_tail_map_sum p hp f).symm
    _ = parafermionicCoverPrimalCycleTurnSum p hp := by
      symm
      apply parafermionicCoverPrimalCycleTurnSum_eq_support_sum_of_local_eq p hp f
      grind

end

/-- The discrete Umlaufsatz for every actual simple cycle in the full cover. -/
theorem parafermionicCoverWalkCyclicCompassTurn_eq_four_or_neg_four
    {u : ParafermionicCoverVertex} (p : parafermionicCoverGraph.Walk u u)
    (hp : p.IsCycle) :
    parafermionicCoverWalkCyclicCompassTurn p = 4 ∨
      parafermionicCoverWalkCyclicCompassTurn p = -4 := by
  obtain ⟨n, hn, hbox, hcycle, hmap⟩ :=
    parafermionicCoverCycle_exists_box_restriction p hp
  have hturn := parafermionicCoverPrimalCycleTurnSum_eq_four_or_neg_four hn _ hcycle
  rw [← parafermionicCoverWalkCyclicCompassTurn_map_boxCycle_eq_primalTurnSum _ hcycle,
    hmap] at hturn
  exact hturn

end PottsDiscontinuity.TorusTopology.Planar.Medial
