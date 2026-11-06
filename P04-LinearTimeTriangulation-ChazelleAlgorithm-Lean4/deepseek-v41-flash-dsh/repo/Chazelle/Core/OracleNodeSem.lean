module

public import Chazelle.Golf

public import Chazelle.Core.OracleRamNode

/-!
# Lemma 3.6 (WP-H), part 13: the points scanned for a node are its `nodeScan`

`nodePts_eq`: with the normal form in memory (`NodeMemOK`: the layout `NFAt`, the bases of its
areas, and the inverse `POS` of the arc-sequence table), the points the program scans for node
`v` (`OracleR.nodePts`) are the scanned points of the node in the sense of the correctness proof
(`OracleQ.nodeScan`).
-/

namespace Chazelle.Core

@[expose] public section

open Set
open OracleQ OracleR

namespace OracleQ

/-- **The normal form in memory, as the scans read it.** -/
structure NodeMemOK (m : ℕ → ℕ) (V : QV) (N : NF) : Prop where
  nf : NFAt m V.NB N
  AB : m (V.NB + 4) = V.AB
  RB : m (V.NB + 5) = V.RB
  SB : m (V.NB + 6) = V.SB
  LB : m (V.NB + 7) = V.LB
  A : V.A = N.arcs.length
  pos : ∀ j, j < V.A → m (V.POS + j) < V.A ∧ N.seq.getD (m (V.POS + j)) 0 = j

variable {C : Chain} {Q : Polygon} {N : NF} {m : ℕ → ℕ} {V : QV}

theorem arcSe_eq (hm : NodeMemOK m V N) {j : ℕ} (hj : j < V.A) :
    arcSe m V j = (N.arc j).s.edge := by
  have := (hm.nf.2.2.2.2.2.2.1 j (by rw [← hm.A]; exact hj)).2.1
  unfold arcSe; rw [← hm.AB]; exact this

theorem arcEe_eq (hm : NodeMemOK m V N) {j : ℕ} (hj : j < V.A) :
    arcEe m V j = (N.arc j).e.edge := by
  have := (hm.nf.2.2.2.2.2.2.1 j (by rw [← hm.A]; exact hj)).2.2.2.1
  unfold arcEe; rw [← hm.AB]; exact this

/-- **The points scanned for an arc record** are the scanned points of its spine position. -/
theorem arcPts_eq (hN : IsNF (chainModel C) Q N) (hP : C.P.Simple) (hm : NodeMemOK m V N)
    (hVm : V.m = C.m) {j : ℕ} (hj : j < V.A) :
    arcPts m V C j = scanSet C Q N (arcPos m V j) := by
  obtain ⟨hpA, hpj⟩ := hm.pos j hj
  have hnW : (chainModel C).W.n = 2 * V.m + 7 := Ρ walk_n, hVm
  have hsj : sj N (arcPos m V j) = j := hpj
  ext x
  Ξ mem_scanSet_iff, scanLen_eq C Q N hN hP (by rw [← hm.A]; exact hpA)
  unfold arcPts scanned
  ϴ mem_ofPred_eq
  have hlen : scanLenR N (chainModel C).W.n N.arcs.length (arcPos m V j) = arcLenM m V j := by
    unfold scanLenR arcLenM lenOf
    Ξ hsj, hnW, ← hm.A, arcSe_eq hm hj, arcEe_eq hm hj
  have hidx : ∀ k, scanIdx (chainModel C).W.n N (arcPos m V j) k =
      scanW (2 * V.m + 7) (arcSe m V j) k := by
    intro k; unfold scanIdx scanW; rw [hsj, hnW, arcSe_eq hm hj]
  Ξ hlen
  constructor
  · rintro ⟨k, hk, hx⟩; exact ⟨k, ⋄, by rw [hidx]; exact hx⟩
  · rintro ⟨k, hk, hx⟩; exact ⟨k, ⋄, by rw [← hidx]; exact hx⟩

/-- **The points scanned for a node are its `nodeScan`.** -/
theorem nodePts_eq (hN : IsNF (chainModel C) Q N) (hP : C.P.Simple) (hm : NodeMemOK m V N)
    (hVm : V.m = C.m) (v : ℕ) : nodePts m V C v = nodeScan C Q N v := by
  obtain ⟨reg, hR, hA, -⟩ := NFLoc.isNF_arcs hN
  have hsl := NFLoc.seq_length hN
  ext x
  ϴ nodePts, nodeScan, mem_ofPred_eq
  Ξ ← hm.A
  by_cases hv : v < V.A
  swap
  · exact ⟨fun h => absurd h.1 hv, fun h => absurd h.1 hv⟩
  have hvA : v < N.arcs.length := by rw [← hm.A]; exact hv
  -- the region of the node
  have hj0 : nodeArc0 m V v = sj N v := by
    have := hm.nf.2.2.2.2.2.2.2.2.1 v (⋄)
    unfold nodeArc0 sj; rw [← hm.SB]; exact this
  have hj0A : sj N v < N.arcs.length := NFLoc.seq_lt hN hvA
  have hr : nodeReg m V v = rgi N v := by
    have := (hm.nf.2.2.2.2.2.2.1 _ hj0A).1
    unfold nodeReg rgi; rw [hj0, ← hm.AB]; exact this
  have hrR : rgi N v < N.regions.length := (hA.1 _ hj0A).1
  obtain ⟨hna, -, -, hlist, -⟩ := hm.nf.2.2.2.2.2.2.2.1 _ hrR
  have hna' : nodeNa m V v = (N.region (rgi N v)).arcs.length := by
    unfold nodeNa; rw [hr, ← hm.RB]; exact hna
  have hls : ∀ t, t < (N.region (rgi N v)).arcs.length →
      nodeArc m V v t = (N.region (rgi N v)).arcs.getD t 0 := by
    intro t ht
    unfold nodeArc nodeLs; rw [hr, ← hm.RB, ← hm.LB]; exact hlist t ht
  have hmemR := hA.2.2.2 _ hrR
  constructor
  · rintro ⟨-, t, ht, hx⟩
    refine ⟨hv, ?_⟩
    rw [hna'] at ht
    rw [hls t ht] at hx
    set j := (N.region (rgi N v)).arcs.getD t 0 with hj
    have hjmem : j ∈ (N.region (rgi N v)).arcs := by
      rw [hj, NFLoc.getD_of_lt 0 ht]; exact List.getElem_mem ht
    obtain ⟨hjA, hjr⟩ := (hmemR j).1 hjmem
    have hjA' : j < V.A := by rw [hm.A]; exact hjA
    obtain ⟨hpA, hpj⟩ := hm.pos j hjA'
    refine ⟨arcPos m V j, hpA, ?_, ?_⟩
    · show (N.arc (N.seq.getD (m (V.POS + j)) 0)).reg = rgi N v
      Ξ hpj, hjr
    · rw [← arcPts_eq hN hP hm hVm hjA']; exact hx
  · rintro ⟨-, p, hp, hrp, hx⟩
    refine ⟨hv, ?_⟩
    have hpN : p < N.arcs.length := by rw [← hm.A]; exact hp
    set j := sj N p with hj
    have hjA : j < N.arcs.length := NFLoc.seq_lt hN hpN
    have hjA' : j < V.A := by rw [hm.A]; exact hjA
    have hjmem : j ∈ (N.region (rgi N v)).arcs := (hmemR j).2 ⟨hjA, hrp⟩
    obtain ⟨t, ht, htj⟩ := List.getElem_of_mem hjmem
    obtain ⟨hpA, hpj⟩ := hm.pos j hjA'
    have hpp : arcPos m V j = p := sj_inj hN (by rw [← hm.A]; exact hpA) hpN hpj
    refine ⟨t, by rw [hna']; exact ht, ?_⟩
    Ξ hls t ht, NFLoc.getD_of_lt 0 ht, htj, arcPts_eq hN hP hm hVm hjA', hpp
    exact hx

end OracleQ

end

end Chazelle.Core
