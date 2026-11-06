module

public import Chazelle.Core.OracleCostQ

/-!
# Lemma 3.6 (WP-H), part 26: the cost bounds of the query from the structure

From `QAt`: the scan of one node costs at most `NCof w` with `w = min(γ, 2 m + 7)`
(`nodeCost_le`: at most five arcs of at most `w + 11` walk edges); a cluster has at most `8 k²`
nodes (`clusSize_le`); the scan of `D*` costs at most `7 k² (NCof w + 6)` (`dstarCost_le`).
-/

namespace Chazelle.Core

namespace OracleR

open OracleQ OracleBook

@[expose] public section

/-- The cost bound of the scan of one node. -/
def NCof (w : ℕ) : ℕ := 5 * (1132 * (w + 11) + 40) + 40

variable {P : Polygon} {m : ℕ → ℕ} {O E : ℕ} {V : QV} {H : Host} {C : Chain} {N : NF}
  {B : BookData} {k : ℕ}

/-- The number of arcs of the region of a node, and its arcs. -/
theorem QAt.nodeNa_eq (h : QAt P m O E V H C N B k) {u : ℕ} (hu : u < V.A) :
    nodeNa m V u = (N.region (rgi N u)).arcs.length ∧ rgi N u < N.regions.length ∧
      ∀ t, t < nodeNa m V u → nodeArc m V u t = (N.region (rgi N u)).arcs.getD t 0 := by
  have hN := h.isNF
  have hm := h.nodeMem
  obtain ⟨reg, -, hA, -⟩ := NFLoc.isNF_arcs hN
  have huA : u < N.arcs.length := by rwa [← h.hA]
  have hj0 : nodeArc0 m V u = sj N u := by
    have := hm.nf.2.2.2.2.2.2.2.2.1 u (by rwa [NFLoc.seq_length hN])
    unfold nodeArc0 sj; rw [← hm.SB]; exact this
  have hj0A : sj N u < N.arcs.length := NFLoc.seq_lt hN huA
  have hr : nodeReg m V u = rgi N u := by
    have := (hm.nf.2.2.2.2.2.2.1 _ hj0A).1
    unfold nodeReg rgi; rw [hj0, ← hm.AB]; exact this
  have hrR : rgi N u < N.regions.length := (hA.1 _ hj0A).1
  obtain ⟨hna, -, -, hlist, -⟩ := hm.nf.2.2.2.2.2.2.2.1 _ hrR
  have hna' : nodeNa m V u = (N.region (rgi N u)).arcs.length := by
    unfold nodeNa; rwa [hr, ← hm.RB]
  refine ⟨hna', hrR, fun t ht => ?_⟩
  rw [hna'] at ht
  unfold nodeArc nodeLs; rw [hr, ← hm.RB, ← hm.LB]; exact hlist t ht

/-- The walk edges scanned for an arc record, from the normal form. -/
theorem QAt.arcLen_eq (h : QAt P m O E V H C N B k) {j : ℕ} (hj : j < V.A) :
    arcLenM m V j = scanLenR N (2 * V.m + 7) N.arcs.length (arcPos m V j) ∧
      arcPos m V j < N.arcs.length := by
  have hm := h.nodeMem
  obtain ⟨hpA, hpj⟩ := hm.pos j hj
  have hsj : sj N (arcPos m V j) = j := hpj
  refine ⟨?_, by rwa [← h.hA]⟩
  unfold scanLenR arcLenM lenOf
  rw [hsj, ← h.hA, arcSe_eq hm hj, arcEe_eq hm hj]

/-- **The cost of the scan of a node.** -/
theorem QAt.nodeCost_le (h : QAt P m O E V H C N B k) (hP : C.P.Simple) {u : ℕ} :
    nodeCost m V u ≤ NCof (min (m (O + 2)) (2 * V.m + 7)) := by
  have hC := h.canon
  have hVm : V.m = C.m := by
    obtain ⟨-, -, -, hd2, -⟩ := h.desc; rw [← h.dm, hd2]
  unfold nodeCost NCof
  split_ifs with hu
  swap
  · omega
  obtain ⟨hna, hrR, -⟩ := h.nodeNa_eq hu
  have h5 := region_arcs_le hP hC hrR
  have hterm : ∀ i ∈ Finset.Ico 0 (nodeNa m V u),
      1132 * (arcLenM m V (nodeArc m V u i) + 1) + 40 ≤
        1132 * (min (m (O + 2)) (2 * V.m + 7) + 11) + 40 := by
    intro i hi
    rw [Finset.mem_Ico] at hi
    have hjA := ((h.qmem (W := E) le_rfl).node u hu).2.2.2.2 i hi.2
    obtain ⟨e1, e2⟩ := h.arcLen_eq hjA.1
    obtain ⟨b1, b2⟩ := scanLen_le hP hC e2
    have hb : arcLenM m V (nodeArc m V u i) ≤ min (m (O + 2)) (2 * V.m + 7) + 10 := by
      rw [e1, hVm]
      rcases le_total (m (O + 2)) (2 * C.m + 7) with hh | hh
      · rw [min_eq_left hh]; omega
      · rw [min_eq_right hh]; omega
    omega
  unfold nodeCostFrom
  have := Finset.sum_le_card_nsmul _ _ _ hterm
  rw [Nat.card_Ico, Nat.sub_zero, smul_eq_mul] at this
  have h5' : nodeNa m V u ≤ 5 := by rwa [hna]
  have := Nat.mul_le_mul_right (1132 * (min (m (O + 2)) (2 * V.m + 7) + 11) + 40) h5'
  omega

/-- The flagged nodes are at most the length of the list of `D*`. -/
theorem QAt.flagged_le (h : QAt P m O E V H C N B k) :
    ((Finset.range V.μ).filter fun v => m (V.FL + v) = 1).card ≤ V.nD := by
  classical
  calc ((Finset.range V.μ).filter fun v => m (V.FL + v) = 1).card
      ≤ ((Finset.range V.nD).image fun i => m (V.DL + i)).card := by
        apply Finset.card_le_card
        intro v hv
        rw [Finset.mem_filter, Finset.mem_range] at hv
        obtain ⟨i, hi, hiv⟩ := h.dl_all v hv.1 hv.2
        exact Finset.mem_image.2 ⟨i, Finset.mem_range.2 hi, hiv⟩
    _ ≤ (Finset.range V.nD).card := Finset.card_image_le
    _ = V.nD := Finset.card_range _

/-- **A cluster has at most `8 k²` nodes.** -/
theorem QAt.clusSize_le (h : QAt P m O E V H C N B k) (l : ℕ) : clusSize m V l ≤ 8 * k ^ 2 := by
  classical
  unfold clusSize
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.range V.μ).filter fun u => lab m V u = l) (fun v => m (V.FL + v) = 1)
  have h1 : (((Finset.range V.μ).filter fun u => lab m V u = l).filter
      fun v => m (V.FL + v) = 1).card ≤ V.nD := by
    refine le_trans (Finset.card_le_card ?_) h.flagged_le
    intro v hv; simp only [Finset.mem_filter] at hv ⊢; exact ⟨hv.1.1, hv.2⟩
  have h2 : (((Finset.range V.μ).filter fun u => lab m V u = l).filter
      fun v => ¬ m (V.FL + v) = 1).card ≤ k ^ 2 := by
    refine le_trans (Finset.card_le_card ?_) (h.clus l)
    intro v hv; simp only [Finset.mem_filter] at hv ⊢; exact ⟨hv.1.1, hv.2, hv.1.2⟩
  have := h.nD_le
  omega

/-- **The cost of the scan of `D*`.** -/
theorem QAt.dstarCost_le (h : QAt P m O E V H C N B k) (hP : C.P.Simple) :
    dstarCost m V ≤ 7 * k ^ 2 * (NCof (min (m (O + 2)) (2 * V.m + 7)) + 6) + 4 := by
  unfold dstarCost dstarCostFrom
  have := Finset.sum_le_card_nsmul (Finset.Ico 0 V.nD) (fun t => nodeCost m V (m (V.DL + t)) + 6)
    (NCof (min (m (O + 2)) (2 * V.m + 7)) + 6) (fun t _ => by
      have := h.nodeCost_le hP (u := m (V.DL + t)); omega)
  rw [Nat.card_Ico, Nat.sub_zero, smul_eq_mul] at this
  have := Nat.mul_le_mul_right (NCof (min (m (O + 2)) (2 * V.m + 7)) + 6) h.nD_le
  omega

end

end OracleR

end Chazelle.Core
