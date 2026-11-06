module

public import Chazelle.Golf

public import Chazelle.Core.OracleAt
public import Chazelle.Core.OracleNodeSem

/-!
# Lemma 3.6 (WP-H), part 15: the memory facts of the query from the structure

From `QAt` (and the word bound `E ≤ W`, which holds since `E` is a word of memory): the facts
the RAM lemmas of the query use (`QMem`, `OrdOK`, `ChordMemOK`, `ChordTabOK`, `LocMemOK`,
`NodeMemOK`).
-/

namespace Chazelle.Core

namespace OracleR

open OracleQ
open NFLoc (seq_lt seq_length)

@[expose] public section

variable {P : Polygon} {m : ℕ → ℕ} {O E : ℕ} {V : QV} {H : Host} {C : Chain} {N : NF}
  {B : OracleBook.BookData} {k : ℕ}

theorem QAt.isNF (h : QAt P m O E V H C N B k) : IsNF (chainModel C) (Qof P) N := h.canon.1

theorem QAt.nodeMem (h : QAt P m O E V H C N B k) : NodeMemOK m V N :=
  ⟨h.nf, h.nAB, h.nRB, h.nSB, h.nLB, h.hA, h.pos⟩

/-- The ends of the arc records lie on walk edges. -/
theorem QAt.edges_lt (h : QAt P m O E V H C N B k) {j : ℕ} (hj : j < N.arcs.length) :
    (N.arc j).s.edge < 2 * V.m + 7 ∧ (N.arc j).e.edge < 2 * V.m + 7 := by
  have hN := h.isNF
  obtain ⟨reg, -, hA, -⟩ := NFLoc.isNF_arcs hN
  obtain ⟨-, harc⟩ := hA.1 j hj
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hprop⟩ := id hN
  obtain ⟨hs, he⟩ := hprop j hj
  have hnW : (chainModel C).W.n = 2 * V.m + 7 := by
    Ξ walk_n
    have := h.desc.2.2.2.1
    Ξ ← h.dm, this
  have hkey : ∀ (w : WPos), ProperPos (chainModel C) (Qof P) (Qof P).n w →
      (chainModel C).key (Qof P) w < (chainModel C).W.n → w.edge < 2 * V.m + 7 := by
    intro w hw hk
    have : (w.edge : ℝ) < (chainModel C).W.n := by
      have := hw.1
      unfold Model.key at hk
      linarith
    rw [hnW] at this
    exact_mod_cast this
  exact ⟨hkey _ hs harc.2.1, hkey _ he harc.2.2.2.1⟩

/-- **The memory facts of the scans** from the structure. -/
theorem QAt.qmem (h : QAt P m O E V H C N B k) {W : ℕ} (hEW : E ≤ W) : QMem V m W := by
  have hN := h.isNF
  have hm := h.nodeMem
  obtain ⟨reg, -, hA, -⟩ := NFLoc.isNF_arcs hN
  have hAB := h.AB_TB
  have hTB := h.TB_le
  have hSB := h.SB_TB
  have hPOS := h.POS_le
  refine ⟨?_, fun j hj => ?_, fun v hv => ?_⟩
  · have := h.POS_le; omega
  · have hjN : j < N.arcs.length := by rw [← h.hA]; exact hj
    obtain ⟨e1, e2⟩ := h.edges_lt hjN
    refine ⟨by rw [arcSe_eq hm hj]; exact e1, by rw [arcEe_eq hm hj]; exact e2,
      (h.pos j hj).1, ⋄, ⋄⟩
  · have hvA : v < N.arcs.length := by rw [← h.hA]; exact hv
    have hj0 : nodeArc0 m V v = sj N v := by
      have := hm.nf.2.2.2.2.2.2.2.2.1 v (by rw [NFLoc.seq_length hN]; exact hvA)
      unfold nodeArc0 sj; rw [← hm.SB]; exact this
    have hj0A : sj N v < N.arcs.length := NFLoc.seq_lt hN hvA
    have hr : nodeReg m V v = rgi N v := by
      have := (hm.nf.2.2.2.2.2.2.1 _ hj0A).1
      unfold nodeReg rgi; rw [hj0, ← hm.AB]; exact this
    have hrR : rgi N v < N.regions.length := (hA.1 _ hj0A).1
    obtain ⟨hna, -, -, hlist, -⟩ := hm.nf.2.2.2.2.2.2.2.1 _ hrR
    have hna' : nodeNa m V v = (N.region (rgi N v)).arcs.length := by
      unfold nodeNa; rw [hr, ← hm.RB]; exact hna
    obtain ⟨hr1, hr2⟩ := h.regs _ hrR
    have hls : nodeLs m V v = m (V.RB + 5 * rgi N v + 1) := by unfold nodeLs; rw [hr]
    have hne : 0 < (N.region (rgi N v)).arcs.length := by
      have hmem : sj N v ∈ (N.region (rgi N v)).arcs := ((hA.2.2.2 _ hrR _).2 ⟨hj0A, rfl⟩)
      exact List.length_pos_of_mem hmem
    have h0 := hr2 0 hne
    refine ⟨⋄, by rw [hj0, ← h.hA] at *; exact hj0A, by rw [hr]; omega, by rw [hls]; omega,
      fun t ht => ⟨?_, by rw [hls]; rw [hna'] at ht; have := hr2 t ht; omega⟩⟩
    rw [hna'] at ht
    have hlt : nodeArc m V v t = (N.region (rgi N v)).arcs.getD t 0 := by
      unfold nodeArc nodeLs; rw [hr, ← hm.RB, ← hm.LB]; exact hlist t ht
    have hmem : (N.region (rgi N v)).arcs.getD t 0 ∈ (N.region (rgi N v)).arcs := by
      rw [NFLoc.getD_of_lt 0 ht]; exact List.getElem_mem ht
    Ξ hlt, h.hA
    exact ((hA.2.2.2 _ hrR _).1 hmem).1

theorem QAt.ordOK (h : QAt P m O E V H C N B k) {W : ℕ} (hEW : E ≤ W) : OrdOK m V W := by
  have := h.ORD_le; have := h.RK_le; have := h.LAB_le
  exact ⟨⋄, h.ord_lt, h.ord_inj, h.ord_rk, h.ord_sorted, ⋄, ⋄, ⋄⟩

theorem QAt.chordMem (h : QAt P m O E V H C N B k) {W : ℕ} (hEW : E ≤ W) :
    ChordMemOK V m W := by
  have := h.TB_le
  exact ⟨h.tab, h.K_lt, h.CH_le, ⋄, fun i hi => by have := h.CB_TB i hi; omega⟩

theorem QAt.chordTab (h : QAt P m O E V H C N B k) {W : ℕ} (hEW : E ≤ W) :
    ChordTabOK V m W := by
  have := h.TB_le; have := h.CH_le
  exact ⟨h.ch_lt, ⋄, fun i hi => by have := h.CB_TB i hi; omega⟩

/-- The chain descriptor copied into the model descriptor. -/
theorem QAt.mdDesc (h : QAt P m O E V H C N B k) : ChainDescAt m (V.MD + 1) (Qof P) H C := by
  obtain ⟨hH, hP, h1, h2, h3, h4⟩ := h.desc
  have e := h.md
  have e0 := e 0 (⋄); have e1 := e 1 (⋄); have e2 := e 2 (⋄)
  have e3 := e 3 (⋄); have e4 := e 4 (⋄)
  simp only [Nat.add_zero] at e0
  refine ⟨by rw [e0]; exact hH, hP, by rw [e1]; exact h1, ?_, ?_, ?_⟩
  · rw [show V.MD + 1 + 2 = V.MD + 1 + 2 from rfl, e2]; exact h2
  · rw [e3]; exact h3
  · rw [e4]; exact h4

theorem QAt.modelDesc (h : QAt P m O E V H C N B k) :
    ModelDescAt m V.MD (Qof P) (chainModel C) :=
  Or.inl ⟨h.md0, H, C, h.mdDesc, rfl⟩

theorem QAt.modelDescWF (h : QAt P m O E V H C N B k) : ModelDescWF P E m V.MD := by
  refine ⟨h.MD_le, fun _ => ⟨by have := h.MD_le; omega, fun H' C' hC' => ?_⟩⟩
  have hH : H' = H := NFLoc.hostAt_unique hC'.1 h.mdDesc.1
  have hC : C' = C := NFLoc.chain_eq_of_desc hC' h.mdDesc
  subst hH hC
  have e0 : m (V.MD + 1) = m V.D := by have := h.md 0 (⋄); simpa using this
  exact ⟨h.hostLen, h.hostWF, by rw [e0]; exact h.host_le, h.s_lt⟩

/-- **The memory facts of double identification** from the structure. -/
theorem QAt.locMem (h : QAt P m O E V H C N B k) {W : ℕ} (hEW : E ≤ W)
    (hW : hostWords P.n ≤ W) : LocMemOK P V m W (chainModel C) N := by
  obtain ⟨hMD, hwf⟩ := NFLoc.locChainWF_of h.modelDescWF hEW hW
  have hN := h.isNF
  have := h.TB_le; have := h.NB_TB; have := h.AB_TB; have := h.SB_TB
  have hAμ : V.A ≤ V.μ := by rw [h.hA, ← h.μ]; exact h.gOK.arcs_le
  refine ⟨h.modelDesc, Or.inl ⟨C, h.simple, rfl⟩, hMD, hwf, h.nf, hN, h.hA, fun j hj => ?_,
    h.tab, h.A_lt, ⋄, by rw [h.nAB]; omega, by rw [h.nSB]; omega, ⋄, hAμ⟩
  obtain ⟨-, -, -, reg, -, -, -, -, -, -, hpp⟩ := hN
  have := (hpp j hj).1
  rwa [show (Qof P).n = P.n from shear_n _ _] at this

end

end OracleR

end Chazelle.Core
