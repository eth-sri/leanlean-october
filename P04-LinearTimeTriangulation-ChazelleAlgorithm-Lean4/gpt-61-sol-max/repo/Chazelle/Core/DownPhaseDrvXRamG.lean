module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.DownPhaseDrvXRamF

/-!
# Down phase, extraction (D6), RAM part 7: a kept chord

`keptS_exec`: for a kept chord (left host point in `217055 … 217057`, right one in
`217070 … 217072`), `keptS` stores the triple `(h, pEdge sL, pEdge sR)` at `LxB + 3 cnt` and the
buckets `keyBkt` of the two interior end positions at `BkB + 2 cnt`.
-/

namespace Chazelle.Core

namespace DrvX

open Machine Machine.Stmt Programs BuildRam SignK
open Chazelle.Chain (sideInArc)
open DrvR (ivB qE keyBkt)

@[expose] public section

section kept

variable {P : Polygon} {W : ℕ}

set_option maxHeartbeats 8000000 in
open Classical in
/-- **A kept chord.** -/
theorem keptS_exec (d : Config) (hw : WordsBounded W d) (hG : GoodEnv P) {li : Bool}
    (hli : li = true ↔ Mountain.LeftInside (Qof P)) (hdh : DistinctHeights (Qof P))
    (hn2 : 2 ≤ (Qof P).n) {N : NF} {sL sR : SymPt} {h LxB BkB cnt AB RA nRA : ℕ}
    {ras : ℕ → ℕ} (hsL : sL.Lt (Qof P).n) (hsR : sR.Lt (Qof P).n)
    (encL : EncV (d.nreg 217055) (d.nreg 217056) (d.nreg 217057) sL) (encR : Enc d sR)
    (hxL : GoodPos (Qof P) ⟨pEdge li (Qof P).n sL, h + 1⟩)
    (hxR : GoodPos (Qof P) ⟨pEdge li (Qof P).n sR, h + 1⟩)
    (hexL : ∃ t, t < nRA ∧ OnArcP (Qof P) li N (ras t) ⟨pEdge li (Qof P).n sL, h + 1⟩)
    (hexR : ∃ t, t < nRA ∧ OnArcP (Qof P) li N (ras t) ⟨pEdge li (Qof P).n sR, h + 1⟩)
    (hgood : ∀ j, j < N.arcs.length → GoodPos (Qof P) (N.arc j).s ∧ GoodPos (Qof P) (N.arc j).e)
    (hinc : ∀ j j', j < j' → j' < N.arcs.length →
      (interiorModel (Qof P)).key (Qof P) (N.arc j).s <
        (interiorModel (Qof P)).key (Qof P) (N.arc j').s)
    (hnext : ∀ j, j < N.arcs.length →
      (interiorModel (Qof P)).key (Qof P) (N.arc j).e =
        (interiorModel (Qof P)).key (Qof P) (N.arc ((j + 1) % N.arcs.length)).s)
    (hfree : ∀ j j', j < N.arcs.length → j' < N.arcs.length →
      ¬ sideInArc ((interiorModel (Qof P)).key (Qof P) (N.arc j).s)
        ((interiorModel (Qof P)).key (Qof P) (N.arc j).e)
        ((interiorModel (Qof P)).key (Qof P) (N.arc j').s))
    (hAm : ∀ j, j < N.arcs.length → d.nmem (AB + 5 * j + 1) = (N.arc j).s.edge ∧
      d.nmem (AB + 5 * j + 2) = (N.arc j).s.hgt ∧ d.nmem (AB + 5 * j + 3) = (N.arc j).e.edge ∧
      d.nmem (AB + 5 * j + 4) = (N.arc j).e.hgt)
    (hRm : ∀ t, t < nRA → d.nmem (RA + t) = ras t ∧ ras t < N.arcs.length)
    (hAW : ∀ j, j < N.arcs.length → AB + 5 * j + 4 ≤ W) (hRW : RA + nRA ≤ W)
    (h2A : 2 * N.arcs.length + 2 ≤ W) (hnW : (Qof P).n ≤ W)
    (h20 : d.nreg 217020 = (Qof P).n) (h26 : d.nreg 217026 = liV li) (h27 : d.nreg 217027 = 1)
    (h30 : d.nreg 217030 = N.arcs.length) (h31 : d.nreg 217031 = AB) (h32 : d.nreg 217032 = nRA)
    (h33 : d.nreg 217033 = RA) (h44 : d.nreg 217044 = 2)
    (h50 : d.nreg 217050 = h) (h53 : d.nreg 217053 = h + 1)
    (h38 : d.nreg 217038 = cnt) (h45 : d.nreg 217045 = LxB + 3 * cnt)
    (h46 : d.nreg 217046 = BkB + 2 * cnt)
    (hLW : LxB + 3 * cnt + 3 ≤ W) (hBW : BkB + 2 * cnt + 2 ≤ W) (hcW : cnt + 1 ≤ W) :
    ∃ d' k, Exec P W keptS d d' k ∧ k ≤ 604 * nRA + 120 ∧
      d'.nmem = upd (upd (upd (upd (upd d.nmem (LxB + 3 * cnt) h) (LxB + 3 * cnt + 1)
        (pEdge li (Qof P).n sL)) (LxB + 3 * cnt + 2) (pEdge li (Qof P).n sR)) (BkB + 2 * cnt)
          (keyBkt (Qof P) N ⟨pEdge li (Qof P).n sL, h + 1⟩)) (BkB + 2 * cnt + 1)
          (keyBkt (Qof P) N ⟨pEdge li (Qof P).n sR, h + 1⟩) ∧
      d'.nreg 217038 = cnt + 1 ∧ d'.nreg 217045 = LxB + 3 * (cnt + 1) ∧
      d'.nreg 217046 = BkB + 2 * (cnt + 1) ∧ FrameM Bkept d d' := by
  -- the buckets agree with `keyBkt`
  have hbkt : ∀ (x : WPos) (t : ℕ), t < nRA → GoodPos (Qof P) x → OnArcP (Qof P) li N (ras t) x →
      bktF N.arcs.length (ras t) (PosEq x (N.arc (ras t)).s) (PosEq x (N.arc (ras t)).e)
        (PosLt (Qof P) li (N.arc (ras t)).s x) = keyBkt (Qof P) N x := by
    intro x t ht hx hon
    have hj := (hRm t ht).2
    exact (bkt_spec hli hdh hn2 rfl hinc hnext hfree hj hx (hgood _ hj).1 (hgood _ hj).2 hon).symm
  -- step 1: save the right point, load the left one
  obtain ⟨d1, k1, e1, hk1, a70, a71, a72, a80, a81, a82⟩ : ∃ d1 k1, Exec P W
      (block [.copyN 217080 217070, .copyN 217081 217071, .copyN 217082 217072,
        .copyN 217070 217055, .copyN 217071 217056, .copyN 217072 217057]) d d1 k1 ∧ k1 ≤ 6 ∧
      d1.nreg 217070 = d.nreg 217055 ∧ d1.nreg 217071 = d.nreg 217056 ∧
      d1.nreg 217072 = d.nreg 217057 ∧ d1.nreg 217080 = d.nreg 217070 ∧
      d1.nreg 217081 = d.nreg 217071 ∧ d1.nreg 217082 = d.nreg 217072 := by
    exec_block
    ram_simp
  have f1 : FrameB (fun r => decide ((217070 ≤ r ∧ r ≤ 217072) ∨ (217080 ≤ r ∧ r ≤ 217082))) d d1 :=
    exec_frameB e1 (by decide)
  have hw1 := e1.wb_right
  have q1 : ∀ r, r < 217070 ∨ (217072 < r ∧ r < 217080) ∨ 217082 < r → d1.nreg r = d.nreg r :=
    fun r hr => f1.1 r (by omega_nf)
  have enc1 : Enc d1 sL := by grind [enc_iff]
  -- step 2: left interior edge
  obtain ⟨d2, k2, e2, hk2, v2, f2⟩ := peS_exec (P := P) d1 hw1 hsL enc1 hnW
    (by ram_grind) (by rw [q1 _ (by omega), h26]) (by ram_grind)
    (by ram_grind)
  have hw2 := e2.wb_right
  -- step 3: save it, restore the right point
  obtain ⟨d3, k3, e3, hk3, a84, b70, b71, b72⟩ : ∃ d3 k3, Exec P W
      (block [.copyN 217084 217100, .copyN 217070 217080, .copyN 217071 217081,
        .copyN 217072 217082]) d2 d3 k3 ∧ k3 ≤ 4 ∧
      d3.nreg 217084 = d2.nreg 217100 ∧ d3.nreg 217070 = d2.nreg 217080 ∧
      d3.nreg 217071 = d2.nreg 217081 ∧ d3.nreg 217072 = d2.nreg 217082 := by
    exec_block
    ram_simp
  have f3 : FrameB (fun r => decide ((217070 ≤ r ∧ r ≤ 217072) ∨ r = 217084)) d2 d3 :=
    exec_frameB e3 (by decide)
  have hw3 := e3.wb_right
  have enc3 : Enc d3 sR := by
    refine encR.congr ?_ ?_ ?_
    · rw [b70, f2.1 _ (by decide), a80]
    · rw [b71, f2.1 _ (by decide), a81]
    · rw [b72, f2.1 _ (by decide), a82]
  -- globals in `d3`
  have q3 : ∀ r, (r < 217070 ∨ (217072 < r ∧ r < 217080) ∨ (217087 < r ∧ r < 217100)) →
      d3.nreg r = d.nreg r := fun r hr => by
    rw [f3.1 _ (by omega_nf),
      f2.1 _ (by simp only [Bpe, decide_eq_false_iff_not]; omega), q1 _ (by omega)]
  -- step 4: right interior edge
  obtain ⟨d4, k4, e4, hk4, v4, f4⟩ := peS_exec (P := P) d3 hw3 hsR enc3 hnW
    (by grind) (by rw [q3 _ (by omega), h26]) (by grind)
    (by grind)
  have hw4 := e4.wb_right
  -- step 5: the left position
  obtain ⟨d5, k5, e5, hk5, a85, a110, a111⟩ : ∃ d5 k5, Exec P W
      (block [.copyN 217085 217100, .copyN 217110 217084, .copyN 217111 217053]) d4 d5 k5 ∧
      k5 ≤ 3 ∧ d5.nreg 217085 = d4.nreg 217100 ∧ d5.nreg 217110 = d4.nreg 217084 ∧
      d5.nreg 217111 = d4.nreg 217053 := by
    exec_block
    ram_simp
  have f5 : FrameB (fun r => decide (r = 217085 ∨ r = 217110 ∨ r = 217111)) d4 d5 :=
    exec_frameB e5 (by decide)
  have hw5 := e5.wb_right
  have q5 : ∀ r, (r < 217070 ∨ (217072 < r ∧ r < 217080) ∨ (217087 < r ∧ r < 217100)) →
      d5.nreg r = d.nreg r := fun r hr => by
    rw [f5.1 _ (by simp only [decide_eq_false_iff_not]; omega),
      f4.1 _ (by simp only [Bpe, decide_eq_false_iff_not]; omega), q3 _ hr]
  have m5 : d5.nmem = d.nmem := by
    rw [f5.2.2.1, f4.2.2.1, f3.2.2.1, f2.2.2.1, f1.2.2.1]
  have eL : d5.nreg 217084 = pEdge li (Qof P).n sL := by
    rw [f5.1 _ (by decide), f4.1 _ (by decide), a84, v2]
  have eR : d5.nreg 217085 = pEdge li (Qof P).n sR := by rw [a85, v4]
  -- step 6: left bucket
  obtain ⟨d6, k6, e6, hk6, ⟨tL, htL, honL, v6⟩, f6⟩ := bktS_exec (P := P) d5 hw5 hG (li := li)
    (N := N) (x := ⟨pEdge li (Qof P).n sL, h + 1⟩) (AB := AB) (RA := RA) (nRA := nRA) (ras := ras)
    hxL hgood (by ram_simp) (by ram_simp) hAW hRW h2A hnW
    (by ram_simp) (by ram_simp) (by ram_simp)
    (by ram_simp) (by ram_simp) (by ram_simp)
    (by ram_simp) (by ram_simp)
    (by rw [a110, f4.1 _ (by decide), a84, v2])
    (by rw [a111, f4.1 _ (by decide), q3 _ (by omega), h53]) hexL
  have hw6 := e6.wb_right
  have kL : d6.nreg 217112 = keyBkt (Qof P) N ⟨pEdge li (Qof P).n sL, h + 1⟩ := by
    ram_simp
  -- step 7: the right position
  obtain ⟨d7, k7, e7, hk7, a86, c110, c111⟩ : ∃ d7 k7, Exec P W
      (block [.copyN 217086 217112, .copyN 217110 217085, .copyN 217111 217053]) d6 d7 k7 ∧
      k7 ≤ 3 ∧ d7.nreg 217086 = d6.nreg 217112 ∧ d7.nreg 217110 = d6.nreg 217085 ∧
      d7.nreg 217111 = d6.nreg 217053 := by
    exec_block
    ram_simp
  have f7 : FrameB (fun r => decide (r = 217086 ∨ r = 217110 ∨ r = 217111)) d6 d7 :=
    exec_frameB e7 (by decide)
  have hw7 := e7.wb_right
  have q7 : ∀ r, (r < 217070 ∨ (217072 < r ∧ r < 217080) ∨ (217087 < r ∧ r < 217100)) →
      d7.nreg r = d.nreg r := fun r hr => by
    rw [f7.1 _ (by simp only [decide_eq_false_iff_not]; omega),
      f6.1 _ (by simp only [Bbkt, decide_eq_false_iff_not]; omega), q5 _ hr]
  have m7 : d7.nmem = d.nmem := by rw [f7.2.2.1, f6.2.2.1, m5]
  -- step 8: right bucket
  obtain ⟨d8, k8, e8, hk8, ⟨tR, htR, honR, v8⟩, f8⟩ := bktS_exec (P := P) d7 hw7 hG (li := li)
    (N := N) (x := ⟨pEdge li (Qof P).n sR, h + 1⟩) (AB := AB) (RA := RA) (nRA := nRA) (ras := ras)
    hxR hgood (by ram_simp) (by ram_simp) hAW hRW h2A hnW
    (by ram_simp) (by ram_simp) (by ram_simp)
    (by ram_simp) (by ram_simp) (by ram_simp)
    (by ram_simp) (by ram_simp)
    (by rw [c110, f6.1 _ (by decide), eR])
    (by rw [c111, f6.1 _ (by decide), q5 _ (by omega), h53]) hexR
  have hw8 := e8.wb_right
  have kR : d8.nreg 217112 = keyBkt (Qof P) N ⟨pEdge li (Qof P).n sR, h + 1⟩ := by
    ram_simp
  -- values in `d8`
  have q8 : ∀ r, (r < 217070 ∨ (217072 < r ∧ r < 217080) ∨ (217087 < r ∧ r < 217100)) →
      d8.nreg r = d.nreg r := fun r hr => by
    rw [f8.1 _ (by simp only [Bbkt, decide_eq_false_iff_not]; omega), q7 _ hr]
  have m8 : d8.nmem = d.nmem := by rw [f8.2.2.1, m7]
  have r45 : d8.nreg 217045 = LxB + 3 * cnt := by ram_simp
  have r46 : d8.nreg 217046 = BkB + 2 * cnt := by ram_simp
  have r38 : d8.nreg 217038 = cnt := by ram_simp
  have r27 : d8.nreg 217027 = 1 := by ram_simp
  have r50 : d8.nreg 217050 = h := by ram_simp
  have r84 : d8.nreg 217084 = pEdge li (Qof P).n sL := by
    rw [f8.1 _ (by decide), f7.1 _ (by decide), f6.1 _ (by decide), eL]
  have r85 : d8.nreg 217085 = pEdge li (Qof P).n sR := by
    rw [f8.1 _ (by decide), f7.1 _ (by decide), f6.1 _ (by decide), eR]
  have r86 : d8.nreg 217086 = keyBkt (Qof P) N ⟨pEdge li (Qof P).n sL, h + 1⟩ := by
    rw [f8.1 _ (by decide), a86, kL]
  -- step 9: the stores
  obtain ⟨d9, k9, e9, hk9, m9, c38, c45, c46⟩ : ∃ d9 k9, Exec P W
      (block [.copyN 217087 217112,
        .storeN 217045 217050, .addN 217045 217045 217027,
        .storeN 217045 217084, .addN 217045 217045 217027,
        .storeN 217045 217085, .addN 217045 217045 217027,
        .storeN 217046 217086, .addN 217046 217046 217027,
        .storeN 217046 217087, .addN 217046 217046 217027,
        .addN 217038 217038 217027]) d8 d9 k9 ∧ k9 ≤ 12 ∧
      d9.nmem = upd (upd (upd (upd (upd d.nmem (LxB + 3 * cnt) h) (LxB + 3 * cnt + 1)
        (pEdge li (Qof P).n sL)) (LxB + 3 * cnt + 2) (pEdge li (Qof P).n sR)) (BkB + 2 * cnt)
          (keyBkt (Qof P) N ⟨pEdge li (Qof P).n sL, h + 1⟩)) (BkB + 2 * cnt + 1)
          (keyBkt (Qof P) N ⟨pEdge li (Qof P).n sR, h + 1⟩) ∧
      d9.nreg 217038 = cnt + 1 ∧ d9.nreg 217045 = LxB + 3 * (cnt + 1) ∧
      d9.nreg 217046 = BkB + 2 * (cnt + 1) := by
    exec_block
    all_goals (try (config_simp; omega))
    refine ⟨by omega, ?_, ?_, ?_, ?_⟩ <;> config_simp
    · rw [m8, r45, r27, r46, r50, r84, r85, r86, kR,
        show LxB + 3 * cnt + 1 + 1 = LxB + 3 * cnt + 2 by omega]
    · omega
    · omega
    · omega
  have ex : Exec P W keptS d d9 (k1 + (k2 + (k3 + (k4 + (k5 + (k6 + (k7 + (k8 + k9)))))))) := by
    simp only [keptS, seqs_cons₂, seqs_one]
    exact .seq e1 (.seq e2 (.seq e3 (.seq e4 (.seq e5 (.seq e6 (.seq e7 (.seq e8 e9)))))))
  have hk : k1 + (k2 + (k3 + (k4 + (k5 + (k6 + (k7 + (k8 + k9))))))) ≤ 604 * nRA + 120 := by
    omega
  exact ⟨d9, _, ex, hk, m9, c38, c45, c46, exec_frameM ex wrM_kept⟩

end kept

end

end DrvX

end Chazelle.Core
