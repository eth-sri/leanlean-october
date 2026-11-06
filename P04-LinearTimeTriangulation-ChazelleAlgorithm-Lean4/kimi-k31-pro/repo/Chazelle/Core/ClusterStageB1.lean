module

public import Chazelle.Core.ClusterInv
public import Chazelle.Core.ClusterFaces
public import Chazelle.Core.ClusterStarArr
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics
public import Chazelle.SimpTactics
public import Chazelle.MiscTactics
set_option maxHeartbeats 8000000

/-!
# WP-I, part 46: stage B1 — the face arrays and the star arrays

After stage A: `FP` (slot `7`, the face permutation), `FPI` (slot `8`, its inverse), `ATT` (slot
`9`, the least dart of every face), `TE` (slot `10`, the tree-dart flags), and the arrays of the
star map indexed by `enc`: `SOPP` (slots `11 … 13`), `SROT` (`14 … 16`), `SFACE` (`17 … 19`),
`SFIRST` (`20`), `SDB` (`21 … 23`, the tree flags of the star tree).

Register `130811` holds `2 N` during the star arrays.
-/

namespace Chazelle.Core.Cluster

open Machine Machine.Stmt Programs
open Chazelle.Separator Chazelle.Separator.CombMap

@[expose] public section

/-- The registers written by stage B. -/
def StBRG (r : ℕ) : Prop := (130100 ≤ r ∧ r ≤ 130130) ∨ (130150 ≤ r ∧ r ≤ 130154) ∨
  (130200 ≤ r ∧ r ≤ 130215) ∨ (130500 ≤ r ∧ r ≤ 130556) ∨ (130800 ≤ r ∧ r ≤ 130811)

/-- The registers of the array loops. -/
def ArrPRG (r : ℕ) : Prop := 130550 ≤ r ∧ r ≤ 130556

/-- The face permutation. -/
def fpP : Stmt := .seq (block [.copyN 130520 130022, .copyN 130521 130021, .copyN 130522 130037,
  .copyN 130523 130014]) fpStmt

/-- Its inverse. -/
def fpiP : Stmt := .seq (block [.copyN 130800 130037, .copyN 130801 130038, .copyN 130802 130014])
  invStmt

/-- The face representatives. -/
def attP : Stmt := .seq (block [.copyN 130530 130037, .copyN 130531 130039, .copyN 130532 130014])
  attStmt

/-- The tree-dart flags. -/
def teP : Stmt := .seq (block [.copyN 130540 130034, .copyN 130541 130021, .copyN 130542 130040,
  .copyN 130543 130011, .copyN 130544 130014]) teStmt

/-- The parameters of an array loop: `OUT = rOut + rOff`, `IN = rIn`, `n = N`, `a = rA`. -/
def arrB (rOut rOff rIn rA : ℕ) : Stmt := block [.addN 130550 rOut rOff, .copyN 130551 rIn,
  .copyN 130552 130014, .copyN 130553 rA]

/-- `OUT[i] = a + i`. -/
def affP (rOut rOff rA : ℕ) : Stmt := .seq (arrB rOut rOff 130009 rA) affStmt
/-- `OUT[i] = a + IN[i]`. -/
def shP (rOut rOff rIn rA : ℕ) : Stmt := .seq (arrB rOut rOff rIn rA) shStmt
/-- `OUT[i] = [IN[i] = i]`. -/
def eqP (rOut rOff rIn : ℕ) : Stmt := .seq (arrB rOut rOff rIn 130009) eqStmt

/-- **The star arrays.** -/
def starP : Stmt := .seq (.instr (.addN 130811 130014 130014))
  (.seq (shP 130041 130009 130021 130009) (.seq (affP 130041 130014 130811)
  (.seq (affP 130041 130811 130014) (.seq (shP 130044 130009 130037 130811)
  (.seq (affP 130044 130014 130009) (.seq (shP 130044 130811 130038 130014)
  (.seq (affP 130047 130009 130009) (.seq (affP 130047 130014 130009)
  (.seq (shP 130047 130811 130038 130009) (.seq (affP 130050 130009 130009)
  (.seq (shP 130051 130009 130040 130009) (.seq (eqP 130051 130014 130039)
  (eqP 130051 130811 130039)))))))))))))

section proofs

variable {P : Polygon} {W : ℕ}

/-- The parameter block. -/
theorem arrB_exec {c : Config} (hw : WordsBounded W c) {rOut rOff rIn rA o f i a N : ℕ}
    (hO : c.nreg rOut = o) (hf : c.nreg rOff = f) (hi : c.nreg rIn = i) (ha : c.nreg rA = a)
    (hN : c.nreg 130014 = N) (hwo : o + f ≤ W)
    (h1 : ¬ (130550 ≤ rIn ∧ rIn ≤ 130552)) (h2 : ¬ (130550 ≤ rA ∧ rA ≤ 130552)) :
    ∃ c' k, Exec P W (arrB rOut rOff rIn rA) c c' k ∧ k = 4 ∧ WordsBounded W c' ∧
      c'.nmem = c.nmem ∧ c'.nreg 130550 = o + f ∧ c'.nreg 130551 = i ∧ c'.nreg 130552 = N ∧
      c'.nreg 130553 = a ∧ (∀ r, ¬ (130550 ≤ r ∧ r ≤ 130553) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold arrB
  exec_block
  · rwx [hO, hf]
  · refine ⟨rfl, ‹_›, rfl, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
    all_goals simp only [Machine.upd_apply]
    all_goals splao

theorem affP_exec {c : Config} (hw : WordsBounded W c) (hone : c.nreg 130001 = 1)
    (hzero : c.nreg 130009 = 0) {rOut rOff rA o f a N : ℕ}
    (hO : c.nreg rOut = o) (hf : c.nreg rOff = f) (ha : c.nreg rA = a) (hN : c.nreg 130014 = N)
    (h2 : ¬ (130550 ≤ rA ∧ rA ≤ 130552)) (hwo : o + f + N ≤ W) (hwa : a + N ≤ W) :
    ∃ c' k, Exec P W (affP rOut rOff rA) c c' k ∧ k ≤ 6 * N + 7 ∧ WordsBounded W c' ∧
      PFr ArrPRG (fun x => o + f ≤ x ∧ x < o + f + N) c c' ∧
      ∀ i, i < N → c'.nmem (o + f + i) = a + i := by
  unfold affP
  obtain ⟨c1, k1, e1, hk1, hw1, hm1, r0, r1, r2, r3, hr1, hrr1, hrm1, ho1⟩ :=
    arrB_exec (P := P) hw (rIn := 130009) hO hf hzero ha hN (by omega) (by omega) h2
  obtain ⟨c', k, e, hk, hw', hf', hv⟩ := affStmt_exec (P := P) hw1
    (by rwx [hr1 _ (by omega)]) r0 r2 r3 (by omega) hwa
  refine ⟨c', k1 + k, .seq e1 e, by omega, hw', ?_, hv⟩
  refine PFr.trans ⟨fun r hr => hr1 r (fun h => hr (by ufo ArrPRG)), hrr1, hrm1, ho1,
    fun a _ => by rw [hm1]⟩ (hf'.mono (fun r h => by unfold ArrRG at h; ufo ArrPRG)
      (fun _ => id))

theorem shP_exec {c : Config} (hw : WordsBounded W c) (hone : c.nreg 130001 = 1)
    {rOut rOff rIn rA o f i a N : ℕ}
    (hO : c.nreg rOut = o) (hf : c.nreg rOff = f) (hi : c.nreg rIn = i) (ha : c.nreg rA = a)
    (hN : c.nreg 130014 = N) (h1 : ¬ (130550 ≤ rIn ∧ rIn ≤ 130552))
    (h2 : ¬ (130550 ≤ rA ∧ rA ≤ 130552)) (hwo : o + f + N ≤ W) (hwi : i + N ≤ W)
    (hd : o + f + N ≤ i ∨ i + N ≤ o + f) (hwa : ∀ j, j < N → a + c.nmem (i + j) ≤ W) :
    ∃ c' k, Exec P W (shP rOut rOff rIn rA) c c' k ∧ k ≤ 8 * N + 7 ∧ WordsBounded W c' ∧
      PFr ArrPRG (fun x => o + f ≤ x ∧ x < o + f + N) c c' ∧
      ∀ j, j < N → c'.nmem (o + f + j) = a + c.nmem (i + j) := by
  unfold shP
  obtain ⟨c1, k1, e1, hk1, hw1, hm1, r0, r1, r2, r3, hr1, hrr1, hrm1, ho1⟩ :=
    arrB_exec (P := P) hw hO hf hi ha hN (by omega) h1 h2
  obtain ⟨c', k, e, hk, hw', hf', hv⟩ := shStmt_exec (P := P) hw1
    (by rwx [hr1 _ (by omega)]) r0 r1 r2 r3 (by omega) hwi hd
    (fun j hj => by rw [hm1]; exact hwa j hj)
  refine ⟨c', k1 + k, .seq e1 e, by omega, hw', ?_, fun j hj => by rw [hv j hj, hm1]⟩
  refine PFr.trans ⟨fun r hr => hr1 r (fun h => hr (by ufo ArrPRG)), hrr1, hrm1, ho1,
    fun a _ => by rw [hm1]⟩ (hf'.mono (fun r h => by unfold ArrRG at h; ufo ArrPRG)
      (fun _ => id))

theorem eqP_exec {c : Config} (hw : WordsBounded W c) (hone : c.nreg 130001 = 1)
    (hzero : c.nreg 130009 = 0) {rOut rOff rIn o f i N : ℕ}
    (hO : c.nreg rOut = o) (hf : c.nreg rOff = f) (hi : c.nreg rIn = i)
    (hN : c.nreg 130014 = N) (h1 : ¬ (130550 ≤ rIn ∧ rIn ≤ 130552)) (hwo : o + f + N ≤ W)
    (hwi : i + N ≤ W) (hd : o + f + N ≤ i ∨ i + N ≤ o + f) :
    ∃ c' k, Exec P W (eqP rOut rOff rIn) c c' k ∧ k ≤ 12 * N + 7 ∧ WordsBounded W c' ∧
      PFr ArrPRG (fun x => o + f ≤ x ∧ x < o + f + N) c c' ∧
      ∀ j, j < N → c'.nmem (o + f + j) = if c.nmem (i + j) = j then 1 else 0 := by
  unfold eqP
  obtain ⟨c1, k1, e1, hk1, hw1, hm1, r0, r1, r2, r3, hr1, hrr1, hrm1, ho1⟩ :=
    arrB_exec (P := P) hw hO hf hi hzero hN (by omega) h1 (by omega)
  obtain ⟨c', k, e, hk, hw', hf', hv⟩ := eqStmt_exec (P := P) hw1
    (by rwx [hr1 _ (by omega)]) (by rwx [hr1 _ (by omega)]) r0 r1 r2
    (by omega) hwi hd
  refine ⟨c', k1 + k, .seq e1 e, by omega, hw', ?_, fun j hj => by rw [hv j hj, hm1]⟩
  refine PFr.trans ⟨fun r hr => hr1 r (fun h => hr (by ufo ArrPRG)), hrr1, hrm1, ho1,
    fun a _ => by rw [hm1]⟩ (hf'.mono (fun r h => by unfold ArrRG at h; ufo ArrPRG)
      (fun _ => id))

/-- **The star arrays.** -/
theorem starP_exec {g : GV} {c : Config} (hw : WordsBounded W c) (hG : GR g c)
    (hFP : ∀ j, j < g.N → c.nmem (g.base 7 + j) < g.N)
    (hFPI : ∀ j, j < g.N → c.nmem (g.base 8 + j) < g.N)
    (hO : g.bO + g.N ≤ g.A0) (hW : g.END ≤ W) :
    ∃ c' k, Exec P W starP c c' k ∧ k ≤ 110 * g.N + 100 ∧ WordsBounded W c' ∧
      PFr (fun r => ArrPRG r ∨ r = 130811) (fun a => g.base 11 ≤ a ∧ a < g.base 24) c c' ∧
      ∀ j, j < g.N →
        c'.nmem (g.base 11 + j) = c.nmem (g.bO + j) ∧
        c'.nmem (g.base 11 + g.N + j) = 2 * g.N + j ∧
        c'.nmem (g.base 11 + 2 * g.N + j) = g.N + j ∧
        c'.nmem (g.base 14 + j) = 2 * g.N + c.nmem (g.base 7 + j) ∧
        c'.nmem (g.base 14 + g.N + j) = j ∧
        c'.nmem (g.base 14 + 2 * g.N + j) = g.N + c.nmem (g.base 8 + j) ∧
        c'.nmem (g.base 17 + j) = j ∧
        c'.nmem (g.base 17 + g.N + j) = j ∧
        c'.nmem (g.base 17 + 2 * g.N + j) = c.nmem (g.base 8 + j) ∧
        c'.nmem (g.base 20 + j) = j ∧
        c'.nmem (g.base 21 + j) = c.nmem (g.base 10 + j) ∧
        c'.nmem (g.base 21 + g.N + j) = (if c.nmem (g.base 9 + j) = j then 1 else 0) ∧
        c'.nmem (g.base 21 + 2 * g.N + j) = (if c.nmem (g.base 9 + j) = j then 1 else 0) := by
  have hU := g.U_ge
  have hE := g.END_eq
  have b7 := g.base_eq 7; have b8 := g.base_eq 8; have b9 := g.base_eq 9; have b10 := g.base_eq 10
  have b11 := g.base_eq 11; have b14 := g.base_eq 14; have b17 := g.base_eq 17
  have b20 := g.base_eq 20; have b21 := g.base_eq 21; have b24 := g.base_eq 24
  unfold starP
  have e0 := Exec.addN (P := P) hw 130811 130014 130014 (by rwo [hG.rN])
  set c0 := { c with nreg := upd c.nreg 130811 (c.nreg 130014 + c.nreg 130014) } with hc0
  have hw0 : WordsBounded W c0 := e0.wb_right
  have h811 : c0.nreg 130811 = 2 * g.N := by sir [c0, hG.rN]
  have hG0 : GR g c0 := hG.frame (fun r hr => by
    simp only [c0, Machine.upd_apply]; unfold GRReg at hr; splao)
  have fr0 : PFr ArrPRG (fun a => g.base 11 ≤ a ∧ a < g.base 24) c0 c0 := PFr.refl c0
  have hm0 : c0.nmem = c.nmem := rfl
  -- step 1
  have hGs : GR g c0 := hG0.frame (fun r hr => fr0.1 r (by unfold GRReg at hr; ufo ArrPRG))
  have h811s : c0.nreg 130811 = 2 * g.N := (fr0.1 130811 (by ufo ArrPRG)).trans h811
  obtain ⟨c1, k1, x1, hk1, hw1, hf1, hv1⟩ := shP_exec (P := P) hw0 hGs.one (hO := (hGs.rbase 11 (by omega))) (hf := hGs.zero) (hi := hGs.rO) (ha := hGs.zero) hGs.rN (by omega) (by omega) (by omega) (by omega) (by omega) (fun j hj => by have := hw0.2 (g.bO + j); omega)
  have fr1 : PFr ArrPRG (fun a => g.base 11 ≤ a ∧ a < g.base 24) c0 c1 := fr0.trans (hf1.mono (fun _ => id) (fun a h => by omega))
  clear hGs h811s
  -- step 2
  have hGs : GR g c1 := hG0.frame (fun r hr => fr1.1 r (by unfold GRReg at hr; ufo ArrPRG))
  have h811s : c1.nreg 130811 = 2 * g.N := (fr1.1 130811 (by ufo ArrPRG)).trans h811
  obtain ⟨c2, k2, x2, hk2, hw2, hf2, hv2⟩ := affP_exec (P := P) hw1 hGs.one hGs.zero (hO := (hGs.rbase 11 (by omega))) (hf := hGs.rN) (ha := h811s) hGs.rN (by omega) (by omega) (by omega)
  have fr2 : PFr ArrPRG (fun a => g.base 11 ≤ a ∧ a < g.base 24) c0 c2 := fr1.trans (hf2.mono (fun _ => id) (fun a h => by omega))
  clear hGs h811s
  -- step 3
  have hGs : GR g c2 := hG0.frame (fun r hr => fr2.1 r (by unfold GRReg at hr; ufo ArrPRG))
  have h811s : c2.nreg 130811 = 2 * g.N := (fr2.1 130811 (by ufo ArrPRG)).trans h811
  obtain ⟨c3, k3, x3, hk3, hw3, hf3, hv3⟩ := affP_exec (P := P) hw2 hGs.one hGs.zero (hO := (hGs.rbase 11 (by omega))) (hf := h811s) (ha := hGs.rN) hGs.rN (by omega) (by omega) (by omega)
  have fr3 : PFr ArrPRG (fun a => g.base 11 ≤ a ∧ a < g.base 24) c0 c3 := fr2.trans (hf3.mono (fun _ => id) (fun a h => by omega))
  clear hGs h811s
  -- step 4
  have hGs : GR g c3 := hG0.frame (fun r hr => fr3.1 r (by unfold GRReg at hr; ufo ArrPRG))
  have h811s : c3.nreg 130811 = 2 * g.N := (fr3.1 130811 (by ufo ArrPRG)).trans h811
  obtain ⟨c4, k4, x4, hk4, hw4, hf4, hv4⟩ := shP_exec (P := P) hw3 hGs.one (hO := (hGs.rbase 14 (by omega))) (hf := hGs.zero) (hi := (hGs.rbase 7 (by omega))) (ha := h811s) hGs.rN (by omega) (by omega) (by omega) (by omega) (by omega) (fun j hj => by rw [fr3.2.2.2.2 (g.base 7 + j) (by omega), hm0]; have := hFP j hj; omega)
  have fr4 : PFr ArrPRG (fun a => g.base 11 ≤ a ∧ a < g.base 24) c0 c4 := fr3.trans (hf4.mono (fun _ => id) (fun a h => by omega))
  clear hGs h811s
  -- step 5
  have hGs : GR g c4 := hG0.frame (fun r hr => fr4.1 r (by unfold GRReg at hr; ufo ArrPRG))
  have h811s : c4.nreg 130811 = 2 * g.N := (fr4.1 130811 (by ufo ArrPRG)).trans h811
  obtain ⟨c5, k5, x5, hk5, hw5, hf5, hv5⟩ := affP_exec (P := P) hw4 hGs.one hGs.zero (hO := (hGs.rbase 14 (by omega))) (hf := hGs.rN) (ha := hGs.zero) hGs.rN (by omega) (by omega) (by omega)
  have fr5 : PFr ArrPRG (fun a => g.base 11 ≤ a ∧ a < g.base 24) c0 c5 := fr4.trans (hf5.mono (fun _ => id) (fun a h => by omega))
  clear hGs h811s
  -- step 6
  have hGs : GR g c5 := hG0.frame (fun r hr => fr5.1 r (by unfold GRReg at hr; ufo ArrPRG))
  have h811s : c5.nreg 130811 = 2 * g.N := (fr5.1 130811 (by ufo ArrPRG)).trans h811
  obtain ⟨c6, k6, x6, hk6, hw6, hf6, hv6⟩ := shP_exec (P := P) hw5 hGs.one (hO := (hGs.rbase 14 (by omega))) (hf := h811s) (hi := (hGs.rbase 8 (by omega))) (ha := hGs.rN) hGs.rN (by omega) (by omega) (by omega) (by omega) (by omega) (fun j hj => by rw [fr5.2.2.2.2 (g.base 8 + j) (by omega), hm0]; have := hFPI j hj; omega)
  have fr6 : PFr ArrPRG (fun a => g.base 11 ≤ a ∧ a < g.base 24) c0 c6 := fr5.trans (hf6.mono (fun _ => id) (fun a h => by omega))
  clear hGs h811s
  -- step 7
  have hGs : GR g c6 := hG0.frame (fun r hr => fr6.1 r (by unfold GRReg at hr; ufo ArrPRG))
  have h811s : c6.nreg 130811 = 2 * g.N := (fr6.1 130811 (by ufo ArrPRG)).trans h811
  obtain ⟨c7, k7, x7, hk7, hw7, hf7, hv7⟩ := affP_exec (P := P) hw6 hGs.one hGs.zero (hO := (hGs.rbase 17 (by omega))) (hf := hGs.zero) (ha := hGs.zero) hGs.rN (by omega) (by omega) (by omega)
  have fr7 : PFr ArrPRG (fun a => g.base 11 ≤ a ∧ a < g.base 24) c0 c7 := fr6.trans (hf7.mono (fun _ => id) (fun a h => by omega))
  clear hGs h811s
  -- step 8
  have hGs : GR g c7 := hG0.frame (fun r hr => fr7.1 r (by unfold GRReg at hr; ufo ArrPRG))
  have h811s : c7.nreg 130811 = 2 * g.N := (fr7.1 130811 (by ufo ArrPRG)).trans h811
  obtain ⟨c8, k8, x8, hk8, hw8, hf8, hv8⟩ := affP_exec (P := P) hw7 hGs.one hGs.zero (hO := (hGs.rbase 17 (by omega))) (hf := hGs.rN) (ha := hGs.zero) hGs.rN (by omega) (by omega) (by omega)
  have fr8 : PFr ArrPRG (fun a => g.base 11 ≤ a ∧ a < g.base 24) c0 c8 := fr7.trans (hf8.mono (fun _ => id) (fun a h => by omega))
  clear hGs h811s
  -- step 9
  have hGs : GR g c8 := hG0.frame (fun r hr => fr8.1 r (by unfold GRReg at hr; ufo ArrPRG))
  have h811s : c8.nreg 130811 = 2 * g.N := (fr8.1 130811 (by ufo ArrPRG)).trans h811
  obtain ⟨c9, k9, x9, hk9, hw9, hf9, hv9⟩ := shP_exec (P := P) hw8 hGs.one (hO := (hGs.rbase 17 (by omega))) (hf := h811s) (hi := (hGs.rbase 8 (by omega))) (ha := hGs.zero) hGs.rN (by omega) (by omega) (by omega) (by omega) (by omega) (fun j hj => by have := hw8.2 (g.base 8 + j); omega)
  have fr9 : PFr ArrPRG (fun a => g.base 11 ≤ a ∧ a < g.base 24) c0 c9 := fr8.trans (hf9.mono (fun _ => id) (fun a h => by omega))
  clear hGs h811s
  -- step 10
  have hGs : GR g c9 := hG0.frame (fun r hr => fr9.1 r (by unfold GRReg at hr; ufo ArrPRG))
  have h811s : c9.nreg 130811 = 2 * g.N := (fr9.1 130811 (by ufo ArrPRG)).trans h811
  obtain ⟨c10, k10, x10, hk10, hw10, hf10, hv10⟩ := affP_exec (P := P) hw9 hGs.one hGs.zero (hO := (hGs.rbase 20 (by omega))) (hf := hGs.zero) (ha := hGs.zero) hGs.rN (by omega) (by omega) (by omega)
  have fr10 : PFr ArrPRG (fun a => g.base 11 ≤ a ∧ a < g.base 24) c0 c10 := fr9.trans (hf10.mono (fun _ => id) (fun a h => by omega))
  clear hGs h811s
  -- step 11
  have hGs : GR g c10 := hG0.frame (fun r hr => fr10.1 r (by unfold GRReg at hr; ufo ArrPRG))
  have h811s : c10.nreg 130811 = 2 * g.N := (fr10.1 130811 (by ufo ArrPRG)).trans h811
  obtain ⟨c11, k11, x11, hk11, hw11, hf11, hv11⟩ := shP_exec (P := P) hw10 hGs.one (hO := (hGs.rbase 21 (by omega))) (hf := hGs.zero) (hi := (hGs.rbase 10 (by omega))) (ha := hGs.zero) hGs.rN (by omega) (by omega) (by omega) (by omega) (by omega) (fun j hj => by have := hw10.2 (g.base 10 + j); omega)
  have fr11 : PFr ArrPRG (fun a => g.base 11 ≤ a ∧ a < g.base 24) c0 c11 := fr10.trans (hf11.mono (fun _ => id) (fun a h => by omega))
  clear hGs h811s
  -- step 12
  have hGs : GR g c11 := hG0.frame (fun r hr => fr11.1 r (by unfold GRReg at hr; ufo ArrPRG))
  have h811s : c11.nreg 130811 = 2 * g.N := (fr11.1 130811 (by ufo ArrPRG)).trans h811
  obtain ⟨c12, k12, x12, hk12, hw12, hf12, hv12⟩ := eqP_exec (P := P) hw11 hGs.one hGs.zero (hO := (hGs.rbase 21 (by omega))) (hf := hGs.rN) (hi := (hGs.rbase 9 (by omega))) hGs.rN (by omega) (by omega) (by omega) (by omega)
  have fr12 : PFr ArrPRG (fun a => g.base 11 ≤ a ∧ a < g.base 24) c0 c12 := fr11.trans (hf12.mono (fun _ => id) (fun a h => by omega))
  clear hGs h811s
  -- step 13
  have hGs : GR g c12 := hG0.frame (fun r hr => fr12.1 r (by unfold GRReg at hr; ufo ArrPRG))
  have h811s : c12.nreg 130811 = 2 * g.N := (fr12.1 130811 (by ufo ArrPRG)).trans h811
  obtain ⟨c13, k13, x13, hk13, hw13, hf13, hv13⟩ := eqP_exec (P := P) hw12 hGs.one hGs.zero (hO := (hGs.rbase 21 (by omega))) (hf := h811s) (hi := (hGs.rbase 9 (by omega))) hGs.rN (by omega) (by omega) (by omega) (by omega)
  have fr13 : PFr ArrPRG (fun a => g.base 11 ≤ a ∧ a < g.base 24) c0 c13 := fr12.trans (hf13.mono (fun _ => id) (fun a h => by omega))
  clear hGs h811s
  have kp1 : ∀ j, j < g.N → c13.nmem (g.base 11 + 0 + j) = c1.nmem (g.base 11 + 0 + j) := fun j hj => by rw [hf13.2.2.2.2 (g.base 11 + 0 + j) (by omega), hf12.2.2.2.2 (g.base 11 + 0 + j) (by omega), hf11.2.2.2.2 (g.base 11 + 0 + j) (by omega), hf10.2.2.2.2 (g.base 11 + 0 + j) (by omega), hf9.2.2.2.2 (g.base 11 + 0 + j) (by omega), hf8.2.2.2.2 (g.base 11 + 0 + j) (by omega), hf7.2.2.2.2 (g.base 11 + 0 + j) (by omega), hf6.2.2.2.2 (g.base 11 + 0 + j) (by omega), hf5.2.2.2.2 (g.base 11 + 0 + j) (by omega), hf4.2.2.2.2 (g.base 11 + 0 + j) (by omega), hf3.2.2.2.2 (g.base 11 + 0 + j) (by omega), hf2.2.2.2.2 (g.base 11 + 0 + j) (by omega)]
  have kp2 : ∀ j, j < g.N → c13.nmem (g.base 11 + g.N + j) = c2.nmem (g.base 11 + g.N + j) := fun j hj => by rw [hf13.2.2.2.2 (g.base 11 + g.N + j) (by omega), hf12.2.2.2.2 (g.base 11 + g.N + j) (by omega), hf11.2.2.2.2 (g.base 11 + g.N + j) (by omega), hf10.2.2.2.2 (g.base 11 + g.N + j) (by omega), hf9.2.2.2.2 (g.base 11 + g.N + j) (by omega), hf8.2.2.2.2 (g.base 11 + g.N + j) (by omega), hf7.2.2.2.2 (g.base 11 + g.N + j) (by omega), hf6.2.2.2.2 (g.base 11 + g.N + j) (by omega), hf5.2.2.2.2 (g.base 11 + g.N + j) (by omega), hf4.2.2.2.2 (g.base 11 + g.N + j) (by omega), hf3.2.2.2.2 (g.base 11 + g.N + j) (by omega)]
  have kp3 : ∀ j, j < g.N → c13.nmem (g.base 11 + 2 * g.N + j) = c3.nmem (g.base 11 + 2 * g.N + j) := fun j hj => by rw [hf13.2.2.2.2 (g.base 11 + 2 * g.N + j) (by omega), hf12.2.2.2.2 (g.base 11 + 2 * g.N + j) (by omega), hf11.2.2.2.2 (g.base 11 + 2 * g.N + j) (by omega), hf10.2.2.2.2 (g.base 11 + 2 * g.N + j) (by omega), hf9.2.2.2.2 (g.base 11 + 2 * g.N + j) (by omega), hf8.2.2.2.2 (g.base 11 + 2 * g.N + j) (by omega), hf7.2.2.2.2 (g.base 11 + 2 * g.N + j) (by omega), hf6.2.2.2.2 (g.base 11 + 2 * g.N + j) (by omega), hf5.2.2.2.2 (g.base 11 + 2 * g.N + j) (by omega), hf4.2.2.2.2 (g.base 11 + 2 * g.N + j) (by omega)]
  have kp4 : ∀ j, j < g.N → c13.nmem (g.base 14 + 0 + j) = c4.nmem (g.base 14 + 0 + j) := fun j hj => by rw [hf13.2.2.2.2 (g.base 14 + 0 + j) (by omega), hf12.2.2.2.2 (g.base 14 + 0 + j) (by omega), hf11.2.2.2.2 (g.base 14 + 0 + j) (by omega), hf10.2.2.2.2 (g.base 14 + 0 + j) (by omega), hf9.2.2.2.2 (g.base 14 + 0 + j) (by omega), hf8.2.2.2.2 (g.base 14 + 0 + j) (by omega), hf7.2.2.2.2 (g.base 14 + 0 + j) (by omega), hf6.2.2.2.2 (g.base 14 + 0 + j) (by omega), hf5.2.2.2.2 (g.base 14 + 0 + j) (by omega)]
  have kp5 : ∀ j, j < g.N → c13.nmem (g.base 14 + g.N + j) = c5.nmem (g.base 14 + g.N + j) := fun j hj => by rw [hf13.2.2.2.2 (g.base 14 + g.N + j) (by omega), hf12.2.2.2.2 (g.base 14 + g.N + j) (by omega), hf11.2.2.2.2 (g.base 14 + g.N + j) (by omega), hf10.2.2.2.2 (g.base 14 + g.N + j) (by omega), hf9.2.2.2.2 (g.base 14 + g.N + j) (by omega), hf8.2.2.2.2 (g.base 14 + g.N + j) (by omega), hf7.2.2.2.2 (g.base 14 + g.N + j) (by omega), hf6.2.2.2.2 (g.base 14 + g.N + j) (by omega)]
  have kp6 : ∀ j, j < g.N → c13.nmem (g.base 14 + 2 * g.N + j) = c6.nmem (g.base 14 + 2 * g.N + j) := fun j hj => by rw [hf13.2.2.2.2 (g.base 14 + 2 * g.N + j) (by omega), hf12.2.2.2.2 (g.base 14 + 2 * g.N + j) (by omega), hf11.2.2.2.2 (g.base 14 + 2 * g.N + j) (by omega), hf10.2.2.2.2 (g.base 14 + 2 * g.N + j) (by omega), hf9.2.2.2.2 (g.base 14 + 2 * g.N + j) (by omega), hf8.2.2.2.2 (g.base 14 + 2 * g.N + j) (by omega), hf7.2.2.2.2 (g.base 14 + 2 * g.N + j) (by omega)]
  have kp7 : ∀ j, j < g.N → c13.nmem (g.base 17 + 0 + j) = c7.nmem (g.base 17 + 0 + j) := fun j hj => by rw [hf13.2.2.2.2 (g.base 17 + 0 + j) (by omega), hf12.2.2.2.2 (g.base 17 + 0 + j) (by omega), hf11.2.2.2.2 (g.base 17 + 0 + j) (by omega), hf10.2.2.2.2 (g.base 17 + 0 + j) (by omega), hf9.2.2.2.2 (g.base 17 + 0 + j) (by omega), hf8.2.2.2.2 (g.base 17 + 0 + j) (by omega)]
  have kp8 : ∀ j, j < g.N → c13.nmem (g.base 17 + g.N + j) = c8.nmem (g.base 17 + g.N + j) := fun j hj => by rw [hf13.2.2.2.2 (g.base 17 + g.N + j) (by omega), hf12.2.2.2.2 (g.base 17 + g.N + j) (by omega), hf11.2.2.2.2 (g.base 17 + g.N + j) (by omega), hf10.2.2.2.2 (g.base 17 + g.N + j) (by omega), hf9.2.2.2.2 (g.base 17 + g.N + j) (by omega)]
  have kp9 : ∀ j, j < g.N → c13.nmem (g.base 17 + 2 * g.N + j) = c9.nmem (g.base 17 + 2 * g.N + j) := fun j hj => by rw [hf13.2.2.2.2 (g.base 17 + 2 * g.N + j) (by omega), hf12.2.2.2.2 (g.base 17 + 2 * g.N + j) (by omega), hf11.2.2.2.2 (g.base 17 + 2 * g.N + j) (by omega), hf10.2.2.2.2 (g.base 17 + 2 * g.N + j) (by omega)]
  have kp10 : ∀ j, j < g.N → c13.nmem (g.base 20 + 0 + j) = c10.nmem (g.base 20 + 0 + j) := fun j hj => by rw [hf13.2.2.2.2 (g.base 20 + 0 + j) (by omega), hf12.2.2.2.2 (g.base 20 + 0 + j) (by omega), hf11.2.2.2.2 (g.base 20 + 0 + j) (by omega)]
  have kp11 : ∀ j, j < g.N → c13.nmem (g.base 21 + 0 + j) = c11.nmem (g.base 21 + 0 + j) := fun j hj => by rw [hf13.2.2.2.2 (g.base 21 + 0 + j) (by omega), hf12.2.2.2.2 (g.base 21 + 0 + j) (by omega)]
  have kp12 : ∀ j, j < g.N → c13.nmem (g.base 21 + g.N + j) = c12.nmem (g.base 21 + g.N + j) := fun j hj => by rw [hf13.2.2.2.2 (g.base 21 + g.N + j) (by omega)]
  have kp13 : ∀ j, j < g.N → c13.nmem (g.base 21 + 2 * g.N + j) = c13.nmem (g.base 21 + 2 * g.N + j) := fun j hj => rfl

  refine ⟨c13, 1 + (k1 + (k2 + (k3 + (k4 + (k5 + (k6 + (k7 + (k8 + (k9 + (k10 + (k11 + (k12 +
    k13)))))))))))), .seq e0 (.seq x1 (.seq x2 (.seq x3 (.seq x4 (.seq x5 (.seq x6 (.seq x7
    (.seq x8 (.seq x9 (.seq x10 (.seq x11 (.seq x12 x13)))))))))))), by omega, hw13, ?_,
    fun j hj => ?_⟩
  · refine PFr.trans (c1 := c0) ⟨fun r hr => ?_, rfl, rfl, rfl, fun a _ => rfl⟩
      (fr13.mono (fun r h => Or.inl h) (fun _ => id))
    simp only [c0, Machine.upd_apply]
    split_ifs with h
    · exact absurd (Or.inr h) hr
    · rfl
  have i0 : ∀ a, (a < g.base 11 ∨ g.base 24 ≤ a) → ∀ (cs : Config),
      PFr ArrPRG (fun a => g.base 11 ≤ a ∧ a < g.base 24) c0 cs → cs.nmem a = c.nmem a :=
    fun a ha cs hfs => (hfs.2.2.2.2 a (by omega)).trans (by rw [hm0])
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show g.base 11 + j = g.base 11 + 0 + j by omega, kp1 j hj, hv1 j hj,
      i0 _ (by omega) c0 fr0]; omega
  · rw [kp2 j hj, hv2 j hj]
  · rw [kp3 j hj, hv3 j hj]
  · rw [show g.base 14 + j = g.base 14 + 0 + j by omega, kp4 j hj, hv4 j hj,
      i0 _ (by omega) c3 fr3]
  · rwo [kp5 j hj, hv5 j hj]
  · rw [kp6 j hj, hv6 j hj, i0 _ (by omega) c5 fr5]
  · rwo [show g.base 17 + j = g.base 17 + 0 + j by omega, kp7 j hj, hv7 j hj]
  · rwo [kp8 j hj, hv8 j hj]
  · rwo [kp9 j hj, hv9 j hj, i0 _ (by omega) c8 fr8]
  · rwo [show g.base 20 + j = g.base 20 + 0 + j by omega, kp10 j hj, hv10 j hj]
  · rw [show g.base 21 + j = g.base 21 + 0 + j by omega, kp11 j hj, hv11 j hj,
      i0 _ (by omega) c10 fr10]; omega
  · rw [kp12 j hj, hv12 j hj, i0 _ (by omega) c11 fr11]
  · rw [hv13 j hj, i0 _ (by omega) c12 fr12]

/-- A copy block of the stage B phases. -/
theorem copyBlockFP {c : Config} (hw : WordsBounded W c) {g : GV} (hG : GR g c) :
    ∃ c' k, Exec P W (block [.copyN 130520 130022, .copyN 130521 130021, .copyN 130522 130037,
      .copyN 130523 130014]) c c' k ∧ k = 4 ∧ WordsBounded W c' ∧ c'.nmem = c.nmem ∧
      c'.nreg 130520 = g.bR ∧ c'.nreg 130521 = g.bO ∧ c'.nreg 130522 = g.base 7 ∧
      c'.nreg 130523 = g.N ∧ (∀ r, ¬ (130520 ≤ r ∧ r ≤ 130523) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  exec_block
  refine ⟨rfl, ‹_›, rfl, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · config_simp; exact hG.rR
  · config_simp; exact hG.rO
  · config_simp; exact hG.rbase 7 (by omega)
  · config_simp; exact hG.rN
  · simp only; repeat (rw [Machine.upd_other _ _ _ (by omega)])

theorem fpP_exec {g : GV} {F : Type} {M : CombMap (Fin g.μ) F (Fin g.N)} {c : Config}
    (hw : WordsBounded W c) (hG : GR g c) (hmap : MapArrays c.nmem g.bO g.bR g.bV g.μ g.N M)
    (hO : g.bO + g.N ≤ g.A0) (hR : g.bR + g.N ≤ g.A0) (hW : g.END ≤ W) :
    ∃ c' k, Exec P W fpP c c' k ∧ k ≤ 9 * g.N + 7 ∧ WordsBounded W c' ∧
      PFr StBRG (fun a => g.base 7 ≤ a ∧ a < g.base 7 + g.N) c c' ∧
      ∀ d : Fin g.N, c'.nmem (g.base 7 + d) = M.fperm d := by
  have hU := g.U_ge; have hE := g.END_eq; have b7 := g.base_eq 7
  unfold fpP
  obtain ⟨c1, k1, e1, hk1, hw1, hm1, r0, r1, r2, r3, hr1, hrr1, hrm1, ho1⟩ := copyBlockFP (P := P) hw hG
  have hone1 : c1.nreg 130001 = 1 := by rw [hr1 _ (by omega)]; exact hG.one
  obtain ⟨c', k, e, hk, hw', hf', hv⟩ := fpStmt_exec (P := P) hw1 hone1 r0 r1 r2 r3 (by omega)
    (by omega) (by omega) (fun d hd => by
      rw [hm1, hmap.opp hd]; have := (M.opp ⟨d, hd⟩).2; omega)
  refine ⟨c', k1 + k, .seq e1 e, by omega, hw', PFr.trans ⟨fun r hr => hr1 r (fun h => hr (by
    ufo StBRG)), hrr1, hrm1, ho1, fun a _ => by rw [hm1]⟩
    (hf'.mono (fun r h => by unfold FpRG at h; ufo StBRG) (fun _ => id)),
    fun d => ?_⟩
  rw [hv d d.2, hm1, hmap.opp d.2, hmap.rot (M.opp ⟨d, d.2⟩).2]
  rfl

theorem fpiP_exec {g : GV} {F : Type} {M : CombMap (Fin g.μ) F (Fin g.N)} {c : Config}
    (hw : WordsBounded W c) (hG : GR g c) (hfp : ∀ d : Fin g.N, c.nmem (g.base 7 + d) = M.fperm d)
    (hW : g.END ≤ W) :
    ∃ c' k, Exec P W fpiP c c' k ∧ k ≤ 7 * g.N + 6 ∧ WordsBounded W c' ∧
      PFr StBRG (fun a => g.base 8 ≤ a ∧ a < g.base 8 + g.N) c c' ∧
      ∀ d : Fin g.N, c'.nmem (g.base 8 + d) = (M.fperm⁻¹ d : Fin g.N) := by
  have hU := g.U_ge; have hE := g.END_eq; have b7 := g.base_eq 7; have b8 := g.base_eq 8
  unfold fpiP
  obtain ⟨c1, k1, e1, hk1, hw1, hm1, r0, r1, r2, hone1, hr1⟩ : ∃ c1 k1, Exec P W
      (block [.copyN 130800 130037, .copyN 130801 130038, .copyN 130802 130014]) c c1 k1 ∧
      k1 = 3 ∧ WordsBounded W c1 ∧ c1.nmem = c.nmem ∧ c1.nreg 130800 = g.base 7 ∧
      c1.nreg 130801 = g.base 8 ∧ c1.nreg 130802 = g.N ∧ c1.nreg 130001 = 1 ∧
      PFr StBRG (fun a => g.base 8 ≤ a ∧ a < g.base 8 + g.N) c c1 := by
    exec_block
    refine ⟨rfl, ‹_›, rfl, ?_, ?_, ?_, ?_, ⟨fun r hr => ?_, rfl, rfl, rfl, fun a _ => rfl⟩⟩
    · config_simp; exact hG.rbase 7 (by omega)
    · config_simp; exact hG.rbase 8 (by omega)
    · config_simp; exact hG.rN
    · config_simp; exact hG.one
    · simp only; unfold StBRG at hr
      repeat (rw [Machine.upd_other _ _ _ (by omega)])
  have hfp1 : ∀ i (hi : i < g.N), c1.nmem (g.base 7 + i) = M.fperm ⟨i, hi⟩ := fun i hi => by
    rw [hm1]; exact hfp ⟨i, hi⟩
  obtain ⟨c', k, e, hk, hw', hf', hv⟩ := invStmt_exec (P := P) hw1 hone1 r0 r1 r2
    (fun i hi => by rw [hfp1 i hi]; exact Fin.isLt _)
    (fun i j hi hj h => by
      rw [hfp1 i hi, hfp1 j hj] at h
      exact congrArg Fin.val (M.fperm.injective (Fin.ext h)))
    (by omega) (by omega) (by omega) (by omega)
  refine ⟨c', k1 + k, .seq e1 e, by omega, hw', hr1.trans (hf'.mono (fun r h => by
    unfold InvRG at h; ufo StBRG) (fun _ => id)), fun d => ?_⟩
  have := hv (M.fperm⁻¹ d) (Fin.isLt _)
  rw [hfp1 _ (Fin.isLt _)] at this
  simpa using this

theorem attP_exec {g : GV} {F : Type} {M : CombMap (Fin g.μ) F (Fin g.N)} {c : Config}
    (hw : WordsBounded W c) (hG : GR g c) (hfp : ∀ d : Fin g.N, c.nmem (g.base 7 + d) = M.fperm d)
    (hW : g.END ≤ W) :
    ∃ c' k, Exec P W attP c c' k ∧ k ≤ 40 * g.N + 15 ∧ WordsBounded W c' ∧
      PFr StBRG (fun a => g.base 9 ≤ a ∧ a < g.base 9 + g.N) c c' ∧
      ∀ x, x < g.N → c'.nmem (g.base 9 + x) = minOrb (fun y => c.nmem (g.base 7 + y)) x := by
  have hU := g.U_ge; have hE := g.END_eq; have b7 := g.base_eq 7; have b9 := g.base_eq 9
  unfold attP
  obtain ⟨c1, k1, e1, hk1, hw1, hm1, r0, r1, r2, hone1, hzero1, hr1⟩ : ∃ c1 k1, Exec P W
      (block [.copyN 130530 130037, .copyN 130531 130039, .copyN 130532 130014]) c c1 k1 ∧
      k1 = 3 ∧ WordsBounded W c1 ∧ c1.nmem = c.nmem ∧ c1.nreg 130530 = g.base 7 ∧
      c1.nreg 130531 = g.base 9 ∧ c1.nreg 130532 = g.N ∧ c1.nreg 130001 = 1 ∧
      c1.nreg 130009 = 0 ∧ PFr StBRG (fun a => g.base 9 ≤ a ∧ a < g.base 9 + g.N) c c1 := by
    exec_block
    refine ⟨rfl, ‹_›, rfl, ?_, ?_, ?_, ?_, ?_, ⟨fun r hr => ?_, rfl, rfl, rfl, fun a _ => rfl⟩⟩
    · config_simp; exact hG.rbase 7 (by omega)
    · config_simp; exact hG.rbase 9 (by omega)
    · config_simp; exact hG.rN
    · config_simp; exact hG.one
    · config_simp; exact hG.zero
    · simp only; unfold StBRG at hr
      repeat (rw [Machine.upd_other _ _ _ (by omega)])
  have hinj : InjOn (fun y => c.nmem (g.base 7 + y)) g.N := fp_injOn (hfp)
  obtain ⟨c', k, e, hk, hw', hf', hv⟩ := attStmt_exec (P := P) hw1 hone1 hzero1 r0 r1 r2 hinj
    (fun x hx => by rw [hm1]) (by omega) (by omega) (by omega) (by omega)
  refine ⟨c', k1 + k, .seq e1 e, by omega, hw', hr1.trans (hf'.mono (fun r h => by
    unfold AttRG at h; ufo StBRG) (fun _ => id)), hv⟩

/-- The tree darts from the parent darts in memory. -/
theorem teSet_iff {g : GV} {F : Type} {M : CombMap (Fin g.μ) F (Fin g.N)} {T : SpanTree M}
    {m : ℕ → ℕ} (hA : AF g M T m) (d : Fin g.N) :
    TeSet m (g.base 4) g.bO g.μ d ↔ T.IsTreeDart d := by
  have hr : ∀ v : Fin g.μ, v ≠ T.root ↔ 1 ≤ (v : ℕ) := by
    intro v
    constructor
    · intro h; by_contra h0; exact h (Fin.ext (by rwo [hA.root]))
    · intro h e; have := congrArg Fin.val e; rwo [hA.root] at this
  have hopp : ∀ v : Fin g.μ, v ≠ T.root →
      (M.opp (T.par v) : ℕ) = m (g.base 4 + v) := by
    intro v hv
    have h1 := hA.par_eq v hv
    have h2 := hA.map.opp (hA.par_lt v hv)
    have : T.par v = M.opp ⟨m (g.base 4 + v), hA.par_lt v hv⟩ := Fin.ext (by rw [h1, h2])
    rw [this, M.opp_opp]
  constructor
  · rintro ⟨v, h1, h2, h3⟩
    have hv  := (hr ⟨v, h2⟩).mpr h1
    refine ⟨⟨v, h2⟩, hv, ?_⟩
    rcases h3 with h3 | h3
    · right; apply Fin.ext; rwx [hopp _ hv]
    · left; apply Fin.ext; rwx [hA.par_eq _ hv]
  · rintro ⟨v, hv, h3⟩
    refine ⟨v, (hr v).mp hv, v.2, ?_⟩
    rcases h3 with h3 | h3
    · right; rw [h3, hA.par_eq v hv]
    · left; rw [h3, hopp v hv]

theorem teP_exec {g : GV} {F : Type} {M : CombMap (Fin g.μ) F (Fin g.N)} {T : SpanTree M}
    {c : Config} (hw : WordsBounded W c) (hG : GR g c) (hA : AF g M T c.nmem) (hμ : 0 < g.μ)
    (hO : g.bO + g.N ≤ g.A0) (hW : g.END ≤ W) :
    ∃ c' k, Exec P W teP c c' k ∧ k ≤ 5 * g.N + 11 * g.μ + 15 ∧ WordsBounded W c' ∧
      PFr StBRG (fun a => g.base 10 ≤ a ∧ a < g.base 10 + g.N) c c' ∧
      ∀ d : Fin g.N, (c'.nmem (g.base 10 + d) = 1 ∧ T.IsTreeDart d) ∨
        (c'.nmem (g.base 10 + d) = 0 ∧ ¬ T.IsTreeDart d) := by
  have hU := g.U_ge; have hE := g.END_eq; have b4 := g.base_eq 4; have b10 := g.base_eq 10
  unfold teP
  obtain ⟨c1, k1, e1, hk1, hw1, hm1, r0, r1, r2, r3, r4, hone1, hzero1, hr1⟩ : ∃ c1 k1, Exec P W
      (block [.copyN 130540 130034, .copyN 130541 130021, .copyN 130542 130040,
        .copyN 130543 130011, .copyN 130544 130014]) c c1 k1 ∧
      k1 = 5 ∧ WordsBounded W c1 ∧ c1.nmem = c.nmem ∧ c1.nreg 130540 = g.base 4 ∧
      c1.nreg 130541 = g.bO ∧ c1.nreg 130542 = g.base 10 ∧ c1.nreg 130543 = g.μ ∧
      c1.nreg 130544 = g.N ∧ c1.nreg 130001 = 1 ∧
      c1.nreg 130009 = 0 ∧ PFr StBRG (fun a => g.base 10 ≤ a ∧ a < g.base 10 + g.N) c c1 := by
    exec_block
    refine ⟨rfl, ‹_›, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨fun r hr => ?_, rfl, rfl, rfl,
      fun a _ => rfl⟩⟩
    · config_simp; exact hG.rbase 4 (by omega)
    · config_simp; exact hG.rO
    · config_simp; exact hG.rbase 10 (by omega)
    · config_simp; exact hG.rμ
    · config_simp; exact hG.rN
    · config_simp; exact hG.one
    · config_simp; exact hG.zero
    · simp only; unfold StBRG at hr
      repeat (rw [Machine.upd_other _ _ _ (by omega)])
  have hvr : ∀ v (_ : 1 ≤ v) (h2 : v < g.μ), (⟨v, h2⟩ : Fin g.μ) ≠ T.root := by
    intro v h1 h2 e; have := congrArg Fin.val e; rw [hA.root] at this; sio at this
  obtain ⟨c', k, e, hk, hw', hf', hv⟩ := teStmt_exec (P := P) hw1 hone1 hzero1 r0 r1 r2 r3 r4 hμ
    (by omega) (by omega) (by omega) (by omega) (by omega) (fun v h1 h2 => by
      rw [hm1]
      have hp : c.nmem (g.base 4 + v) < g.N := hA.par_lt ⟨v, h2⟩ (hvr v h1 h2)
      refine ⟨hp, by omega, ?_⟩
      rw [hA.map.opp hp]; exact Fin.isLt _)
  refine ⟨c', k1 + k, .seq e1 e, by omega, hw', hr1.trans (hf'.mono (fun r h => by
    unfold TeRG at h; ufo StBRG) (fun _ => id)), fun d => ?_⟩
  rw [hm1] at hv
  rcases hv d d.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h1, (teSet_iff hA d).mp h2⟩
  · exact Or.inr ⟨h1, fun h => h2 ((teSet_iff hA d).mpr h)⟩

/-- **Stage B1.** -/
def stageB1 : Stmt := .seq fpP (.seq fpiP (.seq attP (.seq teP starP)))

/-- **The facts of stage B1.** -/
structure B1F (g : GV) {F : Type} [Fintype F] [DecidableEq F] (M : CombMap (Fin g.μ) F (Fin g.N))
    (T : SpanTree M) (a : F → Fin g.N) (ha : ∀ f, M.face (a f) = f) (m : ℕ → ℕ) : Prop where
  fp : ∀ d : Fin g.N, m (g.base 7 + d) = M.fperm d
  fpi : ∀ d : Fin g.N, m (g.base 8 + d) = (M.fperm⁻¹ d : Fin g.N)
  att : ∀ d : Fin g.N, m (g.base 9 + d) = a (M.face d)
  so : ∀ d : Fin g.N, m (g.base 11 + d) = M.opp d ∧ m (g.base 11 + g.N + d) = 2 * g.N + d ∧
    m (g.base 11 + 2 * g.N + d) = g.N + d
  sr : ∀ d : Fin g.N, m (g.base 14 + d) = 2 * g.N + M.fperm d ∧ m (g.base 14 + g.N + d) = d ∧
    m (g.base 14 + 2 * g.N + d) = g.N + (M.fperm⁻¹ d : Fin g.N)
  sf : ∀ d : Fin g.N, m (g.base 17 + d) = d ∧ m (g.base 17 + g.N + d) = d ∧
    m (g.base 17 + 2 * g.N + d) = (M.fperm⁻¹ d : Fin g.N)
  sfirst : ∀ d : Fin g.N, m (g.base 20 + d) = d
  sdb : ∀ x, (m (g.base 21 + enc g.N x) = 1 ↔ (starTree T a ha).IsTreeDart x)

theorem B1F.congr {g : GV} {F : Type} [Fintype F] [DecidableEq F]
    {M : CombMap (Fin g.μ) F (Fin g.N)} {T : SpanTree M} {a : F → Fin g.N}
    {ha : ∀ f, M.face (a f) = f} {m m' : ℕ → ℕ} (h : B1F g M T a ha m)
    (he : ∀ x, g.base 7 ≤ x → x < g.base 24 → m' x = m x) : B1F g M T a ha m' := by
  have hU := g.U_ge
  have b7 := g.base_eq 7; have b8 := g.base_eq 8; have b9 := g.base_eq 9; have b11 := g.base_eq 11
  have b14 := g.base_eq 14; have b17 := g.base_eq 17; have b20 := g.base_eq 20
  have b21 := g.base_eq 21; have b24 := g.base_eq 24
  refine ⟨fun d => ?_, fun d => ?_, fun d => ?_, fun d => ?_, fun d => ?_, fun d => ?_,
    fun d => ?_, fun x => ?_⟩
  · have := d.2; rw [he _ (by omega) (by omega)]; exact h.fp d
  · have := d.2; rw [he _ (by omega) (by omega)]; exact h.fpi d
  · have := d.2; rw [he _ (by omega) (by omega)]; exact h.att d
  · have := d.2
    rw [he _ (by omega) (by omega), he (g.base 11 + g.N + d) (by omega) (by omega),
      he (g.base 11 + 2 * g.N + d) (by omega) (by omega)]; exact h.so d
  · have := d.2
    rw [he _ (by omega) (by omega), he (g.base 14 + g.N + d) (by omega) (by omega),
      he (g.base 14 + 2 * g.N + d) (by omega) (by omega)]; exact h.sr d
  · have := d.2
    rw [he _ (by omega) (by omega), he (g.base 17 + g.N + d) (by omega) (by omega),
      he (g.base 17 + 2 * g.N + d) (by omega) (by omega)]; exact h.sf d
  · have := d.2; rw [he _ (by omega) (by omega)]; exact h.sfirst d
  · have := enc_lt x; rw [he _ (by omega) (by omega)]; exact h.sdb x

open Classical in
theorem stageB1_exec {g : GV} {F : Type} [Fintype F] [DecidableEq F]
    {M : CombMap (Fin g.μ) F (Fin g.N)} {T : SpanTree M} {c : Config} (hw : WordsBounded W c)
    (hG : GR g c) (hA : AF g M T c.nmem) (hμ : 0 < g.μ) (hO : g.bO + g.N ≤ g.A0)
    (hR : g.bR + g.N ≤ g.A0) (hV : g.bV + g.N ≤ g.A0) (hW : g.END ≤ W) :
    ∃ c' k, Exec P W stageB1 c c' k ∧ k ≤ 172 * g.N + 11 * g.μ + 150 ∧ WordsBounded W c' ∧
      PFr StBRG (fun a => g.base 7 ≤ a ∧ a < g.base 24) c c' ∧
      ∃ (a : F → Fin g.N) (ha : ∀ f, M.face (a f) = f), B1F g M T a ha c'.nmem := by
  have hU := g.U_ge; have hE := g.END_eq
  have b7 := g.base_eq 7; have b8 := g.base_eq 8; have b9 := g.base_eq 9; have b10 := g.base_eq 10
  have b11 := g.base_eq 11; have b24 := g.base_eq 24
  have b3 := g.base_eq 3; have b5 := g.base_eq 5; have b6 := g.base_eq 6
  have hGR : ∀ {c1 : Config} {Am : ℕ → Prop}, PFr StBRG Am c c1 → GR g c1 := fun hf =>
    hG.frame (fun r hr => hf.1 r (by unfold GRReg at hr; ufo StBRG))
  have hmono : ∀ {c0 c1 : Config} {Am : ℕ → Prop}, PFr StBRG Am c0 c1 →
      (∀ a, Am a → g.base 7 ≤ a ∧ a < g.base 24) →
      PFr StBRG (fun a => g.base 7 ≤ a ∧ a < g.base 24) c0 c1 :=
    fun hf hAm => hf.mono (fun _ => id) hAm
  -- FP
  obtain ⟨c1, k1, x1, hk1, hw1, hf1, hfp1⟩ := fpP_exec (P := P) hw hG hA.map hO hR hW
  have f1 := hmono hf1 (fun a h => by omega)
  -- FPI
  obtain ⟨c2, k2, x2, hk2, hw2, hf2, hfpi2⟩ := fpiP_exec (P := P) hw1 (hGR f1) hfp1 hW
  have f2 := f1.trans (hmono hf2 (fun a h => by omega))
  have hfp2 : ∀ d : Fin g.N, c2.nmem (g.base 7 + d) = M.fperm d := fun d => by
    rw [hf2.2.2.2.2 _ (by have := d.2; omega)]; exact hfp1 d
  -- ATT
  obtain ⟨c3, k3, x3, hk3, hw3, hf3, hatt3⟩ := attP_exec (P := P) hw2 (hGR f2) hfp2 hW
  have f3 := f2.trans (hmono hf3 (fun a h => by omega))
  -- the representatives
  set fpf : ℕ → ℕ := fun y => c2.nmem (g.base 7 + y) with hfpf
  have hinj : InjOn fpf g.N := fp_injOn (hfp2)
  obtain ⟨a, ha, hatt⟩ := att_fun (M := M) (att := fun d => c3.nmem (g.base 9 + d))
    (fun d => by
      rw [hatt3 d d.2]; exact lt_of_le_of_lt (minOrb_le _) d.2)
    (fun d h => by
      have e1 : c3.nmem (g.base 9 + d) = minOrb fpf d := hatt3 d d.2
      have ho := minOrb_orb (f := fpf) (d : ℕ)
      obtain ⟨i, hi⟩ := ho
      have hm : minOrb fpf d < g.N := lt_of_le_of_lt (minOrb_le _) d.2
      obtain ⟨j, hj, hij⟩ := exists_lt_per_of_iterate hinj hm i
      have := (face_orbit (M := M) (fp := fpf) (hfp2) ⟨_, hm⟩ d).mpr
        ⟨j, hj, by rw [← hij, hi]⟩
      rw [show (⟨c3.nmem (g.base 9 + d), h⟩ : Fin g.N) = ⟨minOrb fpf d, hm⟩ from Fin.ext e1]
      exact this.symm)
    (fun d e h => by
      rw [hatt3 d d.2, hatt3 e e.2]
      obtain ⟨i, -, hi⟩ := (face_orbit (M := M) (fp := fpf) (hfp2) d e).mp h.symm
      exact (minOrb_eq hinj d.2 ⟨i, hi⟩).symm)
  -- TE
  have hA3 : AF g M T c3.nmem := hA.congr ⟨hO, hR, hV⟩
    (fun a ha' => f3.2.2.2.2 a (by ufo KeepA at ha'))
  obtain ⟨c4, k4, x4, hk4, hw4, hf4, hte4⟩ := teP_exec (P := P) hw3 (hGR f3) hA3 hμ hO hW
  have f4 := f3.trans (hmono hf4 (fun a h => by omega))
  have hfp4 : ∀ d : Fin g.N, c4.nmem (g.base 7 + d) = M.fperm d := fun d => by
    have := d.2
    rw [hf4.2.2.2.2 _ (by omega), hf3.2.2.2.2 _ (by omega)]; exact hfp2 d
  have hfpi4 : ∀ d : Fin g.N, c4.nmem (g.base 8 + d) = (M.fperm⁻¹ d : Fin g.N) := fun d => by
    have := d.2
    rw [hf4.2.2.2.2 _ (by omega), hf3.2.2.2.2 _ (by omega)]; exact hfpi2 d
  have hatt4 : ∀ d : Fin g.N, c4.nmem (g.base 9 + d) = a (M.face d) := fun d => by
    have := d.2
    rw [hf4.2.2.2.2 _ (by omega)]; exact (hatt d).symm
  -- the star arrays
  obtain ⟨c5, k5, x5, hk5, hw5, hf5, hst⟩ := starP_exec (P := P) hw4 (hGR f4)
    (fun j hj => by rw [hfp4 ⟨j, hj⟩]; exact Fin.isLt _)
    (fun j hj => by rw [hfpi4 ⟨j, hj⟩]; exact Fin.isLt _) hO hW
  have f5 : PFr StBRG (fun a => g.base 7 ≤ a ∧ a < g.base 24) c c5 :=
    f4.trans (hf5.mono (fun r h => by unfold ArrPRG at h; ufo StBRG) (fun a h => by
      omega))
  have m4 : ∀ a, a < g.A0 → c4.nmem a = c.nmem a := fun a ha' => f4.2.2.2.2 a (by omega)
  refine ⟨c5, k1 + (k2 + (k3 + (k4 + k5))), .seq x1 (.seq x2 (.seq x3 (.seq x4 x5))),
    by omega, hw5, f5, a, ha, ⟨fun d => ?_, fun d => ?_, fun d => ?_, fun d => ?_, fun d => ?_,
    fun d => ?_, fun d => ?_, fun x => ?_⟩⟩
  · have := d.2; rw [hf5.2.2.2.2 _ (by omega)]; exact hfp4 d
  · have := d.2; rw [hf5.2.2.2.2 _ (by omega)]; exact hfpi4 d
  · have := d.2; rw [hf5.2.2.2.2 _ (by omega)]; exact hatt4 d
  · obtain ⟨h1, h2, h3, -⟩ := hst d d.2
    refine ⟨?_, h2, h3⟩
    rw [h1, m4 _ (by omega)]; exact hA.map.opp d.2
  · obtain ⟨-, -, -, h4, h5, h6, -⟩ := hst d d.2
    exact ⟨by rw [h4, hfp4 d], h5, by rw [h6, hfpi4 d]⟩
  · obtain ⟨-, -, -, -, -, -, h7, h8, h9, -⟩ := hst d d.2
    exact ⟨h7, h8, by rw [h9, hfpi4 d]⟩
  · exact (hst d d.2).2.2.2.2.2.2.2.2.2.1
  · rcases x with d | d | d
    · have e := (hst d d.2).2.2.2.2.2.2.2.2.2.2.1
      rw [show enc g.N (Sum.inl d) = d from rfl, e, starTree_isTreeDart_inl]
      rcases hte4 d with ⟨t1, t2⟩ | ⟨t1, t2⟩
      · rw [t1]; exact ⟨fun _ => t2, fun _ => rfl⟩
      · rw [t1]
        constructor
        · intro h; omega
        · intro h; exact absurd h t2
    · have e := (hst d d.2).2.2.2.2.2.2.2.2.2.2.2.1
      rw [show enc g.N (Sum.inr (Sum.inl d)) = g.N + d from rfl,
        show g.base 21 + (g.N + d) = g.base 21 + g.N + d by omega, e, hatt4 d,
        starTree_isTreeDart_inl_inr]
      by_cases hd : ((a (M.face d) : Fin g.N) : ℕ) = d
      · rw [ite_eq_left hd]; exact ⟨fun _ => (Fin.ext hd).symm, fun _ => rfl⟩
      · rw [ite_eq_right hd]
        constructor
        · intro h; omega
        · intro h; exact absurd (congrArg Fin.val h).symm hd
    · have e := (hst d d.2).2.2.2.2.2.2.2.2.2.2.2.2
      rw [show enc g.N (Sum.inr (Sum.inr d)) = 2 * g.N + d from rfl,
        show g.base 21 + (2 * g.N + d) = g.base 21 + 2 * g.N + d by omega, e, hatt4 d,
        starTree_isTreeDart_inr_inr]
      by_cases hd : ((a (M.face d) : Fin g.N) : ℕ) = d
      · rw [ite_eq_left hd]; exact ⟨fun _ => (Fin.ext hd).symm, fun _ => rfl⟩
      · rw [ite_eq_right hd]
        constructor
        · intro h; omega
        · intro h; exact absurd (congrArg Fin.val h).symm hd

end proofs
