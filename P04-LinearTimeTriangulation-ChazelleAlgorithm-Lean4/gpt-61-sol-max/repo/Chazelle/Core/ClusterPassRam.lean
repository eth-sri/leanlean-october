module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.ClusterClassRam
public import Chazelle.Core.ClusterBfsRam

/-!
# WP-I, part 29: one partition pass on the RAM

`passStmt`: for `i = lo, …, hi - 1`, the item `v = TMP[i]` is *selected* if it is not marked
(`DF[v] ≠ 1`) and its key `FPRE[FIRST[v]]` passes the class test `ClassTest mode a b`; a
selected item is appended: `ACT[ptr] := v`, `POS[v] := ptr`, `ptr := ptr + 1`.

`passMem`: the memory and pointer after `j` steps, by recursion; `passStmt_exec`: the loop
computes it.

Registers: `130300` `lo`, `130301` `hi`, `130637 … 130639` the class parameters, static `130650`
(`TMP`), `130651` (`ACT`), `130652` (`POS`), `130653` (`DF`), `130654` (`FIRST`), `130655`
(`FPRE`); the pointer `130656`; the counter `130657`; scratch `130658 … 130661`.
-/

namespace Chazelle.Core.Cluster

open Machine Machine.Stmt Programs

@[expose] public section

instance (mode a b κ : ℕ) : Decidable (ClassTest mode a b κ) := by
  unfold ClassTest; infer_instance

/-- Append `v` (register `130658`). -/
def appendB : Stmt := block [.addN 130661 130651 130656, .storeN 130661 130658,
  .addN 130661 130652 130658, .storeN 130661 130656, .addN 130656 130656 130001]

/-- The test on the key (register `130659`) and the append. -/
def ctestB : Stmt := .seq (.ifLtN 130659 130638 (.instr (.constN 130660 0))
    (.ifLtN 130659 130639 (.instr (.constN 130660 1)) (.instr (.constN 130660 0))))
  (.ifLtN 130637 130001 .skip (.ifLtN 130001 130637
    (.ifLtN 130660 130001 appendB .skip) (.ifLtN 130009 130660 appendB .skip)))

/-- One item of the pass. -/
def passBody : Stmt := .seq (block [.addN 130661 130650 130657, .loadN 130658 130661,
    .addN 130661 130653 130658, .loadN 130660 130661])
  (.seq (ifNe1 130660 (.seq (block [.addN 130661 130654 130658, .loadN 130661 130661,
      .addN 130661 130655 130661, .loadN 130659 130661]) ctestB))
    (.instr (.addN 130657 130657 130001)))

/-- **A partition pass** over `[lo, hi)`. -/
def passStmt : Stmt := .seq (.instr (.copyN 130657 130300)) (.whileLtN 130657 130301 passBody)

/-- The registers written by a pass. -/
def PassRG (r : ℕ) : Prop := 130656 ≤ r ∧ r ≤ 130661

/-- The selection predicate of position `i`. -/
def SelP (m : ℕ → ℕ) (bTMP bDF bFIRST bFPRE mode a b i : ℕ) : Prop :=
  m (bDF + m (bTMP + i)) ≠ 1 ∧ ClassTest mode a b (m (bFPRE + m (bFIRST + m (bTMP + i))))

open Classical in
/-- The memory and the pointer after `j` steps of the pass from position `lo` and pointer `e`. -/
noncomputable def passMem (m0 : ℕ → ℕ) (sel : ℕ → Prop) (bACT bPOS bTMP lo e : ℕ) :
    ℕ → (ℕ → ℕ) × ℕ
  | 0 => (m0, e)
  | j + 1 =>
    let q := passMem m0 sel bACT bPOS bTMP lo e j
    if sel (lo + j) then
      (upd (upd q.1 (bACT + q.2) (m0 (bTMP + (lo + j)))) (bPOS + m0 (bTMP + (lo + j))) q.2,
        q.2 + 1)
    else q

/-- The static registers of a pass. -/
structure PassCtx (c : Config) (lo hi mode a b bTMP bACT bPOS bDF bFIRST bFPRE : ℕ) : Prop where
  one : c.nreg 130001 = 1
  zero : c.nreg 130009 = 0
  rlo : c.nreg 130300 = lo
  rhi : c.nreg 130301 = hi
  rmode : c.nreg 130637 = mode
  ra : c.nreg 130638 = a
  rb : c.nreg 130639 = b
  rTMP : c.nreg 130650 = bTMP
  rACT : c.nreg 130651 = bACT
  rPOS : c.nreg 130652 = bPOS
  rDF : c.nreg 130653 = bDF
  rFIRST : c.nreg 130654 = bFIRST
  rFPRE : c.nreg 130655 = bFPRE

theorem PassCtx.of_frame {c c' : Config} {lo hi mode a b bTMP bACT bPOS bDF bFIRST bFPRE : ℕ}
    (h : PassCtx c lo hi mode a b bTMP bACT bPOS bDF bFIRST bFPRE)
    (hr : ∀ r, ¬ PassRG r → c'.nreg r = c.nreg r) :
    PassCtx c' lo hi mode a b bTMP bACT bPOS bDF bFIRST bFPRE := by
  ram_grind

/-- The static memory of a pass: the read arrays are disjoint from the written ones. -/
structure PassMem (m : ℕ → ℕ) (W lo hi bTMP bACT bPOS bDF bFIRST bFPRE μ N : ℕ) : Prop where
  lh : lo ≤ hi
  item_lt : ∀ i, lo ≤ i → i < hi → m (bTMP + i) < μ
  first_lt : ∀ v, v < μ → m (bFIRST + v) < N
  wTMP : bTMP + hi ≤ W
  wACT : bACT + hi ≤ W
  wPOS : bPOS + μ ≤ W
  wDF : bDF + μ ≤ W
  wFIRST : bFIRST + μ ≤ W
  wFPRE : bFPRE + N ≤ W
  hiW : hi + 1 ≤ W
  -- the written ranges `ACT[lo, hi)` and `POS[0, μ)` avoid the read arrays
  dTA : bTMP + hi ≤ bACT + lo ∨ bACT + hi ≤ bTMP + lo
  dTP : bTMP + hi ≤ bPOS ∨ bPOS + μ ≤ bTMP + lo
  dDA : bDF + μ ≤ bACT + lo ∨ bACT + hi ≤ bDF
  dDP : bDF + μ ≤ bPOS ∨ bPOS + μ ≤ bDF
  dFA : bFIRST + μ ≤ bACT + lo ∨ bACT + hi ≤ bFIRST
  dFP : bFIRST + μ ≤ bPOS ∨ bPOS + μ ≤ bFIRST
  dRA : bFPRE + N ≤ bACT + lo ∨ bACT + hi ≤ bFPRE
  dRP : bFPRE + N ≤ bPOS ∨ bPOS + μ ≤ bFPRE
  dAP : bACT + hi ≤ bPOS ∨ bPOS + μ ≤ bACT + lo

section proofs

variable {P : Polygon} {W : ℕ}

section
variable (m0 : ℕ → ℕ) (sel : ℕ → Prop)
/-- The pointer of a pass stays within `[e, e + j]`. -/
theorem passMem_ptr (bACT bPOS bTMP lo e j : ℕ) :
    e ≤ (passMem m0 sel bACT bPOS bTMP lo e j).2 ∧
      (passMem m0 sel bACT bPOS bTMP lo e j).2 ≤ e + j := by
  classical
  induction j with
  | zero => aesop
  | succ j ih =>
    core_grind

/-- The pointer of a pass grows. -/
theorem passMem_ptr_mono (bACT bPOS bTMP lo e : ℕ) {j j' : ℕ}
    (h : j ≤ j') :
    (passMem m0 sel bACT bPOS bTMP lo e j).2 ≤ (passMem m0 sel bACT bPOS bTMP lo e j').2 := by
  classical
  induction j' with
  | zero => simp_all
  | succ j' ih =>
    core_grind

/-- A pass changes only `ACT` below the pointer and `POS[0, μ)` (for items below `μ`). -/
theorem passMem_other {bACT bPOS bTMP lo e μ : ℕ} (j : ℕ)
    (hit : ∀ i, lo ≤ i → i < lo + j → m0 (bTMP + i) < μ) {x : ℕ}
    (hx : ¬ (bACT + e ≤ x ∧ x < bACT + (passMem m0 sel bACT bPOS bTMP lo e j).2) ∧
      ¬ (bPOS ≤ x ∧ x < bPOS + μ)) :
    (passMem m0 sel bACT bPOS bTMP lo e j).1 x = m0 x := by
  classical
  induction j with
  | zero => rfl
  | succ j ih =>
    have hp := passMem_ptr m0 sel bACT bPOS bTMP lo e j
    
    by_cases hs : sel (lo + j)
    · have e1 : passMem m0 sel bACT bPOS bTMP lo e (j + 1) =
          (upd (upd (passMem m0 sel bACT bPOS bTMP lo e j).1
            (bACT + (passMem m0 sel bACT bPOS bTMP lo e j).2) (m0 (bTMP + (lo + j))))
            (bPOS + m0 (bTMP + (lo + j))) (passMem m0 sel bACT bPOS bTMP lo e j).2,
          (passMem m0 sel bACT bPOS bTMP lo e j).2 + 1) := by
        core_grind
      rw [e1] at hx ⊢
      simp only at hx ⊢
      have := hit (lo + j) (by omega) (by omega)
      core_grind
    core_grind


end

section
variable {c : Config} (hw : WordsBounded W c)
include hw
/-- **Append.** -/
theorem appendB_exec {bACT bPOS v p : ℕ}
    (hone : c.nreg 130001 = 1) (hA : c.nreg 130651 = bACT) (hP : c.nreg 130652 = bPOS)
    (hv : c.nreg 130658 = v) (hp : c.nreg 130656 = p) (hwA : bACT + p ≤ W) (hwP : bPOS + v ≤ W)
    (hpW : p + 1 ≤ W) :
    ∃ c' k, Exec P W appendB c c' k ∧ k = 5 ∧ WordsBounded W c' ∧
      c'.nmem = upd (upd c.nmem (bACT + p) v) (bPOS + v) p ∧ c'.nreg 130656 = p + 1 ∧
      (∀ r, r ≠ 130656 → r ≠ 130660 → r ≠ 130661 → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold appendB
  exec_block
  all_goals (grind [Machine.upd_apply])

/-- **The class test and the append.** -/
theorem ctestB_exec {bACT bPOS v p mode a b κ : ℕ}
    (hone : c.nreg 130001 = 1) (hzero : c.nreg 130009 = 0) (hA : c.nreg 130651 = bACT)
    (hP : c.nreg 130652 = bPOS) (hv : c.nreg 130658 = v) (hp : c.nreg 130656 = p)
    (hm : c.nreg 130637 = mode) (ha : c.nreg 130638 = a) (hb : c.nreg 130639 = b)
    (hk : c.nreg 130659 = κ)
    (hwA : bACT + p ≤ W) (hwP : bPOS + v ≤ W) (hpW : p + 1 ≤ W) :
    ∃ c' k, Exec P W ctestB c c' k ∧ k ≤ 15 ∧ WordsBounded W c' ∧
      (c'.nmem = if ClassTest mode a b κ then upd (upd c.nmem (bACT + p) v) (bPOS + v) p
        else c.nmem) ∧
      c'.nreg 130656 = (if ClassTest mode a b κ then p + 1 else p) ∧
      (∀ r, r ≠ 130656 → r ≠ 130660 → r ≠ 130661 → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  classical
  -- the interval test
  obtain ⟨c1, k1, e1, hk1, hw1, h1i, h1r, hrr1, hrm1, ho1, hm1⟩ : ∃ c1 k1, Exec P W
      (.ifLtN 130659 130638 (.instr (.constN 130660 0))
        (.ifLtN 130659 130639 (.instr (.constN 130660 1)) (.instr (.constN 130660 0)))) c c1 k1 ∧
      k1 ≤ 5 ∧ WordsBounded W c1 ∧ (c1.nreg 130660 = if a ≤ κ ∧ κ < b then 1 else 0) ∧
      (∀ r, r ≠ 130660 → c1.nreg r = c.nreg r) ∧ c1.rreg = c.rreg ∧ c1.rmem = c.rmem ∧
      c1.output = c.output ∧ c1.nmem = c.nmem := by
    by_cases h1 : c.nreg 130659 < c.nreg 130638
    · have e := Exec.constN (P := P) hw 130660 0 (by omega)
      refine ⟨_, _, .ifLtN_true h1 e, by omega, e.wb_right, ?_, fun r hr => ?_, rfl, rfl, rfl,
        rfl⟩
      all_goals simp_all
    · by_cases h2 : c.nreg 130659 < c.nreg 130639
      · have e := Exec.constN (P := P) hw 130660 1 (by omega)
        refine ⟨_, _, .ifLtN_false h1 (.ifLtN_true h2 e), by omega, e.wb_right, ?_,
          fun r hr => ?_, rfl, rfl, rfl, rfl⟩
        all_goals simp_all
      · have e := Exec.constN (P := P) hw 130660 0 (by omega)
        refine ⟨_, _, .ifLtN_false h1 (.ifLtN_false h2 e), by omega, e.wb_right, ?_,
          fun r hr => ?_, rfl, rfl, rfl, rfl⟩
        all_goals simp_all
  have r1 : ∀ x, x ≠ 130660 → c1.nreg x = c.nreg x := h1r
  have hone1 := (r1 130001 (by omega)).trans hone
  have hzero1 := (r1 130009 (by omega)).trans hzero
  have hm1' := (r1 130637 (by omega)).trans hm
  have hA1 := (r1 130651 (by omega)).trans hA
  have hP1 := (r1 130652 (by omega)).trans hP
  have hv1 := (r1 130658 (by omega)).trans hv
  have hp1 := (r1 130656 (by omega)).trans hp
  -- the decision
  have happ := appendB_exec (P := P) hw1 hone1 hA1 hP1 hv1 hp1 hwA hwP hpW
  obtain ⟨cA, kA, eA, hkA, hwA', hmA, hpA, hrA, hrrA, hrmA, hoA⟩ := happ
  have fin : ∀ (c2 : Config) (k2 : ℕ), Exec P W (.ifLtN 130637 130001 .skip (.ifLtN 130001 130637
      (.ifLtN 130660 130001 appendB .skip) (.ifLtN 130009 130660 appendB .skip))) c1 c2 k2 →
      k2 ≤ 10 → WordsBounded W c2 →
      (c2.nmem = if ClassTest mode a b κ then upd (upd c.nmem (bACT + p) v) (bPOS + v) p
        else c.nmem) →
      c2.nreg 130656 = (if ClassTest mode a b κ then p + 1 else p) →
      (∀ r, r ≠ 130656 → r ≠ 130660 → r ≠ 130661 → c2.nreg r = c1.nreg r) →
      c2.rreg = c1.rreg → c2.rmem = c1.rmem →
      c2.output = c1.output → ∃ c' k, Exec P W ctestB c c' k ∧ k ≤ 15 ∧ WordsBounded W c' ∧
      (c'.nmem = if ClassTest mode a b κ then upd (upd c.nmem (bACT + p) v) (bPOS + v) p
        else c.nmem) ∧
      c'.nreg 130656 = (if ClassTest mode a b κ then p + 1 else p) ∧
      (∀ r, r ≠ 130656 → r ≠ 130660 → r ≠ 130661 → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
    intro c2 k2 e2 hk2 hw2 hm2 hp2 hr2 hrr2 hrm2 ho2
    refine ⟨c2, k1 + k2, .seq e1 e2, by omega, hw2, hm2, hp2, fun r h1 h2 h3 => ?_,
      hrr2.trans hrr1, hrm2.trans hrm1, ho2.trans ho1⟩
    grind
  have hA0 : cA.nmem = upd (upd c.nmem (bACT + p) v) (bPOS + v) p := by grind
  by_cases hm0 : c1.nreg 130637 < c1.nreg 130001
  · -- mode 0: never
    rw [hm1', hone1] at hm0
    have hnt : ¬ ClassTest mode a b κ := by unfold ClassTest; omega
    exact fin c1 _ (.ifLtN_true (by omega) (.skip hw1)) (by omega) hw1
      (by grind) (by grind) (fun _ _ _ _ => rfl) rfl rfl rfl
  · by_cases hm2 : c1.nreg 130001 < c1.nreg 130637
    · -- mode 2: outside the interval
      rw [hm1', hone1] at hm2
      
      by_cases hin : c1.nreg 130660 < c1.nreg 130001
      · have htest : ClassTest mode a b κ := by
          grind [ClassTest]
        exact fin cA _ (.ifLtN_false (by omega)
          (.ifLtN_true (by omega) (.ifLtN_true hin eA))) (by omega) hwA'
          (by grind) (by grind)
          (fun r h1 h2 h3 => hrA r h1 h2 h3) hrrA hrmA hoA
      · have hnt : ¬ ClassTest mode a b κ := by
          grind [ClassTest]
        exact fin c1 _ (.ifLtN_false (by omega)
          (.ifLtN_true (by omega) (.ifLtN_false hin (.skip hw1)))) (by omega)
          hw1 (by grind) (by grind) (fun _ _ _ _ => rfl) rfl rfl rfl
    · -- mode 1: inside the interval
      rw [hm1', hone1] at hm0 hm2
      have hmode1 : mode = 1 := by omega
      by_cases hin : c1.nreg 130009 < c1.nreg 130660
      · have htest : ClassTest mode a b κ := by
          grind [ClassTest]
        exact fin cA _ (.ifLtN_false (by omega)
          (.ifLtN_false (by omega) (.ifLtN_true hin eA))) (by omega) hwA'
          (by grind) (by grind)
          (fun r h1 h2 h3 => hrA r h1 h2 h3) hrrA hrmA hoA
      · have hnt : ¬ ClassTest mode a b κ := by
          grind [ClassTest]
        exact fin c1 _ (.ifLtN_false (by omega)
          (.ifLtN_false (by omega) (.ifLtN_false hin (.skip hw1)))) (by omega)
          hw1 (by grind) (by grind) (fun _ _ _ _ => rfl) rfl rfl rfl

/-- **One item of the pass.** -/
theorem passBody_exec {m0 : ℕ → ℕ}
    {lo hi mode a b bTMP bACT bPOS bDF bFIRST bFPRE μ N e j : ℕ}
    (hC : PassCtx c lo hi mode a b bTMP bACT bPOS bDF bFIRST bFPRE)
    (hM : PassMem m0 W lo hi bTMP bACT bPOS bDF bFIRST bFPRE μ N)
    (hlo : lo ≤ e)
    (hfin : (passMem m0 (SelP m0 bTMP bDF bFIRST bFPRE mode a b) bACT bPOS bTMP lo e
      (hi - lo)).2 ≤ hi)
    (hj : lo + j < hi)
    (hmem : c.nmem = (passMem m0 (SelP m0 bTMP bDF bFIRST bFPRE mode a b) bACT bPOS bTMP lo e
      j).1)
    (hptr : c.nreg 130656 = (passMem m0 (SelP m0 bTMP bDF bFIRST bFPRE mode a b) bACT bPOS bTMP
      lo e j).2)
    (hi' : c.nreg 130657 = lo + j) :
    ∃ c' k, Exec P W passBody c c' k ∧ k ≤ 30 ∧ WordsBounded W c' ∧
      c'.nmem = (passMem m0 (SelP m0 bTMP bDF bFIRST bFPRE mode a b) bACT bPOS bTMP lo e
        (j + 1)).1 ∧
      c'.nreg 130656 = (passMem m0 (SelP m0 bTMP bDF bFIRST bFPRE mode a b) bACT bPOS bTMP lo e
        (j + 1)).2 ∧
      c'.nreg 130657 = lo + j + 1 ∧
      (∀ r, ¬ PassRG r → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧
      c'.output = c.output := by
  classical
  set sel := SelP m0 bTMP bDF bFIRST bFPRE mode a b
  set q := passMem m0 sel bACT bPOS bTMP lo e j
  have hit : ∀ i, lo ≤ i → i < hi → m0 (bTMP + i) < μ := hM.item_lt
  have hq := passMem_ptr_mono m0 sel bACT bPOS bTMP lo e (show j ≤ hi - lo by omega)
  
  have hqh : q.2 ≤ hi := le_trans hq hfin
  -- reads outside the written ranges
  have hread : ∀ x, ¬ (bACT + lo ≤ x ∧ x < bACT + hi) → ¬ (bPOS ≤ x ∧ x < bPOS + μ) →
      c.nmem x = m0 x := by
    intro x h1 h2
    rw [hmem]
    grind [Chazelle.Core.Cluster.passMem_other]
  set i := lo + j
  have hvμ := hit i (by omega) hj
  set v := m0 (bTMP + i)
  have rv : c.nmem (bTMP + i) = v := hread _ (by have := hM.dTA; omega) (by have := hM.dTP; omega)
  have rdf : c.nmem (bDF + v) = m0 (bDF + v) :=
    hread _ (by have := hM.dDA; omega) (by have := hM.dDP; omega)
  have hfv := hM.first_lt v hvμ
  have rfi : c.nmem (bFIRST + v) = m0 (bFIRST + v) :=
    hread _ (by have := hM.dFA; omega) (by have := hM.dFP; omega)
  have rpr : c.nmem (bFPRE + m0 (bFIRST + v)) = m0 (bFPRE + m0 (bFIRST + v)) :=
    hread _ (by have := hM.dRA; omega) (by have := hM.dRP; omega)
  have := hM.wTMP; have := hM.wDF; have := hM.wFIRST; have := hM.wFPRE; have := hM.wACT
  have := hM.wPOS; have := hM.hiW
  -- the loads of `v` and `DF[v]`
  obtain ⟨c1, k1, e1, hk1, hw1, h1v, h1f, h1r, hrr1, hrm1, ho1, hm1⟩ : ∃ c1 k1, Exec P W
      (block [.addN 130661 130650 130657, .loadN 130658 130661, .addN 130661 130653 130658,
        .loadN 130660 130661]) c c1 k1 ∧ k1 = 4 ∧ WordsBounded W c1 ∧ c1.nreg 130658 = v ∧
      c1.nreg 130660 = m0 (bDF + v) ∧
      (∀ r, r ≠ 130658 → r ≠ 130660 → r ≠ 130661 → c1.nreg r = c.nreg r) ∧
      c1.rreg = c.rreg ∧ c1.rmem = c.rmem ∧ c1.output = c.output ∧ c1.nmem = c.nmem := by
    exec_block
    all_goals first | omega | (config_simp; simp only [hC.rTMP, hC.rDF, hi', rv]; omega) | skip
    refine ⟨rfl, ‹_›, by config_simp; simp only [hC.rTMP, hi', rv], by
      config_simp; simp only [hC.rTMP, hC.rDF, hi', rv, rdf], fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    ram_simp
  have hC1 := hC.of_frame (fun r hr => h1r r (by grind [PassRG])
    (by grind [PassRG]) (by grind [PassRG]))
  have h1p : c1.nreg 130656 = q.2 := (h1r _ (by omega) (by omega) (by omega)).trans hptr
  have h1i : c1.nreg 130657 = i := (h1r _ (by omega) (by omega) (by omega)).trans hi'
  have hsel_def : passMem m0 sel bACT bPOS bTMP lo e (j + 1) =
      if sel i then (upd (upd q.1 (bACT + q.2) v) (bPOS + v) q.2, q.2 + 1) else q := by
    grind [passMem]
  -- the conditional part
  obtain ⟨c2, k2, e2, hk2, hw2, h2m, h2p, h2i, h2r, hrr2, hrm2, ho2⟩ : ∃ c2 k2, Exec P W
      (ifNe1 130660 (.seq (block [.addN 130661 130654 130658, .loadN 130661 130661,
        .addN 130661 130655 130661, .loadN 130659 130661]) ctestB)) c1 c2 k2 ∧ k2 ≤ 23 ∧
      WordsBounded W c2 ∧ c2.nmem = (passMem m0 sel bACT bPOS bTMP lo e (j + 1)).1 ∧
      c2.nreg 130656 = (passMem m0 sel bACT bPOS bTMP lo e (j + 1)).2 ∧ c2.nreg 130657 = i ∧
      (∀ r, ¬ PassRG r → c2.nreg r = c1.nreg r) ∧ c2.rreg = c1.rreg ∧ c2.rmem = c1.rmem ∧
      c2.output = c1.output := by
    refine weakenX (ifNe1_exec (P := P) (W := W) (K := 19) hw1 hC1.one 130660 (fun hne => ?_)
      (fun heq => ?_)) (by omega) (fun c' h => h)
    · rw [h1f] at hne
      obtain ⟨c3, k3, e3, hk3, hw3, h3k, h3r, hrr3, hrm3, ho3, hm3⟩ : ∃ c3 k3, Exec P W
          (block [.addN 130661 130654 130658, .loadN 130661 130661, .addN 130661 130655 130661,
            .loadN 130659 130661]) c1 c3 k3 ∧ k3 = 4 ∧ WordsBounded W c3 ∧
          c3.nreg 130659 = m0 (bFPRE + m0 (bFIRST + v)) ∧
          (∀ r, r ≠ 130659 → r ≠ 130661 → c3.nreg r = c1.nreg r) ∧ c3.rreg = c1.rreg ∧
          c3.rmem = c1.rmem ∧ c3.output = c1.output ∧ c3.nmem = c1.nmem := by
        exec_block
        all_goals first | omega |
          (config_simp; simp only [hC1.rFIRST, hC1.rFPRE, h1v, hm1, rfi]; omega) | skip
        refine ⟨rfl, ‹_›, by config_simp; simp only [hC1.rFIRST, hC1.rFPRE, h1v, hm1, rfi, rpr],
          fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
        grind [Machine.upd_apply]
      have r3 : ∀ x, x ≠ 130659 → x ≠ 130661 → c3.nreg x = c1.nreg x := h3r
      obtain ⟨c4, k4, e4, hk4, hw4, h4m, h4p, h4r, hrr4, hrm4, ho4⟩ := ctestB_exec (P := P) (bACT := bACT) (bPOS := bPOS)
        (v := v) (p := q.2) (mode := mode) (a := a) (b := b) hw3
        ((r3 _ (by omega) (by omega)).trans hC1.one) ((r3 _ (by omega) (by omega)).trans hC1.zero)
        ((r3 _ (by omega) (by omega)).trans hC1.rACT) ((r3 _ (by omega) (by omega)).trans hC1.rPOS)
        ((r3 _ (by omega) (by omega)).trans h1v) ((r3 _ (by omega) (by omega)).trans h1p)
        ((r3 _ (by omega) (by omega)).trans hC1.rmode) ((r3 _ (by omega) (by omega)).trans hC1.ra)
        ((r3 _ (by omega) (by omega)).trans hC1.rb) h3k
        (by omega) (by omega) (by omega)
      have hselc : sel i ↔ ClassTest mode a b (m0 (bFPRE + m0 (bFIRST + v))) := by
        show (m0 (bDF + m0 (bTMP + i)) ≠ 1 ∧ _) ↔ _
        grind
      refine ⟨c4, k3 + k4, .seq e3 e4, by omega, hw4, ?_, ?_, ?_, fun r hr => ?_,
        hrr4.trans hrr3, hrm4.trans hrm3, ho4.trans ho3⟩
      all_goals (grind [PassRG])
    · rw [h1f] at heq
      have hs : ¬ sel i := fun h => h.1 heq
      grind
  have hC2 := hC1.of_frame h2r
  have e3 := Exec.addN (P := P) hw2 130657 130657 130001 (by rw [h2i, hC2.one]; omega)
  refine ⟨_, k1 + (k2 + 1), .seq e1 (.seq e2 e3), by omega, e3.wb_right, h2m, ?_, ?_,
    fun r hr => ?_, hrr2.trans hrr1, hrm2.trans hrm1, ho2.trans ho1⟩
  · grind [Machine.upd_apply]
  · simp only [Machine.upd_same, h2i, hC2.one]
  grind [Machine.upd_apply, PassRG]

/-- **A partition pass**: starting with the pointer `e` (register `130656`), the memory and the
pointer become `passMem … (hi - lo)`. -/
theorem passStmt_exec
    {lo hi mode a b bTMP bACT bPOS bDF bFIRST bFPRE μ N e : ℕ}
    (hC : PassCtx c lo hi mode a b bTMP bACT bPOS bDF bFIRST bFPRE)
    (hM : PassMem c.nmem W lo hi bTMP bACT bPOS bDF bFIRST bFPRE μ N)
    (hlo : lo ≤ e) (hptr : c.nreg 130656 = e)
    (hfin : (passMem c.nmem (SelP c.nmem bTMP bDF bFIRST bFPRE mode a b) bACT bPOS bTMP lo e
      (hi - lo)).2 ≤ hi) :
    ∃ c' k, Exec P W passStmt c c' k ∧ k ≤ 32 * (hi - lo) + 3 ∧ WordsBounded W c' ∧
      c'.nmem = (passMem c.nmem (SelP c.nmem bTMP bDF bFIRST bFPRE mode a b) bACT bPOS bTMP lo e
        (hi - lo)).1 ∧
      c'.nreg 130656 = (passMem c.nmem (SelP c.nmem bTMP bDF bFIRST bFPRE mode a b) bACT bPOS
        bTMP lo e (hi - lo)).2 ∧
      (∀ r, ¬ PassRG r → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧
      c'.output = c.output := by
  set m0 := c.nmem
  set sel := SelP m0 bTMP bDF bFIRST bFPRE mode a b
  have hlh := hM.lh
  have e0 := Exec.copyN (P := P) hw 130657 130300
  obtain ⟨c', k, e, hk, hw', hi', hn', hm', hp', hr', hrr', hrm', ho'⟩ := forN (P := P) (W := W)
    (ri := 130657) (rn := 130301) (body := passBody)
    (fun i c2 => WordsBounded W c2 ∧ c2.nreg 130657 = i ∧ c2.nreg 130301 = hi ∧
      c2.nmem = (passMem m0 sel bACT bPOS bTMP lo e (i - lo)).1 ∧
      c2.nreg 130656 = (passMem m0 sel bACT bPOS bTMP lo e (i - lo)).2 ∧
      (∀ r, ¬ PassRG r → c2.nreg r = c.nreg r) ∧ c2.rreg = c.rreg ∧ c2.rmem = c.rmem ∧
      c2.output = c.output ∧ lo ≤ i)
    hi 30 (fun i c2 h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun i c2 hih ⟨hw2, hi2, hn2, hm2, hp2, hr2, hrr2, hrm2, ho2, hlo2⟩ => by
      have hC2 := hC.of_frame hr2
      obtain ⟨c3, k3, e3, hk3, hw3, hm3, hp3, hi3, hr3, hrr3, hrm3, ho3⟩ :=
        passBody_exec (P := P) (j := i - lo) hw2 hC2 hM hlo hfin (by omega) hm2 hp2
          (by omega)
      grind [PassRG])
    (j₀ := lo) ⟨e0.wb_right, by simp [hC.rlo], by
      simp only [Machine.upd_apply]; ram_grind, by aesop,
      by aesop (add simp [Machine.upd_apply, Nat.sub_self]) (add safe (by omega)),
      fun r hr => by
        ram_simp,
      rfl, rfl, rfl, le_rfl⟩ hlh
  exact ⟨c', 1 + k, .seq e0 e, by omega, hw', hm', hp', hr', hrr', hrm', ho'.1⟩


end

end proofs

end

end Chazelle.Core.Cluster
