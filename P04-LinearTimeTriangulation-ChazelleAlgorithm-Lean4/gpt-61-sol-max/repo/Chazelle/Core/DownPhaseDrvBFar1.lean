module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.DownPhaseDrvBCorner
public import Chazelle.Core.DownPhaseDrvBShot

/-!
# Down-phase base (D9), RAM: one walk edge of the far-end scan

The far-end scan of the chord of vertex `i = r212070` in direction code `d = r212086` visits walk
edges `w = (st + u) mod n` (`st = r212093`, `u = r212091`) and keeps the σ-nearest candidate
(`DrvB.Cand`) in `r212097` (walk edge), `r212098` (its edge `qE w` of `Q`), with the flag
`r212099`.  One visit:

* `edgeS`: `w`, `q = qE li n w` (`li = r212011`), `q + 1 mod n` (`r212094 … r212096`);
* `candS` + `candB`: the four height tests of `Strad` and the side test (bits `r212100 … r212104`),
  and the candidate bit `r212107`;
* `updS`: if candidate and (no best yet, or strictly nearer: bit `r212105`), the new best.

Constants `r212000 = 1`, `r212001 = 0`, `r212002 = 2`, `r212010 = n`.
-/

namespace Chazelle.Core

namespace DrvB

open Machine Machine.Stmt Programs SignK WalkKey
open Brute (Src testS)
open DrvR (qE)

@[expose] public section

/-! ## The program -/

/-- The walk edge `w = (st + u) mod n`. -/
def wS : Stmt :=
  .seq (.instr (.addN 212094 212093 212091)) (.ifLtN 212094 212010 .skip (.instr (.subN 212094 212094 212010)))

/-- Its edge `q = qE li n w` of `Q`. -/
def qS : Stmt :=
  .ifLtN 212001 212011 (.instr (.copyN 212095 212094))
    (.seq (.instr (.addN 212106 212094 212000))
      (.ifLtN 212106 212010 (block [.subN 212095 212010 212002, .subN 212095 212095 212094])
        (.instr (.subN 212095 212010 212000))))

/-- `q + 1 mod n`. -/
def q1S : Stmt :=
  .seq (.instr (.addN 212096 212095 212000)) (.ifLtN 212096 212010 .skip (.instr (.constN 212096 0)))

/-- The walk edge `w = (st + u) mod n`, its edge `q = qE li n w` of `Q` and `q + 1 mod n`. -/
def edgeS : Stmt := .seq wS (.seq qS q1S)

/-- The tests of a candidate: heights of the ends of edge `q` against `v_i`, and the side. -/
def candS : Stmt :=
  .seq (testS 1 (.v 212095) (.v 212070) (.v 212070) 212100)
    (.seq (testS 1 (.v 212070) (.v 212096) (.v 212070) 212101)
      (.seq (testS 1 (.v 212096) (.v 212070) (.v 212070) 212102)
        (.seq (testS 1 (.v 212070) (.v 212095) (.v 212070) 212103)
          (.ifLtN 212001 212086 (testS 0 (.e 212095 212070) (.v 212070) (.v 212070) 212104)
            (testS 0 (.v 212070) (.e 212095 212070) (.v 212070) 212104)))))

/-- The candidate bit `r212107 = ((b₀ ∧ b₁) ∨ (b₂ ∧ b₃)) ∧ b₄` by bit arithmetic (`x ∧ y = x + y - 1`,
`x ∨ y = s - (s - 1)` for `s = x + y`). -/
def candB : Stmt :=
  block [.addN 212108 212100 212101, .subN 212109 212108 212000, .addN 212108 212102 212103,
    .subN 212110 212108 212000, .addN 212111 212109 212110, .subN 212108 212111 212000,
    .subN 212112 212111 212108, .addN 212108 212112 212104, .subN 212107 212108 212000]

/-- The new best. -/
def setB : Stmt := block [.copyN 212097 212094, .copyN 212098 212095, .constN 212099 1]

/-- The nearness test against the best candidate. -/
def nearS : Stmt :=
  .ifLtN 212001 212086 (testS 0 (.e 212098 212070) (.e 212095 212070) (.v 212070) 212105)
    (testS 0 (.e 212095 212070) (.e 212098 212070) (.v 212070) 212105)

/-- The update of the best candidate. -/
def updS : Stmt :=
  .ifLtN 212001 212107 (.ifLtN 212001 212099 (.seq nearS (.ifLtN 212001 212105 setB .skip)) setB)
    .skip

/-- **One walk edge of the scan.** -/
def visitS : Stmt := .seq edgeS (.seq candS (.seq candB (.seq updS
  (.instr (.addN 212091 212091 212000)))))

/-- The registers `visitS` writes. -/
def Bvis (r : ℕ) : Bool := Bk r || decide (r = 212091) || decide (212094 ≤ r ∧ r ≤ 212112)

theorem wr_candB : wr (fun r => decide (212107 ≤ r ∧ r ≤ 212112)) candB = true := by decide

/-! ## Mathematics of the bits -/

/-- **The candidate condition on the bits.** -/
theorem cand_iff_bits {Q : Polygon} {i q d : ℕ} (hq : q < Q.n) (_hd : d ≤ 1)
    {b0 b1 b2 b3 b4 : Prop}
    (h0 : b0 ↔ (Q.vtx q).2 < (Q.vtx i).2) (h1 : b1 ↔ (Q.vtx i).2 < (Q.vtx ((q + 1) % Q.n)).2)
    (h2 : b2 ↔ (Q.vtx ((q + 1) % Q.n)).2 < (Q.vtx i).2) (h3 : b3 ↔ (Q.vtx i).2 < (Q.vtx q).2)
    (h4 : b4 ↔ (if d = 0 then (Q.vtx i).1 < edgeXAt Q q i else edgeXAt Q q i < (Q.vtx i).1)) :
    (((b0 ∧ b1) ∨ (b2 ∧ b3)) ∧ b4) ↔ Cand Q i (sgnD d) q := by
  unfold Cand Strad
  rw [h0, h1, h2, h3, h4]
  unfold sgnD
  by_cases h : d = 0
  all_goals simp_all

/-- The σ-order of two crossings on the bits. -/
theorem nearer_iff {Q : Polygon} {i q q' d : ℕ} (_hd : d ≤ 1) {b : Prop}
    (hb : b ↔ (if d = 0 then edgeXAt Q q i < edgeXAt Q q' i else edgeXAt Q q' i < edgeXAt Q q i)) :
    b ↔ sgnD d * edgeXAt Q q i < sgnD d * edgeXAt Q q' i := by
  rw [hb]; unfold sgnD
  by_cases h : d = 0
  all_goals simp_all

section exec

variable {P : Polygon} {W : ℕ}

section
variable (c : Config) (hw : WordsBounded W c)
include hw
theorem wS_exec {n st u : ℕ} (hn : c.nreg 212010 = n)
    (hst : c.nreg 212093 = st) (hu : c.nreg 212091 = u) (hsn : st < n) (hun : u ≤ n)
    (hW : 2 * n ≤ W) :
    ∃ c' k, Exec P W wS c c' k ∧ k ≤ 4 ∧ c'.nreg 212094 = (st + u) % n ∧
      FrameB (fun r => decide (r = 212094)) c c' := by
  have e₁ := Exec.addN (P := P) hw 212094 212093 212091 (by omega)
  have w₁ := e₁.wb_right
  set c₁ : Config := { c with nreg := upd c.nreg 212094 (c.nreg 212093 + c.nreg 212091) }
  have v₁ : c₁.nreg 212094 = st + u := by aesop
  have n₁ : c₁.nreg 212010 = n := by aesop
  by_cases h : st + u < n
  · have ex : Exec P W wS c c₁ (1 + (0 + 1)) :=
      .seq e₁ (.ifLtN_true (by omega) (.skip w₁))
    exact ⟨c₁, _, ex, by omega, by rw [v₁, Nat.mod_eq_of_lt h], exec_frameB ex (by decide)⟩
  · have e₂ := Exec.subN (P := P) w₁ 212094 212094 212010
    have ex : Exec P W wS c _ (1 + (1 + 2)) :=
      .seq e₁ (.ifLtN_false (by omega) e₂)
    refine ⟨_, _, ex, by omega, ?_, exec_frameB ex (by decide)⟩
    simp only [Machine.upd_same]
    rw [v₁, n₁, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

theorem qS_exec {n w : ℕ} {li : Bool}
    (hn : c.nreg 212010 = n) (_hn2 : 2 ≤ n) (hwr : c.nreg 212094 = w) (hwn : w < n)
    (hli : c.nreg 212011 = if li then 1 else 0)
    (c0 : c.nreg 212000 = 1) (c1 : c.nreg 212001 = 0) (c2 : c.nreg 212002 = 2) (hW : n + 1 ≤ W) :
    ∃ c' k, Exec P W qS c c' k ∧ k ≤ 6 ∧ c'.nreg 212095 = qE li n w ∧
      FrameB (fun r => decide (r = 212095 ∨ r = 212106)) c c' := by
  cases li with
  | true =>
    have e₁ := Exec.copyN (P := P) hw 212095 212094
    have ex : Exec P W qS c _ (1 + 1) := .ifLtN_true (by simp_all) e₁
    refine ⟨_, _, ex, by omega, ?_, exec_frameB ex (by decide)⟩
    aesop
  | false =>
    have e₁ := Exec.addN (P := P) hw 212106 212094 212000 (by omega)
    have w₁ := e₁.wb_right
    set c₁ : Config := { c with nreg := upd c.nreg 212106 (c.nreg 212094 + c.nreg 212000) }
    have v₁ : c₁.nreg 212106 = w + 1 := by aesop
    have n₁ : c₁.nreg 212010 = n := by aesop
    by_cases h : w + 1 < n
    · obtain ⟨c₂, e₂, v₂⟩ : ∃ c₂, Exec P W (block [.subN 212095 212010 212002,
          .subN 212095 212095 212094]) c₁ c₂ 2 ∧ c₂.nreg 212095 = n - 2 - w := by
        have a₁ := Exec.subN (P := P) w₁ 212095 212010 212002
        have a₂ := Exec.subN (P := P) a₁.wb_right 212095 212095 212094
        refine ⟨_, Exec.block_cons a₁ (Exec.block_cons a₂ (Exec.block_nil a₂.wb_right)), ?_⟩
        simp_all [c₁]
      have ex : Exec P W qS c c₂ _ :=
        .ifLtN_false (by simp_all) (.seq e₁ (.ifLtN_true (by omega) e₂))
      refine ⟨c₂, _, ex, by omega, ?_, exec_frameB ex (by decide)⟩
      grind [qE]
    · have e₂ := Exec.subN (P := P) w₁ 212095 212010 212000
      have ex : Exec P W qS c _ _ :=
        .ifLtN_false (by simp_all) (.seq e₁ (.ifLtN_false (by omega) e₂))
      refine ⟨_, _, ex, by omega, ?_, exec_frameB ex (by decide)⟩
      simp [c₁, hn, c0, qE, h]

theorem q1S_exec {n q : ℕ} (hn : c.nreg 212010 = n)
    (hq : c.nreg 212095 = q) (hqn : q < n) (c0 : c.nreg 212000 = 1) (hW : n + 1 ≤ W) :
    ∃ c' k, Exec P W q1S c c' k ∧ k ≤ 4 ∧ c'.nreg 212096 = (q + 1) % n ∧
      FrameB (fun r => decide (r = 212096)) c c' := by
  have e₁ := Exec.addN (P := P) hw 212096 212095 212000 (by omega)
  have w₁ := e₁.wb_right
  set c₁ : Config := { c with nreg := upd c.nreg 212096 (c.nreg 212095 + c.nreg 212000) }
  have v₁ : c₁.nreg 212096 = q + 1 := by aesop
  have n₁ : c₁.nreg 212010 = n := by aesop
  by_cases h : q + 1 < n
  · have ex : Exec P W q1S c c₁ (1 + (0 + 1)) :=
      .seq e₁ (.ifLtN_true (by omega) (.skip w₁))
    exact ⟨c₁, _, ex, by omega, by rw [v₁, Nat.mod_eq_of_lt h], exec_frameB ex (by decide)⟩
  · have e₂ := Exec.constN (P := P) w₁ 212096 0 (Nat.zero_le _)
    have ex : Exec P W q1S c _ (1 + (1 + 2)) :=
      .seq e₁ (.ifLtN_false (by omega) e₂)
    refine ⟨_, _, ex, by omega, ?_, exec_frameB ex (by decide)⟩
    grind [Machine.upd_same, Nat.mod_self]

/-- **The walk edge and its edge of `Q`.** -/
theorem edgeS_exec {n st u : ℕ} {li : Bool}
    (hn : c.nreg 212010 = n) (hn2 : 2 ≤ n) (hst : c.nreg 212093 = st) (hu : c.nreg 212091 = u)
    (hsn : st < n) (hun : u ≤ n) (hli : c.nreg 212011 = if li then 1 else 0)
    (c0 : c.nreg 212000 = 1) (c1 : c.nreg 212001 = 0) (c2 : c.nreg 212002 = 2)
    (hW : 2 * n + 2 ≤ W) :
    ∃ c' k, Exec P W edgeS c c' k ∧ k ≤ 14 ∧ c'.nreg 212094 = (st + u) % n ∧
      c'.nreg 212095 = qE li n ((st + u) % n) ∧ c'.nreg 212096 = (qE li n ((st + u) % n) + 1) % n ∧
      FrameB (fun r => decide (r = 212094 ∨ r = 212095 ∨ r = 212096 ∨ r = 212106)) c c' := by
  have hwn : (st + u) % n < n := Nat.mod_lt _ (by omega)
  obtain ⟨c₁, k₁, e₁, hk₁, v₁, f₁⟩ := wS_exec (P := P) c hw hn hst hu hsn hun (by omega)
  have g₁ : ∀ r, r ≠ 212094 → c₁.nreg r = c.nreg r := fun r hr => f₁.1 r (by simp [hr])
  obtain ⟨c₂, k₂, e₂, hk₂, v₂, f₂⟩ := qS_exec (P := P) c₁ e₁.wb_right (li := li)
    (by simp_all) hn2 v₁ hwn (by simp_all)
    (by simp_all) (by simp_all) (by simp_all)
    (by omega)
  have g₂ : ∀ r, r ≠ 212095 → r ≠ 212106 → c₂.nreg r = c₁.nreg r := fun r h1 h2 =>
    f₂.1 r (by simp_all)
  obtain ⟨c₃, k₃, e₃, hk₃, v₃, f₃⟩ := q1S_exec (P := P) c₂ e₂.wb_right
    (by simp_all) v₂ (DownMath.qE_lt li hwn)
    (by simp_all) (by omega)
  have g₃ : ∀ r, r ≠ 212096 → c₃.nreg r = c₂.nreg r := fun r hr => f₃.1 r (by simp [hr])
  have ex : Exec P W edgeS c c₃ (k₁ + (k₂ + k₃)) := .seq e₁ (.seq e₂ e₃)
  refine ⟨c₃, _, ex, by omega, ?_, ?_, v₃, exec_frameB ex (by decide)⟩
  · simp_all
  simp_all


end

/-- The registers `candS` writes. -/
def Bcs (r : ℕ) : Bool := Bk r || decide (212100 ≤ r ∧ r ≤ 212104)

theorem bt_cs {d : ℕ} (hd : 212100 ≤ d ∧ d ≤ 212104) (r : ℕ) (h : Brute.Bt d r = true) :
    Bcs r = true := by
  unfold Brute.Bt at h; unfold Bcs
  ram_grind

theorem bvis_cs (r : ℕ) (h : Bcs r = true) : Bvis r = true := by
  unfold Bcs at h; unfold Bvis
  ram_grind

theorem bvis_of {r : ℕ} (h : r = 212091 ∨ (212094 ≤ r ∧ r ≤ 212112)) : Bvis r = true := by
  omega_nf

theorem keep_bt {d : ℕ} {c₁ c₂ : Config} (f : FrameB (Brute.Bt d) c₁ c₂) {r : ℕ}
    (hr : r < 10000 ∨ 10500 ≤ r) (hrd : r ≠ d) : c₂.nreg r = c₁.nreg r := by
  ram_grind

set_option maxHeartbeats 4000000 in
/-- **The tests of a candidate.** -/
theorem candS_exec (hG : GoodEnv P) (hW : P.n + 3 ≤ W) (c : Config) (hw : WordsBounded W c)
    {q q1 i d : ℕ} (hq : c.nreg 212095 = q) (hq1 : c.nreg 212096 = q1) (hi : c.nreg 212070 = i)
    (hd : c.nreg 212086 = d) (hd1 : d ≤ 1) (c1 : c.nreg 212001 = 0) (hqn : q < P.n)
    (hq1n : q1 < P.n) (hin : i < P.n) :
    ∃ c' k, Exec P W candS c c' k ∧ k ≤ 5 * 245 + 2 ∧ FrameB Bcs c c' ∧
      (∀ r, 212100 ≤ r → r ≤ 212104 → c'.nreg r ≤ 1) ∧
      (c'.nreg 212100 = 1 ↔ ((Qof P).vtx q).2 < ((Qof P).vtx i).2) ∧
      (c'.nreg 212101 = 1 ↔ ((Qof P).vtx i).2 < ((Qof P).vtx q1).2) ∧
      (c'.nreg 212102 = 1 ↔ ((Qof P).vtx q1).2 < ((Qof P).vtx i).2) ∧
      (c'.nreg 212103 = 1 ↔ ((Qof P).vtx i).2 < ((Qof P).vtx q).2) ∧
      (c'.nreg 212104 = 1 ↔ if d = 0 then ((Qof P).vtx i).1 < edgeXAt (Qof P) q i
        else edgeXAt (Qof P) q i < ((Qof P).vtx i).1) := by
  have o95 : Src.Out (.v 212095) := Or.inr (by norm_num)
  have o96 : Src.Out (.v 212096) := Or.inr (by norm_num)
  have o70 : Src.Out (.v 212070) := Or.inr (by norm_num)
  have oe : Src.Out (.e 212095 212070) := ⟨Or.inr (by norm_num), Or.inr (by norm_num)⟩
  obtain ⟨c₁, k₁, e₁, hk₁, f₁, b₁, t₁⟩ := Brute.testS_exec (P := P) hG hW (op := 1) (by norm_num)
    o95 o70 o70 (d := 212100) c hw (by grind [Src.pt, SymPt.Lt]) (by grind [Src.pt, SymPt.Lt])
    (by grind [Src.pt, SymPt.Lt])
  have k₁' : ∀ r, (r < 10000 ∨ 10500 ≤ r) → r ≠ 212100 → c₁.nreg r = c.nreg r :=
    fun r h h' => keep_bt f₁ h h'
  obtain ⟨c₂, k₂, e₂, hk₂, f₂, b₂, t₂⟩ := Brute.testS_exec (P := P) hG hW (op := 1) (by norm_num)
    o70 o96 o70 (d := 212101) c₁ e₁.wb_right
    (by simp_all [Src.pt, SymPt.Lt])
    (by simp_all [Src.pt, SymPt.Lt])
    (by simp_all [Src.pt, SymPt.Lt])
  have k₂' : ∀ r, (r < 10000 ∨ 10500 ≤ r) → r ≠ 212101 → c₂.nreg r = c₁.nreg r :=
    fun r h h' => keep_bt f₂ h h'
  obtain ⟨c₃, k₃, e₃, hk₃, f₃, b₃, t₃⟩ := Brute.testS_exec (P := P) hG hW (op := 1) (by norm_num)
    o96 o70 o70 (d := 212102) c₂ e₂.wb_right
    (by grind [Src.pt, SymPt.Lt])
    (by grind [Src.pt, SymPt.Lt])
    (by grind [Src.pt, SymPt.Lt])
  have k₃' : ∀ r, (r < 10000 ∨ 10500 ≤ r) → r ≠ 212102 → c₃.nreg r = c₂.nreg r :=
    fun r h h' => keep_bt f₃ h h'
  have r95 : c₃.nreg 212095 = q := by
    grind
  have r70 : c₃.nreg 212070 = i := by
    grind
  obtain ⟨c₄, k₄, e₄, hk₄, f₄, b₄, t₄⟩ := Brute.testS_exec (P := P) hG hW (op := 1) (by norm_num)
    o70 o95 o70 (d := 212103) c₃ e₃.wb_right (by grind [Src.pt, SymPt.Lt])
    (by grind [Src.pt, SymPt.Lt]) (by grind [Src.pt, SymPt.Lt])
  have k₄' : ∀ r, (r < 10000 ∨ 10500 ≤ r) → r ≠ 212103 → c₄.nreg r = c₃.nreg r :=
    fun r h h' => keep_bt f₄ h h'
  have r95' : c₄.nreg 212095 = q := by grind
  have r70' : c₄.nreg 212070 = i := by grind
  have r86 : c₄.nreg 212086 = d := by
    grind
  have r01 : c₄.nreg 212001 = 0 := by
    grind
  -- the side test
  obtain ⟨c₅, k₅, e₅, hk₅, f₅, b₅, t₅⟩ : ∃ c₅ k₅, Exec P W
      (.ifLtN 212001 212086 (testS 0 (.e 212095 212070) (.v 212070) (.v 212070) 212104)
        (testS 0 (.v 212070) (.e 212095 212070) (.v 212070) 212104)) c₄ c₅ k₅ ∧ k₅ ≤ 247 ∧
      FrameB (Brute.Bt 212104) c₄ c₅ ∧ c₅.nreg 212104 ≤ 1 ∧
      (c₅.nreg 212104 = 1 ↔ if d = 0 then ((Qof P).vtx i).1 < edgeXAt (Qof P) q i
        else edgeXAt (Qof P) q i < ((Qof P).vtx i).1) := by
    by_cases h0 : d = 0
    · obtain ⟨c₅, k₅, e₅, hk₅, f₅, b₅, t₅⟩ := Brute.testS_exec (P := P) hG hW (op := 0)
        (by norm_num) o70 oe o70 (d := 212104) c₄ e₄.wb_right (by grind [Src.pt, SymPt.Lt])
        (by grind [Src.pt, SymPt.Lt]) (by grind [Src.pt, SymPt.Lt])
      refine ⟨c₅, k₅ + 2, .ifLtN_false (by omega) e₅, by omega, f₅, b₅, ?_⟩
      grind [SignTest, Src.pt, SymPt.eval]
    · obtain ⟨c₅, k₅, e₅, hk₅, f₅, b₅, t₅⟩ := Brute.testS_exec (P := P) hG hW (op := 0)
        (by norm_num) oe o70 o70 (d := 212104) c₄ e₄.wb_right
        (by grind [Src.pt, SymPt.Lt]) (by grind [Src.pt, SymPt.Lt])
        (by grind [Src.pt, SymPt.Lt])
      refine ⟨c₅, k₅ + 1, .ifLtN_true (by omega) e₅, by omega, f₅, b₅, ?_⟩
      grind [SignTest, Src.pt, SymPt.eval]
  have k₅' : ∀ r, (r < 10000 ∨ 10500 ≤ r) → r ≠ 212104 → c₅.nreg r = c₄.nreg r :=
    fun r h h' => keep_bt f₅ h h'
  have ex : Exec P W candS c c₅ (k₁ + (k₂ + (k₃ + (k₄ + k₅)))) :=
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ e₅)))
  have hf : FrameB Bcs c c₅ :=
    fbTrans (fbTrans (fbTrans (fbTrans (fbMono f₁ (bt_cs (by norm_num)))
      (fbMono f₂ (bt_cs (by norm_num)))) (fbMono f₃ (bt_cs (by norm_num))))
      (fbMono f₄ (bt_cs (by norm_num)))) (fbMono f₅ (bt_cs (by norm_num)))
  have v100 : c₅.nreg 212100 = c₁.nreg 212100 := by
    grind
  have v101 : c₅.nreg 212101 = c₂.nreg 212101 := by
    grind
  have v102 : c₅.nreg 212102 = c₃.nreg 212102 := by
    grind
  have v103 : c₅.nreg 212103 = c₄.nreg 212103 := by grind
  refine ⟨c₅, _, ex, by omega, hf, ?_, ?_, ?_, ?_, ?_, t₅⟩
  · intro r h1 h2
    interval_cases r
    all_goals omega
  all_goals (grind [SignTest, Src.pt, SymPt.eval])

/-- **The candidate bit.** -/
theorem candB_exec (c : Config) (hw : WordsBounded W c) (hW : 2 ≤ W) (c0 : c.nreg 212000 = 1)
    (h0 : c.nreg 212100 ≤ 1) (h1 : c.nreg 212101 ≤ 1) (h2 : c.nreg 212102 ≤ 1)
    (h3 : c.nreg 212103 ≤ 1) (h4 : c.nreg 212104 ≤ 1) :
    ∃ c' k, Exec P W candB c c' k ∧ k = 9 ∧ c'.nreg 212107 ≤ 1 ∧
      (c'.nreg 212107 = 1 ↔ ((c.nreg 212100 = 1 ∧ c.nreg 212101 = 1) ∨
        (c.nreg 212102 = 1 ∧ c.nreg 212103 = 1)) ∧ c.nreg 212104 = 1) ∧
      FrameB (fun r => decide (212107 ≤ r ∧ r ≤ 212112)) c c' := by
  obtain ⟨c', k, ex, hk, v1, v2⟩ : ∃ c' k, Exec P W candB c c' k ∧ k = 9 ∧
      c'.nreg 212107 ≤ 1 ∧ (c'.nreg 212107 = 1 ↔ ((c.nreg 212100 = 1 ∧ c.nreg 212101 = 1) ∨
        (c.nreg 212102 = 1 ∧ c.nreg 212103 = 1)) ∧ c.nreg 212104 = 1) := by
    unfold candB
    exec_block
    all_goals try (config_simp; omega)
  exact ⟨c', k, ex, hk, v1, v2, exec_frameB ex wr_candB⟩

theorem wr_setB : wr (fun r => decide (212097 ≤ r ∧ r ≤ 212099)) setB = true := by decide

/-- The new best. -/
theorem setB_exec (c : Config) (hw : WordsBounded W c) (hW : 1 ≤ W) :
    ∃ c' k, Exec P W setB c c' k ∧ k = 3 ∧ c'.nreg 212097 = c.nreg 212094 ∧
      c'.nreg 212098 = c.nreg 212095 ∧ c'.nreg 212099 = 1 ∧
      FrameB (fun r => decide (212097 ≤ r ∧ r ≤ 212099)) c c' := by
  obtain ⟨c', k, ex, hk, v1, v2, v3⟩ : ∃ c' k, Exec P W setB c c' k ∧ k = 3 ∧
      c'.nreg 212097 = c.nreg 212094 ∧ c'.nreg 212098 = c.nreg 212095 ∧ c'.nreg 212099 = 1 := by
    unfold setB
    exec_block
    all_goals simp_all
  exact ⟨c', k, ex, hk, v1, v2, v3, exec_frameB ex wr_setB⟩

/-- The registers `updS` writes. -/
def Bup (r : ℕ) : Bool := Bk r || decide (212097 ≤ r ∧ r ≤ 212105)

theorem bup_vis (r : ℕ) (h : Bup r = true) : Bvis r = true := by
  unfold Bup at h; unfold Bvis
  ram_grind

theorem bt_up {d : ℕ} (hd : 212097 ≤ d ∧ d ≤ 212105) (r : ℕ) (h : Brute.Bt d r = true) :
    Bup r = true := by
  unfold Brute.Bt at h; unfold Bup
  ram_grind

set_option maxHeartbeats 2000000 in
/-- **The update of the best candidate**: a candidate replaces the best if there is none or if it
is strictly nearer (in direction `sgnD d`). -/
theorem updS_exec (hG : GoodEnv P) (hW : P.n + 3 ≤ W) (c : Config) (hw : WordsBounded W c)
    {i d q bq : ℕ} (hi : c.nreg 212070 = i) (hd : c.nreg 212086 = d) (hd1 : d ≤ 1)
    (hq : c.nreg 212095 = q) (hbq : c.nreg 212098 = bq) (c1 : c.nreg 212001 = 0)
    (hcb : c.nreg 212107 ≤ 1) (hh : c.nreg 212099 ≤ 1) (hin : i < P.n) (hqn : q < P.n)
    (hbqn : c.nreg 212099 = 1 → bq < P.n) :
    ∃ c' k, Exec P W updS c c' k ∧ k ≤ 260 ∧ FrameB Bup c c' ∧
      ((c.nreg 212107 = 1 ∧ (c.nreg 212099 = 0 ∨
          sgnD d * edgeXAt (Qof P) q i < sgnD d * edgeXAt (Qof P) bq i)) →
        c'.nreg 212097 = c.nreg 212094 ∧ c'.nreg 212098 = q ∧ c'.nreg 212099 = 1) ∧
      (¬ (c.nreg 212107 = 1 ∧ (c.nreg 212099 = 0 ∨
          sgnD d * edgeXAt (Qof P) q i < sgnD d * edgeXAt (Qof P) bq i)) →
        c'.nreg 212097 = c.nreg 212097 ∧ c'.nreg 212098 = c.nreg 212098 ∧
          c'.nreg 212099 = c.nreg 212099) := by
  have fs : ∀ {c₁ c₂ : Config}, FrameB (fun r => decide (212097 ≤ r ∧ r ≤ 212099)) c₁ c₂ →
      FrameB Bup c₁ c₂ := fun f => fbMono f fun r h => by
        simp_all [decide_eq_true_eq, Bup, Bool.or_eq_true] <;> omega_nf
  by_cases hc : c.nreg 212107 = 1
  · by_cases hh0 : c.nreg 212099 = 0
    · obtain ⟨c', k, e, hk, v1, v2, v3, f⟩ := setB_exec (P := P) c hw (by omega)
      have ex : Exec P W updS c c' _ :=
        .ifLtN_true (by omega) (.ifLtN_false (by omega) e)
      grind
    · have hh1 : c.nreg 212099 = 1 := by omega
      
      have oe : Src.Out (.e 212095 212070) := ⟨Or.inr (by norm_num), Or.inr (by norm_num)⟩
      have ob : Src.Out (.e 212098 212070) := ⟨Or.inr (by norm_num), Or.inr (by norm_num)⟩
      have o70 : Src.Out (.v 212070) := Or.inr (by norm_num)
      -- the nearness test
      obtain ⟨c₁, k₁, e₁, hk₁, f₁, b₁, t₁⟩ : ∃ c₁ k₁, Exec P W nearS c c₁ k₁ ∧ k₁ ≤ 247 ∧
          FrameB (Brute.Bt 212105) c c₁ ∧ c₁.nreg 212105 ≤ 1 ∧
          (c₁.nreg 212105 = 1 ↔ sgnD d * edgeXAt (Qof P) q i < sgnD d * edgeXAt (Qof P) bq i) := by
        by_cases h0 : d = 0
        · obtain ⟨c₁, k₁, e₁, hk₁, f₁, b₁, t₁⟩ := Brute.testS_exec (P := P) hG hW (op := 0)
            (by norm_num) oe ob o70 (d := 212105) c hw (by grind [Src.pt, SymPt.Lt])
            (by grind [Src.pt, SymPt.Lt]) (by grind [Src.pt, SymPt.Lt])
          refine ⟨c₁, k₁ + 2, .ifLtN_false (by omega) e₁, by omega, f₁, b₁, ?_⟩
          rw [t₁, ← nearer_iff (Q := Qof P) (i := i) (q := q) (q' := bq) hd1
            (b := edgeXAt (Qof P) q i < edgeXAt (Qof P) bq i) (by simp_all)]
          grind [SignTest, Src.pt, SymPt.eval]
        · obtain ⟨c₁, k₁, e₁, hk₁, f₁, b₁, t₁⟩ := Brute.testS_exec (P := P) hG hW (op := 0)
            (by norm_num) ob oe o70 (d := 212105) c hw (by grind [Src.pt, SymPt.Lt])
            (by grind [Src.pt, SymPt.Lt]) (by grind [Src.pt, SymPt.Lt])
          refine ⟨c₁, k₁ + 1, .ifLtN_true (by omega) e₁, by omega, f₁, b₁, ?_⟩
          rw [t₁, ← nearer_iff (Q := Qof P) (i := i) (q := q) (q' := bq) hd1
            (b := edgeXAt (Qof P) bq i < edgeXAt (Qof P) q i) (by simp_all)]
          grind [SignTest, Src.pt, SymPt.eval]
      have k₁' : ∀ r, (r < 10000 ∨ 10500 ≤ r) → r ≠ 212105 → c₁.nreg r = c.nreg r :=
        fun r h h' => keep_bt f₁ h h'
      have c1' : c₁.nreg 212001 = 0 := by grind
      by_cases hn : c₁.nreg 212105 = 1
      · obtain ⟨c', k, e, hk, v1, v2, v3, f⟩ := setB_exec (P := P) c₁ e₁.wb_right (by omega)
        have ex : Exec P W updS c c' _ :=
          .ifLtN_true (by omega) (.ifLtN_true (by omega)
            (.seq e₁ (.ifLtN_true (by omega) e)))
        refine ⟨c', _, ex, by omega, fbTrans (fbMono f₁ (bt_up (by norm_num))) (fs f),
          fun _ => ⟨?_, ?_, v3⟩, fun h => absurd ⟨hc, Or.inr (t₁.1 hn)⟩ h⟩
        all_goals grind
      · have ex : Exec P W updS c c₁ _ :=
          .ifLtN_true (by omega) (.ifLtN_true (by omega)
            (.seq e₁ (.ifLtN_false (by omega) (.skip e₁.wb_right))))
        ram_grind
  · have ex : Exec P W updS c c _ := .ifLtN_false (by omega) (.skip hw)
    ram_grind

/-- The cost bound of one visit. -/
def visK : ℕ := 1600

set_option maxHeartbeats 4000000 in
/-- **One walk edge of the scan**: the edge `w = (st + u) mod n`; a candidate replaces the best if
there is none or if it is strictly nearer. -/
theorem visitS_exec (hG : GoodEnv P) (hW : P.n + 3 ≤ W) (hW2 : 2 * P.n + 2 ≤ W) (c : Config)
    (hw : WordsBounded W c) {st u i d : ℕ} {li : Bool}
    (hn : c.nreg 212010 = P.n) (hst : c.nreg 212093 = st) (hu : c.nreg 212091 = u)
    (hsn : st < P.n) (hun : u < P.n) (hli : c.nreg 212011 = if li then 1 else 0)
    (hi : c.nreg 212070 = i) (hin : i < P.n) (hd : c.nreg 212086 = d) (hd1 : d ≤ 1)
    (c0 : c.nreg 212000 = 1) (c1 : c.nreg 212001 = 0) (c2 : c.nreg 212002 = 2)
    (hh : c.nreg 212099 ≤ 1) (hbqn : c.nreg 212099 = 1 → c.nreg 212098 < P.n) :
    ∃ c' k, Exec P W visitS c c' k ∧ k ≤ visK ∧ FrameB Bvis c c' ∧ c'.nreg 212091 = u + 1 ∧
      (Cand (Qof P) i (sgnD d) (qE li P.n ((st + u) % P.n)) ∧ (c.nreg 212099 = 0 ∨
          sgnD d * edgeXAt (Qof P) (qE li P.n ((st + u) % P.n)) i <
            sgnD d * edgeXAt (Qof P) (c.nreg 212098) i) →
        c'.nreg 212097 = (st + u) % P.n ∧ c'.nreg 212098 = qE li P.n ((st + u) % P.n) ∧
          c'.nreg 212099 = 1) ∧
      (¬ (Cand (Qof P) i (sgnD d) (qE li P.n ((st + u) % P.n)) ∧ (c.nreg 212099 = 0 ∨
          sgnD d * edgeXAt (Qof P) (qE li P.n ((st + u) % P.n)) i <
            sgnD d * edgeXAt (Qof P) (c.nreg 212098) i)) →
        c'.nreg 212097 = c.nreg 212097 ∧ c'.nreg 212098 = c.nreg 212098 ∧
          c'.nreg 212099 = c.nreg 212099) := by
  have hn3 : 3 ≤ P.n := hG.1.1
  set w := (st + u) % P.n with hwdef
  have hwn : w < P.n := Nat.mod_lt _ (by omega)
  set q := qE li P.n w with hqdef
  have hqn : q < P.n := DownMath.qE_lt li hwn
  -- the edge
  obtain ⟨c₁, k₁, e₁, hk₁, v94, v95, v96, f₁⟩ := edgeS_exec (P := P) c hw hn (by omega) hst hu hsn
    hun.le hli c0 c1 c2 hW2
  have g₁ : ∀ r, r ≠ 212094 → r ≠ 212095 → r ≠ 212096 → r ≠ 212106 → c₁.nreg r = c.nreg r :=
    fun r a b c d => f₁.1 r (by simp_all)
  -- the tests
  obtain ⟨c₂, k₂, e₂, hk₂, f₂, hb₂, t0, t1, t2, t3, t4⟩ := candS_exec (P := P) hG hW c₁ e₁.wb_right
    v95 v96 (by grind)
    (by grind) hd1
    (by grind) hqn
    (Nat.mod_lt _ (by omega)) hin
  have g₂ : ∀ r, (r < 10000 ∨ 10500 ≤ r) → (r < 212100 ∨ 212104 < r) → c₂.nreg r = c₁.nreg r :=
    fun r h h' => f₂.1 r (by omega_nf)
  -- the candidate bit
  obtain ⟨c₃, k₃, e₃, hk₃, hb₃, t₃, f₃⟩ := candB_exec (P := P) c₂ e₂.wb_right (by omega)
    (by grind)
    (hb₂ _ le_rfl (by norm_num)) (hb₂ _ (by norm_num) (by norm_num))
    (hb₂ _ (by norm_num) (by norm_num)) (hb₂ _ (by norm_num) (by norm_num))
    (hb₂ _ (by norm_num) le_rfl)
  have g₃ : ∀ r, (r < 212107 ∨ 212112 < r) → c₃.nreg r = c₂.nreg r := fun r h =>
    f₃.1 r (by simp; omega)
  have hcand : c₃.nreg 212107 = 1 ↔ Cand (Qof P) i (sgnD d) q := by
    rw [t₃]
    have hQn : (Qof P).n = P.n := shear_n _ _
    exact cand_iff_bits (Q := Qof P) (by omega) hd1 t0 (by grind)
      (by grind) t3 t4
  -- registers kept from the start, and the edge registers
  have kc : ∀ r, (r < 10000 ∨ 10500 ≤ r) → (r < 212094 ∨ 212112 < r ∨ r = 212097 ∨ r = 212098 ∨
      r = 212099) → c₃.nreg r = c.nreg r := by
    intro r h h'
    rw [g₃ r (by omega), g₂ r h (by omega), g₁ r (by omega) (by omega) (by omega) (by omega)]
  have k94 : c₃.nreg 212094 = w := by
    grind
  have k95 : c₃.nreg 212095 = q := by
    grind
  -- the update
  obtain ⟨c₄, k₄, e₄, hk₄, f₄, u1, u2⟩ := updS_exec (P := P) hG hW c₃ e₃.wb_right (i := i) (d := d)
    (q := q) (bq := c.nreg 212098) (by grind)
    (by grind) hd1 k95
    (by grind) (by grind)
    hb₃ (by grind) hin hqn
    (by grind)
  have g₄ : ∀ r, Bup r = false → c₄.nreg r = c₃.nreg r := f₄.1
  -- the counter
  have u91 : c₄.nreg 212091 = u := by
    rw [g₄ _ (by decide), g₃ _ (by norm_num), g₂ _ (by norm_num) (by norm_num),
      g₁ _ (by decide) (by decide) (by decide) (by decide), hu]
  have u00 : c₄.nreg 212000 = 1 := by
    rw [g₄ _ (by decide), kc _ (by norm_num) (by norm_num), c0]
  have e₅ := Exec.addN (P := P) e₄.wb_right 212091 212091 212000 (by omega)
  have f₅ : FrameB (fun r => decide (r = 212091)) c₄ _ := exec_frameB e₅ (by decide)
  have ex : Exec P W visitS c _ (k₁ + (k₂ + (k₃ + (k₄ + 1)))) :=
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ e₅)))
  have ec : ∀ r, r ≠ 212091 →
      upd c₄.nreg 212091 (c₄.nreg 212091 + c₄.nreg 212000) r = c₄.nreg r :=
    fun r h => Machine.upd_other _ _ _ h
  refine ⟨_, _, ex, ?_, ?_, ?_, ?_, ?_⟩
  · omega_nf
  · refine fbTrans (fbTrans (fbTrans (fbTrans (fbMono f₁ ?_) (fbMono f₂ bvis_cs)) (fbMono f₃ ?_))
      (fbMono f₄ bup_vis)) (fbMono f₅ ?_) <;> intro r h <;> simp only [decide_eq_true_eq] at h <;>
      exact bvis_of (by omega)
  · simp only [Machine.upd_apply, ite_true, u91, u00]
  all_goals ram_grind

end exec

end

end DrvB

end Chazelle.Core
