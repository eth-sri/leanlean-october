module

public import Chazelle.MacT
public import Chazelle.Core.DownPhaseDrvBCorner
public import Chazelle.Core.DownPhaseDrvRExtSpec
public import Chazelle.Core.DownPhaseDrvBCtx
public import Chazelle.Core.ShootCutShPt

section
set_option hygiene false
local macro "zqbeg" : tactic => `(tactic| refine ⟨_, _, ex, by_omega, ?_, exec_frameB ex by_decide⟩)
local macro "zqbeh" : tactic => `(tactic| exact ⟨c₁, _, ex, by_omega, by rw [v₁, Nat.mod_eq_of_lt h], exec_frameB ex by_decide⟩)
local macro "zqbei" : tactic => `(tactic| have n₁ : c₁.nreg 212010 = n := by_tauto)
local macro "zqbej" : tactic => `(tactic| have oe : Src.Out ztejl := ⟨by_omega, by_omega⟩)
local macro "zqbek" : tactic => `(tactic| (rw [hcand, kc _ by_norm_num by_norm_num]; exact h))
set_option hygiene true

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
  .seq (testS 1 ztpse ztboh ztboh 212100)
    (.seq (testS 1 ztboh ztpsf ztboh 212101)
      (.seq (testS 1 ztpsf ztboh ztboh 212102)
        (.seq (testS 1 ztboh ztpse ztboh 212103)
          (.ifLtN 212001 212086 ztywx
            ztyww))))

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
  .ifLtN 212001 212086 (testS 0 ztnab ztejl ztboh 212105)
    (testS 0 ztejl ztnab ztboh 212105)

/-- The update of the best candidate. -/
def updS : Stmt :=
  .ifLtN 212001 212107 (.ifLtN 212001 212099 (.seq nearS (.ifLtN 212001 212105 setB .skip)) setB)
    .skip

/-- **One walk edge of the scan.** -/
def visitS : Stmt := .seq edgeS (.seq candS (.seq candB (.seq updS
  (.instr (.addN 212091 212091 212000)))))

/-- The registers `visitS` writes. -/
def Bvis (r : ℕ) : Bool := Bk r || decide (r = 212091) || decide ztnfr
theorem wr_candB : wr ztijx candB = true := by_decide

/-! ## Mathematics of the bits -/
variable {Q : Polygon}
/-- **The candidate condition on the bits.** -/
theorem cand_iff_bits {i q d : ℕ} (hq : q < Q.n) (_hd : d ≤ 1)
    {b0 b1 b2 b3 b4 : Prop}
    (h0 : b0 ↔ (Q.vtx q).2 < (Q.vtx i).2) (h1 : b1 ↔ (Q.vtx i).2 < (Q.vtx ztxam).2)
    (h2 : b2 ↔ (Q.vtx ztxam).2 < (Q.vtx i).2) (h3 : b3 ↔ (Q.vtx i).2 < (Q.vtx q).2)
    (h4 : b4 ↔ (if d = 0 then (Q.vtx i).1 < edgeXAt Q q i else edgeXAt Q q i < (Q.vtx i).1)) :
    (((b0 ∧ b1) ∨ (b2 ∧ b3)) ∧ b4) ↔ Cand Q i ztbgl q := by
  unfold Cand Strad
  rw [h0, h1, h2, h3, h4]
  unfold sgnD
  zujsc
  · simp_all
  simp_all

/-- The σ-order of two crossings on the bits. -/
theorem nearer_iff {i q q' d : ℕ} (_hd : d ≤ 1) {b : Prop}
    (hb : b ↔ (if d = 0 then edgeXAt Q q i < edgeXAt Q q' i else edgeXAt Q q' i < edgeXAt Q q i)) :
    b ↔ sgnD d * edgeXAt Q q i < sgnD d * edgeXAt Q q' i := by
  rw [hb]; unfold sgnD
  zujsc
  · zugyx
  simp_all
section exec
variable {P : Polygon} {W : ℕ}
theorem wS_exec (c : Config) (hw : WordsBounded W c) {n st u : ℕ} (hn : c.nreg 212010 = n)
    (hst : c.nreg 212093 = st) (hu : c.nreg 212091 = u) (hsn : st < n) (hun : u ≤ n)
    (hW : 2 * n ≤ W) :
    ∃ c' k, Exec P W wS c c' k ∧ k ≤ 4 ∧ c'.nreg 212094 = ztcfh % n ∧
      FrameB (fun r => decide (r = 212094)) c c' := by
  have e₁ := Exec.addN (P := P) hw 212094 212093 212091 by_omega
  zud
  set c₁ : Config := { c with nreg := upd c.nreg 212094 (c.nreg 212093 + c.nreg 212091) }
  have v₁ : c₁.nreg 212094 = st + u := by simp [c₁, hst, hu]
  zqbei
  by_cases h : st + u < n
  · have ex : Exec P W wS c c₁ _ :=
      .seq e₁ ztxdi
    zqbeh
  · have e₂ := Exec.subN (P := P) w₁ 212094 212094 212010
    have ex : Exec P W wS c _ _ :=
      .seq e₁ ztcry
    zqbeg
    zuvz
    rw [v₁, n₁, Nat.mod_eq_sub_mod by_omega, Nat.mod_eq_of_lt by_omega]
theorem qS_exec (c : Config) (hw : WordsBounded W c) {n w : ℕ} {li : Bool}
    (hn : c.nreg 212010 = n) (_hn2 : 2 ≤ n) (hwr : c.nreg 212094 = w) (hwn : w < n)
    (hli : c.nreg 212011 = if li then 1 else 0)
    (c0 : c.nreg 212000 = 1) (c1 : c.nreg 212001 = 0) (c2 : c.nreg 212002 = 2) (hW : n + 1 ≤ W) :
    ∃ c' k, Exec P W qS c c' k ∧ k ≤ 6 ∧ c'.nreg 212095 = qE li n w ∧
      FrameB (fun r => decide (r = 212095 ∨ r = 212106)) c c' := by
  cases li with
  | true =>
    have e₁ := Exec.copyN (P := P) hw 212095 212094
    have ex : ztpju := .ifLtN_true by_simp_all e₁
    zqbeg
    simp [hwr, qE]
  | false =>
    have e₁ := Exec.addN (P := P) hw 212106 212094 212000 by_omega
    zud
    set c₁ : Config := { c with nreg := upd c.nreg 212106 _ }
    have v₁ : c₁.nreg 212106 = w + 1 := by simp [c₁, hwr, c0]
    zqbei
    by_cases h : w + 1 < n
    · obtain ⟨c₂, e₂, v₂⟩ : ∃ c₂, Exec P W (block [.subN 212095 212010 212002,
          .subN 212095 212095 212094]) c₁ c₂ 2 ∧ c₂.nreg 212095 = n - 2 - w := by
        have a₁ := Exec.subN (P := P) w₁ 212095 212010 212002
        have a₂ := Exec.subN (P := P) a₁.wb_right 212095 212095 212094
        refine ⟨_, Exec.block_cons a₁ (Exec.block_cons a₂ (Exec.block_nil a₂.wb_right)), ?_⟩
        simp [c₁, hn, c2, hwr]
      have ex : Exec P W qS c c₂ _ :=
        .ifLtN_false by_simp_all (.seq e₁ ztbxn)
      refine ⟨c₂, _, ex, by_omega, ?_, exec_frameB ex by_decide⟩
      rw [v₂]; simp [qE, h]
    · have e₂ := Exec.subN (P := P) w₁ 212095 212010 212000
      have ex : ztpju :=
        .ifLtN_false by_simp_all (.seq e₁ ztcry)
      zqbeg
      simp [c₁, hn, c0, qE, h]
theorem q1S_exec (c : Config) (hw : WordsBounded W c) {n q : ℕ} (hn : c.nreg 212010 = n)
    (hq : c.nreg 212095 = q) (hqn : q < n) (c0 : c.nreg 212000 = 1) (hW : n + 1 ≤ W) :
    ∃ c' k, Exec P W q1S c c' k ∧ k ≤ 4 ∧ c'.nreg 212096 = ztfo % n ∧
      FrameB (fun r => decide (r = 212096)) c c' := by
  have e₁ := Exec.addN (P := P) hw 212096 212095 212000 by_omega
  zud
  set c₁ : Config := { c with nreg := upd c.nreg 212096 (c.nreg 212095 + c.nreg 212000) }
  have v₁ : c₁.nreg 212096 = q + 1 := by simp [c₁, hq, c0]
  zqbei
  by_cases h : q + 1 < n
  · have ex : Exec P W q1S c c₁ _ :=
      .seq e₁ ztxdi
    zqbeh
  · have e₂ := Exec.constN (P := P) w₁ 212096 0 ztbg
    have ex : Exec P W q1S c _ _ :=
      .seq e₁ ztcry
    zqbeg
    zuvz
    zubac

/-- **The walk edge and its edge of `Q`.** -/
theorem edgeS_exec (c : Config) (hw : WordsBounded W c) {n st u : ℕ} {li : Bool}
    (hn : c.nreg 212010 = n) (hn2 : 2 ≤ n) (hst : c.nreg 212093 = st) (hu : c.nreg 212091 = u)
    (hsn : st < n) (hun : u ≤ n) (hli : c.nreg 212011 = if li then 1 else 0)
    (c0 : c.nreg 212000 = 1) (c1 : c.nreg 212001 = 0) (c2 : c.nreg 212002 = 2)
    (hW : 2 * n + 2 ≤ W) :
    ∃ c' k, Exec P W edgeS c c' k ∧ k ≤ 14 ∧ c'.nreg 212094 = ztcfh % n ∧
      c'.nreg 212095 = qE li n ztzyz ∧ c'.nreg 212096 = (qE li n ztzyz + 1) % n ∧
      FrameB (fun r => decide (r = 212094 ∨ r = 212095 ∨ r = 212096 ∨ r = 212106)) c c' := by
  have hwn : ztcfh % n < n := Nat.mod_lt _ by_omega
  obtain ⟨c₁, k₁, e₁, hk₁, v₁, f₁⟩ := wS_exec (P := P) c hw hn hst hu hsn hun by_omega
  have g₁ : ∀ r, r ≠ 212094 → c₁.nreg r = c.nreg r := fun r hr => f₁.1 r by_simp_all
  obtain ⟨c₂, k₂, e₂, hk₂, v₂, f₂⟩ := qS_exec (P := P) c₁ e₁.wb_right (li := li)
    by_simp_all hn2 v₁ hwn by_simp_all
    by_simp_all by_simp_all by_simp_all
    by_omega
  have g₂ : ∀ r, r ≠ 212095 → r ≠ 212106 → c₂.nreg r = c₁.nreg r := fun r h1 h2 =>
    f₂.1 r by_simp_all
  obtain ⟨c₃, k₃, e₃, hk₃, v₃, f₃⟩ := q1S_exec (P := P) c₂ e₂.wb_right
    by_simp_all v₂ (DownMath.qE_lt li hwn)
    by_simp_all by_omega
  have g₃ : ∀ r, r ≠ 212096 → c₃.nreg r = c₂.nreg r := fun r hr => f₃.1 r by_simp_all
  have ex : Exec P W edgeS c c₃ _ := .seq e₁ ztcr
  refine ⟨c₃, _, ex, by_omega, ?_, ?_, v₃, exec_frameB ex by_decide⟩
  · simp_all
  simp_all

/-- The registers `candS` writes. -/
def Bcs (r : ℕ) : Bool := Bk r || decide (212100 ≤ r ∧ r ≤ 212104)
variable {d : ℕ}
theorem bt_cs (hd : 212100 ≤ d ∧ d ≤ 212104) (r : ℕ) (h : Brute.Bt d r = true) :
    Bcs r = true := by
  unfold Brute.Bt at h; unfold Bcs
  grind
theorem bvis_cs (r : ℕ) (h : Bcs r = true) : Bvis r = true := by
  unfold Bcs at h; unfold Bvis
  grind
theorem bvis_of {r : ℕ} (h : r = 212091 ∨ ztnfr) : Bvis r = true := by
  unfold Bvis; grind
theorem keep_bt {c₁ c₂ : Config} (f : FrameB ztpwk c₁ c₂) {r : ℕ}
    (hr : r < 10000 ∨ 10500 ≤ r) (hrd : r ≠ d) : c₂.nreg r = c₁.nreg r := by
  zuhiw
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
      (c'.nreg 212104 = 1 ↔ if d = 0 then ((Qof P).vtx i).1 < edgeXAt zta q i
        else edgeXAt zta q i < ((Qof P).vtx i).1) := by
  have o95 : Src.Out ztpse := Or.inr by_norm_num
  have o96 : Src.Out ztpsf := Or.inr by_norm_num
  zuibj
  zqbej
  obtain ⟨c₁, k₁, e₁, hk₁, f₁, b₁, t₁⟩ := Brute.testS_exec (P := P) hG hW (op := 1) by_norm_num
    o95 o70 o70 (d := 212100) c hw (by simp [Src.pt, SymPt.Lt, hq, hqn]) ztcud
    ztcud
  have k₁' : ∀ r, ztcu → r ≠ 212100 → c₁.nreg r = c.nreg r :=
    fun r h h' => keep_bt f₁ h h'
  obtain ⟨c₂, k₂, e₂, hk₂, f₂, b₂, t₂⟩ := Brute.testS_exec (P := P) hG hW (op := 1) by_norm_num
    o70 o96 o70 (d := 212101) c₁ e₁.wb_right
    ztgrc
    (by simp [Src.pt, SymPt.Lt, k₁' 212096 by_norm_num by_norm_num, hq1, hq1n])
    ztgrc
  have k₂' : ∀ r, ztcu → r ≠ 212101 → c₂.nreg r = c₁.nreg r :=
    fun r h h' => keep_bt f₂ h h'
  obtain ⟨c₃, k₃, e₃, hk₃, f₃, b₃, t₃⟩ := Brute.testS_exec (P := P) hG hW (op := 1) by_norm_num
    o96 o70 o70 (d := 212102) c₂ e₂.wb_right
    (by simp [Src.pt, SymPt.Lt, k₂' 212096 by_norm_num by_norm_num,
      k₁' 212096 by_norm_num by_norm_num, hq1, hq1n])
    (by simp [Src.pt, SymPt.Lt, k₂' 212070 by_norm_num by_norm_num,
      k₁' 212070 by_norm_num by_norm_num, hi, hin])
    (by simp [Src.pt, SymPt.Lt, k₂' 212070 by_norm_num by_norm_num,
      k₁' 212070 by_norm_num by_norm_num, hi, hin])
  have k₃' : ∀ r, ztcu → r ≠ 212102 → c₃.nreg r = c₂.nreg r :=
    fun r h h' => keep_bt f₃ h h'
  have r95 : zturz := by
    simp_all
  have r70 : ztury := by
    simp_all
  obtain ⟨c₄, k₄, e₄, hk₄, f₄, b₄, t₄⟩ := Brute.testS_exec (P := P) hG hW (op := 1) by_norm_num
    o70 o95 o70 (d := 212103) c₃ e₃.wb_right ztjqk
    (by simp [Src.pt, SymPt.Lt, r95, hqn]) ztjqk
  have k₄' : ∀ r, ztcu → r ≠ 212103 → c₄.nreg r = c₃.nreg r :=
    fun r h h' => keep_bt f₄ h h'
  have r95' : c₄.nreg 212095 = q := by_grind
  have r70' : ztust := by_grind
  have r86 : c₄.nreg 212086 = d := by
    grind
  have r01 : c₄.nreg 212001 = 0 := by
    grind
  -- the side test
  obtain ⟨c₅, k₅, e₅, hk₅, f₅, b₅, t₅⟩ : ∃ c₅ k₅, Exec P W
      (.ifLtN 212001 212086 ztywx
        ztyww) c₄ c₅ k₅ ∧ k₅ ≤ 247 ∧
      FrameB (Brute.Bt 212104) c₄ c₅ ∧ c₅.nreg 212104 ≤ 1 ∧
      (c₅.nreg 212104 = 1 ↔ if d = 0 then ((Qof P).vtx i).1 < edgeXAt zta q i
        else edgeXAt zta q i < ((Qof P).vtx i).1) := by
    zuckz
    · obtain ⟨c₅, k₅, e₅, hk₅, f₅, b₅, t₅⟩ := Brute.testS_exec hG hW (op := 0)
        by_norm_num o70 oe o70 c₄ e₄.wb_right ztcue
        zthfi ztcue
      refine ⟨c₅, k₅ + 2, .ifLtN_false by_omega e₅, by_omega, f₅, b₅, ?_⟩
      rw [t₅, ite_eq_left h0]
      zufpk
    · obtain ⟨c₅, k₅, e₅, hk₅, f₅, b₅, t₅⟩ := Brute.testS_exec hG hW (op := 0)
        by_norm_num oe o70 o70 c₄ e₄.wb_right
        zthfi ztcue
        ztcue
      refine ⟨c₅, k₅ + 1, .ifLtN_true by_omega e₅, by_omega, f₅, b₅, ?_⟩
      rw [t₅, ite_eq_right h0]
      zufpk
  have k₅' : ∀ r, ztcu → r ≠ 212104 → c₅.nreg r = c₄.nreg r :=
    fun r h h' => keep_bt f₅ h h'
  have ex : Exec P W candS c c₅ _ :=
    .seq e₁ ztbq
  have hf :=
    fbTrans (fbTrans (fbTrans (fbTrans (fbMono f₁ ztqel)
      (fbMono f₂ ztqel)) (fbMono f₃ (bt_cs by_norm_num)))
      (fbMono f₄ ztqel)) (fbMono f₅ (bt_cs by_norm_num))
  have v100 : c₅.nreg 212100 = c₁.nreg 212100 := by
    grind
  have v101 : c₅.nreg 212101 = c₂.nreg 212101 := by
    grind
  have v102 : c₅.nreg 212102 = c₃.nreg 212102 := by
    grind
  have v103 : c₅.nreg 212103 = c₄.nreg 212103 := by_grind
  refine ⟨c₅, _, ex, by_omega, hf, ?_, ?_, ?_, ?_, ?_, t₅⟩
  · zucxf
    interval_cases r
    · omega
    · omega
    · omega
    · omega
    omega
  · rw [v100, t₁]; simp [SignTest, Src.pt, SymPt.eval, hq, hi]
  · rw [v101, t₂]
    simp [SignTest, Src.pt, SymPt.eval, k₁' 212070 by_norm_num by_norm_num,
      k₁' 212096 by_norm_num by_norm_num, hi, hq1]
  · rw [v102, t₃]
    simp [SignTest, Src.pt, SymPt.eval, k₂' 212070 by_norm_num by_norm_num,
      k₁' 212070 by_norm_num by_norm_num, k₂' 212096 by_norm_num by_norm_num,
      k₁' 212096 by_norm_num by_norm_num, hi, hq1]
  · rw [v103, t₄]; simp [SignTest, Src.pt, SymPt.eval, r70, r95]

/-- **The candidate bit.** -/
theorem candB_exec (c : Config) (hw : WordsBounded W c) (hW : 2 ≤ W) (c0 : c.nreg 212000 = 1)
    (h0 : c.nreg 212100 ≤ 1) (h1 : c.nreg 212101 ≤ 1) (h2 : c.nreg 212102 ≤ 1)
    (h3 : c.nreg 212103 ≤ 1) (h4 : c.nreg 212104 ≤ 1) :
    ∃ c' k, Exec P W candB c c' k ∧ k = 9 ∧ c'.nreg 212107 ≤ 1 ∧
      (c'.nreg 212107 = 1 ↔ (ztlkp ∨
        ztlkq) ∧ c.nreg 212104 = 1) ∧
      FrameB ztijx c c' := by
  obtain ⟨c', k, ex, hk, v1, v2⟩ : ∃ c' k, Exec P W candB c c' k ∧ k = 9 ∧
      c'.nreg 212107 ≤ 1 ∧ (c'.nreg 212107 = 1 ↔ (ztlkp ∨
        ztlkq) ∧ c.nreg 212104 = 1) := by
    unfold candB
    exec_block
    all_goals try (config_simp; omega)
  exact ⟨c', k, ex, hk, v1, v2, exec_frameB ex wr_candB⟩
theorem wr_setB : wr ztduo setB = true := by_decide

/-- The new best. -/
theorem setB_exec (c : Config) (hw : WordsBounded W c) (hW : 1 ≤ W) :
    ∃ c' k, Exec P W setB c c' k ∧ k = 3 ∧ c'.nreg 212097 = c.nreg 212094 ∧
      c'.nreg 212098 = c.nreg 212095 ∧ c'.nreg 212099 = 1 ∧
      FrameB ztduo c c' := by
  obtain ⟨c', k, ex, hk, v1, v2, v3⟩ : ∃ c' k, Exec P W setB c c' k ∧ k = 3 ∧
      c'.nreg 212097 = c.nreg 212094 ∧ c'.nreg 212098 = c.nreg 212095 ∧ c'.nreg 212099 = 1 := by
    unfold setB
    exec_block
    · omega
    simp
  exact ⟨c', k, ex, hk, v1, v2, v3, exec_frameB ex wr_setB⟩

/-- The registers `updS` writes. -/
def Bup (r : ℕ) : Bool := Bk r || decide (212097 ≤ r ∧ r ≤ 212105)
theorem bup_vis (r : ℕ) (h : Bup r = true) : Bvis r = true := by
  unfold Bup at h; unfold Bvis
  grind
theorem bt_up (hd : 212097 ≤ d ∧ d ≤ 212105) (r : ℕ) (h : Brute.Bt d r = true) :
    Bup r = true := by
  unfold Brute.Bt at h; unfold Bup
  grind
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
          sgnD d * edgeXAt zta q i < sgnD d * edgeXAt zta bq i)) →
        c'.nreg 212097 = c.nreg 212094 ∧ c'.nreg 212098 = q ∧ c'.nreg 212099 = 1) ∧
      (¬ (c.nreg 212107 = 1 ∧ (c.nreg 212099 = 0 ∨
          sgnD d * edgeXAt zta q i < sgnD d * edgeXAt zta bq i)) →
        c'.nreg 212097 = c.nreg 212097 ∧ c'.nreg 212098 = c.nreg 212098 ∧
          c'.nreg 212099 = c.nreg 212099) := by
  have fs : ∀ {c₁ c₂ : Config}, FrameB ztduo c₁ c₂ →
      FrameB Bup c₁ c₂ := fun f => fbMono f fun r h => by
        zvmwo at h; unfold Bup; grind
  by_cases hc : c.nreg 212107 = 1
  · by_cases hh0 : c.nreg 212099 = 0
    · obtain ⟨c', k, e, hk, v1, v2, v3, f⟩ := setB_exec c hw by_omega
      have ex : ztpjw :=
        .ifLtN_true by_omega ztejp
      grind
    · have hh1 : c.nreg 212099 = 1 := by_omega
      have hbn := hbqn hh1
      zqbej
      have ob : Src.Out ztnab := ztgy
      zuibj
      -- the nearness test
      obtain ⟨c₁, k₁, e₁, hk₁, f₁, b₁, t₁⟩ : ∃ c₁ k₁, Exec P W nearS c c₁ k₁ ∧ k₁ ≤ 247 ∧
          FrameB _ c c₁ ∧ c₁.nreg 212105 ≤ 1 ∧
          (c₁.nreg 212105 = 1 ↔ sgnD d * edgeXAt _ q i < sgnD d * edgeXAt _ bq i) := by
        zuckz
        · obtain ⟨c₁, k₁, e₁, hk₁, f₁, b₁, t₁⟩ := Brute.testS_exec hG hW (op := 0)
            by_norm_num oe ob o70 c hw zthfh
            zthfg ztcud
          refine ⟨c₁, k₁ + 2, .ifLtN_false by_omega e₁, by_omega, f₁, b₁, ?_⟩
          rw [t₁, ← nearer_iff (Q := Qof P) hd1
            (b := edgeXAt zta q i < edgeXAt zta bq i) by_simp_all]
          zueni
        · obtain ⟨c₁, k₁, e₁, hk₁, f₁, b₁, t₁⟩ := Brute.testS_exec hG hW (op := 0)
            by_norm_num ob oe o70 c hw zthfg
            zthfh ztcud
          refine ⟨c₁, k₁ + 1, .ifLtN_true by_omega e₁, by_omega, f₁, b₁, ?_⟩
          rw [t₁, ← nearer_iff (Q := Qof P) hd1
            (b := edgeXAt zta bq i < edgeXAt zta q i) by_simp_all]
          zueni
      have k₁' : ∀ r, ztcu → r ≠ 212105 → c₁.nreg r = c.nreg r :=
        fun r h h' => keep_bt f₁ h h'
      have c1' : ztuqe := by_simp_all
      by_cases hn : c₁.nreg 212105 = 1
      · obtain ⟨c', k, e, hk, v1, v2, v3, f⟩ := setB_exec c₁ e₁.wb_right by_omega
        have ex : ztpjw :=
          .ifLtN_true by_omega (.ifLtN_true by_omega
            (.seq e₁ ztdrx))
        refine ⟨c', _, ex, by_omega, fbTrans (fbMono f₁ ztvfv) (fs f),
          fun _ => ⟨?_, ?_, v3⟩, fun h => absurd ⟨hc, Or.inr (t₁.1 hn)⟩ h⟩
        · simp_all
        simp_all
      · have ex : Exec P W updS c c₁ _ :=
          .ifLtN_true by_omega (.ifLtN_true by_omega
            (.seq e₁ (.ifLtN_false by_omega ztekc)))
        refine ⟨c₁, _, ex, by_omega, fbMono f₁ ztvfv, fun h => ?_, fun _ => ?_⟩
        · grind
        grind
  · have ex : Exec P W updS c c _ := .ifLtN_false by_omega ztjd
    exact ⟨c, _, ex, by_omega, FrameB.refl _ _, by_omega, by_omega⟩

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
      (Cand zta i ztbgl ztwxg ∧ (c.nreg 212099 = 0 ∨
          sgnD d * edgeXAt zta ztwxg i <
            sgnD d * edgeXAt zta ztjrw i) →
        c'.nreg 212097 = ztcfh % P.n ∧ c'.nreg 212098 = qE li P.n (ztcfh % P.n) ∧
          c'.nreg 212099 = 1) ∧
      (¬ (Cand zta i ztbgl ztwxg ∧ (c.nreg 212099 = 0 ∨
          sgnD d * edgeXAt zta ztwxg i <
            sgnD d * edgeXAt zta ztjrw i)) →
        c'.nreg 212097 = c.nreg 212097 ∧ c'.nreg 212098 = c.nreg 212098 ∧
          c'.nreg 212099 = c.nreg 212099) := by
  zucgu
  set w := ztcfh % P.n with hwdef
  have hwn : w < P.n := Nat.mod_lt _ by_omega
  set q := qE li P.n w with hqdef
  have hqn := DownMath.qE_lt li hwn
  -- the edge
  obtain ⟨c₁, k₁, e₁, hk₁, v94, v95, v96, f₁⟩ := edgeS_exec (P := P) c hw hn by_omega hst hu hsn
    hun.le hli c0 c1 c2 hW2
  have g₁ : ∀ r, r ≠ 212094 → r ≠ 212095 → r ≠ 212096 → r ≠ 212106 → c₁.nreg r = c.nreg r :=
    fun r a b c d => f₁.1 r by_simp_all
  -- the tests
  obtain ⟨c₂, k₂, e₂, hk₂, f₂, hb₂, t0, t1, t2, t3, t4⟩ := candS_exec (P := P) hG hW c₁ e₁.wb_right
    v95 v96 by_simp_all
    by_simp_all hd1
    by_simp_all hqn
    ztcv hin
  have g₂ : ∀ r, ztcu → (r < 212100 ∨ 212104 < r) → c₂.nreg r = c₁.nreg r :=
    fun r h h' => f₂.1 r (by unfold Bcs Bk; simp; omega)
  -- the candidate bit
  obtain ⟨c₃, k₃, e₃, hk₃, hb₃, t₃, f₃⟩ := candB_exec (P := P) c₂ e₂.wb_right by_omega
    (by rw [g₂ _ by_norm_num by_norm_num, g₁ _ by_decide by_decide by_decide by_decide,
      c0])
    (hb₂ _ le_rfl by_norm_num) ztlpp
    ztlpp ztlpp
    (hb₂ _ by_norm_num le_rfl)
  have g₃ : ∀ r, (r < 212107 ∨ 212112 < r) → c₃.nreg r = c₂.nreg r := fun r h =>
    f₃.1 r by_grind
  have hcand : c₃.nreg 212107 = 1 ↔ Cand zta i ztbgl q := by
    zuout
    zuc
    exact cand_iff_bits by_omega hd1 t0 by_grind
      by_grind t3 t4
  -- registers kept from the start, and the edge registers
  have kc : ∀ r, ztcu → (r < 212094 ∨ 212112 < r ∨ r = 212097 ∨ r = 212098 ∨
      r = 212099) → c₃.nreg r = c.nreg r := by
    intro r h h'
    rw [g₃ r by_omega, g₂ r h by_omega, g₁ r by_omega by_omega by_omega by_omega]
  have k94 : c₃.nreg 212094 = w := by
    rw [g₃ _ by_norm_num, g₂ _ by_norm_num by_norm_num, v94]
  have k95 : zturz := by
    rw [g₃ _ by_norm_num, g₂ _ by_norm_num by_norm_num, v95]
  -- the update
  obtain ⟨c₄, k₄, e₄, hk₄, f₄, u1, u2⟩ := updS_exec (P := P) hG hW c₃ e₃.wb_right (i := i) (d := d)
    (q := q) (bq := c.nreg 212098) (by rw [kc _ by_norm_num by_norm_num, hi])
    (by rw [kc _ by_norm_num by_norm_num, hd]) hd1 k95
    (by zunjs) (by rw [kc _ by_norm_num by_norm_num, c1])
    hb₃ (by zunjs; exact hh) hin hqn
    (by zunjs; omega)
  zudna
  -- the counter
  have u91 : c₄.nreg 212091 = u := by
    rw [g₄ _ by_decide, g₃ _ by_norm_num, g₂ _ by_norm_num by_norm_num,
      g₁ _ by_decide by_decide by_decide by_decide, hu]
  have u00 : c₄.nreg 212000 = 1 := by
    rw [g₄ _ by_decide, kc _ by_norm_num by_norm_num, c0]
  have e₅ := Exec.addN (P := P) e₄.wb_right 212091 212091 212000 by_omega
  have f₅ : FrameB ztlor c₄ _ := exec_frameB e₅ by_decide
  have ex : Exec P W visitS c _ _ :=
    .seq e₁ ztbq
  have ec : ∀ r, r ≠ 212091 →
      upd c₄.nreg 212091 (c₄.nreg 212091 + c₄.nreg 212000) r = c₄.nreg r :=
    fun r h => Machine.upd_other _ _ _ h
  refine ⟨_, _, ex, ?_, ?_, ?_, ?_, ?_⟩
  · unfold visK; omega
  · refine fbTrans (fbTrans (fbTrans (fbTrans (fbMono f₁ ?_) (fbMono f₂ bvis_cs)) (fbMono f₃ ?_))
      (fbMono f₄ bup_vis)) (fbMono f₅ ?_) <;> intro r h <;> zvmwo at h <;>
      exact bvis_of by_omega
  · simp only [Machine.upd_apply, ite_true, u91, u00]
  · zuq
    have h' : c₃.nreg 212107 = 1 ∧ (c₃.nreg 212099 = 0 ∨
        sgnD d * edgeXAt zta q i < sgnD d * edgeXAt zta ztjrw i) := by
      zqbek
    obtain ⟨a1, a2, a3⟩ := u1 h'
    exact ⟨by dsimp only; rw [ec _ by_norm_num, a1, k94], by dsimp only; rw [ec _ by_norm_num, a2],
      by dsimp only; rw [ec _ by_norm_num, a3]⟩
  · zuq
    have h' : ¬ (c₃.nreg 212107 = 1 ∧ (c₃.nreg 212099 = 0 ∨
        sgnD d * edgeXAt zta q i < sgnD d * edgeXAt zta ztjrw i)) := by
      zqbek
    obtain ⟨a1, a2, a3⟩ := u2 h'
    exact ⟨by dsimp only; rw [ec _ by_norm_num, a1, kc _ by_norm_num by_norm_num],
      by dsimp only; rw [ec _ by_norm_num, a2, kc _ by_norm_num by_norm_num],
      by dsimp only; rw [ec _ by_norm_num, a3, kc _ by_norm_num by_norm_num]⟩
end exec
end
end DrvB
end Chazelle.Core
end
section
set_option hygiene false
local macro "zqbme" : tactic => `(tactic| (have r1 : ztuug := by zunzg
                                           have r2 : ztpoo := by rw [hfe.1 _ by_decide, hR]))
local macro "zqbmf" : tactic => `(tactic| (have w₂ := x₂.wb_right
                                           have e1011 : ztuui := by_simp_all
                                           have e1201 : e₂.nreg 43201 = j := by_simp_all
                                           zueia
                                           have X := Exec.seq x₁ ztsxb))
local macro "zqbmg" : tactic => `(tactic| have r4 : ztizs := by zunhv)
local macro "zqbmh" : tactic => `(tactic| obtain ⟨e₂, k₂, x₂, hk₂, g₂, m₂⟩ := inc by_omega)
local macro "zqbmi" : tactic => `(tactic| simp (disch := omega) only [upd_other])
local macro "zqbmj" : tactic => `(tactic| simp only [upd_apply, regMem, Function.update_apply])
local macro "zqbmk" : tactic => `(tactic| exact ⟨d', k, e, by_omega, hw', hf, hm'⟩)
set_option hygiene true

/-!
# WP-C (BuildNF), RAM part 15: counting the arcs and exit chords of the regions

Three arrays of `R` words at `CA` (arc counts), `CA + R` (chord counts), `CA + 2R` (largest arc
weight) — `regMem` — are filled by:

* `zeroLoop`: all zero;
* `arcCntLoop`: for each arc `j < A` (region `key j = AT[5 j]`, weight `WT[j]`), count it and take
  the maximum of the weights (`cntF`, `wmaxF`);
* `chCntLoop`: for each chord `i < K` (regions `u i = CT[5 i + 3]`, `v i = CT[5 i + 4]`), count it
  once in each of its regions (`cnt2F`).

Registers: `r43200 = R`, `r43201` the counter, `r43202 … r43209` scratch, `r44008 = CA`,
`r44002 = AT`, `r44007 = WT`, `r44001 = CT`, `r43102 = A`, `r43002 = K`, `r43010 = 0`,
`r43011 = 1`, `r43013 = 3`.
-/
namespace Chazelle.Core
namespace BuildRam
open Machine Machine.Stmt Programs SignK
@[expose] public section
def lstF (key : ℕ → ℕ) (n r : ℕ) : List ℕ := (List.range n).filter fun j => key j = r

/-- Their number. -/
def cntF (key : ℕ → ℕ) (n r : ℕ) : ℕ := (lstF key n r).length

/-- The largest weight among them. -/
def wmaxF (key w : ℕ → ℕ) (n r : ℕ) : ℕ := ((lstF key n r).map w).foldr max 0

/-- The chords below `n` with a side `r`. -/
def lst2F (u v : ℕ → ℕ) (n r : ℕ) : List ℕ := (List.range n).filter fun i => u i = r ∨ v i = r

/-- Their number. -/
def cnt2F (u v : ℕ → ℕ) (n r : ℕ) : ℕ := (lst2F u v n r).length
theorem lstF_succ (key : ℕ → ℕ) (n r : ℕ) :
    lstF key ztkk r = lstF key n r ++ (if key n = r then [n] else []) := by
  unfold lstF
  zubic
theorem lst2F_succ (u v : ℕ → ℕ) (n r : ℕ) :
    lst2F u v ztkk r = lst2F u v n r ++ (if u n = r ∨ v n = r then [n] else []) := by
  unfold lst2F
  zubic
theorem cntF_succ (key : ℕ → ℕ) (n r : ℕ) :
    cntF key ztkk r = cntF key n r + ztlqc := by
  unfold cntF; zuoza; grind
theorem cnt2F_succ (u v : ℕ → ℕ) (n r : ℕ) :
    cnt2F u v ztkk r = cnt2F u v n r + ztdor := by
  unfold cnt2F; rw [lst2F_succ]; grind
theorem foldr_max_append (l : List ℕ) (x : ℕ) :
    (l ++ [x]).foldr max 0 = max (l.foldr max 0) x := by
  induction l with
  | nil => simp
  | cons y l ih => simp only [List.cons_append, List.foldr_cons, ih]; omega
theorem wmaxF_succ (key w : ℕ → ℕ) (n r : ℕ) :
    wmaxF key w ztkk r = if key n = r then max (wmaxF key w n r) (w n) else wmaxF key w n r := by
  unfold wmaxF; zuoza
  split_ifs
  · rw [List.map_append, List.map_singleton, foldr_max_append]
  · simp

/-! ## The three arrays -/

/-- The memory with the three arrays at `CA`. -/
def regMem (m₀ : ℕ → ℕ) (CA R : ℕ) (fA fC fW : ℕ → ℕ) (a : ℕ) : ℕ :=
  if CA ≤ a ∧ a < CA + R then fA (a - CA)
  else if CA + R ≤ a ∧ a < CA + 2 * R then fC (a - (CA + R))
  else if CA + 2 * R ≤ a ∧ a < CA + 3 * R then fW (a - (CA + 2 * R)) else m₀ a
theorem regMem_A (m₀ : ℕ → ℕ) (CA R : ℕ) (fA fC fW : ℕ → ℕ) {r v : ℕ} (hr : r < R) :
    upd zthkf ztnkc v = regMem m₀ CA R (Function.update fA r v) fC fW := by
  funext a
  zqbmj
  grind
theorem regMem_C (m₀ : ℕ → ℕ) (CA R : ℕ) (fA fC fW : ℕ → ℕ) {r v : ℕ} (hr : r < R) :
    upd zthkf ztjhp v =
      regMem m₀ CA R fA (Function.update fC r v) fW := by
  funext a
  zqbmj
  grind
theorem regMem_W (m₀ : ℕ → ℕ) (CA R : ℕ) (fA fC fW : ℕ → ℕ) {r v : ℕ} (hr : r < R) :
    upd zthkf zthad v =
      regMem m₀ CA R fA fC (Function.update fW r v) := by
  funext a
  zqbmj
  grind
theorem regMem_rdA (m₀ : ℕ → ℕ) (CA R : ℕ) (fA fC fW : ℕ → ℕ) {r : ℕ} (hr : r < R) :
    regMem m₀ CA R fA fC fW ztnkc = fA r := by
  unfold regMem
  simp_all
theorem regMem_rdC (m₀ : ℕ → ℕ) (CA R : ℕ) (fA fC fW : ℕ → ℕ) {r : ℕ} (hr : r < R) :
    regMem m₀ CA R fA fC fW ztjhp = fC r := by
  zujqu
theorem regMem_rdW (m₀ : ℕ → ℕ) (CA R : ℕ) (fA fC fW : ℕ → ℕ) {r : ℕ} (hr : r < R) :
    regMem m₀ CA R fA fC fW zthad = fW r := by
  zujqu
theorem regMem_out (m₀ : ℕ → ℕ) (CA R : ℕ) (fA fC fW : ℕ → ℕ) {a : ℕ}
    (ha : a < CA ∨ CA + 3 * R ≤ a) : regMem m₀ CA R fA fC fW a = m₀ a := by
  zujqu
theorem regMem_congr (m₀ : ℕ → ℕ) (CA R : ℕ) {fA fC fW gA gC gW : ℕ → ℕ}
    (hA : ∀ r, r < R → fA r = gA r) (hC : ∀ r, r < R → fC r = gC r)
    (hW : ∀ r, r < R → fW r = gW r) : regMem m₀ CA R fA fC fW = regMem m₀ CA R gA gC gW := by
  funext a
  zujqu
theorem regMem_self (m₀ : ℕ → ℕ) (CA R : ℕ) :
    regMem m₀ CA R (fun r => m₀ ztnkc) (fun r => m₀ ztjhp) (fun r => m₀ zthad)
      = m₀ := by
  funext a
  unfold regMem
  simp_all

/-! ## The programs -/

/-- Zero the three arrays. -/
def zeroLoop : Stmt :=
  .whileLtN 43201 43200 (block [.addN 43202 44008 43201, .storeN 43202 43010,
    .addN 43202 43202 43200, .storeN 43202 43010, .addN 43202 43202 43200, .storeN 43202 43010,
    .addN 43201 43201 43011])

/-- Count the arcs by region and take the largest weight. -/
def arcCntLoop : Stmt :=
  .whileLtN 43201 43102
    (.seq (block [.addN 43202 43201 43201, .addN 43202 43202 43202, .addN 43202 43202 43201,
        .addN 43202 43202 44002, .loadN 43203 43202,
        .addN 43204 44008 43203, .loadN 43205 43204, .addN 43205 43205 43011,
        .storeN 43204 43205,
        .addN 43206 44007 43201, .loadN 43207 43206,
        .addN 43208 44008 43200, .addN 43208 43208 43200, .addN 43208 43208 43203,
        .loadN 43209 43208])
      (.seq ztips
        ztgwu))

/-- One increment of a chord count. -/
def incV : Stmt :=
  block [.addN 43207 44008 43200, .addN 43207 43207 43204, .loadN 43208 43207,
    .addN 43208 43208 43011, .storeN 43207 43208]

/-- Count the chords by side region. -/
def chCntLoop : Stmt :=
  .whileLtN 43201 43002
    (.seq (block [.addN 43202 43201 43201, .addN 43202 43202 43202, .addN 43202 43202 43201,
        .addN 43202 43202 44001, .addN 43202 43202 43013, .loadN 43203 43202,
        .addN 43202 43202 43011, .loadN 43204 43202,
        .addN 43205 44008 43200, .addN 43205 43205 43203, .loadN 43206 43205,
        .addN 43206 43206 43011, .storeN 43205 43206])
      (.seq ztjda
        ztgwu))
theorem wr_zeroLoop : wrM ztrb zeroLoop = true := by_decide
theorem wr_arcCntLoop : wrM ztrb arcCntLoop = true := by
  decide
theorem wr_chCntLoop : wrM ztrb chCntLoop = true := by
  decide

/-- `f` with its first `i` values zeroed. -/
def zU (i : ℕ) (f : ℕ → ℕ) (r : ℕ) : ℕ := if r < i then 0 else f r
theorem zU_succ (i : ℕ) (f : ℕ → ℕ) : Function.update (zU i f) i 0 = zU ztg f := by
  funext r
  simp only [Function.update_apply, zU]
  grind
section exec
variable {P : Polygon} {W : ℕ}

/-- **Zeroing the arrays.** -/
theorem zeroLoop_exec (d : Config) (hw : WordsBounded W d) {m₀ : ℕ → ℕ} {CA R : ℕ}
    {fA fC fW : ℕ → ℕ} (hCA : d.nreg 44008 = CA) (hR : d.nreg 43200 = R) (h0 : d.nreg 43010 = 0)
    (h1 : d.nreg 43011 = 1) (hi : d.nreg 43201 = 0) (hRW : CA + 3 * R ≤ W)
    (hm : d.nmem = regMem m₀ CA R fA fC fW) :
    ∃ d' k, Exec P W zeroLoop d d' k ∧ k ≤ 9 * R + 2 ∧ WordsBounded W d' ∧
      FrameM ztrb d d' ∧
      d'.nmem = regMem m₀ CA R ztczh ztczh ztczh := by
  obtain ⟨d', k, e, ⟨hw', i, hi', hiR, hf, hm'⟩, htest, hk⟩ := Exec.whileLtN_potential (P := P)
    (W := W) (a := 43201) (b := 43200) (body := block [.addN 43202 44008 43201, .storeN 43202 43010,
      .addN 43202 43202 43200, .storeN 43202 43010, .addN 43202 43202 43200, .storeN 43202 43010,
      .addN 43201 43201 43011])
    (fun e => WordsBounded W e ∧ ∃ i, e.nreg 43201 = i ∧ i ≤ R ∧
      FrameM ztrb d e ∧
      e.nmem = regMem m₀ CA R (zU i fA) (zU i fC) (zU i fW))
    (fun e => 9 * ztrkd) ztchu
    (fun e ⟨hwe, i, hie, hiR, hfe, hme⟩ htest => by
      zqbme
      have r3 : e.nreg 43010 = 0 := by rw [hfe.1 _ by_decide, h0]
      zqbmg
      rw [hie, r2] at htest
      have X : ∃ e' k, Exec P W (block [.addN 43202 44008 43201, .storeN 43202 43010,
          .addN 43202 43202 43200, .storeN 43202 43010, .addN 43202 43202 43200,
          .storeN 43202 43010, .addN 43201 43201 43011]) e e' k ∧ k = 7 ∧
          e'.nreg 43201 = i + 1 ∧
          e'.nmem = upd (upd (upd e.nmem (CA + i) 0) (CA + R + i) 0) (CA + 2 * R + i) 0 := by
        exec_block
        all_goals first
          | (config_simp; simp (config := { failIfUnchanged := false }) only [r1, r2, r3, r4, hie];
             omega)
          | skip
        refine ztkw <;> config_simp
        · omega
        grind
      obtain ⟨e', k, x, hk, hi', hm'⟩ := X
      refine ⟨e', k, x, ⟨x.wb_right, i + 1, hi', by_omega,
        hfe.trans ztjux, ?_⟩, ?_⟩
      · rw [hm', hme, regMem_A _ _ _ _ _ _ by_omega, regMem_C _ _ _ _ _ _ by_omega,
          regMem_W _ _ _ _ _ _ by_omega, zU_succ, zU_succ, zU_succ]
      omega)
    ⟨hw, 0, hi, Nat.zero_le _, FrameM.refl _ _, by
      tauto⟩
  have hiR' : i = R := by
    rw [hi', hf.1 _ by_decide, hR] at htest; omega
  subst hiR'
  refine ⟨d', k, e, by_omega, hw', hf, ?_⟩
  zumnn
  exact regMem_congr _ _ _ ztess ztess
    ztess
end exec
theorem cntF_update (key : ℕ → ℕ) (j : ℕ) :
    Function.update (cntF key j) zteai (cntF key j zteai + 1) = cntF key ztl := by
  funext r
  zuire
  · subst h; rw [Function.update_self, cntF_succ, ite_eq_left rfl]
  · rw [Function.update_of_ne h, cntF_succ, ite_eq_right zthrm, Nat.add_zero]
theorem wmaxF_update (key w : ℕ → ℕ) (j : ℕ) (hlt : wmaxF key w j zteai < w j) :
    Function.update (wmaxF key w j) zteai (w j) = wmaxF key w ztl := by
  funext r
  zuire
  · subst h; rw [Function.update_self, wmaxF_succ, ite_eq_left rfl]; omega
  · rw [Function.update_of_ne h, wmaxF_succ, ite_eq_right zthrm]
theorem wmaxF_same (key w : ℕ → ℕ) (j : ℕ) (hge : ¬ wmaxF key w j zteai < w j) :
    wmaxF key w j = wmaxF key w ztl := by
  funext r
  rw [wmaxF_succ]
  grind
section exec
variable {P : Polygon} {W : ℕ}

/-- **Counting the arcs by region**, with the largest weight. -/
theorem arcCntLoop_exec (d : Config) (hw : WordsBounded W d) {m₀ : ℕ → ℕ} {CA R A AT WT : ℕ}
    {fC : ℕ → ℕ} (hCA : d.nreg 44008 = CA) (hR : d.nreg 43200 = R) (h1 : d.nreg 43011 = 1)
    (hi : d.nreg 43201 = 0) (hA : d.nreg 43102 = A) (hAT : d.nreg 44002 = AT)
    (hWT : d.nreg 44007 = WT) (hRW : CA + 3 * R ≤ W) (hATC : AT + 5 * A ≤ CA) (hWTC : WT + A ≤ CA)
    (hkey : ∀ j, j < A → m₀ ztdkr < R)
    (hm : d.nmem = regMem m₀ CA R ztczh fC ztczh) :
    ∃ d' k, Exec P W arcCntLoop d d' k ∧ k ≤ 21 * A + 2 ∧ WordsBounded W d' ∧
      FrameM ztrb d d' ∧
      d'.nmem = regMem m₀ CA R (cntF ztzff A) fC
        (wmaxF ztzff (fun j => m₀ ztjnq) A) := by
  obtain ⟨key, hkeydef⟩ : ∃ f : ℕ → ℕ, f = fun j => m₀ (AT + 5 * j) := by_simp_all
  obtain ⟨wt, hwdef⟩ : ∃ f : ℕ → ℕ, f = fun j => m₀ (WT + j) := by_simp_all
  rw [← hkeydef, ← hwdef]
  have hkey' : ∀ j, j < A → key j < R := by_simp_all
  obtain ⟨d', k, e, ⟨hw', i, hi', hiA, hf, hm'⟩, htest, hk⟩ := Exec.whileLtN_potential (P := P)
    (W := W) (a := 43201) (b := 43102) (body := _)
    (fun e => WordsBounded W e ∧ ∃ i, e.nreg 43201 = i ∧ i ≤ A ∧
      FrameM ztrb d e ∧
      e.nmem = regMem m₀ CA R (cntF key i) fC (wmaxF key wt i))
    (fun e => 21 * ztldu) ztchu
    (fun e ⟨hwe, j, hje, hjA, hfe, hme⟩ htest => by
      zqbme
      zqbmg
      zuehx
      have r6 : e.nreg 44007 = WT := by rw [hfe.1 _ by_decide, hWT]
      have r7 : ztpon := by zunhw
      zuijx
      have hkj := hkey' j htest
      have mk : e.nmem ztdkr = key j := by
        rw [hme, regMem_out _ _ _ _ _ _ by_omega, hkeydef]
      have mw : e.nmem ztjnq = wt j := by
        rw [hme, regMem_out _ _ _ _ _ _ by_omega, hwdef]
      have mc : e.nmem (CA + key j) = cntF key j zteai := by
        rw [hme, regMem_rdA _ _ _ _ _ _ hkj]
      have hcW : cntF key j zteai + 1 ≤ W := by
        have : cntF key j zteai ≤ j := by
          unfold cntF lstF; grind
        omega
      obtain ⟨e₁, k₁, x₁, hk₁, v7, v8, v9, v1, m₁, g₁⟩ : ∃ e₁ k₁, Exec P W
          (block [.addN 43202 43201 43201, .addN 43202 43202 43202, .addN 43202 43202 43201,
            .addN 43202 43202 44002, .loadN 43203 43202,
            .addN 43204 44008 43203, .loadN 43205 43204, .addN 43205 43205 43011,
            .storeN 43204 43205,
            .addN 43206 44007 43201, .loadN 43207 43206,
            .addN 43208 44008 43200, .addN 43208 43208 43200, .addN 43208 43208 43203,
            .loadN 43209 43208]) e e₁ k₁ ∧ k₁ = 15 ∧
          e₁.nreg 43207 = wt j ∧ e₁.nreg 43208 = CA + 2 * R + key j ∧
          e₁.nreg 43209 = wmaxF key wt j zteai ∧ e₁.nreg 43201 = j ∧
          e₁.nmem = regMem m₀ CA R ztzvh fC (wmaxF key wt j) ∧
          ztfyt := by
        exec_block
        all_goals first
          | (config_simp; simp (config := { failIfUnchanged := false }) only [r1, r2, r4, r5,
              r6, hje, show j + j + ztcvv + j + AT = AT + 5 * j by omega, mk, mc]; omega)
          | skip
        refine ztbth <;> config_simp
        · rw [r1, r5, r6, r4, hje, show j + j + ztcvv + j + AT = AT + 5 * j by omega, mk,
            upd_other _ _ _ by_omega, mw]
        · grind
        · rw [r1, r2, hje, r5, r4, show j + j + ztcvv + j + AT = AT + 5 * j by omega, mk, mc,
            hme, regMem_A _ _ _ _ _ _ hkj, show CA + R + R + key j = CA + 2 * R + key j by omega,
            regMem_rdW _ _ _ _ _ _ hkj]
        · zumnk
        · rw [r1, r5, r4, hje, show j + j + ztcvv + j + AT = AT + 5 * j by omega, mk, mc,
            hme, regMem_A _ _ _ _ _ _ hkj, cntF_update]
        · zqbmi
      zubcr
      -- the maximum
      obtain ⟨e₂, k₂, x₂, hk₂, v1', m₂⟩ : ∃ e₂ k₂, Exec P W
          ztips e₁ e₂ k₂ ∧ k₂ ≤ 2 ∧
          e₂.nreg = e₁.nreg ∧
          e₂.nmem = regMem m₀ CA R ztzvh fC (wmaxF key wt ztl) := by
        by_cases hlt : wmaxF key wt j zteai < wt j
        · refine spec_ifLtN_true by_omega
            (spec_instr (Exec.storeN w₁ _ _) fun _ => ztras)
          zubi
          rw [v8, v7, m₁, regMem_W _ _ _ _ _ _ hkj, wmaxF_update _ _ _ hlt]
        · refine spec_ifLtN_false by_omega (spec_skip w₁ ztras)
          rw [m₁, wmaxF_same _ _ _ hlt]
      zqbmf
      refine ⟨_, _, X, ⟨X.wb_right, j + 1, by_simp_all, by_omega,
        hfe.trans ztnyc, by_omega⟩, ?_⟩
      zudls
      omega)
    ⟨hw, 0, hi, Nat.zero_le _, FrameM.refl _ _, by
      tauto⟩
  have hiA' : i = A := by
    rw [hi', hf.1 _ by_decide, hA] at htest; omega
  subst hiA'
  zqbmk
end exec
theorem cnt2_update_eq (u v : ℕ → ℕ) (i : ℕ) (h : u i = v i) :
    Function.update ztdnc ztbic ztwtt = cnt2F u v ztg := by
  funext r
  zuirt
  · subst hr; zunwa
  · rw [Function.update_of_ne hr, cnt2F_succ, ite_eq_right by_omega, Nat.add_zero]
theorem cnt2_update_ne (u v : ℕ → ℕ) (i : ℕ) (_h : u i ≠ v i) :
    Function.update (Function.update ztdnc ztbic ztwtt) ztewd
      (cnt2F u v i ztewd + 1) = cnt2F u v ztg := by
  funext r
  zuiru
  · subst hr; rw [Function.update_self, cnt2F_succ, ite_eq_left ztbt]
  · zufmm

    · subst hr'; zunwa
    · rw [Function.update_of_ne hr', cnt2F_succ, ite_eq_right by_omega, Nat.add_zero]
section exec
variable {P : Polygon} {W : ℕ}
theorem incV_exec (e : Config) (hw : WordsBounded W e) {CA R v : ℕ} (hCA : e.nreg 44008 = CA)
    (hR : e.nreg 43200 = R) (hv : e.nreg 43204 = v) (h1 : e.nreg 43011 = 1)
    (hW : CA + R + v ≤ W) (hc : e.nmem ztjhq + 1 ≤ W) :
    ∃ e' k, Exec P W incV e e' k ∧ k = 5 ∧
      e'.nmem = upd e.nmem ztjhq (e.nmem ztjhq + 1) ∧
      (∀ r, (r < 43207 ∨ 43208 < r) → e'.nreg r = e.nreg r) := by
  unfold incV
  exec_block
  · omega
  · simp_all
  · simp_all
  · refine ztui <;> config_simp
    · simp_all
    · zqbmi

/-- **Counting the chords by side region.** -/
theorem chCntLoop_exec (d : Config) (hw : WordsBounded W d) {m₀ : ℕ → ℕ} {CA R K CT : ℕ}
    {fA fW : ℕ → ℕ} (hCA : d.nreg 44008 = CA) (hR : d.nreg 43200 = R) (h1 : d.nreg 43011 = 1)
    (h3 : d.nreg 43013 = 3) (hi : d.nreg 43201 = 0) (hK : d.nreg 43002 = K)
    (hCT : d.nreg 44001 = CT) (hRW : CA + 3 * R ≤ W) (hCTC : CT + 5 * K ≤ CA)
    (hu : ∀ i, i < K → m₀ ztbjh < R) (hv : ∀ i, i < K → m₀ ztbji < R)
    (hm : d.nmem = regMem m₀ CA R fA ztczh fW) :
    ∃ d' k, Exec P W chCntLoop d d' k ∧ k ≤ 26 * K + 2 ∧ WordsBounded W d' ∧
      FrameM ztrb d d' ∧
      d'.nmem = regMem m₀ CA R fA
        (cnt2F (fun i => m₀ ztbjh) (fun i => m₀ ztbji) K) fW := by
  obtain ⟨u, hudef⟩ : ∃ f : ℕ → ℕ, f = fun i => m₀ (CT + 5 * i + 3) := by_simp_all
  obtain ⟨v, hvdef⟩ : ∃ f : ℕ → ℕ, f = fun i => m₀ (CT + 5 * i + 4) := by_simp_all
  rw [← hudef, ← hvdef]
  have hu' : ztlbu := by_simp_all
  have hv' : ztlbv := by_simp_all
  obtain ⟨d', k, e, ⟨hw', i, hi', hiK, hf, hm'⟩, htest, hk⟩ := Exec.whileLtN_potential (P := P)
    (W := W) (a := 43201) (b := 43002) (body := _)
    (fun e => WordsBounded W e ∧ ∃ i, e.nreg 43201 = i ∧ i ≤ K ∧
      FrameM ztrb d e ∧
      e.nmem = regMem m₀ CA R fA ztdnc fW)
    (fun e => 26 * ztrju) ztchu
    (fun e ⟨hwe, j, hje, hjK, hfe, hme⟩ htest => by
      zqbme
      zqbmg
      zuboi

      have r7 : ztuub := by zunzh
      zuijx
      have huj := hu' j htest
      have hvj := hv' j htest
      have mu : e.nmem (CT + 5 * j + 3) = u j := by
        rw [hme, regMem_out _ _ _ _ _ _ by_omega, hudef]
      have mv : e.nmem (CT + 5 * j + 4) = v j := by
        rw [hme, regMem_out _ _ _ _ _ _ by_omega, hvdef]
      have mc : e.nmem (CA + R + u j) = cnt2F u v j ztmpa := by
        rw [hme, regMem_rdC _ _ _ _ _ _ huj]
      have hcle : ∀ r, cnt2F u v j r ≤ j := fun r => by
        unfold cnt2F lst2F; grind
      have hcW : cnt2F u v j ztmpa + 1 ≤ W := by_grind
      obtain ⟨e₁, k₁, x₁, hk₁, v3, v4, v1, m₁, g₁⟩ : ∃ e₁ k₁, Exec P W
          (block [.addN 43202 43201 43201, .addN 43202 43202 43202, .addN 43202 43202 43201,
            .addN 43202 43202 44001, .addN 43202 43202 43013, .loadN 43203 43202,
            .addN 43202 43202 43011, .loadN 43204 43202,
            .addN 43205 44008 43200, .addN 43205 43205 43203, .loadN 43206 43205,
            .addN 43206 43206 43011, .storeN 43205 43206]) e e₁ k₁ ∧ k₁ = 13 ∧
          e₁.nreg 43203 = u j ∧ e₁.nreg 43204 = v j ∧ e₁.nreg 43201 = j ∧
          e₁.nmem = regMem m₀ CA R fA
            (Function.update (cnt2F u v j) ztmpa (cnt2F u v j ztmpa + 1)) fW ∧
          ztfyt := by
        exec_block
        all_goals first
          | (config_simp; simp (config := { failIfUnchanged := false }) only [r1, r2, r3, r4, r5,
              hje, show j + j + ztcvv + j + CT + 3 = CT + 5 * j + 3 by omega,
              show CT + 5 * j + 3 + 1 = CT + 5 * j + 4 by omega, mu, mv, mc]; omega)
          | skip
        refine zthno <;> config_simp
        · grind
        · grind
        · zumnk
        · rw [r1, r2, r3, r4, r5, hje, show j + j + ztcvv + j + CT + 3 = CT + 5 * j + 3 by omega,
            mu, mc, hme, regMem_C _ _ _ _ _ _ huj]
        · zqbmi
      zubcr
      -- the other side
      obtain ⟨e₂, k₂, x₂, hk₂, g₂, m₂⟩ : ∃ e₂ k₂, Exec P W
          ztjda e₁ e₂ k₂ ∧ k₂ ≤ 9 ∧
          ztfyu ∧
          e₂.nmem = regMem m₀ CA R fA (cnt2F u v ztl) fW := by
        have inc : u j ≠ v j → ∃ e₂ k₂, Exec P W incV e₁ e₂ k₂ ∧ k₂ = 5 ∧
            ztfyu ∧
            e₂.nmem = regMem m₀ CA R fA _ fW := fun hne => by
          have hrd : e₁.nmem (CA + R + v j) = cnt2F u v j (v j) := by
            rw [m₁, regMem_rdC _ _ _ _ _ _ hvj, Function.update_of_ne ztnr]
          obtain ⟨e₂, k₂, x₂, hk₂, m₂, g₂⟩ := incV_exec (P := P) e₁ w₁ (CA := CA) (R := R)
            (v := v j) by_simp_all by_simp_all v4
            by_simp_all by_omega by_grind
          refine ztkkx
          rw [m₂, hrd, m₁, regMem_C _ _ _ _ _ _ hvj, cnt2_update_ne u v j hne]
        by_cases a1 : u j < v j
        · zqbmh
          exact ⟨e₂, _, .ifLtN_true by_omega x₂, by_omega, g₂, m₂⟩
        by_cases a2 : v j < u j
        · zqbmh
          exact ⟨e₂, _, .ifLtN_false by_omega
            ztspf, by_omega, g₂, m₂⟩
        · refine ⟨e₁, _, .ifLtN_false by_omega
            ztzrm, by_omega, by_omega, ?_⟩
          rw [m₁, cnt2_update_eq u v j by_omega]
      zqbmf
      refine ⟨_, _, X, ⟨X.wb_right, j + 1, by_simp_all, by_omega,
        hfe.trans ztnyc, by_omega⟩, ?_⟩
      zudls
      omega)
    ⟨hw, 0, hi, Nat.zero_le _, FrameM.refl _ _, by
      tauto⟩
  have hiK' : i = K := by
    zuelx
  subst hiK'
  zqbmk
end exec
end
end BuildRam
end Chazelle.Core
end
section
set_option hygiene false
local macro "zqbgf" : tactic => `(tactic| (config_simp; ((try simp only [Machine.upd_apply]); (repeat' split_ifs) <;> omega)))
local macro "zqbgg" : tactic => `(tactic| (rw [hv.m]; have := C.m_lt; zvmxw at this; omega))
set_option hygiene true

/-!
# Lemma 3.6 (WP-H), RAM part 12: the stopping point and its walk positions

`tchS` chooses the stopping point of the ray: the first hit on the nodes of `D*` (chain edge in
`120052`), or the near end of the chord at the ray's height (walk edge in `120141`), whichever
comes first, or the side of the box.  The result is a **mode** (`120150`): `0` a point of the chain
edge in `120151` (at the ray's height), `1` a walk position on the walk edge in `120152`.

`posS` computes four walk edges `120160 … 120163` (height code `hz + 1`) covering all the walk
positions of the stopping point: the two tour edges of the chain edge (one step further when the
point is the end of the tour edge), and the two positions of the top vertex when the point is the
top vertex.
-/
namespace Chazelle.Core
namespace OracleR
open Machine Machine.Stmt Programs SignK SearchR WalkKey
open OracleQ
@[expose] public section
def tciS : Stmt :=
  .seq ztiqz
    (.seq (modSub 120182 120019)
      (.ifLtN 120182 120016 (.instr (.copyN 120181 120182))
        ztiqy))
theorem tciS_exec {P : Polygon} {W : ℕ} (hW : 4 * P.n + 8 ≤ W) {C : Chain} {V : QV}
    (hv : QVOK P C V) (c : Config) (hw : WordsBounded W c) (hq : QConst P V c)
    (h6 : 6 ≤ c.nreg 120180) (hE : c.nreg 120180 < 2 * V.m + 6) :
    ∃ c' k, Exec P W tciS c c' k ∧ k ≤ 9 ∧ c'.nreg 120181 = tci C (c.nreg 120180 - 6) ∧
      (∀ r, r ≠ 120181 → r ≠ 120182 → c'.nreg r = c.nreg r) := by
  have hmn : ztgaj := by
    have := C.m_lt; zvmxw at this; omega
  zubb
  zubqz
  obtain ⟨w, hwdef⟩ : ∃ w, c.nreg 120180 = w := by_simp_all
  zuiks
  obtain ⟨c₁, k₁, e₁, hk₁, v₁, r₁⟩ : ∃ c₁ k₁, Exec P W
      ztiqz c c₁ k₁ ∧ k₁ = 2 ∧
      c₁.nreg 120182 = w - 6 + V.sS ∧ (∀ r, r ≠ 120182 → c₁.nreg r = c.nreg r) := by
    exec_block
    · config_simp; rw [hq.six, hq.sS, hwdef]; rw [hv.m] at hE; omega
    · zuhjd
      · config_simp; rw [hq.six, hq.sS, hwdef]
      simp_all
  obtain ⟨c₂, k₂, e₂, hk₂, v₂, r₂, -⟩ := modSub_exec (P := P) (r := 120182) (nr := 120019)
    by_decide c₁ e₁.wb_right ztezr
  zubsp
  have htj : c₂.nreg 120182 = tj C ztvu := by
    zubmg
  have R₂ : ∀ r, r ≠ 120182 → c₂.nreg r = c.nreg r := by_simp_all
  zufwp
  zupn

  · refine ⟨_, _, .seq e₁ (.seq e₂ (.ifLtN_true by_omega
      ztlei)), by_omega, ?_, fun r h1 h2 => ?_⟩
    · config_simp; rw [htj]; unfold tci; simp_all
    simp_all
  · zue
    obtain ⟨c₃, k₃, e₃, hk₃, v₃, r₃⟩ : ∃ c₃ k₃, Exec P W
        ztiqy c₂ c₃ k₃ ∧ k₃ = 2 ∧
        c₃.nreg 120181 = 2 * C.m - 1 - tj C _ ∧
        (∀ r, r ≠ 120181 → c₃.nreg r = c₂.nreg r) := by
      exec_block
      zuhjd
      · config_simp
        rw [R₂ _ by_decide, R₂ _ by_decide, hq.twoM, hq.one, htj, hv.m]
      simp_all
    refine ⟨c₃, _, .seq e₁ ztejy, by_omega,
      ?_, by_simp_all⟩
    zudkr

/-! ## The choice of the stopping point -/

/-- Use the hit on `D*`. -/
def useD : Stmt := block [.constN 120150 0, .copyN 120151 120052]

/-- Use the near end of the chord. -/
def useCh : Stmt :=
  .ifLtN 120141 120028 ztouz
    (.ifLtN 120141 120029
      (.seq (.instr (.copyN 120180 120141)) zthqj)
      (ifEq 120141 120029
        (.seq (.instr (.subN 120180 120029 120011)) (.seq tciS (block [.constN 120150 0,
          .copyN 120151 120181])))
        ztouz))

/-- **The choice of the stopping point.** -/
def tchS : Stmt :=
  .seq (.instr (.constN 120150 1))
    (.seq (.ifLtN 120024 120011 ztotj ztotk)
      (.ifLtN 120012 120140
        (.ifLtN 120012 120050
          (.seq (block [.copyN 120120 120141, .copyN 120121 120023])
            (.seq (.ifLtN 120024 120011 gtDS ltDS) (.ifLtN 120012 120128 useCh useD)))
          useCh)
        (.ifLtN 120012 120050 useD .skip)))

/-- The registers written by `tchS`. -/
def BT (r : ℕ) : Bool :=
  BX2 r || decide ztgxo || decide (120150 ≤ r ∧ r ≤ 120152) ||
    decide (120180 ≤ r ∧ r ≤ 120182)
theorem wr_tchS : wr BT tchS = true := by_decide
section Sel
variable (C : Chain) (V : QV)
open Classical in
/-- The stopping point at the near end `w` of the chord: a point of a chain edge (mode `0`) or
the walk position itself (mode `1`). -/
noncomputable def chordSel (w : ℕ) : ℕ × ℕ :=
  if 6 ≤ w ∧ w < 2 * V.m + 6 then (0, tci C ztvu)
  else if w = 2 * V.m + 6 then (0, tci C (2 * V.m - 1)) else (1, w)

/-- The stopping point on the side of the box. -/
def boxSel : ℕ × ℕ := ztkpu
open Classical in
/-- **The stopping point**: the near end of the chord if it exists and comes before the hit on
`D*` (`cb`), else the hit on `D*`, else the side of the box. -/
noncomputable def selOf (bestD : Option ℕ) (found : Prop) (w : ℕ) (cb : Prop) : ℕ × ℕ :=
  if found ∧ (bestD = none ∨ cb) then chordSel C V w
  else match bestD with
    | some cD => ztsqo
    | none => boxSel V
end Sel

/-- The selected stopping point held in the registers. -/
def SelIn (c : Config) (sel : ℕ × ℕ) : Prop :=
  c.nreg 120150 = sel.1 ∧ (sel.1 = 0 → c.nreg 120151 = sel.2) ∧ (sel.1 = 1 → c.nreg 120152 = sel.2)
variable {P : Polygon} {W : ℕ}
theorem useD_exec (c : Config) (hw : WordsBounded W c) (hW : 1 ≤ W) :
    ∃ c' k, Exec P W useD c c' k ∧ k = 2 ∧ SelIn c' (0, c.nreg 120052) ∧
      (∀ r, r ≠ 120150 → r ≠ 120151 → c'.nreg r = c.nreg r) := by
  unfold useD
  exec_block
  · omega
  · exact ⟨rfl, ⟨by config_simp, by_simp_all, by_omega⟩,
      by simp_all⟩
theorem useCh_exec (hW : 4 * P.n + 8 ≤ W) {C : Chain} {V : QV}
    (hv : QVOK P C V) (c : Config) (hw : WordsBounded W c) (hq : QConst P V c)
    (h150 : c.nreg 120150 = 1) :
    ∃ c' k, Exec P W useCh c c' k ∧ k ≤ 20 ∧ SelIn c' (chordSel C V ztdcq) ∧
      (∀ r, (r < 120150 ∨ 120152 < r) → r < 120180 ∨ 120182 < r → c'.nreg r = c.nreg r) := by
  zubb
  obtain ⟨w, hwdef⟩ : ∃ w, c.nreg 120141 = w := by_simp_all
  zumoi
  unfold useCh
  zufqv
  · refine ⟨_, _, .ifLtN_true ztdck ztbim, by_omega,
      ⟨?_, ?_, ?_⟩, fun r h1 h2 => ?_⟩
    · config_simp; zupae; unfold chordSel; grind
    · zuhgl
    · intro _; config_simp; rw [hwdef]; unfold chordSel
      grind
    · config_simp; upd_solve
  have mid : ∀ (w' : ℕ), 6 ≤ w' → w' < 2 * V.m + 6 → ∀ (d : Config), WordsBounded W d →
      QConst P V d → d.nreg 120180 = w' →
      ∃ d' k, Exec P W zthqj d d' k ∧
        k ≤ 11 ∧ d'.nreg 120150 = 0 ∧ d'.nreg 120151 = tci C (w' - 6) ∧
        (∀ r, r ≠ 120150 → r ≠ 120151 → r ≠ 120181 → r ≠ 120182 → d'.nreg r = d.nreg r) := by
    intro w' h1 h2 d hd hqd h180
    obtain ⟨d₁, k₁, e₁, hk₁, v₁, r₁⟩ := tciS_exec (P := P) hW hv d hd hqd by_omega
      by_omega
    rw [h180] at v₁
    zud
    obtain ⟨d₂, k₂, e₂, hk₂, v₂⟩ : ∃ d₂ k₂, Exec P W (block [.constN 120150 0, .copyN 120151 120181])
        d₁ d₂ k₂ ∧ k₂ = 2 ∧ (d₂.nreg 120150 = 0 ∧ d₂.nreg 120151 = d₁.nreg 120181 ∧
          ∀ r, r ≠ 120150 → r ≠ 120151 → d₂.nreg r = d₁.nreg r) := by
      exec_block
      · omega
      simp_all
    obtain ⟨a1, a2, a3⟩ := v₂
    exact ⟨d₂, _, .seq e₁ e₂, by_omega, a1, by_omega, by_simp_all⟩
  zugjh
  · obtain ⟨c₁, e₁, v₁, r₁⟩ := copy_exec hw 120180 120141
    rw [hwdef] at v₁
    obtain ⟨d', k, ex, hk, a1, a2, a3⟩ := mid w by_omega hE c₁ e₁.wb_right
      ztvwe v₁
    refine ⟨d', _, .ifLtN_false ztdck
      (.ifLtN_true ztktx ztncm), by_omega, ztcg,
      fun r h1 h2 => ?_⟩
    · zuhkn
    · intro _; zungr; unfold chordSel; grind
    · zuhgl
    · rw [a3 r by_omega by_omega by_omega by_omega, r₁ r by_omega]
  by_cases hT : w = 2 * V.m + 6
  · have w₀ := hw
    obtain ⟨c₁, e₁, v₁⟩ : ∃ c₁, Exec P W (.instr (.subN 120180 120029 120011)) c c₁ 1 ∧
        c₁.nreg 120180 = 2 * V.m + 5 ∧ ∀ r, r ≠ 120180 → c₁.nreg r = c.nreg r :=
      ⟨_, Exec.subN hw _ _ _, by config_simp; rw [hq.tEnd, hq.one]; omega, fun r hr => by
        config_simp; upd_solve⟩
    obtain ⟨d', k, ex, hk, a1, a2, a3⟩ := mid _ ztdgt by_omega c₁
      e₁.wb_right
      ztvwe v₁.1
    have hq12 : c.nreg 120141 = c.nreg 120029 := by rw [hwdef, hq.tEnd, hT]
    refine ⟨d', _, .ifLtN_false ztdck
      (.ifLtN_false by_omega (ifEq_eq_exec hq12 ztncm)), by_omega,
      ⟨?_, ?_, ?_⟩, fun r h1 h2 => ?_⟩
    · zuhkn
    · intro _; zungr; unfold chordSel
      grind
    · zuibq

    · rw [a3 r by_omega by_omega by_omega by_omega, v₁.2 r by_omega]
  · have hq12 : c.nreg 120141 ≠ c.nreg 120029 := by rw [hwdef, hq.tEnd]; exact hT
    obtain ⟨k', ex', hk'⟩ := ifEq_ne_exec hq12 (Exec.copyN hw 120152 120141)
    refine ⟨_, _, .ifLtN_false ztdck
      (.ifLtN_false ztktx ex'), by_omega, ztcg,
      fun r h1 h2 => ?_⟩
    · config_simp; zupae; unfold chordSel
      grind
    · zuibq

    · intro _; config_simp; rw [hwdef]; unfold chordSel
      grind
    · config_simp; upd_solve
open Classical in
/-- **The choice of the stopping point.** -/
theorem tchS_exec (hG : GoodEnv P) (hW : 8 * P.n + 32 ≤ W) {C : Chain}
    {V : QV} (hv : QVOK P C V) (htv : V.tv < P.n) (c : Config) (hw : WordsBounded W c)
    (hq : QConst P V c) (hf : c.nreg 120140 ≤ 1) (hb : BestOK P.n V.s V.m c) :
    ∃ c' k, Exec P W tchS c c' k ∧ k ≤ 340 ∧ FrameB BT c c' ∧
      SelIn c' (selOf C V ztchc zthui ztdcq
        (if V.σb = 1 then EndLtD P C V ztfgp ztdcq V.hz
          else EndGtD P C V ztfgp ztdcq V.hz)) := by
  suffices H : ∃ c' k, Exec P W tchS c c' k ∧ k ≤ 340 ∧
      SelIn c' _ by
    obtain ⟨c', k, ex, hk, hs⟩ := H
    exact ⟨c', k, ex, hk, exec_frameB ex wr_tchS, hs⟩
  obtain ⟨c₁, e₁, v₁, r₁⟩ := const_exec (P := P) hw 120150 1 by_omega
  -- the side of the box
  obtain ⟨c₂, k₂, e₂, hk₂, v₂, v150, r₂⟩ : ∃ c₂ k₂, Exec P W (.ifLtN 120024 120011
      ztotj ztotk) c₁ c₂ k₂ ∧ k₂ ≤ 3 ∧
      c₂.nreg 120152 = (boxSel V).2 ∧ c₂.nreg 120150 = 1 ∧
      (∀ r, r ≠ 120152 → r ≠ 120150 → c₂.nreg r = c.nreg r) := by
    have x24 := (r₁ _ by_decide).trans hq.σb
    have x11 := (r₁ _ by_decide).trans hq.one
    zudmj
    · obtain ⟨c₂, e₂, v₂, r₂⟩ := const_exec e₁.wb_right 120152 1 by_omega
      refine ⟨c₂, _, .ifLtN_true by_omega e₂, by_omega, ?_, ?_, ?_⟩
      · rw [v₂]; unfold boxSel; simp_all
      · simp_all
      simp_all
    · obtain ⟨c₂, e₂, v₂, r₂⟩ := const_exec e₁.wb_right 120152 3 by_omega
      refine ⟨c₂, _, .ifLtN_false by_omega e₂, by_omega, ?_, ?_, ?_⟩
      · rw [v₂]; unfold boxSel; rw [ite_eq_left (by have := hv.σb_le; omega)]
      · simp_all
      simp_all
  zuesb
  zue
  have x140 : ztsgv := by_simp_all
  have x50 : c₂.nreg 120050 = c.nreg 120050 := by_simp_all
  have x141 : ztsgw := by_simp_all
  have x52 : c₂.nreg 120052 = c.nreg 120052 := by_simp_all
  have hbo : bestOf c = if c.nreg 120050 = 1 then some _ else none := rfl
  set CB := (if V.σb = 1 then EndLtD P C V _ _ V.hz
    else EndGtD P C V _ _ V.hz) with hCB
  have hb1 := hb.1
  by_cases hF : c.nreg 120140 = 1
  · zuirj
    · -- both: compare
      obtain ⟨c₃, k₃, e₃, hk₃, v₃⟩ : ∃ c₃ k₃, Exec P W (block [.copyN 120120 120141,
          .copyN 120121 120023]) c₂ c₃ k₃ ∧ k₃ = 2 ∧ (c₃.nreg 120120 = c.nreg 120141 ∧
            c₃.nreg 120121 = V.hz ∧ ∀ r, r ≠ 120120 → r ≠ 120121 → c₃.nreg r = c₂.nreg r) := by
        exec_block
        exact ⟨rfl, by_simp_all, by config_simp; exact hq₂.hz,
          by simp_all⟩
      zubeb

      have heD : c₃.nreg 120051 < P.n := by
        rw [r₃ _ by_decide by_decide, r₂ _ by_decide by_decide, (hb.2 hD).1]
        zuisr
      have x51 : c₃.nreg 120051 = c.nreg 120051 := by
        simp_all
      obtain ⟨c₄, k₄, e₄, hk₄, f₄, b₄, g₄⟩ : ∃ c₄ k₄, Exec P W (.ifLtN 120024 120011 gtDS ltDS)
          c₃ c₄ k₄ ∧ k₄ ≤ 302 ∧ FrameB BX2 c₃ c₄ ∧ c₄.nreg 120128 ≤ 1 ∧ (c₄.nreg 120128 = 1 ↔ CB) := by
        zudmj
        · obtain ⟨c₄, k₄, e₄, hk₄, f₄, b₄, g₄⟩ := gtDS_exec hG by_omega hv htv c₃
            e₃.wb_right hq₃ ztdyz heD
          zugxk
          refine ⟨c₄, _, .ifLtN_true ztktu e₄, by_omega, f₄, b₄, ?_⟩
          simp_all
        · obtain ⟨c₄, k₄, e₄, hk₄, f₄, b₄, g₄⟩ := ltDS_exec hG by_omega hv htv c₃
            e₃.wb_right hq₃ ztdyz heD
          zugxk
          refine ⟨c₄, _, .ifLtN_false ztktu e₄, by_omega, f₄, b₄, ?_⟩
          rw [g₄, hCB, ite_eq_left (by have := hv.σb_le; omega)]
      have hq₄ := hq₃.frame f₄ fun r h1 h2 => by
        simp only [BX2, Bk, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega
      have R₄ : ∀ r, BX2 r = false → r ≠ 120120 → r ≠ 120121 → c₄.nreg r = c₂.nreg r :=
        fun r h1 h2 h3 => (f₄.1 r h1).trans by_simp_all
      by_cases hc : c₄.nreg 120128 = 1
      · obtain ⟨c₅, k₅, e₅, hk₅, s₅, -⟩ := useCh_exec by_omega hv c₄ e₄.wb_right hq₄
          (by rw [R₄ _ by_decide by_decide by_decide, v150])
        rw [R₄ _ by_decide by_decide by_decide, x141] at s₅
        refine ⟨c₅, _, .seq e₁ (.seq e₂ (.ifLtN_true ztfpn
          (.ifLtN_true ztfpo (.seq e₃ (.seq e₄
            (.ifLtN_true (by rw [hq₄.zero]; omega) e₅)))))), by_omega, ?_⟩
        zuhaw
      · have hdc : ¬ CB := by_simp_all
        obtain ⟨c₅, k₅, e₅, hk₅, s₅, -⟩ := useD_exec c₄ e₄.wb_right by_omega
        rw [R₄ _ by_decide by_decide by_decide, x52] at s₅
        refine ⟨c₅, _, .seq e₁ (.seq e₂ (.ifLtN_true ztfpn
          (.ifLtN_true ztfpo (.seq e₃ (.seq e₄
            ztsox))))), by_omega, ?_⟩
        unfold selOf
        simp_all
    · -- only the chord
      obtain ⟨c₅, k₅, e₅, hk₅, s₅, -⟩ := useCh_exec by_omega hv c₂ w₂ hq₂ v150
      rw [x141] at s₅
      refine ⟨c₅, _, .seq e₁ (.seq e₂ (.ifLtN_true ztfpn
        ztsox)), by_omega, ?_⟩
      zuhaw
  · zuirj
    · obtain ⟨c₅, k₅, e₅, hk₅, s₅, -⟩ := useD_exec c₂ w₂ by_omega
      rw [x52] at s₅
      refine ⟨c₅, _, .seq e₁ (.seq e₂ (.ifLtN_false by_omega
        (.ifLtN_true ztfpo e₅))), by_omega, ?_⟩
      zuhaw
    · refine ⟨c₂, _, .seq e₁ (.seq e₂ (.ifLtN_false by_omega
        (.ifLtN_false by_omega ztbun))), by_omega, ?_⟩
      unfold selOf; rw [ite_eq_right by_omega, hbo, ite_eq_right hD]
      exact ⟨v150, fun h => absurd h by_tauto, by_simp_all⟩

/-! ## The walk positions of the stopping point -/
section PosDef
variable (V : QV) (n : ℕ)

/-- The walk edge of the stopping point on the tour edge of chain edge `c` running forward. -/
def wAOf (c : ℕ) : ℕ :=
  (c + 2 * V.m - V.sS) % ztdsk + 6 + (if V.hz = ztqde % n then 1 else 0)

/-- The walk edge of the stopping point on the tour edge of chain edge `c` running backward. -/
def wBOf (c : ℕ) : ℕ :=
  (2 * V.m - 1 - c + 2 * V.m - V.sS) % ztdsk + 6 + (if V.hz = zthdd % n then 1 else 0)

/-- **The four walk edges of the stopping point** (height code `hz + 1`). -/
def posOf (sel : ℕ × ℕ) : ℕ × ℕ × ℕ × ℕ :=
  if sel.1 = 0 then
    (wAOf V n sel.2, wBOf V n sel.2, if V.hz = V.tv then 6 else wAOf V n sel.2,
      if V.hz = V.tv then 2 * V.m + 6 else wBOf V n sel.2)
  else (sel.2, sel.2, sel.2, sel.2)
end PosDef

/-- One end: the tour index in `120184`, then the walk edge in `rd`, one step further when the
height vertex is the end vertex `(s + c + δ) mod n`. -/
def endS (rd : ℕ) (δ : Bool) : Stmt :=
  .seq (modSub 120184 120019)
    (.seq (block ([.addN rd 120184 120028, .addN 120185 120015 120151] ++
        (if δ then [.addN 120185 120185 120011] else [])))
      (.seq (modSub 120185 120010) (ifEq 120023 120185 (.instr (.addN rd rd 120011)) .skip)))

/-- **The walk positions of the stopping point.** -/
def posS : Stmt :=
  .ifLtN 120150 120011
    (.seq (block [.addN 120184 120151 120019, .subN 120184 120184 120021])
      (.seq (endS 120160 true)
        (.seq (block [.subN 120184 120019 120011, .subN 120184 120184 120151,
            .addN 120184 120184 120019, .subN 120184 120184 120021])
          (.seq (endS 120161 false)
            (ifEq 120023 120022 (block [.copyN 120162 120028, .copyN 120163 120029])
              (block [.copyN 120162 120160, .copyN 120163 120161]))))))
    (block [.copyN 120160 120152, .copyN 120161 120152, .copyN 120162 120152, .copyN 120163 120152])

/-- The registers written by `posS`. -/
def BPo (r : ℕ) : Bool := decide (120160 ≤ r ∧ r ≤ 120163) || decide (120184 ≤ r ∧ r ≤ 120185)
theorem wr_posS : wr BPo posS = true := by_decide
variable {P : Polygon} {W : ℕ}
theorem endS_exec (hW : 8 * P.n + 32 ≤ W) {C : Chain} {V : QV}
    (hv : QVOK P C V) (c : Config) (hw : WordsBounded W c) (hq : QConst P V c) {rd : ℕ}
    (hrd : rd = 120160 ∨ rd = 120161) (δ : Bool) {x cc : ℕ} (hx : c.nreg 120184 = x)
    (hx4 : x < 2 * ztdsk) (hc : c.nreg 120151 = cc) (hcm : cc < V.m) :
    ∃ c' k, Exec P W (endS rd δ) c c' k ∧ k ≤ 16 ∧
      c'.nreg rd = x % ztdsk + 6 + (if V.hz = ztzdf % P.n then 1 else 0) ∧
      (∀ r, r ≠ rd → r ≠ 120184 → r ≠ 120185 → c'.nreg r = c.nreg r) := by
  have hmn : V.m < P.n := by
    zqbgg
  have hm1 : 1 ≤ V.m := by_omega
  have hs := hv.s_lt
  zuiz
  unfold endS
  obtain ⟨c₁, k₁, e₁, hk₁, v₁, r₁, -⟩ := modSub_exec (P := P) (r := 120184) (nr := 120019)
    by_decide c hw (by rw [hx, hq.twoM]; omega)
  rw [hx, hq.twoM] at v₁
  zubwn
  have hr1 : rd ≠ 120184 ∧ rd ≠ 120185 ∧ rd ≠ 120015 ∧ rd ≠ 120151 ∧ rd ≠ 120011 ∧
      rd ≠ 120028 ∧ rd ≠ 120010 ∧ rd ≠ 120023 := by
    omega
  obtain ⟨c₂, k₂, e₂, hk₂, v₂, v₂', r₂⟩ : ∃ c₂ k₂, Exec P W (block ([.addN rd 120184 120028,
      .addN 120185 120015 120151] ++ (if δ then [.addN 120185 120185 120011] else []))) c₁ c₂ k₂ ∧
      k₂ ≤ 3 ∧ c₂.nreg rd = x % ztdsk + 6 ∧
      c₂.nreg 120185 = V.s + cc + ztilf ∧
      (∀ r, r ≠ rd → r ≠ 120185 → c₂.nreg r = c₁.nreg r) := by
    have hxm : ztyze := Nat.mod_lt _ by_omega
    have h151 : c₁.nreg 120151 = cc := by_simp_all
    zud
    zujuq
    have q6 := hq₁.six
    have qs := hq₁.s
    have q1 := hq₁.one
    have hrd' := hr1
    cases δ
    · simp only [List.append_nil, Bool.false_eq_true, ite_false]
      exec_block
      · omega
      · zqbgf
      · refine ⟨by omega, ?_, ?_, fun r h1 h2 => ?_⟩ <;>
          (config_simp; ((try simp only [Machine.upd_apply]); (repeat' split_ifs) <;>
            first | omega))
    · simp only [List.cons_append, List.nil_append, ite_true]
      exec_block
      · omega
      · zqbgf
      · zqbgf
      · refine ⟨by omega, ?_, ?_, fun r h1 h2 => ?_⟩ <;>
          (config_simp; ((try simp only [Machine.upd_apply]); (repeat' split_ifs) <;>
            first | omega))
  zuesc
  obtain ⟨c₃, k₃, e₃, hk₃, v₃, r₃, -⟩ := modSub_exec (P := P) (r := 120185) (nr := 120010)
    by_decide c₂ e₂.wb_right (by rw [v₂', hq₂.n]; grind)
  rw [v₂', hq₂.n] at v₃
  have x23 := (r₃ _ by_decide).trans hq₂.hz
  have xrd : c₃.nreg rd = x % ztdsk + 6 := by_simp_all
  by_cases heq : V.hz = ztzdf % P.n
  · have hq12 : c₃.nreg 120023 = c₃.nreg 120185 := by_omega
    obtain ⟨c₄, e₄, v₄, r₄, -⟩ := add_exec e₃.wb_right rd rd 120011 (by
      rw [xrd, (r₃ _ by_decide).trans hq₂.one]
      have : ztyze := Nat.mod_lt _ by_omega
      omega)
    refine ⟨c₄, _, .seq e₁ (.seq e₂ (.seq e₃ (ifEq_eq_exec hq12 e₄))), by_omega, ?_,
      fun r h1 h2 h3 => ?_⟩
    · rw [v₄, xrd, (r₃ _ by_decide).trans hq₂.one, ite_eq_left heq]
    simp_all
  · have hq12 : c₃.nreg 120023 ≠ c₃.nreg 120185 := by_omega
    obtain ⟨k', ex', hk'⟩ := ifEq_ne_exec hq12
      ztjdx
    refine ⟨c₃, _, .seq e₁ (.seq e₂ (.seq e₃ ex')), by_omega, ?_, fun r h1 h2 h3 => ?_⟩
    · simp_all
    simp_all

/-- **The walk positions of the stopping point.** -/
theorem posS_exec (hW : 8 * P.n + 32 ≤ W) {C : Chain} {V : QV}
    (hv : QVOK P C V) (c : Config) (hw : WordsBounded W c) (hq : QConst P V c) {sel : ℕ × ℕ}
    (hs : SelIn c sel) (hsel : sel.1 = 0 ∨ sel.1 = 1) (hcm : sel.1 = 0 → sel.2 < V.m) :
    ∃ c' k, Exec P W posS c c' k ∧ k ≤ 60 ∧ FrameB BPo c c' ∧
      ztjrj = posOf V P.n sel := by
  suffices H : ∃ c' k, Exec P W posS c c' k ∧ k ≤ 60 ∧
      ztjrj = posOf V P.n sel by
    obtain ⟨c', k, ex, hk, h⟩ := H
    exact ⟨c', k, ex, hk, exec_frameB ex wr_posS, h⟩
  have hsS : V.sS ≤ 2 * V.m := by rw [hv.sS, hv.m]; exact C.sideS_lt C.sideBeta
  have hm1 : 1 ≤ V.m := by rw [hv.m]; exact C.one_le
  have hmn : V.m < P.n := by
    zqbgg
  rcases hsel with h0 | h1
  · obtain ⟨cc, hcc⟩ : ∃ cc, sel.2 = cc := by_simp_all
    have hccm := hcm h0
    rw [hcc] at hccm
    have x151 : c.nreg 120151 = cc := by rw [hs.2.1 h0, hcc]
    have x150 : c.nreg 120150 = 0 := by rw [hs.1, h0]
    -- the forward tour edge
    obtain ⟨c₁, k₁, e₁, hk₁, v₁, r₁⟩ : ∃ c₁ k₁, Exec P W (block [.addN 120184 120151 120019,
        .subN 120184 120184 120021]) c c₁ k₁ ∧ k₁ = 2 ∧ c₁.nreg 120184 = cc + 2 * V.m - V.sS ∧
        (∀ r, r ≠ 120184 → c₁.nreg r = c.nreg r) := by
      exec_block
      · rw [x151, hq.twoM]; omega
      · refine ⟨rfl, ?_, by_simp_all⟩
        config_simp; rw [x151, hq.twoM, hq.sS]
    zubwn
    obtain ⟨c₂, k₂, e₂, hk₂, v₂, r₂⟩ := endS_exec hW hv c₁ e₁.wb_right hq₁ ztp true
      v₁ by_omega by_simp_all hccm
    have hq₂ := hq₁.congr fun r h1 h2 => r₂ r by_omega by_omega by_omega
    -- the backward tour edge
    obtain ⟨c₃, k₃, e₃, hk₃, v₃, r₃⟩ : ∃ c₃ k₃, Exec P W (block [.subN 120184 120019 120011,
        .subN 120184 120184 120151, .addN 120184 120184 120019, .subN 120184 120184 120021]) c₂ c₃ k₃ ∧
        k₃ = 4 ∧ c₃.nreg 120184 = 2 * V.m - 1 - cc + 2 * V.m - V.sS ∧
        (∀ r, r ≠ 120184 → c₃.nreg r = c₂.nreg r) := by
      have x151' : c₂.nreg 120151 = cc := by
        simp_all
      have q2 := hq₂.twoM
      have q1 := hq₂.one
      have q21 := hq₂.sS
      zue
      zujuq
      exec_block
      · config_simp; omega
      · refine ⟨rfl, ?_, fun r hr => by config_simp; upd_solve⟩
        config_simp; omega
    have hq₃ := hq₂.congr fun r h1 h2 => r₃ r by_omega
    obtain ⟨c₄, k₄, e₄, hk₄, v₄, r₄⟩ := endS_exec hW hv c₃ e₃.wb_right hq₃ ztbt false
      v₃ by_omega by_simp_all hccm
    have hq₄ := hq₃.congr fun r h1 h2 => r₄ r by_omega by_omega by_omega
    have x160 : c₄.nreg 120160 = wAOf V P.n cc := by
      rw [r₄ _ by_decide by_decide by_decide, r₃ _ by_decide, v₂]; rfl
    have x161 : c₄.nreg 120161 = wBOf V P.n cc := by zuntf; rfl
    have ex₀ : Exec P W _ c c₄
        _ := .seq e₁ ztcb
    zucc
    by_cases htv : V.hz = V.tv
    · have hq12 : c₄.nreg 120023 = c₄.nreg 120022 := by rw [hq₄.hz, hq₄.tv, htv]
      obtain ⟨c₅, k₅, e₅, hk₅, v₅⟩ : ∃ c₅ k₅, Exec P W (block [.copyN 120162 120028,
          .copyN 120163 120029]) c₄ c₅ k₅ ∧ k₅ = 2 ∧ (c₅.nreg 120160 = c₄.nreg 120160 ∧
            c₅.nreg 120161 = c₄.nreg 120161 ∧ c₅.nreg 120162 = 6 ∧
            c₅.nreg 120163 = 2 * V.m + 6) := by
        exec_block
        exact ⟨rfl, by config_simp, by config_simp, by config_simp; exact hq₄.six,
          by config_simp; exact hq₄.tEnd⟩
      zufip
      refine ⟨c₅, _, .ifLtN_true ztfpv (.seq e₁ (.seq e₂ (.seq e₃ (.seq e₄
        (ifEq_eq_exec hq12 e₅))))), by_omega, ?_⟩
      zumty
    · have hq12 : c₄.nreg 120023 ≠ c₄.nreg 120022 := by rw [hq₄.hz, hq₄.tv]; omega
      obtain ⟨c₅, k₅, e₅, hk₅, v₅⟩ : ∃ c₅ k₅, Exec P W (block [.copyN 120162 120160,
          .copyN 120163 120161]) c₄ c₅ k₅ ∧ k₅ = 2 ∧ (c₅.nreg 120160 = c₄.nreg 120160 ∧
            c₅.nreg 120161 = c₄.nreg 120161 ∧ c₅.nreg 120162 = c₄.nreg 120160 ∧
            c₅.nreg 120163 = c₄.nreg 120161) := by
        exec_block
        simp
      zufip
      obtain ⟨k', ex', hk'⟩ := ifEq_ne_exec
        hq12 e₅
      refine ⟨c₅, _, .ifLtN_true ztfpv (.seq e₁ (.seq e₂ (.seq e₃ (.seq e₄
        ex')))), by_omega, ?_⟩
      zumty
  · have x150 : c.nreg 120150 = 1 := by rw [hs.1, h1]
    have x152 := hs.2.2 h1
    obtain ⟨c₁, k₁, e₁, hk₁, v₁⟩ : ∃ c₁ k₁, Exec P W (block [.copyN 120160 120152,
        .copyN 120161 120152, .copyN 120162 120152, .copyN 120163 120152]) c c₁ k₁ ∧ k₁ = 4 ∧
        (c₁.nreg 120160 = sel.2 ∧ c₁.nreg 120161 = sel.2 ∧ c₁.nreg 120162 = sel.2 ∧
          c₁.nreg 120163 = sel.2) := by
      exec_block
      simp_all
    obtain ⟨a0, a1, a2, a3⟩ := v₁
    refine ⟨c₁, _, .ifLtN_false ztfpv e₁, by_omega, ?_⟩
    unfold posOf; simp_all
end
end OracleR
end Chazelle.Core
end
section
set_option hygiene false
local macro "zqbfu" : tactic => `(tactic| (have hW : ztmd := by have := E.hW; unfold hostWords at this; omega))
local macro "zqbfv" : tactic => `(tactic| obtain ⟨c', k, ex, hk, ca, f⟩ := ocase by_tauto)
local macro "zqbfw" : tactic => `(tactic| obtain ⟨c', k, ex, hk, ca, f⟩ := T2 by_grind)
local macro "zqbfx" : tactic => `(tactic| (have fe₂ := FrameB.wk f₂ ztuwu
                                           have E₂ := E₁.frame fe₂ Bedge_env))
set_option hygiene true

/-!
# WP-G, part 45: the segment machine `edgeH`

The decision tree of `edgeSel` on the RAM (see `ShootCutShEdgeR`).  `eqTree`: the ends at one
height; `neTree`: the ends at different heights, with `midTree` for the origin strictly between.
-/
namespace Chazelle.Core
namespace ShootCut
open Machine Machine.Stmt Programs SignK WalkKey NFLoc SweepPrim
@[expose] public section
def eqTree : Stmt :=
  .ifLtN 140312 K1 cand0
    (.seq zttfc (.ifLtN 140314 K1 cand0
      (.seq (nearT 140316) (.ifLtN 140316 K1 ztrna
        ztrnb))))

/-- The point at the height of the origin, strictly inside the segment. -/
def xTree : Stmt :=
  .seq (.instr (.addN 140304 140236 K1)) (.seq (ptLoad 140262 140304 140292)
    (.seq (aheadT 140292 140314) (.ifLtN 140314 K1 cand0 (candFrom 140292 140262 140304))))

/-- The origin neither at the height of `U` nor at the one of `V`. -/
def midTree : Stmt :=
  .seq (hLess 140274 140234 140317) (.seq (hLess 140234 140285 140318)
    (.seq (hLess 140285 140234 140319) (.seq (hLess 140234 140274 140320)
      (.ifLtN 140317 K1 ztjcy
        (.ifLtN 140318 K1 ztjcy xTree)))))

/-- The ends at different heights. -/
def neTree : Stmt :=
  .ifLtN 140312 K1
    (.ifLtN 140313 K1 midTree
      (.seq (aheadT 140281 140314) (.ifLtN 140314 K1 cand0 ztrnb)))
    (.seq zttfc (.ifLtN 140314 K1 cand0 ztrna))

/-- **The segment machine.** -/
def edgeH : Stmt :=
  .seq (ptLoad 140263 140264 140270) (.seq (ptLoad 140265 140266 140281)
    (.seq (hEq 140274 140285 140311) (.seq (hEq 140234 140274 140312)
      (.seq (hEq 140234 140285 140313) (.ifLtN 140311 K1 neTree eqTree)))))
variable {P : Polygon} {W : ℕ} {H : Host} {C : Chain} {z : Point} {σ : ℝ}

/-! ## Frames -/
variable {c c' : Config} {B : ℕ}
theorem PtRecB.keep {q : Point} {R : ℝ} (h : PtRecB P c B q R)
    (hk : ∀ r, B ≤ r → r < B + 11 → c'.nreg r = c.nreg r) : PtRecB P c' B q R := by
  obtain ⟨ax, hy, fr⟩ := h
  refine ⟨absRec_copy' ax by_simp_all by_simp_all
    by_simp_all by_simp_all,
    hy.copy by_simp_all by_grind
      by_grind, fun h7 => ?_⟩
  obtain ⟨s, hs, hl, hv⟩ := fr by_simp_all
  exact ⟨s, NFLoc.symPtIn_copy hs by_grind by_grind
    by_grind, hl, hv⟩
theorem Bkb_bedge {dst : ℕ} (hd : Bedge dst = true) (r : ℕ) (h : Bkb dst r = true) :
    Bedge r = true := by
  simp only [Bkb, Bk, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  rcases h with h | rfl
  · zuonr; omega
  omega
theorem Bld_bedge (hB : 140262 ≤ B ∧ B + 11 ≤ 140330) (r : ℕ) (h : Bld B r = true) :
    Bedge r = true := by
  simp only [Bld, Bool.or_eq_true, decide_eq_true_eq] at h
  simp only [Bedge, Bool.or_eq_true, decide_eq_true_eq]
  grind

/-! ## The ends at one height -/

/-- The walk position in `e`, `h` has the point `q`, is proper, on a walk edge. -/
def PosAt (P : Polygon) (C : Chain) (c : Config) (e h : ℕ) (q : Point) : Prop :=
  (chainModel C).pos zta ztkv = q ∧
    ProperPos ztc zta P.n ztkv ∧ c.nreg e < (chainModel C).W.n
theorem PosAt.keep {e h : ℕ} {q : Point} (hp : PosAt P C c e h q)
    (he : c'.nreg e = c.nreg e) (hh : c'.nreg h = c.nreg h) : PosAt P C c' e h q := by
  unfold PosAt at *; simp_all
theorem ne_of_seg {U V z X : Point} (hz : z ∉ seg U V) (hX : X ∈ seg U V) (hy : z.2 = X.2) :
    X.1 ≠ z.1 := by_grind
theorem eqTree_exec (c : Config) (hw : WordsBounded W c) (E : ShEnv P W H C z σ c)
    {pU pV : Point} (rU : PtRecB P c 140270 pU C.radius) (rV : PtRecB P c 140281 pV C.radius)
    (pU' : PosAt P C c 140263 140264 pU) (pV' : PosAt P C c 140265 140266 pV)
    (hUV : pU.2 = pV.2) (b12 : BitIs c 140312 ztuey) (hz : z ∉ seg pU pV) :
    ∃ c' k, Exec P W eqTree c c' k ∧ k ≤ 600 ∧ CandAt P C c' 140220 ztdwc z σ ∧
      FrameB Bedge c c' := by
  zqbfu
  have hc := edge_cand (X := pU) E.hσ hz (fun h => by
    grind)
  dsimp only at hc
  unfold eqTree
  by_cases t0 : c.nreg 140312 < c.nreg K1
  · have hzU : ¬ z.2 = pU.2 := fun h => by have := b12.2.2 h; rw [E.k1] at t0; omega
    rw [show edgeSel _ _ _ _ _ _ _ _ = 0 by unfold edgeSel; rw [ite_eq_left hUV,
      ite_eq_right hzU]] at hc
    obtain ⟨c', k, ex, hk, ca, f⟩ := cand0_exec c hw
      ztmlb
    exact ⟨c', _, .ifLtN_true t0 ex, by_omega, ca, f⟩
  have hzU := b12.2.1 (by have := b12.1; rw [E.k1] at t0; omega)
  obtain ⟨c₁, k₁, e₁, hk₁, a₁, f₁⟩ := aheadT_exec (P := P) c hw E (A := 140270) (dst := 140314)
    by_norm_num by_norm_num rU.1 (ne_of_seg hz zttdp hzU)
  have E₁ := E.frame f₁ fun r hr => by
    have := Bedge_env r hr
    cases h : Bkb 140314 r
    · rfl
    · exact absurd ztriq by_simp_all
  have kp : ∀ r, 140260 ≤ r → r < 140300 → r ≠ 140314 → c₁.nreg r = c.nreg r := fun r h1 h2 h3 =>
    f₁.1 r ztbvt
  have rU₁ := rU.keep fun r h1 h2 => kp r by_omega by_omega by_omega
  have rV₁ := rV.keep fun r h1 h2 => kp r by_omega by_omega by_omega
  have pU₁ := pU'.keep by_grind
    ztqso
  have pV₁ := pV'.keep by_grind
    ztqso
  zujxp
  zud
  have t0' := t0
  by_cases t1 : c₁.nreg 140314 < c₁.nreg K1
  · have hA : ¬ 0 < σ * (pU.1 - z.1) := fun h => by
      have := a₁.2.2 h; rw [E₁.k1] at t1; omega
    rw [show edgeSel _ _ _ _ _ _ _ _ = 0 by unfold edgeSel; rw [ite_eq_left hUV,
      ite_eq_left hzU, ite_eq_right hA]] at hc
    obtain ⟨c', k, ex, hk, ca, f⟩ := cand0_exec c₁ w₁
      ztmlb
    exact ⟨c', _, .ifLtN_false t0' (.seq e₁ ztspp), by_omega, ca, fe₁.trans f⟩
  have hA := a₁.2.1 (by have := a₁.1; rw [E₁.k1] at t1; omega)
  obtain ⟨c₂, k₂, e₂, hk₂, a₂, f₂⟩ := nearT_exec (P := P) c₁ w₁ E₁ (dst := 140316) by_norm_num
    rU₁.1 rV₁.1
  have E₂ := E₁.frame f₂ fun r hr => by
    have := Bedge_env r hr
    cases h : Bkb 140316 r
    · rfl
    · exact absurd ztriq by_grind
  have kp₂ : ∀ r, 140260 ≤ r → r < 140300 → r ≠ 140316 → c₂.nreg r = c₁.nreg r :=
    fun r h1 h2 h3 => f₂.1 r ztbvt
  have rU₂ := rU₁.keep fun r h1 h2 => kp₂ r by_omega by_omega by_omega
  have rV₂ := rV₁.keep fun r h1 h2 => kp₂ r by_omega by_omega by_omega
  have pU₂ := pU₁.keep by_grind
    ztqsp
  have pV₂ := pV₁.keep by_grind
    ztqsp
  have fe₂ := FrameB.wk f₂ ztgdg
  zue
  have t1' := t1
  by_cases t2 : c₂.nreg 140316 < c₂.nreg K1
  · have hn : σ * pU.1 ≤ σ * pV.1 := by
      by_contra h; have := a₂.2.2 h; rw [E₂.k1] at t2; omega
    rw [show edgeSel _ _ _ _ _ _ _ _ = 1 by unfold edgeSel; rw [ite_eq_left hUV,
      ite_eq_left hzU, ite_eq_left hA, ite_eq_left hn]] at hc
    obtain ⟨c', k, ex, hk, ca, f⟩ := candFrom_exec c₂ w₂
      by_omega by_norm_num by_norm_num
      by_norm_num rU₂.1 ztmla pU₂.2.1 pU₂.2.2 (by rw [pU₂.1, hzU])
    exact ⟨c', _, .ifLtN_false t0' (.seq e₁ (.ifLtN_false t1' (.seq e₂ ztspr))),
      by omega, ca, (fe₁.trans fe₂).trans f⟩
  have hn := a₂.2.1 (by have := a₂.1; rw [E₂.k1] at t2; omega)
  rw [show edgeSel _ _ _ _ _ _ _ _ = 2 by unfold edgeSel; rw [ite_eq_left hUV,
    ite_eq_left hzU, ite_eq_left hA, ite_eq_right hn]] at hc
  obtain ⟨c', k, ex, hk, ca, f⟩ := candFrom_exec (P := P) (C := C) (S := seg pU pV) c₂ w₂
    by_omega (A := 140281) (e := 140265) (h := 140266) by_norm_num by_norm_num
    by_norm_num rV₂.1 ztmla pV₂.2.1 pV₂.2.2 (by rw [pV₂.1, hzU, hUV])
  exact ⟨c', _, .ifLtN_false t0' (.seq e₁ (.ifLtN_false t1' (.seq e₂ ztjdk))),
    by omega, ca, (fe₁.trans fe₂).trans f⟩

/-! ## The point at the height of the origin -/

/-- A step framed by `Bkb dst` keeps the environment. -/
theorem ShEnv.bkb (E : ShEnv P W H C z σ c) {dst : ℕ} (hd : Bedge dst = true)
    (f : FrameB ztdks c c') : ShEnv P W H C z σ c' :=
  E.frame f fun r hr => by
    have := Bedge_env r hr
    cases h : Bkb dst r
    · rfl
    · exact absurd (Bkb_bedge hd r h) by_simp_all
theorem xTree_exec (c : Config) (hw : WordsBounded W c) (E : ShEnv P W H C z σ c)
    {pU pV : Point} {p i : ℕ} (h62 : c.nreg 140262 = p) (h36 : c.nreg 140236 = i)
    (hq : (chainModel C).pos zta zteys ∈ seg pU pV)
    (hqy : ((chainModel C).pos zta zteys).2 = z.2)
    (hpp : ProperPos ztc zta P.n zteys) (hpn : p < (chainModel C).W.n)
    (hqR : |((chainModel C).pos zta ⟨p, i + 1⟩).2| < C.radius)
    (hUV : pU.2 ≠ pV.2) (hz : z ∉ seg pU pV) (hroom : c.nreg ALLOC + 15800 ≤ W) :
    ∃ c' k, Exec P W xTree c c' k ∧ k ≤ 16200 ∧ CandAt P C c' 140220 ztdwc z σ ∧
      FrameB Bedge c c' := by
  zqbfu
  have hin : i + 1 ≤ P.n := hpp.2.2
  have e₁ := Exec.addN (P := P) hw 140304 140236 K1 (by rw [h36, E.k1]; omega)
  set c₁ : Config := { c with nreg := upd c.nreg 140304 _ } with hc₁
  have g₁ : ∀ r, r ≠ 140304 → c₁.nreg r = c.nreg r := by_simp_all
  have fe₁ : FrameB Bedge c c₁ := frameB_upd c _ by_decide
  zujwb
  have q04 : c₁.nreg 140304 = i + 1 := by zvmxj; simp [h36, E.k1]
  have q62 : c₁.nreg 140262 = p := by_simp_all
  have hA₁ : ztdc := g₁ _ by_decide
  obtain ⟨c₂, k₂, e₂, hk₂, r₂, f₂⟩ := ptLoad_exec (P := P) c₁ e₁.wb_right E₁ (e := 140262)
    (h := 140304) (B := 140292) by_norm_num by_norm_num by_norm_num by_omega
    by_simp_all ztcgy by_omega
  rw [q62, q04] at r₂
  zqbfx
  have k₂' : ∀ r, (r = 140262 ∨ r = 140304) → c₂.nreg r = c₁.nreg r := fun r hr =>
    f₂.1 r (by rcases hr with rfl | rfl <;> decide)
  obtain ⟨c₃, k₃, e₃, hk₃, a₃, f₃⟩ := aheadT_exec (P := P) c₂ e₂.wb_right E₂ (A := 140292)
    (dst := 140314) by_norm_num by_norm_num r₂.1 (ne_of_seg hz hq hqy.symm)
  have fe₃ := FrameB.wk f₃ ztgdg
  have E₃ := E₂.bkb by_decide f₃
  have kp : ∀ r, 140260 ≤ r → r < 140310 → c₃.nreg r = c₂.nreg r := fun r h1 h2 =>
    f₃.1 r ztbvt
  have r₃ := r₂.keep fun r h1 h2 => kp r by_omega by_omega
  have hc := seg_at E.hσ hUV hq hqy
  zubj
  unfold xTree
  by_cases t : c₃.nreg 140314 < c₃.nreg K1
  · have hA : ¬ 0 < σ * ztxrt := fun h => by
      have := a₃.2.2 h; rw [E₃.k1] at t; omega
    rw [ite_eq_right hA] at hc
    obtain ⟨c', k, ex, hk, ca, f⟩ := cand0_exec c₃ w₃
      ztmlb
    exact ⟨c', _, .seq e₁ (.seq e₂ (.seq e₃ ztspn)), by_omega, ca,
      ((fe₁.trans fe₂).trans fe₃).trans f⟩
  · have hA : 0 < σ * ztxrt :=
      a₃.2.1 (by have := a₃.1; rw [E₃.k1] at t; omega)
    rw [ite_eq_left hA] at hc
    obtain ⟨c', k, ex, hk, ca, f⟩ := candFrom_exec c₃ w₃
      by_omega (e := 140262) (h := 140304) by_norm_num by_norm_num
      by_norm_num r₃.1 ztmla
      by_simp_all
      by_simp_all
      by_grind
    exact ⟨c', _, .seq e₁ (.seq e₂ (.seq e₃ ztspa)), by_omega, ca,
      ((fe₁.trans fe₂).trans fe₃).trans f⟩

/-! ## The origin strictly inside the heights -/

/-- The geometry of the segment on the walk edge `p`. -/
def SegGeo (C : Chain) (p : ℕ) (pU pV : Point) : Prop :=
  p < (chainModel C).W.n ∧ ∃ α β : ℝ, 0 ≤ α ∧ α ≤ β ∧ β ≤ 1 ∧
    pU = Chazelle.Geometry.lerp ztbkd ztbke α ∧
    pV = Chazelle.Geometry.lerp ztbkd ztbke β
theorem midTree_exec (c : Config) (hw : WordsBounded W c) (E : ShEnv P W H C z σ c)
    {pU pV : Point} {p : ℕ} (rU : PtRecB P c 140270 pU C.radius)
    (rV : PtRecB P c 140281 pV C.radius) (h62 : c.nreg 140262 = p)
    (geo : SegGeo C p pU pV) (hUV : pU.2 ≠ pV.2) (hzU : z.2 ≠ pU.2) (hzV : z.2 ≠ pV.2)
    (hz : z ∉ seg pU pV) (hroom : c.nreg ALLOC + 15800 ≤ W) :
    ∃ c' k, Exec P W midTree c c' k ∧ k ≤ 17300 ∧ CandAt P C c' 140220 ztdwc z σ ∧
      FrameB Bedge c c' := by
  zqbfu
  zubo
  -- the four height bits
  have step : ∀ (c₀ : Config) (dst : ℕ), WordsBounded W c₀ → ShEnv P W H C z σ c₀ →
      PtRecB P c₀ 140270 pU C.radius → PtRecB P c₀ 140281 pV C.radius →
      c₀.nreg 140262 = p → c₀.nreg ALLOC = c.nreg ALLOC → 140317 ≤ dst → dst < 140321 →
      ∀ a b ya yb, (a = 140274 ∨ a = 140234 ∨ a = 140285) → (b = 140274 ∨ b = 140234 ∨ b = 140285) →
      HRecS P c₀ a ya C.radius → HRecS P c₀ b yb C.radius →
      ∃ c₁ k, Exec P W _ c₀ c₁ k ∧ k ≤ 250 ∧ BitIs c₁ dst _ ∧
        FrameB _ c₀ c₁ ∧ ShEnv P W H C z σ c₁ ∧ PtRecB P c₁ 140270 pU C.radius ∧
        PtRecB P c₁ 140281 pV C.radius ∧ c₁.nreg 140262 = p ∧ c₁.nreg ALLOC = c.nreg ALLOC ∧
        ∀ r, r ≠ dst → 140262 ≤ r → r < 140330 → c₁.nreg r = c₀.nreg r :=
    fun c₀ dst hw₀ E₀ rU₀ rV₀ h62₀ hA₀ hd1 hd2 a b ya yb ha hb hA hB => by
      obtain ⟨c₁, k, ex, hk, bt, f⟩ := hLess_exec E₀.hG hW c₀ hw₀ (a := a) (b := b) (dst := dst)
        by_omega by_omega by_omega E₀.k1 hR hA hB
      have kp : ∀ r, r ≠ dst → 140262 ≤ r → r < 140330 → c₁.nreg r = c₀.nreg r :=
        fun r h1 h2 h3 => f.1 r ztbvt
      exact ⟨c₁, k, ex, hk, bt, f, E₀.bkb ztnun f,
        rU₀.keep by_grind,
        rV₀.keep by_grind,
        by grind,
        by rw [f.1 ALLOC (by simp [Bkb, Bk, ALLOC]; omega), hA₀], kp⟩
  obtain ⟨c₁, k₁, e₁, hk₁, b17, f₁, E₁, rU₁, rV₁, q₁, a₁, kp₁⟩ := step c 140317 hw E rU rV h62 rfl
    le_rfl by_norm_num 140274 140234 _ _ ztp ztwiz rU.2.1 E.oy
  obtain ⟨c₂, k₂, e₂, hk₂, b18, f₂, E₂, rU₂, rV₂, q₂, a₂, kp₂⟩ := step c₁ 140318 e₁.wb_right E₁ rU₁
    rV₁ q₁ a₁ by_norm_num by_norm_num 140234 140285 _ _ ztwiz
    ztwrm E₁.oy rV₁.2.1
  obtain ⟨c₃, k₃, e₃, hk₃, b19, f₃, E₃, rU₃, rV₃, q₃, a₃, kp₃⟩ := step c₂ 140319 e₂.wb_right E₂ rU₂
    rV₂ q₂ a₂ by_norm_num by_norm_num 140285 140234 _ _ ztwrm
    ztwiz rV₂.2.1 E₂.oy
  obtain ⟨c₄, k₄, e₄, hk₄, b20, f₄, E₄, rU₄, rV₄, q₄, a₄, kp₄⟩ := step c₃ 140320 e₃.wb_right E₃ rU₃
    rV₃ q₃ a₃ by_norm_num by_norm_num 140234 140274 _ _ ztwiz
    ztp E₃.oy rU₃.2.1
  -- the bits survive
  have b17' : BitIs c₄ 140317 _ :=
    ((b17.of_eq by_grind).of_eq
      (kp₃ _ by_norm_num by_norm_num by_norm_num)).of_eq
      ztqsq
  have b18' : BitIs c₄ 140318 _ :=
    (b18.of_eq by_grind).of_eq
      ztqsq
  have b19' : BitIs c₄ 140319 _ :=
    b19.of_eq by_grind
  have fe :=
    (((FrameB.wk f₁ ztgdg).trans (FrameB.wk f₂ ztgdg)).trans
      (FrameB.wk f₃ ztgdg)).trans (FrameB.wk f₄ (Bkb_bedge by_decide))
  have hpre : ∀ {s : Stmt} {c' : Config} {k : ℕ}, Exec P W s c₄ c' k →
      Exec P W _ c c'
        _ := fun ex => .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ ex)))
  zucc
  -- the answer when the origin is strictly between
  obtain ⟨hpn, α, β, hα, hαβ, hβ, hpU, hpV⟩ := geo
  have xcase : zthjd ∨ ztoeg →
      ∃ c' k, Exec P W xTree c₄ c' k ∧ k ≤ 16200 ∧ CandAt P C c' 140220 _ z σ ∧
        FrameB Bedge c₄ c' := fun hmid => by
    have bU := rU.2.1.bounds hR
    have bV := rV.2.1.bounds hR
    -- the origin is at the height of a vertex of `Q`
    obtain ⟨-, hzR, -, hi, hzi⟩ : c₄.nreg 140234 = 1 ∧ |z.2| < C.radius ∧
        c₄.nreg ztsrv = 0 ∧ c₄.nreg ztfmr < P.n ∧
        z.2 = ((Qof P).vtx (c₄.nreg ztfmr)).2 := by
      rcases E₄.oy with ⟨_, h⟩ | ⟨_, h⟩ | h
      · exfalso; zvmwc at hmid; grind
      · grind
      omega
    set i := c₄.nreg ztfmr with hi_def
    have hm := mid_pos _ _ hα hαβ hβ (by
      rw [← hpU, ← hpV, ← hzi]; omega)
    rw [← hpU, ← hpV] at hm
    obtain ⟨hmem, hy, hp0, hp1⟩ := hm
    exact xTree_exec c₄ w₄ E₄ q₄ rfl hmem by_grind
      ⟨hp0.le, hp1, by_grind⟩ hpn by_grind hUV hz
      by_omega
  have ocase : ¬ (zthjd ∨ ztoeg) →
      ∃ c' k, Exec P W cand0 c₄ c' k ∧ k = 1 ∧ CandAt P C c' 140220 ztdwc z σ ∧
        FrameB Bedge c₄ c' := fun hmid => by
    refine cand0_exec c₄ w₄ ((seg_out (x := 0) ?_).2 by_norm_num)
    zubf
    apply hmid
    rcases le_total pU.2 pV.2 with h | h
    · rw [min_eq_left h] at h1; rw [max_eq_right h] at h2
      exact Or.inl ztsr
    · rw [min_eq_right h] at h1; rw [max_eq_left h] at h2
      exact Or.inr ztsr
  have k1 := E₄.k1
  unfold midTree
  -- the tree
  have T2 : (¬ zthjd) → ∃ c' k, Exec P W (.ifLtN 140319 K1 cand0
      (.ifLtN 140320 K1 cand0 xTree)) c₄ c' k ∧ k ≤ 16210 ∧
      CandAt P C c' 140220 ztdwc z σ ∧ FrameB Bedge c₄ c' := fun hn => by
    by_cases t19 : c₄.nreg 140319 < c₄.nreg K1
    · have h19 : ¬ pV.2 < z.2 := fun h => by have := b19'.2.2 h; omega
      zqbfv
      exact ⟨c', _, .ifLtN_true t19 ex, by_omega, ca, f⟩
    have h19 := b19'.2.1 (by have := b19'.1; omega)
    by_cases t20 : c₄.nreg 140320 < c₄.nreg K1
    · have h20 : ¬ z.2 < pU.2 := fun h => by have := b20.2.2 h; omega
      zqbfv
      exact ⟨c', _, .ifLtN_false t19 (.ifLtN_true t20 ex), by_omega, ca, f⟩
    have h20 := b20.2.1 (by have := b20.1; omega)
    obtain ⟨c', k, ex, hk, ca, f⟩ := xcase (Or.inr ⟨h19, h20⟩)
    exact ⟨c', _, .ifLtN_false t19 (.ifLtN_false t20 ex), by_omega, ca, f⟩
  by_cases t17 : c₄.nreg 140317 < c₄.nreg K1
  · have h17 : ¬ pU.2 < z.2 := fun h => by have := b17'.2.2 h; omega
    zqbfw
    exact ⟨c', _, hpre (.ifLtN_true t17 ex), by_omega, ca, fe.trans f⟩
  have h17 := b17'.2.1 (by have := b17'.1; omega)
  by_cases t18 : c₄.nreg 140318 < c₄.nreg K1
  · have h18 : ¬ z.2 < pV.2 := fun h => by have := b18'.2.2 h; omega
    zqbfw
    exact ⟨c', _, hpre (.ifLtN_false t17 (.ifLtN_true t18 ex)), by_omega, ca, fe.trans f⟩
  have h18 := b18'.2.1 (by have := b18'.1; omega)
  obtain ⟨c', k, ex, hk, ca, f⟩ := xcase (Or.inl ⟨h17, h18⟩)
  exact ⟨c', _, hpre (.ifLtN_false t17 (.ifLtN_false t18 ex)), by_omega, ca, fe.trans f⟩

/-! ## The ends at different heights -/

/-- The answer at an end of the segment at the height of the origin. -/
theorem endCase_exec (c : Config) (hw : WordsBounded W c) (E : ShEnv P W H C z σ c)
    {pU pV q : Point} {A e h : ℕ} (hq : q ∈ seg pU pV) (hqz : q.2 = z.2) (hUV : pU.2 ≠ pV.2)
    (hz : z ∉ seg pU pV) (hA : 140262 ≤ A ∧ A + 11 ≤ 140310) (he : 140262 ≤ e ∧ e < 140270)
    (hh : 140262 ≤ h ∧ h < 140270) (rq : PtRecB P c A q C.radius) (pq : PosAt P C c e h q) :
    ∃ c' k, Exec P W (.seq (aheadT A 140314) (.ifLtN 140314 K1 cand0 ztrnc)) c c' k ∧
      k ≤ 270 ∧ CandAt P C c' 140220 ztdwc z σ ∧ FrameB Bedge c c' := by
  zqbfu
  obtain ⟨c₁, k₁, e₁, hk₁, a₁, f₁⟩ := aheadT_exec (P := P) c hw E (A := A) (dst := 140314)
    by_omega by_norm_num rq.1 (ne_of_seg hz hq hqz.symm)
  have E₁ := E.bkb by_decide f₁
  have kp : ∀ r, 140262 ≤ r → r < 140310 → c₁.nreg r = c.nreg r := fun r h1 h2 =>
    f₁.1 r ztbvt
  have rq₁ := rq.keep fun r h1 h2 => kp r by_omega by_omega
  have pq₁ := pq.keep by_grind (kp h by_omega by_omega)
  zujxp
  have hc := seg_at E.hσ hUV hq hqz
  zud
  by_cases t : c₁.nreg 140314 < c₁.nreg K1
  · have hA' : ¬ 0 < σ * zttxc := fun h => by
      have := a₁.2.2 h; rw [E₁.k1] at t; omega
    rw [ite_eq_right hA'] at hc
    obtain ⟨c', k, ex, hk, ca, f⟩ := cand0_exec c₁ w₁
      ztmlb
    exact ⟨c', _, .seq e₁ ztspn, by_omega, ca, fe₁.trans f⟩
  · have hA' := a₁.2.1 (by have := a₁.1; rw [E₁.k1] at t; omega)
    rw [ite_eq_left hA'] at hc
    obtain ⟨c', k, ex, hk, ca, f⟩ := candFrom_exec c₁ w₁
      by_omega by_omega by_omega by_omega rq₁.1 ztmla
      pq₁.2.1 pq₁.2.2 (by rw [pq₁.1, ← hqz])
    exact ⟨c', _, .seq e₁ ztspa, by_omega, ca, fe₁.trans f⟩
theorem neTree_exec (c : Config) (hw : WordsBounded W c) (E : ShEnv P W H C z σ c)
    {pU pV : Point} {p : ℕ} (rU : PtRecB P c 140270 pU C.radius)
    (rV : PtRecB P c 140281 pV C.radius) (pU' : PosAt P C c 140263 140264 pU)
    (pV' : PosAt P C c 140265 140266 pV) (h62 : c.nreg 140262 = p) (geo : SegGeo C p pU pV)
    (hUV : pU.2 ≠ pV.2) (b12 : BitIs c 140312 ztuey) (b13 : BitIs c 140313 (z.2 = pV.2))
    (hz : z ∉ seg pU pV) (hroom : c.nreg ALLOC + 15800 ≤ W) :
    ∃ c' k, Exec P W neTree c c' k ∧ k ≤ 17400 ∧ CandAt P C c' 140220 ztdwc z σ ∧
      FrameB Bedge c c' := by
  zujac
  unfold neTree
  by_cases t12 : c.nreg 140312 < c.nreg K1
  · have hzU : z.2 ≠ pU.2 := fun h => by have := b12.2.2 h; omega
    by_cases t13 : c.nreg 140313 < c.nreg K1
    · have hzV : z.2 ≠ pV.2 := fun h => by have := b13.2.2 h; omega
      obtain ⟨c', k, ex, hk, ca, f⟩ := midTree_exec c hw E rU rV h62 geo hUV hzU hzV hz hroom
      exact ⟨c', _, .ifLtN_true t12 (.ifLtN_true t13 ex), by_omega, ca, f⟩
    have hzV := b13.2.1 (by have := b13.1; omega)
    obtain ⟨c', k, ex, hk, ca, f⟩ := endCase_exec c hw E (V_mem_seg pU pV) hzV.symm hUV hz by_norm_num by_norm_num by_norm_num rV pV'
    exact ⟨c', _, .ifLtN_true t12 (.ifLtN_false t13 ex), by_omega, ca, f⟩
  have hzU := b12.2.1 (by have := b12.1; omega)
  obtain ⟨c', k, ex, hk, ca, f⟩ := endCase_exec c hw E zttdp hzU.symm hUV hz
    (A := 140270) (e := 140263) (h := 140264) by_norm_num by_norm_num by_norm_num rU pU'
  exact ⟨c', _, .ifLtN_false t12 ex, by_omega, ca, f⟩

/-! ## The segment machine -/

/-- The input of the segment machine: an end position, proper, and a box vertex or strictly
inside the height range of the box. -/
def EndIn (P : Polygon) (C : Chain) (c : Config) (e h : ℕ) (q : Point) : Prop :=
  PosAt P C c e h q ∧ (c.nreg h = 0 ∨ |q.2| < C.radius)
theorem edgeH_exec (c : Config) (hw : WordsBounded W c) (E : ShEnv P W H C z σ c)
    {pU pV : Point} {p : ℕ} (iU : EndIn P C c 140263 140264 pU) (iV : EndIn P C c 140265 140266 pV)
    (h62 : c.nreg 140262 = p) (geo : SegGeo C p pU pV) (hz : z ∉ seg pU pV)
    (hroom : c.nreg ALLOC + 50000 ≤ W) :
    ∃ c' k, Exec P W edgeH c c' k ∧ k ≤ 50000 ∧ CandAt P C c' 140220 ztdwc z σ ∧
      FrameB Bedge c c' := by
  zqbfu
  zubo
  -- `U`
  obtain ⟨⟨pUe, pUp, pUn⟩, pUy⟩ := iU
  obtain ⟨c₁, k₁, e₁, hk₁, rU₁, f₁⟩ := ptLoad_exec (P := P) c hw E (e := 140263) (h := 140264)
    (B := 140270) by_norm_num by_norm_num by_norm_num pUn pUp by_simp_all
    by_omega
  rw [pUe] at rU₁
  have fe₁ := FrameB.wk f₁ ztuwu
  zujwb
  have kp₁ : ∀ r, 140262 ≤ r → r < 140270 → c₁.nreg r = c.nreg r := fun r h1 h2 =>
    f₁.1 r ztljm
  have hA₁ := f₁.1 ALLOC by_rfl
  -- `V`
  obtain ⟨⟨pVe, pVp, pVn⟩, pVy⟩ := iV
  obtain ⟨c₂, k₂, e₂, hk₂, rV₂, f₂⟩ := ptLoad_exec (P := P) c₁ e₁.wb_right E₁ (e := 140265)
    (h := 140266) (B := 140281) by_norm_num by_norm_num by_norm_num
    by_simp_all
    by_simp_all
    by_simp_all
    by_omega
  rw [kp₁ _ by_norm_num by_norm_num, kp₁ _ by_norm_num by_norm_num, pVe] at rV₂
  zqbfx
  have kp₂ : ∀ r, 140262 ≤ r → r < 140281 → c₂.nreg r = c₁.nreg r := fun r h1 h2 =>
    f₂.1 r ztljm
  have hA₂ : ztbae := by
    rw [f₂.1 ALLOC by_rfl, hA₁]
  have rU₂ := rU₁.keep fun r h1 h2 => kp₂ r by_omega by_omega
  have pU₂ : PosAt P C c₂ 140263 140264 pU := by
    refine PosAt.keep ⟨pUe, pUp, pUn⟩ ?_ ?_
    · simp_all
    simp_all
  have pV₂ : PosAt P C c₂ 140265 140266 pV := by
    refine PosAt.keep ⟨pVe, pVp, pVn⟩ ?_ ?_
    · simp_all
    simp_all
  have q62 : c₂.nreg 140262 = p := by
    simp_all
  -- the three height bits
  have hEqStep : ∀ (c₀ : Config) (a b dst : ℕ) (ya yb : ℝ), WordsBounded W c₀ →
      ShEnv P W H C z σ c₀ → 140311 ≤ dst → dst < 140314 → HRecS P c₀ a ya C.radius →
      HRecS P c₀ b yb C.radius →
      ∃ c₁ k, Exec P W _ c₀ c₁ k ∧ k ≤ 20 ∧ BitIs c₁ dst _ ∧
        (∀ r, r ≠ dst → c₁.nreg r = c₀.nreg r) ∧ FrameB Bedge c₀ c₁ ∧ ShEnv P W H C z σ c₁ :=
    fun c₀ a b dst ya yb hw₀ E₀ hd1 hd2 hA hB => by
      obtain ⟨c₁, k, ex, hk, bt, hc⟩ := hEq_exec E₀.hG by_omega c₀ hw₀ (dst := dst) E₀.k1 hR hA hB
      have kp : ∀ r, r ≠ dst → c₁.nreg r = c₀.nreg r := fun r hr => by zvnmd; zumwy
      have fr : FrameB Bedge c₀ c₁ := by
        zvnmd; exact frameB_upd c₀ _ ztnun
      exact ⟨c₁, k, ex, hk, bt, kp, fr, E₀.frame fr Bedge_env⟩
  obtain ⟨c₃, k₃, e₃, hk₃, b11, kp₃, fe₃, E₃⟩ := hEqStep c₂ 140274 140285 140311 _ _ e₂.wb_right
    E₂ le_rfl by_norm_num rU₂.2.1 rV₂.2.1
  have rU₃ := rU₂.keep fun r h1 h2 => kp₃ r by_omega
  have rV₃ := rV₂.keep fun r h1 h2 => kp₃ r by_omega
  obtain ⟨c₄, k₄, e₄, hk₄, b12, kp₄, fe₄, E₄⟩ := hEqStep c₃ 140234 140274 140312 _ _ e₃.wb_right
    E₃ by_norm_num by_norm_num E₃.oy rU₃.2.1
  have rU₄ := rU₃.keep fun r h1 h2 => kp₄ r by_omega
  have rV₄ := rV₃.keep fun r h1 h2 => kp₄ r by_omega
  obtain ⟨c₅, k₅, e₅, hk₅, b13, kp₅, fe₅, E₅⟩ := hEqStep c₄ 140234 140285 140313 _ _ e₄.wb_right
    E₄ by_norm_num by_norm_num E₄.oy rV₄.2.1
  have rU₅ := rU₄.keep fun r h1 h2 => kp₅ r by_omega
  have rV₅ := rV₄.keep fun r h1 h2 => kp₅ r by_omega
  have kk : ∀ r, 140262 ≤ r → r < 140270 → c₅.nreg r = c₂.nreg r := by_grind
  have pU₅ := pU₂.keep by_grind ztrst
  have pV₅ := pV₂.keep by_grind ztrst
  have q62' : c₅.nreg 140262 = p := by_grind
  have b11' : BitIs c₅ 140311 _ :=
    (b11.of_eq by_grind).of_eq (kp₅ _ by_norm_num)
  have b12' : BitIs c₅ 140312 _ := b12.of_eq by_grind
  have hA₅ : ztizp := by
    rw [kp₅ _ by_decide, kp₄ _ by_decide, kp₃ _ by_decide, hA₂]
  have fe := (((fe₁.trans fe₂).trans fe₃).trans fe₄).trans fe₅
  zuef
  have hpre : ∀ {s : Stmt} {c' : Config} {k : ℕ}, Exec P W s c₅ c' k →
      Exec P W _ c c' _ :=
    fun ex => .seq e₁ ztgxd
  unfold edgeH
  by_cases t11 : c₅.nreg 140311 < c₅.nreg K1
  · have hUV : pU.2 ≠ pV.2 := fun h => by have := b11'.2.2 h; rw [E₅.k1] at t11; omega
    obtain ⟨c', k, ex, hk, ca, f⟩ := neTree_exec c₅ w₅ E₅ rU₅ rV₅ pU₅ pV₅ q62' geo hUV b12' b13
      hz by_omega
    exact ⟨c', _, hpre (.ifLtN_true t11 ex), by_omega, ca, fe.trans f⟩
  · have hUV := b11'.2.1 (by have := b11'.1; rw [E₅.k1] at t11; omega)
    obtain ⟨c', k, ex, hk, ca, f⟩ := eqTree_exec c₅ w₅ E₅ rU₅ rV₅ pU₅ pV₅ hUV b12' hz
    exact ⟨c', _, hpre (.ifLtN_false t11 ex), by_omega, ca, fe.trans f⟩
end
end ShootCut
end Chazelle.Core
end
namespace Chazelle.Core
namespace ShootCut
open Machine Machine.Stmt Programs SignK WalkKey NFLoc SweepPrim
@[expose] public section
def copyC : Stmt :=
  block (copies [ztsrl, ztsrm, ztsrn, ztsro,
    ztsrp, ztsrq, ztsrr])

/-- The comparison bit: the candidate is nearer. -/
def cmpT : Stmt := .ifLtN 140241 K1 (xLess 140211 140221 140310) (xLess 140221 140211 140310)

/-- **Keep the nearest.** -/
def mrg : Stmt :=
  .ifLtN 140220 K1 .skip (.ifLtN 140210 K1 copyC (.seq cmpT (.ifLtN 140310 K1 .skip copyC)))

/-- The registers written by `mrg`. -/
def Bmrg (r : ℕ) : Bool := Bk r || decide (140210 ≤ r ∧ r < 140217) || r == 140310
variable {P : Polygon} {W : ℕ} {H : Host} {C : Chain} {z : Point} {σ : ℝ}
variable {c : Config} {b : ℕ} {S : Set Point}
theorem CandAt.cand (h : CandAt P C c b S z σ) :
    ∃ x : ℝ, Cand S z σ ztfgv x ∧ (c.nreg b = 1 → AbsRec P c ztds x C.radius ∧
      ProperPos ztc zta P.n ztbgg ∧
      c.nreg ztnrm < (chainModel C).W.n ∧
      (chainModel C).pos zta ztbgg = ztewp) := by
  zuirf
  · obtain ⟨x, a, f, p, n, q⟩ := h.2.2 h1
    exact ⟨x, ⟨fun _ => f, fun h' => absurd h1 h'⟩, fun _ => ⟨a, p, n, q⟩⟩
  · exact ⟨0, ⟨fun h' => absurd h' h1, fun _ => h.2.1 h1⟩, fun h' => absurd h' h1⟩
theorem CandAt.of_cand {x : ℝ} (hb : c.nreg b ≤ 1)
    (hc : Cand S z σ ztfgv x)
    (hr : c.nreg b = 1 → AbsRec P c ztds x C.radius ∧
      ProperPos ztc zta P.n ztbgg ∧
      c.nreg ztnrm < (chainModel C).W.n ∧
      (chainModel C).pos zta ztbgg = ztewp) :
    CandAt P C c b S z σ :=
  ⟨hb, hc.2, fun h1 => ⟨x, (hr h1).1, hc.1 h1, (hr h1).2⟩⟩
theorem copyC_exec (c : Config) (hw : WordsBounded W c) :
    ∃ c', Exec P W copyC c c' 7 ∧ (∀ j, j < 7 → c'.nreg ztnej = c.nreg ztnek) ∧
      FrameB Bmrg c c' := by
  obtain ⟨c', e, v, k, rr, m, rm, o⟩ := copies_exec (P := P) [ztsrl, ztsrm,
    ztsrn, ztsro, ztsrp, ztsrq, ztsrr] c hw
    by_decide by_decide
  zvmwt at v
  refine ⟨c', e, fun j hj => ?_, fun r hr => k r (by simp [Bmrg] at hr ⊢; omega),
    fun r _ => by zuofy, m, rm, o⟩
  obtain ⟨v0, v1, v2, v3, v4, v5, v6⟩ := v
  interval_cases j <;> zvmxv <;> assumption

/-- The register facts of a candidate copied over the best answer. -/
theorem recs_copied {c c' : Config} {x : ℝ}
    (hk : ∀ j, j < 7 → c'.nreg ztnej = c.nreg ztnek)
    (r : c.nreg 140220 = 1 → AbsRec P c (140220 + 1) x C.radius ∧
      ProperPos ztc zta P.n ztiod ∧
      c.nreg (140220 + 5) < (chainModel C).W.n ∧
      (chainModel C).pos zta ztiod = ztewp) :
    c'.nreg 140210 = 1 → AbsRec P c' (140210 + 1) x C.radius ∧
      ProperPos ztc zta P.n ztiob ∧
      c'.nreg (140210 + 5) < (chainModel C).W.n ∧
      (chainModel C).pos zta ztiob = ztewp := by
  zujya
  zudca
  zudqd
  obtain ⟨a, p, n, q⟩ := r by_omega
  zugux
  exact ⟨absRec_copy' a (hk 1 by_norm_num) (hk 2 by_norm_num) (hk 3 by_norm_num)
    (hk 4 by_norm_num), p, n, q⟩
theorem mrg_exec (c : Config) (hw : WordsBounded W c) (E : ShEnv P W H C z σ c)
    {S₁ S₂ : Set Point} (hB : CandAt P C c 140210 S₁ z σ) (hC : CandAt P C c 140220 S₂ z σ) :
    ∃ c' k, Exec P W mrg c c' k ∧ k ≤ 270 ∧ CandAt P C c' 140210 ztbzc z σ ∧
      FrameB Bmrg c c' := by
  zubfx
  zujac
  zugqx
  obtain ⟨x₂, c₂', r₂⟩ := hC.cand
  have hu := cand_union E.hσ c₁' c₂'
  unfold mrg
  by_cases t0 : c.nreg 140220 < c.nreg K1
  · -- no candidate: keep
    have hf₂ : ¬ c.nreg 140220 = 1 := by_omega
    simp only [hf₂, false_and, ↓reduceIte] at hu
    exact ⟨c, _, .ifLtN_true t0 ztjd, by_norm_num, CandAt.of_cand hB.1 hu r₁,
      FrameB.refl _ _⟩
  have hf₂ : c.nreg 140220 = 1 := by have := hC.1; omega
  by_cases t1 : c.nreg 140210 < c.nreg K1
  · have hf₁ : ¬ c.nreg 140210 = 1 := by_omega
    simp only [hf₂, hf₁, ne_eq, not_false_eq_true, true_or, and_self, ↓reduceIte] at hu
    obtain ⟨c', e, hk, f⟩ := copyC_exec (P := P) c hw
    have h0 : ztseb := hk 0 by_norm_num
    refine ⟨c', _, .ifLtN_false t0 (.ifLtN_true t1 e), by_norm_num,
      CandAt.of_cand by_omega by_simp_all (recs_copied hk r₂), f⟩
  have hf₁ : c.nreg 140210 = 1 := by have := hB.1; omega
  obtain ⟨xr₁, -⟩ := r₁ hf₁
  obtain ⟨xr₂, -⟩ := r₂ hf₂
  -- the comparison bit
  have st : ztdro :=
    fun {r} {x} h hk => by
      zubhs
  obtain ⟨c₁, k₁, e₁, hk₁, bt, f₁⟩ : ∃ c₁ k₁, Exec P W cmpT c c₁ k₁ ∧ k₁ ≤ 252 ∧
      BitIs c₁ 140310 (σ * x₂ < σ * x₁) ∧ FrameB (Bkb 140310) c c₁ := by
    unfold cmpT
    zudxb
    · have hσ : ztgbb := by
        zufzo
        · have := E.sig.2.2 h; omega
        omega
      obtain ⟨c₁, k, ex, hk, b, f⟩ := xLess_exec E.hG hW c hw (dst := 140310) by_norm_num by_norm_num
        by_norm_num k1 ztuwg ztuwh (Or.inr ⟨st xr₁, st xr₂⟩)
      refine ⟨c₁, _, .ifLtN_true hs ex, by_omega, b.congr ?_, f⟩
      simp_all
    · have hσ : ztgbc := E.sig.2.1 (by rw [k1] at hs; have := E.sig.1; omega)
      obtain ⟨c₁, k, ex, hk, b, f⟩ := xLess_exec E.hG hW c hw (dst := 140310) by_norm_num by_norm_num
        by_norm_num k1 ztuwh ztuwg (Or.inr ⟨st xr₂, st xr₁⟩)
      refine ⟨c₁, _, .ifLtN_false hs ex, by_omega, b.congr ?_, f⟩
      simp_all
  have kp : ∀ r, 140210 ≤ r → r < 140227 → c₁.nreg r = c.nreg r := fun r h1 h2 =>
    f₁.1 r ztbvt
  have fm₁ : FrameB Bmrg c c₁ := FrameB.wk f₁ (fun r h => by
    simp only [Bkb, Bool.or_eq_true, beq_iff_eq] at h
    simp only [Bmrg, Bool.or_eq_true, beq_iff_eq]
    grind)
  zud
  have k1' : ztcpf := by rw [f₁.1 K1 by_decide, k1]
  have t0' : ¬ c.nreg 140220 < c.nreg K1 := t0
  have t1' : ¬ c.nreg 140210 < c.nreg K1 := t1
  by_cases t2 : c₁.nreg 140310 < c₁.nreg K1
  · have hn : ¬ σ * x₂ < σ * x₁ := fun h => by have := bt.2.2 h; omega
    simp only [hf₂, hf₁, ne_eq, not_true_eq_false, false_or, hn, and_false, ↓reduceIte] at hu
    refine ⟨c₁, _, .ifLtN_false t0' (.ifLtN_false t1' (.seq e₁ (.ifLtN_true t2 ztwd))),
      by omega, CandAt.of_cand by_simp_all
        (by rw [kp _ by_norm_num by_norm_num, hf₁]; exact hu) ztep, fm₁⟩
    obtain ⟨a, p, n, q⟩ := r₁ by_omega
    rw [kp _ by_norm_num by_norm_num, kp _ by_norm_num by_norm_num]
    exact ⟨absRec_copy' a zthyn zthyn
      zthyn zthyn, p, n, q⟩
  · have hn : σ * x₂ < σ * x₁ := bt.2.1 (by have := bt.1; omega)
    simp only [hf₂, hf₁, ne_eq, not_true_eq_false, false_or, hn, and_self, ↓reduceIte] at hu
    obtain ⟨c', e, hk, f⟩ := copyC_exec (P := P) c₁ w₁
    have hk' : ∀ j, j < 7 → c'.nreg ztnej = c.nreg ztnek := fun j hj => by
      grind
    have h0 : ztseb := hk' 0 by_norm_num
    refine ⟨c', _, .ifLtN_false t0' (.ifLtN_false t1' (.seq e₁ (.ifLtN_false t2 e))), by_omega,
      CandAt.of_cand by_omega by_simp_all (recs_copied hk' r₂),
      fm₁.trans f⟩
end
end ShootCut
end Chazelle.Core
namespace Chazelle.Core
@[expose] public section
open Set
open Chazelle.Geometry (lerp lerp_fst lerp_snd)
namespace ShootCut
def pcU (n : ℕ) (x : WPos) (d : ℕ) : WPos := if d = 0 then x else ⟨pcEdge n x.edge d, 0⟩

/-- The end of the `d`-th segment. -/
def pcV (n : ℕ) (x y : WPos) (D d : ℕ) : WPos :=
  if d = D then y else ⟨pcEdge n x.edge ztet, 0⟩
theorem pcEdge_D {n sE eE : ℕ} (hs : sE < n) (he : eE < n) : pcEdge n sE (pcD n sE eE) = eE := by
  unfold pcEdge pcD
  rcases Nat.lt_or_ge eE sE with h | h
  · rw [Nat.mod_eq_of_lt (show eE + n - sE < n by omega),
      show sE + ztqmi = eE + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt he]
  · rw [show eE + n - sE = ztnxw + n by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (show eE - sE < n by omega), show sE + ztnxw = eE by omega,
      Nat.mod_eq_of_lt he]
theorem pcEdge_lt {n sE : ℕ} (hn : 0 < n) (d : ℕ) : pcEdge n sE d < n := Nat.mod_lt _ hn
theorem pcEdge_succ (n sE d : ℕ) : pcEdge n sE ztet = (pcEdge n sE d + 1) % n := by
  unfold pcEdge; grind
variable {C : Chain} {Q : Polygon}
variable {x y : WPos} {N : ℕ}
/-- **The ends of the `d`-th segment** as points of the walk edge. -/
theorem pc0_pts (hxn : x.edge < 2 * C.m + 7) (hyn : y.edge < 2 * C.m + 7) {d : ℕ}
    (hd : d ≤ pcD ztz x.edge y.edge) :
    (chainModel C).pos Q (pcU ztz x d) =
        lerp ztbaon
          ztbaoo (pcA ztuy d) ∧
      (chainModel C).pos Q (pcV ztz x y ztwqs d) =
        lerp ztbaon
          ztbaoo
          (pcB ztwqs ztqq d) := by
  zucwl
  set n := 2 * C.m + 7
  set D := pcD n x.edge y.edge
  constructor
  · unfold pcU pcA
    zuckz
    · zubvi
      zubvh
      rw [show pcEdge n x.edge 0 = x.edge by unfold pcEdge; rw [Nat.add_zero, Nat.mod_eq_of_lt hxn]]
      rfl
    · simp only [h0, ↓reduceIte]; rfl
  · unfold pcV pcB
    by_cases hD : d = D
    · subst hD
      zubvh
      rw [pcEdge_D hxn hyn]; rfl
    · simp only [hD, ↓reduceIte]
      rw [lerp_one']
      show lerp ztiez ztifa 0 = _
      rw [lerp_zero']
      zujqa
      rw [hnW, pcEdge_succ]
theorem pc0_ab (hx : ProperPos ztc Q N x)
    (hy : ProperPos ztc Q N y) (hxn : x.edge < 2 * C.m + 7)
    (hyn : y.edge < 2 * C.m + 7)
    (hwt : (chainModel C).arcWt ztlb ztov ≤ 1) (d : ℕ) :
    0 ≤ pcA ztuy d ∧
      pcA ztuy d ≤ pcB ztwqs
        ztqq d ∧
      pcB ztwqs ztqq d ≤ 1 := by
  zubgj

  unfold pcA pcB
  by_cases h0 : d = 0 <;> by_cases hD : d = pcD ztz x.edge y.edge
  · -- one edge
    rw [ite_eq_left h0, ite_eq_left hD]
    have hxy : ztsnc := by
      have := pcEdge_D (n := 2 * C.m + 7) hxn hyn
      rw [← hD, h0] at this
      unfold pcEdge at this; rw [Nat.add_zero, Nat.mod_eq_of_lt hxn] at this; omega
    exact ⟨hx0, (piece0_nowrap hx hy hxy hxn hwt).le, hy1.le⟩
  · grind
  · grind
  simp_all

/-- The segments `0 … d' - 1` of a kind-0 piece. -/
def segSet (C : Chain) (Q : Polygon) (x y : WPos) (d' : ℕ) : Set Point :=
  ⋃ d ∈ List.range d', seg ztxrv
    ztbali
theorem segSet_zero (x y : WPos) : segSet C Q x y 0 = ∅ := by
  unfold segSet; simp
theorem segSet_succ (x y : WPos) (d : ℕ) : segSet C Q x y ztet = segSet C Q x y d ∪
    seg ztxrv
      ztbali := by
  unfold segSet
  zumlp
  ext p; simp

/-- **The segments of a kind-0 piece cover it.** -/
theorem segSet_full {x y : WPos} (hx : ProperPos ztc Q N x)
    (hy : ProperPos ztc Q N y) (hxn : x.edge < 2 * C.m + 7)
    (hyn : y.edge < 2 * C.m + 7)
    (hwt : (chainModel C).arcWt ztlb ztov ≤ 1) :
    segSet C Q x y (pcD ztz x.edge y.edge + 1) =
      (chainModel C).arcSet ztlb ztov := by
  rw [piece0_union hx hy hxn hyn hwt]
  unfold segSet pcSet
  zucwl
  zufj
  simp only [mem_iUnion, List.mem_range, exists_prop]
  constructor
  · zupv

    rw [hnW, subSeg_eq_seg _ _ ab, ← hU, ← hV]; exact hp
  · zupv

    rw [hnW, subSeg_eq_seg _ _ ab, ← hU, ← hV] at hp; exact hp
end ShootCut
end
end Chazelle.Core
namespace Chazelle.Core
namespace ShootCut
open Machine Machine.Stmt Programs SignK WalkKey NFLoc SweepPrim
@[expose] public section
def k0Init : Stmt :=
  .seq (.ifLtN 140252 140250 ztirc
      ztnbf)
    (block [.addN 140332 140331 K1, .constN 140330 0, .copyN 140333 140250])

/-- The ends of segment `d`. -/
def setUV : Stmt :=
  .seq (block [.copyN 140262 140333, .copyN 140263 140333])
    (.seq (.ifLtN 140330 K1 ztova ztotp)
      (.ifLtN 140330 140331
        (.seq ztnan
          (.seq ztyzr
            ztotq))
        ztkrs))

/-- The next segment. -/
def adv : Stmt :=
  .seq (block [.addN 140330 140330 K1, .addN 140333 140333 K1])
    (.ifLtN 140333 140334 .skip ztotr)

/-- **A kind-0 piece.** -/
def pieceK0 : Stmt :=
  .seq k0Init (.whileLtN 140330 140332 (.seq setUV ztncl))

/-- The registers written by `pieceK0`. -/
def Bk0 (r : ℕ) : Bool := Bedge r || Bmrg r || decide (140330 ≤ r ∧ r < 140334)
variable (r : ℕ) (c : Config)
theorem Bk0_env (h : envR r) : Bk0 r = false := by
  have := Bedge_env r h
  zufdg
  simp only [Bk0, this, Bmrg, Bk, K1, ALLOC, Bool.false_or, Bool.or_eq_false_iff,
    decide_eq_false_iff_not, beq_eq_false_iff_ne] at h ⊢
  omega
variable {P : Polygon} {W : ℕ} {H : Host} {C : Chain} {z : Point} {σ : ℝ}
theorem CandAt.keep {c c' : Config} {b : ℕ} {S : Set Point} (h : CandAt P C c b S z σ)
    (hk : ∀ j, j < 7 → c'.nreg zttfi = c.nreg zttfi) : CandAt P C c' b S z σ := by
  zujya
  zudca
  obtain ⟨hb, hn, hy⟩ := h
  refine ztmqh
  obtain ⟨x, a, f, p, n, q⟩ := hy by_omega
  zugux
  exact ⟨x, absRec_copy' a by_grind by_grind by_grind
    by_grind, f, p, n, q⟩
theorem CandAt.of_eq {c : Config} {b : ℕ} {S S' : Set Point} (h : CandAt P C c b S z σ)
    (hS : S = S') : CandAt P C c b S' z σ := by_simp_all

/-! ## The set-up -/
theorem k0Init_exec (hw : WordsBounded W c) (h1 : c.nreg K1 = 1) {n sE eE : ℕ}
    (h34 : c.nreg 140334 = n) (h50 : c.nreg 140250 = sE) (h52 : c.nreg 140252 = eE)
    (hs : sE < n) (he : eE < n) (hnW : n + 1 ≤ W) :
    ∃ c' k, Exec P W k0Init c c' k ∧ k ≤ 8 ∧ c'.nreg 140330 = 0 ∧
      c'.nreg 140331 = pcD n sE eE ∧ c'.nreg 140332 = pcD n sE eE + 1 ∧
      c'.nreg 140333 = sE ∧ (∀ r, (r < 140330 ∨ 140334 ≤ r) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₂, k₂, e₂, hk₂, q31', r₂, m₂⟩ : ∃ c₂ k₂, Exec P W (.ifLtN 140252 140250
      ztirc
      ztnbf) c c₂ k₂ ∧ k₂ ≤ 4 ∧ c₂.nreg 140331 = pcD n sE eE ∧
      (∀ r, r ≠ 140331 → c₂.nreg r = c.nreg r) ∧ c₂ = { c with nreg := c₂.nreg } := by
    unfold pcD
    by_cases hl : eE < sE
    · obtain ⟨c₁, k₁, e₁, hk₁, q31, r₁, m₁⟩ : ∃ c₁ k₁, Exec P W (block [.subN 140331 140334 140250,
          .addN 140331 140331 140252]) c c₁ k₁ ∧ k₁ = 2 ∧ c₁.nreg 140331 = n - sE + eE ∧
          (∀ r, r ≠ 140331 → c₁.nreg r = c.nreg r) ∧ c₁ = { c with nreg := c₁.nreg } := by
        exec_block
        all_goals first | omega | (config_simp; rw [h34, h50, h52]; omega) | skip
        simp_all
      refine ⟨c₁, _, .ifLtN_true by_omega e₁, by_omega, ?_, r₁, m₁⟩
      rw [q31, Nat.mod_eq_of_lt by_omega]; omega
    · refine ⟨_, _, .ifLtN_false by_omega ztbbq, by_norm_num,
        ?_, by_simp_all, rfl⟩
      zufb
      rw [h52, h50, show eE + n - sE = ztnxw + n by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt by_omega]
  zue
  have hD : pcD n sE eE < n := Nat.mod_lt _ by_omega
  obtain ⟨c₃, k₃, e₃, hk₃, q32, q30, q33, r₃, m₃⟩ : ∃ c₃ k₃, Exec P W (block [.addN 140332 140331 K1,
      .constN 140330 0, .copyN 140333 140250]) c₂ c₃ k₃ ∧ k₃ = 3 ∧
      c₃.nreg 140332 = pcD n sE eE + 1 ∧ c₃.nreg 140330 = 0 ∧ c₃.nreg 140333 = sE ∧
      (∀ r, r ≠ 140332 → r ≠ 140330 → r ≠ 140333 → c₃.nreg r = c₂.nreg r) ∧
      c₃ = { c₂ with nreg := c₃.nreg } := by
    have g1 : ztgat := by rw [r₂ _ by_decide, h1]
    have g50 : c₂.nreg 140250 = sE := by_grind
    exec_block
    all_goals first | omega | (config_simp; rw [q31', g1]; omega) | skip
    refine ⟨rfl, by config_simp; omega, by config_simp, by_tauto,
      fun r h1 h2 h3 => ?_, rfl⟩
    zubd
  refine ⟨c₃, _, .seq e₂ e₃, by_omega, q30, ?_, q32, q33, fun r hr => ?_, ?_, ?_, ?_, ?_⟩
  · grind
  · grind
  all_goals zundc

/-! ## One segment's ends, and the next segment -/
theorem wr_setUV : wr ztiju setUV = true := by_decide
theorem setUV_exec (hw : WordsBounded W c) (h1 : c.nreg K1 = 1) {n : ℕ} {x y : WPos}
    {d D : ℕ} (h30 : c.nreg 140330 = d) (h31 : c.nreg 140331 = D)
    (h33 : c.nreg 140333 = pcEdge n x.edge d) (h34 : c.nreg 140334 = n)
    (h50 : c.nreg 140250 = x.edge) (h51 : c.nreg 140251 = x.hgt) (h52 : c.nreg 140252 = y.edge)
    (h53 : c.nreg 140253 = y.hgt) (hxn : x.edge < n) (hdD : d ≤ D) (hnW : n + 1 ≤ W) :
    ∃ c' k, Exec P W setUV c c' k ∧ k ≤ 12 ∧ c'.nreg 140262 = pcEdge n x.edge d ∧
      c'.nreg 140263 = (pcU n x d).edge ∧ c'.nreg 140264 = (pcU n x d).hgt ∧
      c'.nreg 140265 = (pcV n x y D d).edge ∧ c'.nreg 140266 = (pcV n x y D d).hgt ∧
      FrameB ztiju c c' := by
  zuqi
  have hj : pcEdge n x.edge d < n := pcEdge_lt hn d
  have e0 : pcEdge n x.edge 0 = x.edge := by
    unfold pcEdge; rw [Nat.add_zero, Nat.mod_eq_of_lt hxn]
  -- the edge and `U.edge`
  have ea := Exec.copyN (P := P) hw 140262 140333
  have eb := Exec.copyN (P := P) ea.wb_right 140263 140333
  set c₁ := ({ ({ c with nreg := upd c.nreg 140262 _ } : Config) with
    nreg := upd (upd c.nreg 140262 _) 140263
      (upd c.nreg 140262 _ 140333) } : Config) with hc₁
  have e₁ : ztpjj :=
    Exec.block_cons ea ztbws
  have g₁ : ∀ r, r ≠ 140262 → r ≠ 140263 → c₁.nreg r = c.nreg r := by_simp_all
  have q62 : c₁.nreg 140262 = pcEdge n x.edge d := by_simp_all
  have q63 : c₁.nreg 140263 = pcEdge n x.edge d := by_simp_all
  zud
  have p30 : c₁.nreg 140330 = d := by_simp_all
  have pK : ztcpf := by_tauto
  -- `U.hgt`
  obtain ⟨c₂, k₂, e₂, hk₂, q64, g₂⟩ : ∃ c₂ k₂, Exec P W (.ifLtN 140330 K1
      ztova ztotp) c₁ c₂ k₂ ∧ k₂ ≤ 3 ∧
      c₂.nreg 140264 = (pcU n x d).hgt ∧ ∀ r, r ≠ 140264 → c₂.nreg r = c₁.nreg r := by
    zuckz
    · refine ⟨_, _, .ifLtN_true by_omega zteeh, by_norm_num, ?_,
        by simp_all⟩
      simp [pcU, h0, g₁ _ (by decide : (140251 : ℕ) ≠ 140262) by_decide, h51]
    · refine ⟨_, _, .ifLtN_false by_omega (Exec.constN w₁ _ _ ztbg),
        by norm_num, ?_,
        by simp_all⟩
      simp [pcU, h0]
  zue
  have gg : ∀ r, r ≠ 140262 → r ≠ 140263 → r ≠ 140264 → c₂.nreg r = c.nreg r :=
    by simp_all
  have q30 : c₂.nreg 140330 = d := by_simp_all
  have q31 : c₂.nreg 140331 = D := by_simp_all
  have q33 : c₂.nreg 140333 = pcEdge n x.edge d := by
    simp_all
  have q34 : c₂.nreg 140334 = n := by_simp_all
  have qK : ztgat := by rw [gg _ by_decide by_decide by_decide, h1]
  -- `V`
  obtain ⟨c₃, k₃, e₃, hk₃, v5, v6, g₃⟩ : ∃ c₃ k₃, Exec P W (.ifLtN 140330 140331
      (.seq ztnan
        (.seq ztyzr
          ztotq))
      ztkrs) c₂ c₃ k₃ ∧ k₃ ≤ 6 ∧
      c₃.nreg 140265 = (pcV n x y D d).edge ∧ c₃.nreg 140266 = (pcV n x y D d).hgt ∧
      (∀ r, r ≠ 140265 → r ≠ 140266 → c₃.nreg r = c₂.nreg r) := by
    by_cases hD : d < D
    · have hne : d ≠ D := by_omega
      have ea := Exec.addN (P := P) w₂ 140265 140333 K1 by_omega
      set ca : Config := { c₂ with nreg := upd c₂.nreg 140265 _ }
        with hca
      have a65 : ca.nreg 140265 = pcEdge n x.edge d + 1 := by_simp_all
      have a34 : ca.nreg 140334 = n := by_simp_all
      have ga : ∀ r, r ≠ 140265 → ca.nreg r = c₂.nreg r := by_simp_all
      obtain ⟨cb, kb, eb, hkb, b65, gb⟩ : ∃ cb kb, Exec P W (.ifLtN 140265 140334 .skip
          ztifs) ca cb kb ∧ kb ≤ 3 ∧
          cb.nreg 140265 = (pcEdge n x.edge d + 1) % n ∧
          ∀ r, r ≠ 140265 → cb.nreg r = ca.nreg r := by
        by_cases hl : pcEdge n x.edge d + 1 < n
        · exact ⟨ca, _, .ifLtN_true by_omega (.skip ea.wb_right),
            by norm_num, by rw [a65, Nat.mod_eq_of_lt hl], by_omega⟩
        · refine ⟨_, _, .ifLtN_false by_omega
            (Exec.constN ea.wb_right _ _ ztbg), by_norm_num, ?_,
            by simp_all⟩
          zufas
          rw [show pcEdge n x.edge d + 1 = n by omega, Nat.mod_self]
      have ec := Exec.constN (P := P) eb.wb_right 140266 0 ztbg
      refine ⟨_, _, .ifLtN_true by_omega (.seq ea (.seq eb ec)), by_omega,
        ?_, ?_, fun r h1 h2 => ?_⟩
      · simp only [Config.nreg_mk, upd_other _ _ _ (by decide : (140265 : ℕ) ≠ 140266)]
        rw [b65]; simp [pcV, hne, pcEdge_succ]
      · simp [pcV, hne]
      simp_all
    · have hD' : d = D := by_omega
      have ea := Exec.copyN (P := P) w₂ 140265 140252
      have eb := Exec.copyN (P := P) ea.wb_right 140266 140253
      refine ⟨_, _, .ifLtN_false by_omega
        ztyos, by_norm_num,
        ?_, ?_, by_simp_all⟩
      · simp [pcV, hD', gg _ (by decide : (140252 : ℕ) ≠ 140262) by_decide by_decide, h52]
      · simp [pcV, hD', gg _ (by decide : (140253 : ℕ) ≠ 140262) by_decide by_decide, h53]
  have ex : Exec P W setUV c c₃ _ := .seq e₁ ztcr
  refine ⟨c₃, _, ex, by_omega, ?_, ?_, ?_, v5, v6, exec_frameB ex wr_setUV⟩
  · simp_all
  · rw [g₃ _ by_decide by_decide, g₂ _ by_decide, q63]
    unfold pcU; grind
  simp_all
theorem wr_adv : wr (fun r => r == 140330 || r == 140333) adv = true := by_decide
theorem adv_exec (hw : WordsBounded W c) (h1 : c.nreg K1 = 1) {n j d : ℕ}
    (h30 : c.nreg 140330 = d) (h33 : c.nreg 140333 = j) (h34 : c.nreg 140334 = n) (hj : j < n)
    (hW : d + 1 ≤ W) (hnW : n + 1 ≤ W) :
    ∃ c' k, Exec P W adv c c' k ∧ k ≤ 5 ∧ c'.nreg 140330 = d + 1 ∧
      c'.nreg 140333 = ztl % n ∧ FrameB (fun r => r == 140330 || r == 140333) c c' := by
  zubfu
  have ea := Exec.addN (P := P) hw 140330 140330 K1 by_omega
  have eb := Exec.addN (P := P) ea.wb_right 140333 140333 K1 (by zuobb; omega)
  set c₁ := ({ ({ c with nreg := upd c.nreg 140330 _ } : Config) with
    nreg := upd (upd c.nreg 140330 _) 140333
      (upd c.nreg 140330 _ 140333 +
        upd c.nreg 140330 _ K1) } : Config) with hc₁
  have e₁ : ztpjj :=
    Exec.block_cons ea ztbws
  have q30 : c₁.nreg 140330 = d + 1 := by_simp_all
  have q33 : c₁.nreg 140333 = j + 1 := by zvmxj; zuobb
  have q34 : c₁.nreg 140334 = n := by_simp_all
  zud
  obtain ⟨c₂, k₂, e₂, hk₂, v33, v30⟩ : ∃ c₂ k₂, Exec P W (.ifLtN 140333 140334 .skip
      ztotr) c₁ c₂ k₂ ∧ k₂ ≤ 3 ∧ c₂.nreg 140333 = (j + 1) % n ∧
      c₂.nreg 140330 = d + 1 := by
    by_cases hl : j + 1 < n
    · exact ⟨c₁, _, .ifLtN_true by_omega ztwd, by_norm_num,
        by rw [q33, Nat.mod_eq_of_lt hl], q30⟩
    · refine ⟨_, _, .ifLtN_false by_omega (Exec.constN w₁ _ _
        ztbg), by_norm_num, ?_, by_simp_all⟩
      zufas
      rw [show j + 1 = n by omega, Nat.mod_self]
  have ex : Exec P W adv c c₂ _ := .seq e₁ e₂
  exact ⟨c₂, _, ex, by_omega, v30, v33, exec_frameB ex wr_adv⟩

/-! ## The loop -/
theorem Bmrg_env (h : envR r) : Bmrg r = false := by
  zufdg
  simp only [Bmrg, Bk, K1, ALLOC, Bool.or_eq_false_iff, decide_eq_false_iff_not,
    beq_eq_false_iff_ne] at h ⊢
  omega

/-- The loop invariant of `pieceK0`. -/
def K0Inv (P : Polygon) (W : ℕ) (H : Host) (C : Chain) (z : Point) (σ : ℝ) (x y : WPos)
    (S₀ : Set Point) (A : ℕ) (c₀ c : Config) : Prop :=
  WordsBounded W c ∧ ShEnv P W H C z σ c ∧ ∃ d, d ≤ pcD ztz x.edge y.edge + 1 ∧
    c.nreg 140330 = d ∧ c.nreg 140331 = pcD ztz x.edge y.edge ∧
    c.nreg 140332 = pcD ztz x.edge y.edge + 1 ∧
    c.nreg 140333 = pcEdge ztz x.edge d ∧ c.nreg 140334 = 2 * C.m + 7 ∧
    c.nreg 140250 = x.edge ∧ c.nreg 140251 = x.hgt ∧ c.nreg 140252 = y.edge ∧
    c.nreg 140253 = y.hgt ∧ CandAt P C c 140210 ztyib z σ ∧
    c.nreg ALLOC = A ∧ FrameB Bk0 c₀ c
theorem pieceK0_exec (hw : WordsBounded W c) (E : ShEnv P W H C z σ c)
    {x y : WPos} (h50 : c.nreg 140250 = x.edge) (h51 : c.nreg 140251 = x.hgt)
    (h52 : c.nreg 140252 = y.edge) (h53 : c.nreg 140253 = y.hgt)
    (h34 : c.nreg 140334 = 2 * C.m + 7)
    (hx : ProperPos ztc zta P.n x) (hy : ProperPos ztc zta P.n y)
    (hxn : x.edge < 2 * C.m + 7) (hyn : y.edge < 2 * C.m + 7)
    (hwt : (chainModel C).arcWt ztwol
      ztxjm ≤ 1)
    (hxe : x.hgt = 0 ∨ |((chainModel C).pos zta x).2| < C.radius)
    (hye : y.hgt = 0 ∨ |((chainModel C).pos zta y).2| < C.radius)
    (hz : z ∉ (chainModel C).arcSet ztwol ztxjm)
    {S₀ : Set Point} (hB : CandAt P C c 140210 S₀ z σ) (hnW : ztz + 1 ≤ W)
    (hroom : c.nreg ALLOC + 600000 ≤ W) :
    ∃ c' k, Exec P W pieceK0 c c' k ∧ k ≤ 600000 ∧
      CandAt P C c' 140210 (S₀ ∪ (chainModel C).arcSet ztwol
        ztxjm) z σ ∧ FrameB Bk0 c c' := by
  have hnWn := chainModel_n C
  zulz
  set D := pcD n x.edge y.edge with hDdef
  have hD9 := piece0_D_le hx hy hxn hyn hwt
  have hDn : D < n := Nat.mod_lt _ by_omega
  have hfull := segSet_full hx hy hxn hyn hwt
  -- the set-up
  obtain ⟨c₁, k₁, e₁, hk₁, q30, q31, q32, q33, r₁, m₁, rr₁, rm₁, o₁⟩ :=
    k0Init_exec (P := P) c hw E.k1 h34 h50 h52 hxn hyn by_omega
  have f₁ : FrameB Bk0 c c₁ := ⟨fun r hr => r₁ r (by simp [Bk0] at hr; omega),
    by simp_all, m₁, rm₁, o₁⟩
  have E₁ := E.frame f₁ Bk0_env
  have I₁ : K0Inv P W H C z σ x y S₀ ztm c c₁ := by
    refine ⟨e₁.wb_right, E₁, 0, by_omega, q30, q31, q32, ?_, by_simp_all,
      by simp_all, by_simp_all, by_simp_all,
      by simp_all, ?_, by zvmww, f₁⟩
    · rw [q33]; unfold pcEdge; rw [Nat.add_zero, Nat.mod_eq_of_lt hxn]
    · rw [segSet_zero, Set.union_empty]
      exact hB.keep by_grind
  -- the body
  obtain ⟨c₂, k₂, e₂, I₂, hx₂, hk₂⟩ := Exec.whileLtN_bounded (P := P) (a := 140330)
    (b := 140332) (body := .seq setUV ztncl)
    (K0Inv P W H C z σ x y S₀ ztm c) (fun c' => D + 1 - c'.nreg 140330) 50300
    ztsa (fun c₀ ⟨hw₀, E₀, d, hd, i30, i31, i32, i33, i34, i50, i51, i52, i53, iB,
      iA, iF⟩ hlt => by
      rw [i30, i32] at hlt
      have hdD : d ≤ D := Nat.lt_succ_iff.mp hlt
      -- the ends
      obtain ⟨c₁', k₁', e₁', hk₁', u62, u63, u64, u65, u66, fu⟩ := setUV_exec (P := P) c₀ hw₀
        E₀.k1 (n := n) (x := x) (y := y) (d := d) (D := D) i30 i31 i33 i34 i50 i51 i52 i53
        hxn hdD by_omega
      have E₁' := E₀.frame fu fun r hr => by
        unfold envR at hr; simp only [decide_eq_false_iff_not, K1, ALLOC] at hr ⊢; omega
      have ku : ∀ r, (r < 140262 ∨ 140267 ≤ r) → c₁'.nreg r = c₀.nreg r := fun r hr =>
        fu.1 r by_grind
      -- the segment
      obtain ⟨hU, hV⟩ := pc0_pts (Q := Qof P) hxn hyn hdD
      obtain ⟨a0, ab, b1⟩ := pc0_ab hx hy hxn hyn hwt d
      have hU' : PosAt P C c₁' 140263 140264 ztymw := by
        zujft
        · rw [u63, u64]
          unfold pcU; split_ifs
          · zufsg
          · zujvh
        · rw [u63, hnWn]; unfold pcU; split_ifs
          · omega
          · zulzk
      have hV' : PosAt P C c₁' 140265 140266 ztymt := by
        zujft
        · rw [u65, u66]
          unfold pcV; split_ifs
          · zulfn
          · zujvh
        · rw [u65, hnWn]; unfold pcV; split_ifs
          · omega
          · zulzk
      have iU : EndIn P C c₁' 140263 140264 _ :=
        ⟨hU', by rw [u64]; unfold pcU; grind⟩
      have iV : EndIn P C c₁' 140265 140266 _ :=
        ⟨hV', by rw [u66]; unfold pcV; grind⟩
      have geo : SegGeo C (pcEdge n x.edge d) ((chainModel C).pos _ ztlrq)
          ((chainModel C).pos _ ztilt) :=
        ⟨by rw [hnWn]; exact pcEdge_lt by_omega _, _, _, a0, ab, b1, hU, hV⟩
      have hzd : z ∉ seg ztymw
          ztymt := fun hm => hz (by
        rw [← hfull]
        unfold segSet
        simp only [Set.mem_iUnion, List.mem_range, exists_prop]
        grind)
      have hA₁' : c₁'.nreg ALLOC = c.nreg ALLOC := by rw [ku _ by_decide, iA]
      obtain ⟨c₂', k₂', e₂', hk₂', ca, fe⟩ := edgeH_exec c₁' e₁'.wb_right E₁' iU iV u62 geo hzd
        by_omega
      have E₂' := E₁'.frame fe Bedge_env
      have ke := fe.1
      have iB' : CandAt P C c₂' 140210 ztyib z σ := by
        refine iB.keep fun j hj => ?_
        rw [ke _ (by simp [Bedge, Bprim]; omega), ku _ by_omega]
      obtain ⟨c₃', k₃', e₃', hk₃', cb, fm⟩ := mrg_exec c₂' e₂'.wb_right E₂' iB' ca
      have E₃' := E₂'.frame fm Bmrg_env
      have km := fm.1
      -- registers kept through the segment
      have keep3 : ∀ r, (140330 ≤ r ∧ r < 140335) ∨ ztnel ∨ r = ALLOC →
          c₃'.nreg r = c₀.nreg r := fun r hr => by
        rw [km r (by zuons; unfold ALLOC at hr; omega),
          ke r (by zuonr; unfold ALLOC at hr; omega),
          ku r zthfk]
      obtain ⟨c₄', k₄', e₄', hk₄', v30, v33, fa⟩ := adv_exec (P := P) c₃' e₃'.wb_right E₃'.k1
        (n := n) (j := pcEdge n x.edge d) (d := d)
        by_grind
        by_grind
        by_grind (pcEdge_lt by_omega _)
        by_omega by_omega
      have E₄' := E₃'.frame fa fun r hr => by
        unfold envR at hr; simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, K1, ALLOC] at hr ⊢
        omega
      have ka : ∀ r, r ≠ 140330 → r ≠ 140333 → c₄'.nreg r = c₃'.nreg r := fun r h1 h2 =>
        fa.1 r by_grind
      have kk : ∀ r, (r = 140331 ∨ r = 140332 ∨ r = 140334 ∨ ztnel ∨
          r = ALLOC) → c₄'.nreg r = c₀.nreg r := fun r hr => by
        rw [ka r zthfk zthfk,
          keep3 r (by unfold ALLOC at hr ⊢; omega)]
      have fb : FrameB Bk0 c₀ c₄' :=
        (((FrameB.wk fu (fun r h => by simp at h; simp [Bk0, Bedge]; omega)).trans
          (FrameB.wk fe ztjwf)).trans
          (FrameB.wk fm ztjwf)).trans
          (FrameB.wk fa (fun r h => by simp at h; simp [Bk0]; omega))
      refine ⟨c₄', _, .seq e₁' ztnco, ⟨e₄'.wb_right, E₄', d + 1, by_omega,
        v30, by rw [kk _ ztp, i31], by rw [kk _ by_omega, i32],
        by rw [v33, pcEdge_succ], by rw [kk _ by_omega, i34],
        by rw [kk _ by_omega, i50], by rw [kk _ by_omega, i51], by rw [kk _ by_omega, i52],
        by rw [kk _ by_omega, i53], ?_, by rw [kk _ by_simp, iA], iF.trans fb⟩,
        by omega, by_omega⟩
      refine (cb.keep fun j hj => ka _ by_omega by_omega).of_eq ?_
      rw [segSet_succ, Set.union_assoc]) I₁
  obtain ⟨-, E₂, d, hd, i30, -, i32, -, -, -, -, -, -, iB, -, iF⟩ := I₂
  have i32' : c₂.nreg 140332 = D + 1 := i32
  have hd' := hd
  rw [i30, i32'] at hx₂
  have hdD : d = D + 1 := by_omega
  rw [hdD, hfull] at iB
  refine ⟨c₂, _, .seq e₁ e₂, ?_, iB, iF⟩
  omega
