module

public import Chazelle.MacT
public import Chazelle.Core.DownPhaseDrvBCtx
public import Chazelle.Core.OracleQuery
public import Chazelle.Core.DownPhaseDrvTPiece
public import Chazelle.Core.FuseMathCut
public import Chazelle.Core.ShootCutGrade
public import Chazelle.Core.DownPhaseTransWt
public import Chazelle.Core.GranInitL3

namespace Chazelle.Core
namespace DrvB
open Machine Machine.Stmt Programs SignK WalkKey
@[expose] public section
def emD (A1 A2 B1 B2 D X1 X2 X3 X4 : Bool) : Bool × Bool :=
  if !A1 && !A2 then
    (if !B1 && !B2 then (false, false) else if B2 then (false, X1) else (X2, false))
  else if !B1 && !B2 then
    (if A2 then (X3, false) else (false, X4))
  else if A2 == B2 then (!D, !D) else (B1, !B1)

/-- **The bit decision is the corner decision.** -/
theorem emD_iff {a v b : Point} {A1 A2 B1 B2 D X1 X2 X3 X4 : Bool}
    (hA1 : A1 = true ↔ a.2 < v.2) (hA2 : A2 = true ↔ v.2 < a.2)
    (hB1 : B1 = true ↔ b.2 < v.2) (hB2 : B2 = true ↔ v.2 < b.2)
    (hD : D = true ↔ 0 < det a v b) (hX1 : X1 = true ↔ v.1 < a.1) (hX2 : X2 = true ↔ a.1 < v.1)
    (hX3 : X3 = true ↔ b.1 < v.1) (hX4 : X4 = true ↔ v.1 < b.1) :
    ((emD A1 A2 B1 B2 D X1 X2 X3 X4).1 = true ↔ emitG a v b 1) ∧
      ((emD A1 A2 B1 B2 D X1 X2 X3 X4).2 = true ↔ emitG a v b (-1)) := by
  have e1 : A1 = decide ztnqx := by_grind
  have e2 : A2 = decide ztojp := by_grind
  have e3 : B1 = decide ztnrt := by_grind
  have e4 : B2 = decide ztojq := by_grind
  have e5 : D = decide ztigq := by_grind
  have e6 : X1 = decide ztojl := by_grind
  have e7 : X2 = decide ztnqv := Bool.eq_iff_iff.2 by_simp_all
  have e8 : X3 = decide ztnrs := Bool.eq_iff_iff.2 by_simp_all
  have e9 : X4 = decide ztojm := Bool.eq_iff_iff.2 by_simp_all
  subst e1 e2 e3 e4 e5 e6 e7 e8 e9
  have h1 : (1 : ℝ) ≠ -1 := by_norm_num
  have h2 : (-1 : ℝ) ≠ 1 := by_norm_num
  unfold emD emitG Brute.emitR
  rcases lt_trichotomy a.2 v.2 with ha | ha | ha <;>
    rcases lt_trichotomy b.2 v.2 with hb | hb | hb
  · grind
  · grind
  · grind
  · grind
  · simp_all
  · grind
  · grind
  · grind
  grind

/-! ## The program -/

/-- The nine tests. -/
def testsS : Stmt :=
  .seq (tstR 1 212060 212063 212063 212071) (.seq (tstR 1 212063 212060 212063 212072)
    (.seq (tstR 1 212066 212063 212063 212073) (.seq (tstR 1 212063 212066 212063 212074)
      (.seq (tstR 2 212060 212063 212066 212075) (.seq (tstR 0 212063 212060 212063 212076)
        (.seq (tstR 0 212060 212063 212063 212077) (.seq (tstR 0 212066 212063 212063 212078)
          (tstR 0 212063 212066 212063 212079))))))))

/-- Set the two answers to constants. -/
def setE (v0 v1 : ℕ) : Stmt := block [.constN 212084 v0, .constN 212085 v1]

/-- **The decision tree** on the bits `212071 … 212079` (`emD`). -/
def decideS : Stmt :=
  .seq (block [.addN 212082 212071 212072, .addN 212083 212073 212074])
    (.ifLtN 212001 212082
      -- `a` not at the height of `v`
      (.ifLtN 212001 212083
        (.ifLtN 212072 212074 ztjpm
          (.ifLtN 212074 212072 ztjpm
            (block [.subN 212084 212000 212075, .subN 212085 212000 212075])))
        (.ifLtN 212001 212072 (block [.copyN 212084 212078, .constN 212085 0])
          (block [.constN 212084 0, .copyN 212085 212079])))
      -- `a` at the height of `v`
      (.ifLtN 212001 212083
        (.ifLtN 212001 212074 (block [.constN 212084 0, .copyN 212085 212076])
          (block [.copyN 212084 212077, .constN 212085 0]))
        (setE 0 0)))

/-- **The corner test.** -/
def cornerS : Stmt := .seq testsS decideS

/-- The registers `cornerS` writes. -/
def Bcor (r : ℕ) : Bool := Bk r || decide (212071 ≤ r ∧ r ≤ 212085)
section exec
variable {P : Polygon} {W : ℕ}
theorem bt_cor {d : ℕ} (hd : 212071 ≤ d ∧ d ≤ 212085) (r : ℕ) (h : Brute.Bt d r = true) :
    Bcor r = true := by
  unfold Brute.Bt at h; unfold Bcor
  grind
theorem wr_decideS : wr (fun r => decide ztgym) decideS = true := by_decide
set_option maxHeartbeats 4000000 in
/-- **The nine tests.** -/
theorem testsS_exec (hG : GoodEnv P) (hW : P.n + 3 ≤ W) (c : Config) (hw : WordsBounded W c)
    {sa sv sb : SymPt} (ia : SymPtIn c 212060 sa) (iv : SymPtIn c 212063 sv)
    (ib : SymPtIn c 212066 sb) (la : sa.Lt P.n) (lv : sv.Lt P.n) (lb : sb.Lt P.n) :
    ∃ c' k, Exec P W testsS c c' k ∧ k ≤ 9 * 245 ∧ FrameB Bcor c c' ∧
      (∀ r, 212071 ≤ r → r ≤ 212079 → c'.nreg r ≤ 1) ∧
      (c'.nreg 212071 = 1 ↔ (sa.eval zta).2 < (sv.eval zta).2) ∧
      (c'.nreg 212072 = 1 ↔ (sv.eval zta).2 < (sa.eval zta).2) ∧
      (c'.nreg 212073 = 1 ↔ (sb.eval zta).2 < (sv.eval zta).2) ∧
      (c'.nreg 212074 = 1 ↔ (sv.eval zta).2 < (sb.eval zta).2) ∧
      (c'.nreg 212075 = 1 ↔ 0 < det ztxhi ztzhg ztxoq) ∧
      (c'.nreg 212076 = 1 ↔ (sv.eval zta).1 < (sa.eval zta).1) ∧
      (c'.nreg 212077 = 1 ↔ (sa.eval zta).1 < (sv.eval zta).1) ∧
      (c'.nreg 212078 = 1 ↔ (sb.eval zta).1 < (sv.eval zta).1) ∧
      (c'.nreg 212079 = 1 ↔ (sv.eval zta).1 < (sb.eval zta).1) := by
  have oa : OutK 212060 := Or.inr by_norm_num
  have ov : OutK 212063 := Or.inr by_norm_num
  have ob : OutK 212066 := Or.inr by_norm_num
  -- a test keeps the three triples and the earlier bits
  have keep : ∀ {d : ℕ} {c₁ c₂ : Config}, 212071 ≤ d → d ≤ 212079 → FrameB ztpwk c₁ c₂ →
      ∀ r, ztcu → r ≠ d → c₂.nreg r = c₁.nreg r := by
    intro d c₁ c₂ _ _ f r hr hrd
    zuhiw

  have tr : ∀ {c₁ c₂ : Config} {x : ℕ} {s : SymPt}, SymPtIn c₁ x s → x = 212060 ∨ x = 212063 ∨
      x = 212066 → (∀ r, 212060 ≤ r → r < 212069 → c₂.nreg r = c₁.nreg r) → SymPtIn c₂ x s := by
    intro c₁ c₂ x s h hx hr
    exact symPtIn_of_eq h by_grind
  obtain ⟨c₁, k₁, e₁, hk₁, f₁, b₁, t₁⟩ := tstR_exec (P := P) hG hW (op := 1) by_norm_num
    (d := 212071) oa ov ov c hw ia iv iv la lv lv
  have g₁ := keep by_norm_num by_norm_num f₁
  have tr₁ : ∀ {x : ℕ} {s : SymPt}, SymPtIn c x s → x = 212060 ∨ x = 212063 ∨ x = 212066 →
      SymPtIn c₁ x s := by_grind
  obtain ⟨c₂, k₂, e₂, hk₂, f₂, b₂, t₂⟩ := tstR_exec (P := P) hG hW (op := 1) by_norm_num
    (d := 212072) ov oa ov c₁ e₁.wb_right ztucb (tr₁ ia by_norm_num)
    ztucb lv la lv
  have g₂ := keep by_norm_num by_norm_num f₂
  have tr₂ : ∀ {x : ℕ} {s : SymPt}, SymPtIn c x s → x = 212060 ∨ x = 212063 ∨ x = 212066 →
      SymPtIn c₂ x s := fun h hx => tr by_grind hx fun r h1 h2 => g₂ r by_omega by_omega
  obtain ⟨c₃, k₃, e₃, hk₃, f₃, b₃, t₃⟩ := tstR_exec (P := P) hG hW (op := 1) by_norm_num
    (d := 212073) ob ov ov c₂ e₂.wb_right (tr₂ ib by_norm_num) ztucc
    ztucc lb lv lv
  have g₃ := keep by_norm_num by_norm_num f₃
  have tr₃ : ∀ {x : ℕ} {s : SymPt}, SymPtIn c x s → x = 212060 ∨ x = 212063 ∨ x = 212066 →
      SymPtIn c₃ x s := fun h hx => tr by_grind hx fun r h1 h2 => g₃ r by_omega by_omega
  obtain ⟨c₄, k₄, e₄, hk₄, f₄, b₄, t₄⟩ := tstR_exec (P := P) hG hW (op := 1) by_norm_num
    (d := 212074) ov ob ov c₃ e₃.wb_right ztucd (tr₃ ib by_norm_num)
    ztucd lv lb lv
  have g₄ := keep by_norm_num by_norm_num f₄
  have tr₄ : ∀ {x : ℕ} {s : SymPt}, SymPtIn c x s → x = 212060 ∨ x = 212063 ∨ x = 212066 →
      SymPtIn c₄ x s := fun h hx => tr by_grind hx fun r h1 h2 => g₄ r by_omega by_omega
  obtain ⟨c₅, k₅, e₅, hk₅, f₅, b₅, t₅⟩ := tstR_exec (P := P) hG hW (op := 2) by_norm_num
    (d := 212075) oa ov ob c₄ e₄.wb_right (tr₄ ia by_norm_num) (tr₄ iv by_norm_num)
    (tr₄ ib by_norm_num) la lv lb
  have g₅ := keep by_norm_num by_norm_num f₅
  have tr₅ : ∀ {x : ℕ} {s : SymPt}, SymPtIn c x s → x = 212060 ∨ x = 212063 ∨ x = 212066 →
      SymPtIn c₅ x s := fun h hx => tr by_grind hx fun r h1 h2 => g₅ r by_omega by_omega
  obtain ⟨c₆, k₆, e₆, hk₆, f₆, b₆, t₆⟩ := tstR_exec (P := P) hG hW (op := 0) by_norm_num
    (d := 212076) ov oa ov c₅ e₅.wb_right ztuce (tr₅ ia by_norm_num)
    ztuce lv la lv
  have g₆ := keep by_norm_num by_norm_num f₆
  have tr₆ : ∀ {x : ℕ} {s : SymPt}, SymPtIn c x s → x = 212060 ∨ x = 212063 ∨ x = 212066 →
      SymPtIn c₆ x s := fun h hx => tr by_grind hx fun r h1 h2 => g₆ r by_omega by_omega
  obtain ⟨c₇, k₇, e₇, hk₇, f₇, b₇, t₇⟩ := tstR_exec (P := P) hG hW (op := 0) by_norm_num
    (d := 212077) oa ov ov c₆ e₆.wb_right (tr₆ ia by_norm_num) ztucf
    ztucf la lv lv
  have g₇ := keep by_norm_num by_norm_num f₇
  have tr₇ : ∀ {x : ℕ} {s : SymPt}, SymPtIn c x s → x = 212060 ∨ x = 212063 ∨ x = 212066 →
      SymPtIn c₇ x s := fun h hx => tr by_grind hx fun r h1 h2 => g₇ r by_omega by_omega
  obtain ⟨c₈, k₈, e₈, hk₈, f₈, b₈, t₈⟩ := tstR_exec (P := P) hG hW (op := 0) by_norm_num
    (d := 212078) ob ov ov c₇ e₇.wb_right (tr₇ ib by_norm_num) ztucg
    ztucg lb lv lv
  have g₈ := keep by_norm_num by_norm_num f₈
  have tr₈ : ∀ {x : ℕ} {s : SymPt}, SymPtIn c x s → x = 212060 ∨ x = 212063 ∨ x = 212066 →
      SymPtIn c₈ x s := fun h hx => tr (tr₇ h hx) hx by_grind
  obtain ⟨c₉, k₉, e₉, hk₉, f₉, b₉, t₉⟩ := tstR_exec (P := P) hG hW (op := 0) by_norm_num
    (d := 212079) ov ob ov c₈ e₈.wb_right ztuch (tr₈ ib by_norm_num)
    ztuch lv lb lv
  have g₉ := keep by_norm_num by_norm_num f₉
  -- the bits survive the later tests
  have v1 : c₉.nreg 212071 = c₁.nreg 212071 := by
    rw [g₉ _ by_norm_num by_norm_num, g₈ _ by_norm_num by_norm_num,
      g₇ _ by_norm_num by_norm_num, g₆ _ by_norm_num by_norm_num,
      g₅ _ by_norm_num by_norm_num, g₄ _ by_norm_num by_norm_num,
      g₃ _ by_norm_num by_norm_num, g₂ _ by_norm_num by_norm_num]
  have v2 : c₉.nreg 212072 = c₂.nreg 212072 := by
    rw [g₉ _ by_norm_num by_norm_num, g₈ _ by_norm_num by_norm_num,
      g₇ _ by_norm_num by_norm_num, g₆ _ by_norm_num by_norm_num,
      g₅ _ by_norm_num by_norm_num, g₄ _ by_norm_num by_norm_num,
      g₃ _ by_norm_num by_norm_num]
  have v3 : c₉.nreg 212073 = c₃.nreg 212073 := by
    rw [g₉ _ by_norm_num by_norm_num, g₈ _ by_norm_num by_norm_num,
      g₇ _ by_norm_num by_norm_num, g₆ _ by_norm_num by_norm_num,
      g₅ _ by_norm_num by_norm_num, g₄ _ by_norm_num by_norm_num]
  have v4 : c₉.nreg 212074 = c₄.nreg 212074 := by
    rw [g₉ _ by_norm_num by_norm_num, g₈ _ by_norm_num by_norm_num,
      g₇ _ by_norm_num by_norm_num, g₆ _ by_norm_num by_norm_num,
      g₅ _ by_norm_num by_norm_num]
  have v5 : c₉.nreg 212075 = c₅.nreg 212075 := by
    rw [g₉ _ by_norm_num by_norm_num, g₈ _ by_norm_num by_norm_num,
      g₇ _ by_norm_num by_norm_num, g₆ _ by_norm_num by_norm_num]
  have v6 : c₉.nreg 212076 = c₆.nreg 212076 := by
    rw [g₉ _ by_norm_num by_norm_num, g₈ _ by_norm_num by_norm_num,
      g₇ _ by_norm_num by_norm_num]
  have v7 : c₉.nreg 212077 = c₇.nreg 212077 := by
    rw [g₉ _ by_norm_num by_norm_num, g₈ _ by_norm_num by_norm_num]
  have v8 : c₉.nreg 212078 = c₈.nreg 212078 := by
    grind
  have hf : FrameB Bcor c c₉ := by
    have hh : ∀ {d : ℕ} {c₁ c₂ : Config}, 212071 ≤ d ∧ d ≤ 212085 → FrameB _ c₁ c₂ →
        FrameB Bcor c₁ c₂ := fun hd f => fbMono f (bt_cor hd)
    exact fbTrans (fbTrans (fbTrans (fbTrans (fbTrans (fbTrans (fbTrans (fbTrans
      (hh by_norm_num f₁) (hh by_norm_num f₂)) (hh by_norm_num f₃)) (hh by_norm_num f₄))
      (hh by_norm_num f₅)) (hh by_norm_num f₆)) (hh by_norm_num f₇)) (hh by_norm_num f₈))
      (hh by_norm_num f₉)
  refine ⟨c₉, k₁ + (k₂ + (k₃ + (k₄ + (k₅ + (k₆ + ztock))))),
    .seq e₁ ztqr,
    by omega, hf, ?_, by rw [v1]; exact t₁, by rw [v2]; exact t₂, by zunrr; exact t₃,
    by rw [v4]; exact t₄, by rw [v5]; exact t₅, by rw [v6]; exact t₆, by zuouq; exact t₇,
    by zuour; exact t₈, t₉⟩
  zucxf
  interval_cases r
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  omega

/-- The value of a bit. -/
def bv (b : Bool) : ℕ := if b then 1 else 0
theorem bv_le (b : Bool) : bv b ≤ 1 := by unfold bv; grind
theorem bv_eq_one (b : Bool) : bv b = 1 ↔ b = true := by unfold bv; simp

/-- A test bit as a Boolean. -/
theorem bv_of_bit {n : ℕ} (h : n ≤ 1) : n = bv (decide (n = 1)) := by
  unfold bv; grind
set_option maxHeartbeats 4000000 in
/-- **The decision tree.** -/
theorem decideS_exec (c : Config) (hw : WordsBounded W c) (hW : 2 ≤ W)
    {A1 A2 B1 B2 D X1 X2 X3 X4 : Bool}
    (c0 : c.nreg 212000 = 1) (c1 : c.nreg 212001 = 0)
    (h1 : c.nreg 212071 = bv A1) (h2 : c.nreg 212072 = bv A2) (h3 : c.nreg 212073 = bv B1)
    (h4 : c.nreg 212074 = bv B2) (h5 : c.nreg 212075 = bv D) (h6 : c.nreg 212076 = bv X1)
    (h7 : c.nreg 212077 = bv X2) (h8 : c.nreg 212078 = bv X3) (h9 : c.nreg 212079 = bv X4) :
    ∃ c' k, Exec P W decideS c c' k ∧ k ≤ 12 ∧
      c'.nreg 212084 = bv (emD A1 A2 B1 B2 D X1 X2 X3 X4).1 ∧
      c'.nreg 212085 = bv (emD A1 A2 B1 B2 D X1 X2 X3 X4).2 ∧
      FrameB (fun r => decide (212082 ≤ r ∧ r ≤ 212085)) c c' := by
  obtain ⟨c', k, ex, hk, q1, q2⟩ : ∃ c' k, Exec P W decideS c c' k ∧ k ≤ 12 ∧
      c'.nreg 212084 = bv (emD A1 A2 B1 B2 D X1 X2 X3 X4).1 ∧
      c'.nreg 212085 = bv (emD A1 A2 B1 B2 D X1 X2 X3 X4).2 := by
    unfold decideS
    refine spec_seq ?_
    exec_block
    · zvmza; have := bv_le A1; have := bv_le A2; omega
    · config_simp; rw [h3, h4]; have := bv_le B1; have := bv_le B2; omega
    · cases A1 <;> cases A2 <;> cases B1 <;> cases B2 <;>
        simp only [bv, ite_true, ite_false, Bool.false_eq_true] at h1 h2 h3 h4 ⊢ <;>
        (repeat (first
          | refine spec_ifLtN_true (by config_simp; simp only [h1, h2, h3, h4, c1]; omega) ?_
          | refine spec_ifLtN_false (by config_simp; linarith) ?_)) <;>
        (try unfold setE) <;> exec_block <;> (try omega) <;>
        refine ztss <;> config_simp <;>
        (try simp only [c0, h5, h6, h7, h8, h9]) <;>
        cases D <;> cases X1 <;> cases X2 <;> cases X3 <;> cases X4 <;> simp [emD, bv, h3]
  exact ⟨c', k, ex, hk, q1, q2, exec_frameB ex wr_decideS⟩
theorem bcor_dec (r : ℕ) (h : decide ztgym = true) : Bcor r = true := by
  simp only [Bcor, Bool.or_eq_true, decide_eq_true_eq] at h ⊢; omega
set_option maxHeartbeats 2000000 in
/-- **The corner test** (at most `2300` steps). -/
theorem cornerS_exec (hG : GoodEnv P) (hW : P.n + 3 ≤ W) (c : Config) (hw : WordsBounded W c)
    {sa sv sb : SymPt} (ia : SymPtIn c 212060 sa) (iv : SymPtIn c 212063 sv)
    (ib : SymPtIn c 212066 sb) (la : sa.Lt P.n) (lv : sv.Lt P.n) (lb : sb.Lt P.n)
    (c0 : c.nreg 212000 = 1) (c1 : c.nreg 212001 = 0) :
    ∃ c' k, Exec P W cornerS c c' k ∧ k ≤ 2300 ∧ FrameB Bcor c c' ∧
      c'.nreg 212084 ≤ 1 ∧ c'.nreg 212085 ≤ 1 ∧
      (c'.nreg 212084 = 1 ↔ emitG ztxhi ztzhg ztxoq 1) ∧
      (c'.nreg 212085 = 1 ↔ emitG ztxhi ztzhg ztxoq (-1)) := by
  obtain ⟨c₁, k₁, e₁, hk₁, f₁, hb, t1, t2, t3, t4, t5, t6, t7, t8, t9⟩ :=
    testsS_exec (P := P) hG hW c hw ia iv ib la lv lb
  zuefw
  have c1' : ztuqe := by rw [f₁.1 _ by_decide, c1]
  obtain ⟨c₂, k₂, e₂, hk₂, q1, q2, f₂⟩ := decideS_exec (P := P) c₁ e₁.wb_right by_omega c0' c1'
    (bv_of_bit (hb 212071 by_norm_num by_norm_num))
    (bv_of_bit (hb 212072 by_norm_num by_norm_num))
    (bv_of_bit (hb 212073 by_norm_num by_norm_num))
    (bv_of_bit (hb 212074 by_norm_num by_norm_num))
    (bv_of_bit (hb 212075 by_norm_num by_norm_num))
    (bv_of_bit (hb 212076 by_norm_num by_norm_num))
    (bv_of_bit (hb 212077 by_norm_num by_norm_num))
    (bv_of_bit (hb 212078 by_norm_num by_norm_num))
    (bv_of_bit (hb 212079 by_norm_num by_norm_num))
  obtain ⟨m1, m2⟩ := emD_iff (a := sa.eval zta) (v := sv.eval zta) (b := sb.eval zta)
    (A1 := decide (c₁.nreg 212071 = 1)) (A2 := decide (c₁.nreg 212072 = 1))
    (B1 := decide (c₁.nreg 212073 = 1)) (B2 := decide (c₁.nreg 212074 = 1))
    (D := decide (c₁.nreg 212075 = 1)) (X1 := decide (c₁.nreg 212076 = 1))
    (X2 := decide (c₁.nreg 212077 = 1)) (X3 := decide (c₁.nreg 212078 = 1))
    (X4 := decide (c₁.nreg 212079 = 1))
    by_simp_all by_simp_all
    by_simp_all by_simp_all
    by_simp_all by_simp_all
    by_simp_all by_simp_all
    by_simp_all
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by_omega, fbTrans f₁ (fbMono f₂ bcor_dec),
    by zunrs; exact bv_le _, by rw [q2]; exact bv_le _, ?_, ?_⟩
  · rw [q1, bv_eq_one]; exact m1
  · rw [q2, bv_eq_one]; exact m2
end exec
end
end DrvB
end Chazelle.Core
namespace Chazelle.Core
namespace OracleR
open Machine Machine.Stmt Programs SignK SearchR WalkKey
@[expose] public section
def tsInit (rT rL : ℕ) : Stmt :=
  block [.constN 50106 1, .copyN 50109 rT, .constN 50105 0, .constN 50115 0, .copyN 50112 rL]

/-- **The search with a stored table.** -/
def tsearch (rT rL : ℕ) (cmp : Stmt) : Stmt := .seq (tsInit rT rL) ztqtb

/-- **The search with a stored table.**  From a configuration satisfying `J` with the items
`lr 104 = n` at `lr 103` (below the table), the table of the powers `2 ^ j`, `j < L`, at `T`
(`n < 2 ^ L`), the search leaves the partition point `t ≤ n` in `lr 105`. -/
theorem tsearch_exec {P : Polygon} {W : ℕ} {cmp : Stmt} {Bc : Finset ℕ} {J : Config → Prop}
    {pr : ℕ → Bool} {κ : ℕ} (hcmp : PredOK P W cmp Bc J pr κ) (hB : bLocate ∉ Bc)
    {rT rL T L : ℕ} (hrT5 : bandOf rT ≠ bLocate) (hrL5 : bandOf rL ≠ bLocate)
    {c : Config} (hw : WordsBounded W c) (hJ : J c) (hJs : JStableL J T)
    (hrT : c.nreg rT = T) (hrL : c.nreg rL = L) (htab : ∀ j, j < L → c.nmem ztnps = 2 ^ j)
    (hbig : c.nreg 50104 < 2 ^ L) (hA : c.nreg 50103 + c.nreg 50104 ≤ T) (hTW : T + L ≤ W)
    (hmono : ∀ i j, i ≤ j → j < c.nreg 50104 → pr ztequ = true →
      pr ztnwq = true) (hW1 : 1 ≤ W) :
    ∃ c' k, Exec P W (tsearch rT rL cmp) c c' k ∧ k ≤ zthlp * L + 7 ∧ J c' ∧
      LocL Bc T c c' ∧ c'.nmem = c.nmem ∧ c'.nreg ALLOC = c.nreg ALLOC ∧
      c'.nreg 50105 ≤ c.nreg 50104 ∧
      ztxsn ∧
      (c'.nreg 50105 < c.nreg 50104 → pr (c.nmem (c.nreg 50103 + c'.nreg 50105)) = false) := by
  zuemw

  have hr5 := bandOf_loc hrT5
  have hl5 := bandOf_loc hrL5
  obtain ⟨c₁, k₁, e₁, hk₁, q⟩ : ∃ c₁ k₁, Exec P W (tsInit rT rL) c c₁ k₁ ∧ k₁ = 5 ∧
      (c₁.nreg 50106 = 1 ∧ c₁.nreg 50109 = T ∧ c₁.nreg 50105 = 0 ∧ c₁.nreg 50115 = 0 ∧
        c₁.nreg 50112 = L ∧
        (∀ r, r ≠ 50106 → r ≠ 50109 → r ≠ 50105 → r ≠ 50115 → r ≠ 50112 → c₁.nreg r = c.nreg r) ∧
        c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output) := by
    unfold tsInit
    exec_block
    · omega
    · omega
    · omega
    · refine ⟨rfl, by config_simp, ?_, by config_simp, by config_simp, ?_, fun r h1 h2 h3 h4 h5 => ?_,
        rfl, rfl, rfl, rfl⟩
      · config_simp; ((try simp only [Machine.upd_apply]); (repeat' split_ifs) <;>
          first | omega)
      · config_simp; ((try simp only [Machine.upd_apply]); (repeat' split_ifs) <;>
          first | omega)
      simp_all
  obtain ⟨o₁, t₁, s₁, z₁, i₁, r₁, m₁, rr₁, rm₁, out₁⟩ := q
  have sl₁ : SLL T c c₁ := ⟨fun r hb _ => by
      have := bandOf_loc hb
      exact r₁ r by_omega by_omega by_omega by_omega by_omega,
    rr₁, by_simp_all, rm₁, out₁⟩
  have I₁ : LiftInv W J Bc T c c₁ pr A n L c₁ :=
    { wb := e₁.wb_right, hJ := hJs c c₁ hJ sl₁.1 sl₁.2.1 sl₁.2.2.1 sl₁.2.2.2.1 sl₁.2.2.2.2,
      loc := (LocL.refl Bc T c).sl sl₁,
      rA := by_grind,
      rn := by_grind,
      one := o₁, rT := t₁, zero := z₁, mem := rfl, alloc := rfl, iL := by rw [i₁],
      posn := by_omega, tab := by_simp_all,
      bA := hA, bT := hTW, pre := by_grind,
      post := by_grind }
  obtain ⟨c₂, k₂, e₂, I₂, hk₂, hfin⟩ := liftLoop_inv (P := P) hcmp hJs hB hmono I₁
  rw [i₁] at hk₂
  refine ⟨c₂, _, .seq e₁ e₂, by_omega, I₂.hJ, I₂.loc, by rw [I₂.mem, m₁], ?_, I₂.posn, I₂.pre,
    hfin⟩
  rw [I₂.alloc, r₁ _ by_decide by_decide by_decide by_decide by_decide]

/-! ## The search predicate on the chords -/
section Chord
variable (m : ℕ → ℕ) (V : QV)

/-- The height vertex of chord record `i`. -/
def chH (i : ℕ) : ℕ := m (V.CB + 5 * i)
/-- The walk edge of the left end of chord record `i`. -/
def chL (i : ℕ) : ℕ := m (V.CB + 5 * i + 1)
/-- The walk edge of the right end of chord record `i`. -/
def chR (i : ℕ) : ℕ := m (V.CB + 5 * i + 2)
/-- The chord at position `q` of the sorted chord table. -/
def chAt (q : ℕ) : ℕ := m ztjnm
end Chord
open Classical in
/-- **The search predicate** on the chord record `i`: below the height of the ray, or at it and
before the origin (the right end not ahead, rightwards; the left end behind, leftwards). -/
noncomputable def chPr (P : Polygon) (C : Chain) (V : QV) (m : ℕ → ℕ) (i : ℕ) : Bool :=
  decide (i < V.K ∧ (chH m V i < V.hz ∨ (chH m V i = V.hz ∧
    (if V.σb = 1 then ¬ EndGtZ P C V ztbrg V.hz else EndLtZ P C V ztbdb V.hz))))

/-- **The search predicate procedure** (item in `lr 100`, bit in `lr 102`). -/
def chordPr : Stmt :=
  .ifLtN 50100 120039
    (.seq (t5 120130 50100 120043)
      (.seq (block [.loadN 120131 120130, .addN 120130 120130 120011, .loadN 120132 120130,
          .addN 120130 120130 120011, .loadN 120133 120130])
        (.ifLtN 120131 120023 ztouc
          (.ifLtN 120023 120131 ztcyo
            (.ifLtN 120024 120011
              (.seq (block [.copyN 120120 120132, .copyN 120121 120023])
                (.seq ltZS (.instr (.copyN 50102 120128))))
              (.seq (block [.copyN 120120 120133, .copyN 120121 120023])
                (.seq gtZS (.instr (.subN 50102 120011 120128)))))))))
    ztcyo

/-- The registers written by `chordPr`. -/
def BP (r : ℕ) : Bool := BX2 r || decide (120120 ≤ r ∧ r ≤ 120133) || decide zttxt
theorem wr_chordPr : wr BP chordPr = true := by_decide

/-- The invariant of the chord search: the constants, and the memory below the table. -/
def ChJ (P : Polygon) (V : QV) (T : ℕ) (m₀ : ℕ → ℕ) (c : Config) : Prop :=
  QConst P V c ∧ ∀ a, a < T → c.nmem a = m₀ a
theorem chJ_stable (P : Polygon) (V : QV) (T : ℕ) (m₀ : ℕ → ℕ) : JStableL ztpwt T := by
  zuhgf
  refine ⟨h.1.congr fun r h1 h2 => hr r ?_ ztu, fun a ha => (hm a ha).trans (h.2 a ha)⟩
  zulue
theorem BP_band (r : ℕ) (h : BP r = true) : bandOf r = bSign ∨ bandOf r = bOQuery ∨ r = 50102 := by
  simp only [BP, BX2, Bk, Bool.or_eq_true, decide_eq_true_eq] at h
  unfold bandOf bSign bOQuery
  omega
open Classical in
/-- **The search predicate procedure meets the contract of the binary search.** -/
theorem chordPr_ok {P : Polygon} {W : ℕ} (hG : GoodEnv P) (hW : 8 * P.n + 32 ≤ W) {C : Chain}
    {V : QV} (hv : QVOK P C V) (htv : V.tv < P.n) {T : ℕ} {m₀ : ℕ → ℕ}
    (hKT : ∀ i, i < V.K → V.CB + 5 * i + 2 < T) (hTW : T ≤ W) :
    PredOK P W chordPr {bSign, bOQuery} ztpwt (chPr P C V m₀) 700 := by
  intro c hw ⟨hq, hm⟩
  suffices H : ∃ c' k, Exec P W chordPr c c' k ∧ k ≤ 700 ∧
      c'.nreg 50102 = (if chPr P C V m₀ _ then 1 else 0) by
    obtain ⟨c', k, ex, hk, hv'⟩ := H
    have fb := exec_frameB ex wr_chordPr
    have hBP : ∀ r, BP r = true → bandOf r ∈ ({bSign, bOQuery} : Finset ℕ) ∨ r = 50102 := by
      zuz
      rcases BP_band r hr with h | h | h
      · simp_all
      · simp_all
      omega
    refine ⟨c', k, ex, hk, ⟨hq.frame fb fun r h1 h2 => ?_, fun a ha => by zuodf; simp_all⟩,
      hv', fun r h1 h2 h3 h4 => fb.1 r ?_, fun r h1 => exec_rframe ex (B := Bk) by_decide r ?_,
      fb.2.2.1, fb.2.2.2.1, fb.2.2.2.2⟩
    · simp only [BP, BX2, Bk, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega
    · zukr
      zujni
      rcases hBP r hc with h | h
      · rcases h4 with h4 | h4
        · simp_all
        · subst h4; tauto
      omega
    · zukr
      zujni
      apply h1
      have : ztiyx := by
        simp only [Bk, decide_eq_true_eq] at hc; unfold bandOf bSign; omega
      simp_all
  obtain ⟨i, hi⟩ : ∃ i, c.nreg 50100 = i := by_simp_all
  zumni
  by_cases hiK : i < V.K
  swap
  · obtain ⟨c₁, e₁, v₁, -⟩ := const_exec hw 50102 0 by_omega
    refine ⟨c₁, _, .ifLtN_false ztcme e₁, by_omega, ?_⟩
    rw [v₁]; unfold chPr; simp_all
  have haddr := hKT i hiK
  -- read the record
  obtain ⟨c₁, e₁, v₁, r₁, m₁, -, -, -⟩ := t5_exec (P := P) (rd := 120130) (rs := 50100) (rb := 120043)
    by_decide by_decide c hw (by rw [hi, hq.CB]; omega)
  rw [hi, hq.CB] at v₁
  obtain ⟨c₂, k₂, e₂, hk₂, v₂⟩ : ∃ c₂ k₂, Exec P W (block [.loadN 120131 120130,
      .addN 120130 120130 120011, .loadN 120132 120130, .addN 120130 120130 120011,
      .loadN 120133 120130]) c₁ c₂ k₂ ∧ k₂ = 5 ∧
      (c₂.nreg 120131 = chH m₀ V i ∧ c₂.nreg 120132 = chL m₀ V i ∧ c₂.nreg 120133 = chR m₀ V i ∧
        (∀ r, r < 120130 ∨ 120133 < r → c₂.nreg r = c₁.nreg r) ∧ c₂.nmem = c₁.nmem) := by
    zud
    have one₁ : ztdxr := by rw [r₁ _ by_decide, hq.one]
    exec_block
    · config_simp; omega
    · config_simp; omega
    · refine ⟨rfl, ?_, ?_, ?_, fun r hr => ?_, rfl⟩
      · config_simp; rw [v₁, m₁, hm _ by_omega]; rfl
      · config_simp; rw [v₁, one₁, m₁, hm _ by_omega]; rfl
      · config_simp; rw [v₁, one₁, m₁, hm _ by_omega]; rfl
      · config_simp; upd_solve
  obtain ⟨x131, x132, x133, r₂, m₂⟩ := v₂
  zuesb
  have ex₀ : ztpjk := .seq e₁ e₂
  have hpr : chPr P C V m₀ i = decide (chH m₀ V i < V.hz ∨ (chH m₀ V i = V.hz ∧
      (if V.σb = 1 then ¬ EndGtZ P C V (chR m₀ V i) V.hz else EndLtZ P C V (chL m₀ V i) V.hz))) := by
    unfold chPr; simp_all
  rw [hpr]
  zue
  by_cases hlt : chH m₀ V i < V.hz
  · obtain ⟨c₃, e₃, v₃, -⟩ := const_exec w₂ 50102 1 by_omega
    refine ⟨c₃, _, .ifLtN_true ztcme (.seq e₁ (.seq e₂
      (.ifLtN_true ztbmj e₃))), by_omega, ?_⟩
    simp_all
  by_cases hgt : V.hz < chH m₀ V i
  · obtain ⟨c₃, e₃, v₃, -⟩ := const_exec w₂ 50102 0 by_omega
    refine ⟨c₃, _, .ifLtN_true ztcme (.seq e₁ (.seq e₂
      (.ifLtN_false ztbmj (.ifLtN_true ztbmj
        e₃)))), by_omega, ?_⟩
    grind
  have heq : chH m₀ V i = V.hz := by_omega
  zudmj
  · -- leftwards: the left end is behind
    obtain ⟨c₃, k₃, e₃, hk₃, v₃⟩ : ∃ c₃ k₃, Exec P W (block [.copyN 120120 120132,
        .copyN 120121 120023]) c₂ c₃ k₃ ∧ k₃ = 2 ∧ (c₃.nreg 120120 = chL m₀ V i ∧
          c₃.nreg 120121 = V.hz ∧ ∀ r, r ≠ 120120 → r ≠ 120121 → c₃.nreg r = c₂.nreg r) := by
      exec_block
      exact ⟨rfl, by_simp_all, by config_simp; exact hq₂.hz,
        by simp_all⟩
    zubeb

    obtain ⟨c₄, k₄, e₄, hk₄, f₄, b₄, g₄⟩ := ltZS_exec hG by_omega hv htv c₃ e₃.wb_right hq₃
      ztdyz
    obtain ⟨c₅, e₅, v₅, -⟩ := copy_exec e₄.wb_right 50102 120128
    refine ⟨c₅, _, .ifLtN_true ztcme (.seq e₁ (.seq e₂
      (.ifLtN_false ztbmj (.ifLtN_false ztbmj
        (.ifLtN_true ztktt ztbpd))))), by_omega, ?_⟩
    grind
  · -- rightwards: the right end is not ahead
    obtain ⟨c₃, k₃, e₃, hk₃, v₃⟩ : ∃ c₃ k₃, Exec P W (block [.copyN 120120 120133,
        .copyN 120121 120023]) c₂ c₃ k₃ ∧ k₃ = 2 ∧ (c₃.nreg 120120 = chR m₀ V i ∧
          c₃.nreg 120121 = V.hz ∧ ∀ r, r ≠ 120120 → r ≠ 120121 → c₃.nreg r = c₂.nreg r) := by
      exec_block
      exact ⟨rfl, by_simp_all, by config_simp; exact hq₂.hz,
        by simp_all⟩
    zubeb

    obtain ⟨c₄, k₄, e₄, hk₄, f₄, b₄, g₄⟩ := gtZS_exec hG by_omega hv htv c₃ e₃.wb_right hq₃
      ztdyz
    have one₄ : ztpnq := by
      rw [f₄.1 _ by_decide, r₃ _ by_decide by_decide, hq₂.one]
    zucc
    obtain ⟨c₅, e₅, v₅, -⟩ : ∃ c₅, Exec P W (.instr (.subN 50102 120011 120128)) c₄ c₅ 1 ∧
        c₅.nreg 50102 = c₄.nreg 120011 - c₄.nreg 120128 ∧ True :=
      ⟨_, Exec.subN w₄ _ _ _, by config_simp, trivial⟩
    refine ⟨c₅, _, .ifLtN_true ztcme (.seq e₁ (.seq e₂
      (.ifLtN_false ztbmj (.ifLtN_false ztbmj
        (.ifLtN_false ztktt ztbpd))))), by_omega, ?_⟩
    rw [v₅, one₄, x120, x121] at *
    zuesr
    grind
end
end OracleR
end Chazelle.Core
namespace Chazelle.Core
namespace OracleR
open Machine Machine.Stmt Programs SignK SearchR WalkKey
open OracleQ
@[expose] public section
def chordSearchS : Stmt :=
  .seq (block [.copyN 50103 120038, .copyN 50104 120039]) (tsearch 120041 120042 chordPr)

/-- The registers written by `chordSearchS`. -/
def BCS (r : ℕ) : Bool := BP r || decide ztgzf
theorem wr_chordSearchS : wr BCS chordSearchS = true := by_decide

/-- **The memory facts of the chord search.** -/
structure ChordMemOK (V : QV) (m : ℕ → ℕ) (W : ℕ) : Prop where
  tab : ∀ j, j < V.L → m ztnqe = 2 ^ j
  K_lt : V.K < 2 ^ V.L
  CH_le : V.CH + V.K ≤ V.TB
  TB_le : V.TB + V.L ≤ W
  recs : ∀ i, i < V.K → V.CB + 5 * i + 2 < V.TB
open Classical in
/-- **The chord search.** -/
theorem chordSearch_exec {P : Polygon} {W : ℕ} (hG : GoodEnv P) (hW : 8 * P.n + 32 ≤ W)
    {C : Chain} {V : QV} (hv : QVOK P C V) (htv : V.tv < P.n) (c : Config)
    (hw : WordsBounded W c) (hq : QConst P V c) (hm : ChordMemOK V c.nmem W)
    (hmono : ∀ i j, i ≤ j → j < V.K → chPr P C V c.nmem zteet = true →
      chPr P C V c.nmem ztrnd = true) :
    ∃ c' k, Exec P W chordSearchS c c' k ∧ k ≤ 715 * V.L + 10 ∧ FrameB BCS c c' ∧
      c'.nreg 50105 ≤ V.K ∧
      (∀ j, j < c'.nreg 50105 → chPr P C V c.nmem zteet = true) ∧
      (c'.nreg 50105 < V.K → chPr P C V c.nmem (chAt c.nmem V (c'.nreg 50105)) = false) := by
  obtain ⟨c₁, k₁, e₁, hk₁, v₁⟩ : ∃ c₁ k₁, Exec P W (block [.copyN 50103 120038,
      .copyN 50104 120039]) c c₁ k₁ ∧ k₁ = 2 ∧ (c₁.nreg 50103 = V.CH ∧ c₁.nreg 50104 = V.K ∧
        ∀ r, r ≠ 50103 → r ≠ 50104 → c₁.nreg r = c.nreg r) ∧ c₁.nmem = c.nmem := by
    exec_block
    exact ⟨rfl, ⟨by config_simp; exact hq.CH, by config_simp; exact hq.K,
      by simp_all⟩, rfl⟩
  obtain ⟨x103, x104, r₁⟩ := v₁.1
  have m₁ := v₁.2
  have hq₁ := hq.congr fun r h1 h2 => r₁ r by_omega by_omega
  have hTW : V.TB ≤ W := by have := hm.TB_le; omega
  have hpr := chordPr_ok hG hW hv htv (m₀ := c.nmem) hm.recs hTW
  obtain ⟨c₂, k₂, e₂, hk₂, hJ₂, -, m₂, -, ht₂, hpre, hpost⟩ := tsearch_exec (P := P) hpr
    by_decide (rT := 120041) (rL := 120042) (T := V.TB) (L := V.L)
    by_decide by_decide e₁.wb_right
    ⟨hq₁, fun a _ => by zvmxn⟩ (chJ_stable P V V.TB c.nmem) hq₁.TB hq₁.L
    (fun j hj => by zvmxn; exact hm.tab j hj) (by rw [x104]; exact hm.K_lt)
    (by rw [x103, x104]; exact hm.CH_le) hm.TB_le
    (fun i j hij hj h => by
      rw [x104] at hj; rw [x103, m₁] at h ⊢; exact hmono i j hij hj h) by_omega
  rw [x104] at ht₂ hpost
  rw [x103, m₁] at hpre hpost
  refine ⟨c₂, _, .seq e₁ e₂, by_omega, exec_frameB ztyv wr_chordSearchS, ht₂,
    hpre, hpost⟩

/-! ## The chord at the ray's height next to the origin -/

/-- Read the height of the chord record in `120145` (into `120147`). -/
def readRec : Stmt := .seq (t5 120146 120145 120043) (.instr (.loadN 120147 120146))

/-- The ends of the found chord, rightwards. -/
def foundPos : Stmt := block [.constN 120140 1, .addN 120146 120146 120011, .loadN 120141 120146,
  .addN 120146 120146 120011, .loadN 120142 120146, .copyN 120120 120141, .copyN 120121 120023]

/-- The ends of the found chord, leftwards. -/
def foundNeg : Stmt := block [.constN 120140 1, .addN 120146 120146 120011, .loadN 120142 120146,
  .addN 120146 120146 120011, .loadN 120141 120146, .copyN 120120 120141, .copyN 120121 120023]

/-- The found chord, rightwards. -/
def postPos : Stmt :=
  .ifLtN 50105 120039
    (.seq (block [.addN 120144 120038 50105, .loadN 120145 120144])
      (.seq readRec
        (ifEq 120147 120023 (.seq foundPos (.seq gtZS ztgwv))
          .skip)))
    .skip

/-- The found chord, leftwards. -/
def postNeg : Stmt :=
  .ifLtN 120012 50105
    (.seq (block [.subN 120148 50105 120011, .addN 120144 120038 120148, .loadN 120145 120144])
      (.seq readRec
        (ifEq 120147 120023 (.seq foundNeg (.seq ltZS ztgwv))
          .skip)))
    .skip

/-- **The chord at the ray's height next to the origin.** -/
def chordPostS : Stmt := .seq (.instr (.constN 120140 0)) (.ifLtN 120024 120011 postNeg postPos)

/-- The registers written by `chordPostS`. -/
def BCP (r : ℕ) : Bool := BX2 r || decide ztgxo || decide (120140 ≤ r ∧ r ≤ 120148)
theorem wr_chordPostS : wr BCP chordPostS = true := by_decide
section Post
variable (P : Polygon) (C : Chain) (V : QV) (m : ℕ → ℕ) (t : ℕ)

/-- The position of the chord next to the origin in the sorted table. -/
def jCOf : ℕ := if V.σb = 1 then t else t - 1

/-- The chord next to the origin exists and lies at the ray's height. -/
def FoundC : Prop :=
  (if V.σb = 1 then t < V.K else 0 < t) ∧ chH m V ztcva = V.hz

/-- The near end of the chord next to the origin. -/
def nearC : ℕ := if V.σb = 1 then chL m V ztcva else chR m V ztcva

/-- The far end of the chord next to the origin. -/
def farC : ℕ := if V.σb = 1 then chR m V ztcva else chL m V ztcva

/-- The origin lies on the chord (its near end is not ahead). -/
def DegC : Prop :=
  ¬ (if V.σb = 1 then EndGtZ P C V ztbbb V.hz else EndLtZ P C V ztbbb V.hz)
end Post

/-- **The memory facts of the sorted chord table.** -/
structure ChordTabOK (V : QV) (m : ℕ → ℕ) (W : ℕ) : Prop where
  lt : ∀ q, q < V.K → chAt m V q < V.K
  CH_le : V.CH + V.K ≤ W
  rec_le : ∀ i, i < V.K → V.CB + 5 * i + 2 ≤ W

/-- Read the height of the chord record in `120145`. -/
theorem readRec_exec {P : Polygon} {W : ℕ} {V : QV} (c : Config) (hw : WordsBounded W c)
    (hCB : c.nreg 120043 = V.CB) {i : ℕ} (hi : c.nreg 120145 = i) (hrec : V.CB + 5 * i + 2 ≤ W) :
    ∃ c' k, Exec P W readRec c c' k ∧ k = 5 ∧ c'.nreg 120146 = V.CB + 5 * i ∧ c'.nreg 120147 = chH c.nmem V i ∧
      (∀ r, r ≠ 120146 → r ≠ 120147 → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem := by
  unfold readRec
  obtain ⟨c₁, e₁, v₁, r₁, m₁, -, -, -⟩ := t5_exec (P := P) (rd := 120146) (rs := 120145)
    (rb := 120043) by_decide by_decide c hw by_omega
  rw [hi, hCB] at v₁
  refine ⟨_, _, .seq e₁ (Exec.loadN e₁.wb_right 120147 120146), rfl, ?_, ?_, fun r h1 h2 => ?_,
    ?_⟩
  · simp_all
  · config_simp; rw [v₁, m₁]; rfl
  · simp_all
  omega

/-- The found chord's ends, rightwards. -/
theorem foundPos_exec {P : Polygon} {W : ℕ} {V : QV} (c : Config) (hw : WordsBounded W c)
    (hone : c.nreg 120011 = 1) (hhz : c.nreg 120023 = V.hz) {i : ℕ}
    (h46 : c.nreg 120146 = V.CB + 5 * i) (hrec : V.CB + 5 * i + 2 ≤ W) :
    ∃ c' k, Exec P W foundPos c c' k ∧ k = 7 ∧ c'.nreg 120140 = 1 ∧
      c'.nreg 120141 = chL c.nmem V i ∧ c'.nreg 120142 = chR c.nmem V i ∧
      c'.nreg 120120 = chL c.nmem V i ∧ c'.nreg 120121 = V.hz ∧
      (∀ r, r ≠ 120140 → r ≠ 120146 → r ≠ 120141 → r ≠ 120142 → r ≠ 120120 → r ≠ 120121 →
        c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem := by
  first | unfold foundPos
  exec_block
  · omega
  · config_simp; omega
  · simp_all
  · refine ⟨rfl, by config_simp, ?_, ?_, ?_, by_simp_all,
      by simp_all, rfl⟩
    · config_simp; rw [h46, hone]; rfl
    · config_simp; rw [h46, hone]; rfl
    · config_simp; rw [h46, hone]; rfl

/-- The found chord's ends, leftwards. -/
theorem foundNeg_exec {P : Polygon} {W : ℕ} {V : QV} (c : Config) (hw : WordsBounded W c)
    (hone : c.nreg 120011 = 1) (hhz : c.nreg 120023 = V.hz) {i : ℕ}
    (h46 : c.nreg 120146 = V.CB + 5 * i) (hrec : V.CB + 5 * i + 2 ≤ W) :
    ∃ c' k, Exec P W foundNeg c c' k ∧ k = 7 ∧ c'.nreg 120140 = 1 ∧
      c'.nreg 120141 = chR c.nmem V i ∧ c'.nreg 120142 = chL c.nmem V i ∧
      c'.nreg 120120 = chR c.nmem V i ∧ c'.nreg 120121 = V.hz ∧
      (∀ r, r ≠ 120140 → r ≠ 120146 → r ≠ 120141 → r ≠ 120142 → r ≠ 120120 → r ≠ 120121 →
        c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem := by
  first | unfold foundPos | unfold foundNeg
  exec_block
  · omega
  · config_simp; omega
  · simp_all
  · refine ⟨rfl, by config_simp, ?_, ?_, ?_, by_simp_all,
      by simp_all, rfl⟩
    · config_simp; rw [h46, hone]; rfl
    · config_simp; rw [h46, hone]; rfl
    · config_simp; rw [h46, hone]; rfl

/-- **The chord at the ray's height next to the origin.** -/
theorem chordPost_exec {P : Polygon} {W : ℕ} (hG : GoodEnv P) (hW : 8 * P.n + 32 ≤ W)
    {C : Chain} {V : QV} (hv : QVOK P C V) (htv : V.tv < P.n) (c : Config)
    (hw : WordsBounded W c) (hq : QConst P V c) (hT : ChordTabOK V c.nmem W)
    (ht : c.nreg 50105 ≤ V.K) :
    ∃ c' k, Exec P W chordPostS c c' k ∧ k ≤ 360 ∧ FrameB BCP c c' ∧ c'.nreg 120140 ≤ 1 ∧
      (c'.nreg 120140 = 1 ↔ FoundC V c.nmem ztjsb) ∧
      (FoundC V c.nmem ztjsb → c'.nreg 120141 = nearC V c.nmem ztjsb ∧
        c'.nreg 120142 = farC V c.nmem ztjsb ∧ c'.nreg 120143 ≤ 1 ∧
        (c'.nreg 120143 = 1 ↔ DegC P C V c.nmem ztjsb)) := by
  obtain ⟨t, htd⟩ : ∃ t, c.nreg 50105 = t := by_simp_all
  rw [htd] at ht ⊢
  suffices H : ∃ c' k, Exec P W chordPostS c c' k ∧ k ≤ 360 ∧ c'.nreg 120140 ≤ 1 ∧
      (c'.nreg 120140 = 1 ↔ FoundC V c.nmem t) ∧
      (FoundC V c.nmem t → c'.nreg 120141 = nearC V c.nmem t ∧ c'.nreg 120142 = farC V c.nmem t ∧
        c'.nreg 120143 ≤ 1 ∧ (c'.nreg 120143 = 1 ↔ DegC P C V c.nmem t)) by
    obtain ⟨c', k, ex, hk, h1, h2, h3⟩ := H
    exact ⟨c', k, ex, hk, exec_frameB ex wr_chordPostS, h1, h2, h3⟩
  obtain ⟨c₀, e₀, v₀, r₀⟩ := const_exec (P := P) hw 120140 0 by_omega
  have hq₀ : QConst P V c₀ := hq.congr by_grind
  have m₀ :=
    (exec_frameB e₀ (B := fun r => decide (r = 120140)) by_decide).2.2.1
  zumft
  have t₀ : c₀.nreg 50105 = t := by_simp_all
  -- the common tail: the chord at position `j`
  have tail : ∀ (pos : Bool) (j : ℕ), j < V.K → (pos = true ↔ V.σb = 1) →
      jCOf V t = j → ∀ d : Config, WordsBounded W d → QConst P V d → d.nmem = c.nmem →
      d.nreg 120140 = 0 → d.nreg 120145 = chAt c.nmem V j →
      ∃ d' k, Exec P W (.seq readRec (ifEq 120147 120023
          (.seq ztpcj
            (.seq (if pos then gtZS else ltZS) ztgwv)) .skip))
        d d' k ∧ k ≤ 340 ∧ d'.nreg 120140 ≤ 1 ∧
        (d'.nreg 120140 = 1 ↔ chH c.nmem V zteet = V.hz) ∧
        (chH c.nmem V zteet = V.hz → d'.nreg 120141 = nearC V c.nmem t ∧
          d'.nreg 120142 = farC V c.nmem t ∧ d'.nreg 120143 ≤ 1 ∧
          (d'.nreg 120143 = 1 ↔ DegC P C V c.nmem t)) := by
    intro pos j hj hpos hjc d hd hqd hmd h140 h145
    have hi := hT.lt j hj
    have hrec := hT.rec_le _ hi
    obtain ⟨d₁, k₁, e₁, hk₁, v146, v147, r₁, m₁⟩ := readRec_exec (P := P) (V := V) d hd hqd.CB h145
      hrec
    rw [hmd] at v147
    have hq₁ : QConst P V d₁ := hqd.congr by_grind
    by_cases heq : chH c.nmem V zteet = V.hz
    · have hq12 : d₁.nreg 120147 = d₁.nreg 120023 := by rw [v147, hq₁.hz, heq]
      have hmd₁ := m₁.trans hmd
      -- the ends
      obtain ⟨d₂, k₂, e₂, hk₂, a140, a141, a142, a120, a121, r₂, m₂⟩ :
          ∃ d₂ k₂, Exec P W ztpcj d₁ d₂ k₂ ∧ k₂ = 7 ∧
            d₂.nreg 120140 = 1 ∧ d₂.nreg 120141 = nearC V c.nmem t ∧
            d₂.nreg 120142 = farC V c.nmem t ∧ d₂.nreg 120120 = nearC V c.nmem t ∧
            d₂.nreg 120121 = V.hz ∧
            (∀ r, r ≠ 120140 → r ≠ 120146 → r ≠ 120141 → r ≠ 120142 → r ≠ 120120 → r ≠ 120121 →
              d₂.nreg r = d₁.nreg r) ∧ d₂.nmem = d₁.nmem := by
        cases pos
        · have hσ : ztscz := by_simp_all
          obtain ⟨d₂, k₂, e₂, hk₂, a1, a2, a3, a4, a5, a6, a7⟩ := foundNeg_exec
            d₁ e₁.wb_right hq₁.one hq₁.hz v146 hrec
          zuikc
          refine ztfdf <;>
            simp only [nearC, farC, ite_eq_right hσ, hjc] <;> assumption
        · zullx
          obtain ⟨d₂, k₂, e₂, hk₂, a1, a2, a3, a4, a5, a6, a7⟩ := foundPos_exec
            d₁ e₁.wb_right hq₁.one hq₁.hz v146 hrec
          zuikc
          refine ztfdf <;>
            simp only [nearC, farC, ite_eq_left hσ, hjc] <;> assumption
      have hq₂ : QConst P V d₂ := hq₁.congr by_grind
      -- the comparison
      obtain ⟨d₃, k₃, e₃, hk₃, f₃, b₃, g₃⟩ : ∃ d₃ k₃, Exec P W (if pos then gtZS else ltZS) d₂ d₃ k₃ ∧
          k₃ ≤ 300 ∧ FrameB BX2 d₂ d₃ ∧ d₃.nreg 120128 ≤ 1 ∧
          (d₃.nreg 120128 = 1 ↔ (if V.σb = 1 then EndGtZ P C V ztftk V.hz
            else EndLtZ P C V ztftk V.hz)) := by
        cases pos
        · have hσ : ztscz := by_grind
          obtain ⟨d₃, k₃, e₃, hk₃, f₃, b₃, g₃⟩ := ltZS_exec hG by_omega hv htv d₂
            e₂.wb_right hq₂ ztmcw
          grind
        · zullx
          obtain ⟨d₃, k₃, e₃, hk₃, f₃, b₃, g₃⟩ := gtZS_exec hG by_omega hv htv d₂
            e₂.wb_right hq₂ ztmcw
          grind
      have one₃ := (f₃.1 _ by_decide).trans hq₂.one
      zubj
      obtain ⟨d₄, e₄, v₄, v₄'⟩ : ∃ d₄, Exec P W (.instr (.subN 120143 120011 120128)) d₃ d₄ 1 ∧
          d₄.nreg 120143 = d₃.nreg 120011 - d₃.nreg 120128 ∧
          ∀ r, r ≠ 120143 → d₄.nreg r = d₃.nreg r :=
        ⟨_, Exec.subN w₃ _ _ _, by config_simp, fun r hr => by config_simp; upd_solve⟩
      have R₄ : ∀ r, r ≠ 120143 → BX2 r = false → d₄.nreg r = d₂.nreg r := fun r h1 h2 => by
        rw [v₄' r h1, f₃.1 r h2]
      refine ⟨d₄, _, .seq e₁ (ifEq_eq_exec hq12 ztcb), by_omega, ?_, ?_, fun _ => ?_⟩
      · zunwl
      · zunwl; omega
      · refine ⟨by rw [R₄ _ by_decide by_decide, a141], by rw [R₄ _ by_decide by_decide, a142],
          by omega, ?_⟩
        rw [v₄, one₃]
        unfold DegC
        grind
    · have hq12 : d₁.nreg 120147 ≠ d₁.nreg 120023 := by rw [v147, hq₁.hz]; omega
      obtain ⟨k', ex', hk'⟩ := ifEq_ne_exec hq12
        ztekc
      refine ⟨d₁, _, .seq e₁ ex', by_omega, by_simp_all,
        ?_, by_omega⟩
      simp_all
  have hCH := hT.CH_le
  zudmj
  · -- leftwards
    have hσ' : ztscz := by_omega
    have hjc : ztpoz := by unfold jCOf; grind
    by_cases ht0 : 0 < t
    · obtain ⟨d, k, e, hk, v⟩ : ∃ d k, Exec P W (block [.subN 120148 50105 120011,
          .addN 120144 120038 120148, .loadN 120145 120144]) c₀ d k ∧ k = 3 ∧
          (d.nreg 120145 = chAt c.nmem V _ ∧
            (∀ r, r ≠ 120148 → r ≠ 120144 → r ≠ 120145 → d.nreg r = c₀.nreg r) ∧ d.nmem = c₀.nmem) := by
        exec_block
        · config_simp; rw [hq₀.CH, t₀, hq₀.one]; omega
        · refine ⟨rfl, ?_, fun r h1 h2 h3 => by config_simp; upd_solve, rfl⟩
          config_simp; rw [hq₀.CH, t₀, hq₀.one, m₀]; rfl
      zudje

      obtain ⟨d', k', e', hk', b', f', g'⟩ := tail false _ by_omega
        by_grind hjc d e.wb_right hqd ztvyr
        by_grind v145
      refine ⟨d', _, .seq e₀ (.ifLtN_true ztdcj
        (.ifLtN_true (by rw [hq₀.zero, t₀]; omega) ztspw)), by_omega, b', ?_, ?_⟩
      · zuhlf
      · zubwy
    · refine ⟨c₀, _, .seq e₀ (.ifLtN_true ztdcj
        (.ifLtN_false by_omega ztjdy)), by_omega,
        by omega, ?_, ?_⟩
      · zuhnr
      · zubwy
  · -- rightwards
    zuesr
    have hjc : ztsjw := by unfold jCOf; grind
    by_cases htK : t < V.K
    · obtain ⟨d, k, e, hk, v⟩ : ∃ d k, Exec P W (block [.addN 120144 120038 50105,
          .loadN 120145 120144]) c₀ d k ∧ k = 2 ∧
          (d.nreg 120145 = chAt c.nmem V t ∧
            (∀ r, r ≠ 120144 → r ≠ 120145 → d.nreg r = c₀.nreg r) ∧ d.nmem = c₀.nmem) := by
        exec_block
        · rw [hq₀.CH, t₀]; omega
        · refine ⟨rfl, ?_, fun r h1 h2 => by config_simp; upd_solve, rfl⟩
          config_simp; rw [hq₀.CH, t₀, m₀]; rfl
      zudje

      obtain ⟨d', k', e', hk', b', f', g'⟩ := tail true t htK
        by_grind hjc d e.wb_right hqd ztvyr
        by_grind v145
      refine ⟨d', _, .seq e₀ (.ifLtN_false ztdcj
        (.ifLtN_true ztlia ztspw)), by_omega, b', ?_, ?_⟩
      · zuhlf
      · zubwy
    · refine ⟨c₀, _, .seq e₀ (.ifLtN_false ztdcj
        (.ifLtN_false ztlia ztjdy)), by_omega,
        by omega, ?_, ?_⟩
      · zuhnr
      · zubwy
end
end OracleR
end Chazelle.Core
namespace Chazelle.Core
namespace OracleR
open Machine Machine.Stmt Programs SignK SearchR WalkKey NFLoc
open Chazelle.Chain (sideInArc)
@[expose] public section
def myFinish : Stmt :=
  .ifLtN 120012 50105 (.instr (.subN 120170 50105 120011)) (.instr (.subN 120170 10504 120011))

/-- **Double identification with the stored table.** -/
def myLoc : Stmt := .seq locDir (.seq locSetup (.seq (tsearch 120041 120042 keyCmp) myFinish))

/-- The registers written by `myLoc`. -/
def BL (r : ℕ) : Bool :=
  Bdir r || Bloc r || Bcmp r || decide ztgzf || decide zttxn

/-- **Double identification with the stored table.**  With the model descriptor in `50000`, the
normal form in `50001`, the position in `50002`, `50003`, the table of powers at `TB` (register
`120041`, length `L` in `120042`), it leaves in `120170` a spine position `p` whose arc contains
the key of the position (as in `LocateSpec`). -/
theorem myLoc_exec (hcov : ArcCoverSpec) {P : Polygon} {W : ℕ} {c : Config}
    (hw : WordsBounded W c) (hD : LocDPre P W c) (hG : GoodEnv P) (hW : P.n + 3 ≤ W)
    {M : Model} {N : NF} (hM : ModelDescAt c.nmem zthut zta M) (hGM : GoodModel M)
    (hN : NFAt c.nmem ztvii N) (hNF : IsNF M zta N)
    (hx : ProperPos M zta P.n ztbig)
    (hst : ∀ j, j < N.arcs.length → ProperPos M zta P.n (N.arc j).s)
    {TB L : ℕ} (hTBr : c.nreg 120041 = TB) (hLr : c.nreg 120042 = L)
    (h12 : c.nreg 120012 = 0) (h11 : c.nreg 120011 = 1)
    (htab : ∀ j, j < L → c.nmem ztjnh = 2 ^ j) (hbig : N.arcs.length < 2 ^ L)
    (hB : c.nreg 50001 + 7 ≤ TB)
    (hAB : c.nmem ztrme + 5 * N.arcs.length ≤ TB)
    (hSB : c.nmem ztrmf + N.arcs.length ≤ TB) (hTW : TB + L ≤ W) :
    ∃ c' k, Exec P W myLoc c c' k ∧ k ≤ 5500 * ztgt ∧ FrameB BL c c' ∧
      c'.nreg 120170 < N.arcs.length ∧
      (¬ M.IsCut ztwiv ztxvk →
        N.F M zta = ∅ ∨ sideInArc (M.key zta (N.arc ztffr).s)
          (M.key zta (N.arc ztffr).e)
          ztxvk) ∧
      (M.IsCut ztwiv ztxvk →
        M.key zta (N.arc ztffr).s =
            M.key zta ztbig ∨
          M.key zta (N.arc ztffr).e =
            M.key zta ztbig) := by
  zubce

  zudyc

  have hseq : ztguz := fun i hi =>
    hN.2.2.2.2.2.2.2.2.1 i by_omega
  obtain ⟨hcov1, hcov2⟩ := hcov M zta ztwiv hGM hNF.1
  have hA0 : ztrzd := by
    zueie
    obtain ⟨j, hj, -⟩ := listed_of_isArc hNF hU hab
    omega
  -- 1. the direction
  zubrh

  zud
  zucal

  zudqa
  -- 2. the setup
  obtain ⟨c₂, k₂, e₂, hk₂, q⟩ : ∃ c₂ k₂, Exec P W locSetup c₁ c₂ k₂ ∧ k₂ = 14 ∧
      (c₂.nreg 10500 = c.nreg 50002 ∧ c₂.nreg 10501 = c.nreg 50003 ∧
        c₂.nreg 10502 = c₁.nreg 10502 ∧ c₂.nreg 10503 = AB ∧ c₂.nreg 10504 = A ∧
        c₂.nreg 10505 = SB ∧ c₂.nreg 50103 = SB ∧ c₂.nreg 50104 = A) := by
    unfold locSetup
    exec_block
    · omega
    · config_simp; omega
    · config_simp; omega
    · config_simp; omega
    · config_simp; omega
    · config_simp; omega
    · config_simp; omega
    · zubee
      config_simp
      grind
  zucsz
  zue
  zujxq
  zucxa
  have R₂ : ∀ r, Bloc r = false → Bdir r = false → c₂.nreg r = c.nreg r := fun r h1 h2 =>
    (f₂.1 r h1).trans (f₁.1 r h2)
  -- 3. the search
  zuioe
  have hJ₂ : CmpJ x d AB A SB TB c.nmem c₂ :=
    ⟨q500, q501, by_omega, q503, q504, q505, fun a _ => by zunbg⟩
  have hcmp := keyCmp_predOK hG hW x hx.2.2 d AB A SB TB c.nmem hAB by_omega
  have hpr : ∀ i, i < A → (cmpPr P x d AB A c.nmem ztbagf = true ↔
      KeyPred M zta x (N.arc ztdfs).s) := fun i hi => by
    zueyi

  obtain ⟨c₃, k₃, e₃, hk₃, hJ₃, hL₃, m₃, a₃, ht₃, hpre₃, hpost₃⟩ := tsearch_exec (P := P) hcmp
    by_decide (rT := 120041) (rL := 120042) (T := TB) (L := L) by_decide
    by_decide w₂ hJ₂ (cmpJ_stable x d AB A SB TB c.nmem)
    ztksr ztksr
    ztjwa by_omega
    by_omega hTW
    (fun i j hij hj hprj => by
      zueds

      exact (hpr i by_omega).2 ztgqo)
    by_omega
  rw [q104] at ht₃ hpost₃
  zuhng
  obtain ⟨-, -, -, -, h504, -, -⟩ := hJ₃
  -- 4. the spine position
  zujnc
  have hpick := locate_pick (fun y hy => hcov2 y hy) hNF x hA0 ht₃
    zthgz
    (fun hi hk => by
      grind)
  zubj
  have c12 : c₃.nreg 120012 = 0 := by
    rw [hL₃.1 _ by_decide by_decide by_decide,
      R₂ _ by_decide by_decide, h12]
  have c11 : zthos := by
    rw [hL₃.1 _ by_decide by_decide by_decide,
      R₂ _ by_decide by_decide, h11]
  obtain ⟨c₄, k₄, e₄, hk₄, v₄⟩ : ∃ c₄ k₄, Exec P W myFinish c₃ c₄ k₄ ∧ k₄ ≤ 3 ∧
      c₄.nreg 120170 = (if 0 < t then t - 1 else A - 1) := by
    unfold myFinish
    zujsg
    · exact ⟨_, _, .ifLtN_true by_omega ztgdp, by_omega,
        by config_simp; grind⟩
    · exact ⟨_, _, .ifLtN_false by_omega ztgdp, by_omega,
        by config_simp; rw [c11, h504, ite_eq_right h0]⟩
  have ex : Exec P W myLoc c c₄ ztwwh := .seq e₁ ztcb
  have f₃ := exec_frameB e₃ (B := fun r => Bcmp r || decide ztgzf) by_decide
  have f₄ := exec_frameB e₄ (B := fun r => decide zttxn) by_decide
  have fr : FrameB BL c c₄ :=
    (FrameB.mono f₁ fun r hr => by zungq).trans
      ((FrameB.mono f₂ fun r hr => by zungq).trans
        ((FrameB.mono f₃ fun r hr => by
          simp only [Bool.or_eq_true] at hr
          rcases hr with hr | hr <;> zungq).trans
          (FrameB.mono f₄ fun r hr => by zvmwo at hr; zungq)))
  refine ⟨c₄, _, ex, ?_, fr, ?_, ?_⟩
  · omega
  · zuntf; split_ifs <;> omega
  grind
end
end OracleR
namespace Restore
open Chazelle.Chain (regionsIn TouchesIn)
open Chazelle.Merge (exitsIn)
@[expose] public section
variable {M : Model} {Q : Polygon} {N : NF} {reg : ℕ → Set Point}
theorem recOf_toSet (x : CRec) : (recOf ztqyz).toSet M Q = x.toSet M Q := rfl

/-- The new chords of a round. -/
def newSet (M : Model) (Q : Polygon) (newL : List ztwjg) : Set ztf :=
  {c | ∃ p ∈ newL, c = (recOf p.2).toSet M Q}
theorem mem_highList {D r r' : ℕ} : r' ∈ highList N D r ↔ r' < r ∧ D < degOf N r' := by
  unfold highList; simp
theorem highList_nodup (D r : ℕ) : (highList N D r).Nodup := List.nodup_range.filter _
theorem chords_map_nodup (hN : IsNF M Q N) : (N.chords.map fun x => x.toSet M Q).Nodup := by
  zujgx
  rintro ⟨i, hi⟩ ⟨j, hj⟩ h
  simp only [List.get_eq_getElem, List.getElem_map] at h
  simp only [List.length_map] at hi hj
  have e : ∀ k (hk : k < N.chords.length), N.chords[k] = N.chord k := fun k hk => by
    zuub
  rw [e i hi, e j hj] at h
  exact Fin.ext (hN.2.1 i j hi hj h)
theorem chord_toSet_mem {i : ℕ} (hi : i < N.nChords) : (N.chord i).toSet M Q ∈ N.F M Q :=
  ⟨N.chord i, OutNF.chord_mem hi, rfl⟩

/-- The new chord of a region lies in that region. -/
theorem found_sub {r : ℕ} {t : ℕ × ℕ × ℕ} (h : FoundOK M Q N reg r t) :
    (recOf t).toSet M Q ∩ M.D ⊆ reg r := h.2.2.2.2.1

/-- **Distinct high regions get distinct chords** (and a chord determines its region). -/
theorem found_region (hM : WalkAx M) (_hN : IsNF M Q N) (hregs : NFRegs M Q N reg) {r r' : ℕ}
    (hr : r < N.nRegions) (hr' : r' < N.nRegions) {t t' : ℕ × ℕ × ℕ}
    (h : FoundOK M Q N reg r t) (h' : FoundOK M Q N reg r' t')
    (he : (recOf t).toSet M Q = (recOf t').toSet M Q) : r = r' := by
  obtain ⟨z, hz⟩ := inter_nonempty_of_adm hM h.2.2.1
  have hz1 := found_sub h hz
  have hz2 := found_sub h' ztjxs
  zufjh
  have e1 := hRC.1 r hr
  have e2 := hRC.1 r' hr'
  have : reg r = reg r' := by
    rw [Chazelle.Chain.regionsIn_eq_component e1 hz1, Chazelle.Chain.regionsIn_eq_component e2 hz2]
  exact hRC.2.1 r r' hr hr' this
theorem fst_inj {l : List ztwjg} (hl : (l.map Prod.fst).Nodup) {p p' : ℕ × zte}
    (hp : p ∈ l) (hp' : p' ∈ l) (h : p.1 = p'.1) : p = p' := by
  induction l with
  | nil => simp at hp
  | cons a l ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hl
    rcases List.mem_cons.1 hp with h1 | h1 <;> rcases List.mem_cons.1 hp' with h2 | h2
    · simp_all
    · simp_all
    · grind
    · simp_all

/-- The data of the end of a region loop. -/
structure NewOK (M : Model) (Q : Polygon) (N : NF) (reg : ℕ → Set Point) (D : ℕ)
    (newL : List ztwjg) : Prop where
  fst : newL.map Prod.fst = highList N D N.nRegions
  good : ∀ p ∈ newL, FoundOK M Q N reg p.1 p.2
variable {D : ℕ}
theorem NewOK.lt {newL : List ztwjg} (h : NewOK M Q N reg D newL)
    {p : ℕ × zte} (hp : p ∈ newL) : p.1 < N.nRegions := by
  have : p.1 ∈ newL.map Prod.fst := List.mem_map_of_mem hp
  rw [h.fst, mem_highList] at this
  omega
theorem NewOK.nodup_fst {newL : List ztwjg} (h : NewOK M Q N reg D newL) :
    (newL.map Prod.fst).Nodup := by rw [h.fst]; exact highList_nodup _ _

/-- **The list of a round is a valid input of the normal-form construction.** -/
theorem round_list_ok (hM : WalkAx M) (hN : IsNF M Q N) (hregs : NFRegs M Q N reg) {D : ℕ}
    {newL : List ztwjg} (h : NewOK M Q N reg D newL) :
    ChordTriplesOK M Q ztpcx := by
  have hmem : ∀ x ∈ oldL N ++ newL.map Prod.snd,
      (recOf x).toSet M Q ∈ M.Adm ∧ x.1 < Q.n ∧ (recOf x).Attached M Q := by
    zuh
    zuoy
    · zufzg
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hy
      have e : ztiym := by
        zuub
      zui
      obtain ⟨-, -, -, -, -, -, hh, -⟩ := hN.2.2.2
      exact ⟨hN.1.2.1 (chord_toSet_mem hi), hh i hi, hN.2.2.1 i hi⟩
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
      obtain ⟨h1, h2, h3, -⟩ := h.good p hp
      simp_all
  refine ⟨⟨(List.finite_toSet ((oldL N ++ newL.map Prod.snd).map
      fun x => (recOf x).toSet M Q)).subset ?_, fun c ⟨x, hx, hc⟩ => hc ▸ (hmem x hx).1,
    fun c ⟨x, hx, hc⟩ => ⟨x.1, (hmem x hx).2.1, _, _, hc⟩⟩, ?_, fun x hx => (hmem x hx).2.2,
    fun x hx => (hmem x hx).2.1⟩
  · grind
  · zujgt
    refine List.nodup_append.2 ztcg
    · have : (oldL N).map (fun x => (recOf x).toSet M Q) = N.chords.map fun x => x.toSet M Q := by
        simp [oldL, recOf_toSet]
      zvmwk; exact chords_map_nodup hN
    · zuczm
      refine List.Nodup.map_on ?_ (List.Nodup.of_map _ h.nodup_fst)
      intro p hp p' hp' he
      exact fst_inj h.nodup_fst hp hp' (found_region hM hN hregs ztqoy ztvrx
        (h.good p hp) (h.good p' hp') he)
    · zubtp
      zumqb
      zufzf
      obtain ⟨t, ht, hpe⟩ := List.mem_map.1 hb
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ht
      have hold : (recOf x).toSet M Q ∈ N.F M Q := by
        zufzg
        tauto
      exact (h.good p hp).2.2.2.1 (hpe ▸ hold)

/-- **The chords of the list of a round.** -/
theorem round_lset {newL : List ztwjg} :
    Gran.lset M Q ztpcx = N.F M Q ∪ newSet M Q newL := by
  zubcj
  simp only [Gran.lset, newSet, oldL, List.mem_append, List.mem_map, Set.mem_union,
    Set.mem_ofPred_eq, NF.F]
  constructor
  · rintro ⟨x, hx | ⟨p, hp, rfl⟩, rfl⟩
    · left
      obtain ⟨y, hy, rfl⟩ := hx
      tauto
    grind
  · rintro (⟨y, hy, rfl⟩ | ⟨p, hp, rfl⟩)
    · exact ⟨_, Or.inl ⟨y, hy, rfl⟩, rfl⟩
    grind

/-- **The new chords of a round are round data.** -/
theorem round_data (hM : WalkAx M) (_hN : IsNF M Q N) (hregs : NFRegs M Q N reg) {D : ℕ}
    {newL : List ztwjg} (h : NewOK M Q N reg D newL) :
    RoundData M ztdu (newSet M Q newL) := by
  zufjh
  refine ⟨fun c ⟨p, hp, hc⟩ => hc ▸ (h.good p hp).2.2.1, (List.finite_toSet (newL.map fun p =>
    (recOf p.2).toSet M Q)).subset fun c ⟨p, hp, hc⟩ => by
      grind,
    fun c ⟨p, hp, hc⟩ => ⟨reg p.1, hRC.1 _ ztqoy, hc ▸ (h.good p hp).2.2.2⟩, ?_⟩
  rintro e ⟨p, hp, rfl⟩ e' ⟨p', hp', rfl⟩ R hR hw hw'
  obtain ⟨z, hz⟩ := inter_nonempty_of_adm hM (h.good p hp).2.2.1
  obtain ⟨z', hz'⟩ := inter_nonempty_of_adm hM (h.good p' hp').2.2.1
  have hreg : ∀ q ∈ newL, ∀ y ∈ (recOf q.2).toSet M Q ∩ M.D,
      SplitsWell M ztdu R ((recOf q.2).toSet M Q) → reg q.1 = R := by
    intro q hq y hy hwq
    have e1 := hRC.1 _ (h.lt hq)
    rw [Chazelle.Chain.regionsIn_eq_component e1 (found_sub (h.good q hq) hy),
      Chazelle.Chain.regionsIn_eq_component hR (hwq.2.1 hy)]
  have h1 := hreg p hp z hz hw
  have h2 := hreg p' hp' z' hz' hw'
  have := hRC.2.1 _ _ ztqoy ztvrx ztmkm
  rw [fst_inj h.nodup_fst hp hp' this]

/-- **Every high region received a chord.** -/
theorem round_all (hN : IsNF M Q N) (hregs : NFRegs M Q N reg) {D : ℕ}
    {newL : List ztwjg} (h : NewOK M Q N reg D newL) :
    ∀ R ∈ regionsIn M.D ztdu, D < (exitsIn M.D ztdu R).ncard →
      ∃ e ∈ newSet M Q newL, SplitsWell M ztdu R e := by
  zufji
  intro R hR hD
  obtain ⟨r, hr, rfl⟩ := hRC.2.2 R hR
  have hdeg : (exitsIn M.D ztdu ztcz).ncard = degOf N r :=
    Gran.deg_region hN hRC hRO hr
  have : r ∈ newL.map Prod.fst := by
    rw [h.fst, mem_highList]; omega
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 this
  exact ⟨_, ⟨p, hp, rfl⟩, (h.good p hp).2.2.2⟩
open Machine Machine.Stmt Programs
variable {P : Polygon} {W : ℕ} (c : Config)
set_option maxHeartbeats 2000000 in
theorem head_exec (hw : WordsBounded W c) {H : ℕ}
    (h12 : c.nreg 80012 = H) (h21 : c.nreg 80021 = 2) (h22 : c.nreg 80022 = 3)
    (hH : H + 5 ≤ W) :
    ∃ c' k, Exec P W headS c c' k ∧ k = 10 ∧
      c'.nreg 80013 = c.nmem H ∧ c'.nreg 80014 = c.nmem ztfnq ∧
      c'.nreg 80015 = c.nmem ztjiy ∧ c'.nreg 80016 = c.nmem ztwj ∧
      c'.nreg 80017 = c.nreg ALLOC ∧ c'.nreg 80031 = c.nmem ztjiy ∧ c'.nreg 80030 = 0 ∧
      (∀ r, (r < 80013 ∨ (80017 < r ∧ r < 80030) ∨ (80031 < r ∧ r ≠ 80036)) →
        c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold headS
  exec_block
  all_goals try omega
  all_goals try (simp (disch := omega) only [Machine.upd_same,
    Machine.upd_other, h12, h21, h22, ALLOC]; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩ <;>
    (try simp (disch := omega) only [Machine.upd_same,
      Machine.upd_other, h12, h21, h22, ALLOC])
theorem mid_exec (hw : WordsBounded W c) :
    ∃ c' k, Exec P W midS c c' k ∧ k = 3 ∧ c'.nreg 80018 = c.nreg 80013 ∧
      c'.nreg 80043 = c.nreg ALLOC ∧ c'.nreg 80034 = 0 ∧
      (∀ r, r ≠ 80018 → r ≠ 80043 → r ≠ 80034 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold midS
  exec_block
  · omega
  · refine ztbfo <;>
      simp (disch := omega) only [Machine.upd_same, Machine.upd_other, ALLOC]
theorem preReg_exec (hw : WordsBounded W c)
    (h : c.nreg 80016 + c.nreg 80021 ≤ W) :
    ∃ c' k, Exec P W preRegS c c' k ∧ k = 2 ∧ c'.nreg 80040 = 0 ∧
      c'.nreg 80041 = c.nreg 80016 + c.nreg 80021 ∧
      (∀ r, r ≠ 80040 → r ≠ 80041 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold preRegS
  exec_block
  · omega
  · simp_all
  simp_all
theorem bargs_exec (hw : WordsBounded W c) :
    ∃ c' k, Exec P W zthtf c c' k ∧
      k = 3 ∧ c'.nreg 40000 = c.nreg 80000 ∧ c'.nreg 40001 = c.nreg 80017 ∧
      c'.nreg 40002 = c.nreg 80018 ∧
      (∀ r, r ≠ 40000 → r ≠ 40001 → r ≠ 40002 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  exec_block
  simp_all
theorem copy1_exec' (hw : WordsBounded W c) (a b : ℕ) :
    ∃ c' k, Exec P W ztozb c c' k ∧ k = 1 ∧ c'.nreg a = c.nreg b ∧
      ztivh ∧ c'.rreg = c.rreg ∧
      c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output :=
  Gran.copy1_exec c hw a b
theorem incr_exec (hw : WordsBounded W c)
    (h : c.nreg 80010 + c.nreg 80020 ≤ W) :
    ∃ c' k, Exec P W ztnse c c' k ∧ k = 1 ∧
      c'.nreg 80010 = c.nreg 80010 + c.nreg 80020 ∧
      (∀ r, r ≠ 80010 → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧
      c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  exec_block
  · zubh
  simp_all
set_option maxHeartbeats 2000000 in
theorem init_exec (hw : WordsBounded W c)
    (hW : 5 ≤ W) (h1 : c.nreg 80002 + 1 ≤ W) (h2 : c.nreg 80002 + c.nreg 80003 ≤ W) :
    ∃ c' k, Exec P W initS c c' k ∧ k = 9 ∧
      c'.nreg 80020 = 1 ∧ c'.nreg 80021 = 2 ∧ c'.nreg 80022 = 3 ∧ c'.nreg 80023 = 5 ∧
      c'.nreg 80024 = 0 ∧ c'.nreg 80012 = c.nreg 80001 ∧ c'.nreg 80010 = 0 ∧
      c'.nreg 80011 = c.nreg 80002 + 1 ∧ c'.nreg 80019 = c.nreg 80002 + c.nreg 80003 ∧
      (∀ r, (r < 80010 ∨ 80025 ≤ r) → r ≠ 80012 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  zujqm
  exec_block
  all_goals try omega
  all_goals try (simp (disch := omega) only [Machine.upd_same,
    Machine.upd_other]; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r a1 a2 => ?_, rfl, rfl, rfl, rfl⟩ <;>
    zusb
end
end Restore
end Chazelle.Core
namespace Chazelle.Core
namespace Restore
open Machine Machine.Stmt Programs
open Chazelle.Chain (regionsIn)
@[expose] public section
structure DrvEnv where
  P : Polygon
  W : ℕ
  M : Model
  A₀ : ℕ
  m₀ : ℕ → ℕ
  MD : ℕ
  d0 : ℕ
  D : ℕ
  γ : ℕ
  ctx : ℕ
  sF : Stmt
  sB : Stmt
  κf : ℕ → ℕ
  κB : ℕ
  F : ℕ → ℕ
  G : ℕ → ℕ
  Hc : ℕ → ℕ
  X : MemCtx
  Ok : Polygon → Model → Prop
  S₀ : Set ztf
  K₀ : ℕ
namespace DrvEnv
variable (E : DrvEnv)

/-- A bound on the number of chords during the driver. -/
def Kc : ℕ := 2 ^ ztfnl * ztbjj

/-- The body bound of the region loop. -/
def Bf : ℕ := costF E.κf E.F E.G E.Hc ztjig E.γ + 20

/-- The bound of one round. -/
def Br : ℕ := 40 + 21 * E.Kc + ztnd * E.Kc +
  E.κB * (2 * E.Kc * ztlfj + 1)
end DrvEnv

/-- The facts about the driver data. -/
structure DrvGood (E : DrvEnv) : Prop where
  hF : FindOK E.sF E.κf E.F E.G E.Hc E.X E.Ok oracleBands
  hB : Gran.BuildOK E.sB E.κB
  hG : GoodEnv E.P
  hWh : hostWords E.P.n ≤ E.W
  hX : E.X.holds E.P E.m₀ E.ctx E.A₀
  hcap : ∀ m : ℕ → ℕ, ztcqf → E.γ ≤ E.X.cap E.P m E.ctx
  hwf : ModelDescWF E.P E.A₀ E.m₀ E.MD
  hMD : ModelDescAt E.m₀ E.MD zti E.M
  hreg : E.m₀ E.MD = 0 → ∀ H C, ChainDescAt E.m₀ ztcsy zti H C →
    HostRegular (Qof E.P).n H
  hsimp : E.m₀ E.MD = 0 → ∀ H C, ChainDescAt E.m₀ ztcsy zti H C → C.P.Simple
  hGM : GoodModel E.M
  hOk : E.Ok E.P E.M
  hfull : E.M.FullDegLe zti E.D

/-- The mathematical state of a round: the current normal form. -/
structure CurOK (E : DrvEnv) (t : ℕ) (m : ℕ → ℕ) (H A : ℕ) (N : NF) : Prop where
  nw : NFWithin m H A N
  nf : IsNF E.M zti N
  sub : E.S₀ ⊆ N.F E.M zti
  deg : E.M.DegLe ztzuh (max E.D ztemm)
  sg : E.M.Semigranular ztzuh E.γ
  size : N.nChords + 1 ≤ 2 ^ t * ztbjj
  fresh : 0 < t → E.A₀ ≤ H

/-- **The round invariant.** -/
structure OutI (E : DrvEnv) (t : ℕ) (c : Config) : Prop where
  wb : WordsBounded E.W c
  r00 : c.nreg 80000 = E.MD
  r02 : c.nreg 80002 = E.d0
  r03 : c.nreg 80003 = E.D
  r04 : c.nreg 80004 = E.γ
  r06 : c.nreg 80006 = E.ctx
  r10 : c.nreg 80010 = t
  r11 : c.nreg 80011 = E.d0 + 1
  r19 : c.nreg 80019 = E.d0 + E.D
  r20 : c.nreg 80020 = 1
  r21 : c.nreg 80021 = 2
  r22 : c.nreg 80022 = 3
  r23 : c.nreg 80023 = 5
  r24 : c.nreg 80024 = 0
  cur : ∃ N, CurOK E t c.nmem ztqia ztm N
  low : ∀ a, a < E.A₀ → c.nmem a = E.m₀ a
  alloc : E.A₀ ≤ c.nreg ALLOC
  t_le : t ≤ E.d0 + 1
  room : c.nreg ALLOC + ztgdn * ztbgq + 3 ≤ E.W

/-- The data of the region loop of a round. -/
def regEnvOf (E : DrvEnv) (N : NF) (reg : ℕ → Set Point) (LB H : ℕ) : RegEnv where
  P := E.P
  W := E.W
  M := E.M
  N := N
  reg := reg
  A₀ := E.A₀
  m₀ := E.m₀
  LB := LB
  H := H
  MD := E.MD
  D := E.D
  γ := E.γ
  ctx := E.ctx
  dcap := E.d0 + E.D
  sF := E.sF
  κf := E.κf
  F := E.F
  G := E.G
  Hc := E.Hc
  X := E.X
  Ok := E.Ok
theorem size_le_Kc {E : DrvEnv} {t K : ℕ} (ht : t ≤ E.d0) (h : K + 1 ≤ 2 ^ t * ztbjj) :
    2 * K + 2 ≤ E.Kc := by
  unfold DrvEnv.Kc
  have : ztixy := Nat.pow_le_pow_right by_norm_num ht
  zugwx
  nlinarith
set_option maxHeartbeats 8000000 in
/-- **The first part of a round**: header, copy, reservation, set-up of the region loop. -/
theorem phaseA {E : DrvEnv} (hE : DrvGood E) {t : ℕ} {c : Config} (hI : OutI E t c)
    (ht : t < E.d0 + 1) {N : NF} (hcur : CurOK E t c.nmem ztqia ztm N)
    {reg : ℕ → Set Point} (hregs : NFRegs E.M zti N reg)
    (rest : Stmt) (Qp : Config → ℕ → Prop)
    (hrest : ∀ c₅ k, RegGood (regEnvOf E N reg ztm ztqia) c₅ →
      RF dBands E.A₀ c c₅ k → k ≤ 20 + 15 * N.nChords + 6 * N.nRegions →
      c₅.nreg 80002 = E.d0 → c₅.nreg 80010 = t → c₅.nreg 80011 = E.d0 + 1 →
      c₅.nreg 80021 = 2 → c₅.nreg 80022 = 3 → c₅.nreg 80017 = c.nreg ALLOC →
      c₅.nreg 80012 = c.nreg 80012 →
      ∃ c' k', Exec E.P E.W rest c₅ c' k' ∧ Qp c' zttqb) :
    ∃ c' k, Exec E.P E.W (.seq headS (.seq copyS (.seq midS (.seq resS (.seq preRegS rest)))))
      c c' k ∧ Qp c' k := by
  set H := c.nreg 80012 with hHd
  set LB := c.nreg ALLOC with hLBd
  zukzk
  set R := N.nRegions with hRd
  zuclv
  have hRK : ztsch := Gran.nRegions_eq hcur.nf hM
  have hNAt := hcur.nw.nfAt
  have hareas := Gran.nf_areas hcur.nw
  zumcq
  have hLBW : LB ≤ E.W := hW.1 ALLOC
  have hKc : 2 * K + 2 ≤ E.Kc := size_le_Kc by_omega hcur.size
  have hBr : 21 * E.Kc + 40 ≤ E.Br := by unfold DrvEnv.Br; omega
  zugnc
  have hroom' : LB + E.Br + 2 ≤ E.W := by
    have : ztyyd :=
      Nat.le_mul_of_pos_left _ by_omega
    omega
  -- header
  obtain ⟨c₁, k₁, e₁, hk₁, a13, a14, a15, a16, a17, a31, a30, R₁, rr₁, m₁, rm₁, o₁⟩ :=
    head_exec (P := E.P) c hW rfl hI.r21 hI.r22 by_omega
  have hK : c.nmem H = K := hNAt.1
  have hR : c.nmem _ = R := hNAt.2.2.1
  rw [hK] at a13
  rw [hR] at a14
  set CB := c.nmem ztjiy with hCBd
  set RB := c.nmem ztwj with hRBd
  zud
  have g₁ := R₁
  have A₁ : c₁.nreg ALLOC = LB := g₁ _ by_decide
  -- copy
  obtain ⟨c₂, k₂, e₂, hk₂, A₂, h30, R₂, low₂, cop₂, RF₂⟩ := copy_exec (P := E.P) (A₀ := E.A₀)
    w₁ a13 a30 a31 A₁ (by rw [g₁ _ by_omega, hI.r20])
    (by rw [g₁ _ by_omega, hI.r22])
    (fun i hi => hareas.2.1 i hi) by_omega by_omega hI.alloc
  zue
  -- mid
  obtain ⟨c₃, k₃, e₃, hk₃, b18, b43, b34, R₃, rr₃, m₃, rm₃, o₃⟩ := mid_exec (P := E.P) c₂ w₂
  zubj
  have A₃ : c₃.nreg ALLOC = LB + 3 * K := by rw [R₃ _ by_decide by_decide by_decide, A₂]
  -- reservation
  obtain ⟨c₄, k₄, e₄, hk₄, A₄, R₄, m₄, RF₄⟩ := res_exec (P := E.P) (A₀ := E.A₀) w₃
    (by rw [R₃ _ by_decide by_decide by_decide, R₂ _ by_decide by_decide by_decide
      by_decide, a14])
    b34 A₃ (by rw [R₃ _ by_decide by_decide by_decide, R₂ _ by_decide by_decide
      by_decide by_decide, g₁ _ ztozf, hI.r20]) by_omega by_omega
  zucc
  -- region-loop set-up
  have d16 : c₄.nreg 80016 = RB := by
    rw [R₄ _ by_decide by_decide, R₃ _ by_decide by_decide by_decide,
      R₂ _ by_decide by_decide by_decide by_decide, a16]
  have d21 : c₄.nreg 80021 = 2 := by
    rw [R₄ _ by_decide by_decide, R₃ _ by_decide by_decide by_decide,
      R₂ _ by_decide by_decide by_decide by_decide, g₁ _ ztozf,
      hI.r21]
  have hRB : RB + 4 < LB := by
    have := hareas.2.2.1 0 by_omega; omega
  obtain ⟨c₅, k₅, e₅, hk₅, f40, f41, R₅, rr₅, m₅, rm₅, o₅⟩ := preReg_exec (P := E.P) c₄ w₄
    (by rw [d16, d21]; omega)
  rw [d16, d21] at f41
  zuef
  -- the registers of `c₅`
  have G : ∀ r, 80000 ≤ r → r ≤ 80024 → r ≠ 80013 → r ≠ 80014 → r ≠ 80015 → r ≠ 80016 →
      r ≠ 80017 → r ≠ 80018 → c₅.nreg r = c.nreg r := by
    intro r h1 h2 h3 h4 h5 h6 h7 h8
    zucvq
    rw [R₅ r by_omega by_omega, R₄ r by_omega hA,
      R₃ r by_omega by_omega by_omega, R₂ r by_omega by_omega by_omega hA,
      g₁ r by_omega]
  have f17 : c₅.nreg 80017 = LB := by
    rw [R₅ _ by_decide by_decide, R₄ _ by_decide by_decide,
      R₃ _ by_decide by_decide by_decide, R₂ _ by_decide by_decide by_decide
        by_decide, a17]
  have f14 : c₅.nreg 80014 = R := by
    rw [R₅ _ by_decide by_decide, R₄ _ by_decide by_decide,
      R₃ _ by_decide by_decide by_decide, R₂ _ by_decide by_decide by_decide
        by_decide, a14]
  have f18 : c₅.nreg 80018 = K := by
    rw [R₅ _ by_decide by_decide, R₄ _ by_decide by_decide, b18,
      R₂ _ by_decide by_decide by_decide by_decide, a13]
  have f43 : c₅.nreg 80043 = LB + 3 * K := by
    rw [R₅ _ by_decide by_decide, R₄ _ by_decide by_decide, b43, A₂]
  have A₅ : c₅.nreg ALLOC = LB + 3 * K + 3 * R := by
    rw [R₅ _ by_decide by_decide, A₄]
  -- memory of `c₅`
  have mem5 : ∀ a, a < LB → c₅.nmem a = c.nmem a := fun a ha => by
    rw [m₅, m₄, m₃, low₂ a ha, m₁]
  have hlist : ChordListAt c₅.nmem LB (oldL N) := by
    zug
    simp only [oldL, List.length_map] at hi
    have hc := hNAt.2.2.2.2.2.1 i hi
    have e : (oldL N).getD i ztt = ztgbh := by
      unfold oldL NF.chord
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
      rfl
    rw [e, m₅, m₄, m₃]
    have c0 := cop₂ i hi 0 by_omega
    have c1 := cop₂ i hi 1 by_omega
    have c2 := cop₂ i hi 2 by_omega
    simp only [add_zero] at c0
    zvmxn at c0 c1 c2
    zusk
    · rw [c0]; exact hc.1
    · rw [c1]; exact hc.2.1
    · rw [c2]; exact hc.2.2.1
  -- the frame
  have hb : ∀ r, bandOf r ∉ dBands → r < 80000 ∨ 90000 ≤ r := fun r hr => by
    by_contra h; push Not at h; exact hr (band8 h.1 h.2 ▸ mem_dBands_8)
  have RF₁ : ztlag := rf_of_regs (fun r hr => g₁ r by_omega) rr₁ m₁ rm₁ o₁
  have RF₃ : ztrft :=
    rf_of_regs (fun r hr => R₃ r by_omega by_omega by_omega) rr₃ m₃ rm₃ o₃
  have RF₅ : RF dBands E.A₀ c₄ c₅ k₅ :=
    rf_of_regs (fun r hr => R₅ r by_omega by_omega) rr₅ m₅ rm₅ o₅
  have RFA : RF dBands E.A₀ c c₅ _ :=
    RF₁.trans ztmcg
  -- the region-loop facts
  have hgood : RegGood (regEnvOf E N reg LB H) c₅ := by
    refine ⟨hE.hF, hE.hG, hE.hWh, hE.hX, hE.hcap, hI.alloc, hE.hwf, hE.hMD, hE.hreg, hE.hsimp, hE.hGM, hE.hOk,
      hE.hfull, ?_, hcur.nf, hregs, ?_, hcur.sg, fun a ha => ?_, w₅, ?_, ?_, ?_, ?_, ?_, f14,
      ?_, ?_, ?_, ?_, f40, ?_, f18, f43, ?_, hlist, ?_⟩
    · exact (hcur.nw.transport by_omega)
    · exact Model.DegLe.mono _ hcur.deg (max_le (by show E.D ≤ E.d0 + E.D; omega)
        (by show E.d0 - t ≤ E.d0 + E.D; omega))
    · change a < E.A₀ at ha
      change c₅.nmem a = E.m₀ a
      rw [mem5 a (by have := hI.alloc; omega), hI.low a ha]
    · rw [G _ by_omega by_omega by_omega by_omega by_omega by_omega by_omega
        by_omega, hI.r00]; rfl
    · rw [G _ by_omega by_omega by_omega by_omega by_omega by_omega by_omega
        by_omega, hI.r03]; rfl
    · rw [G _ by_omega by_omega by_omega by_omega by_omega by_omega by_omega
        by_omega, hI.r04]; rfl
    · rw [G _ by_omega by_omega by_omega by_omega by_omega by_omega by_omega
        by_omega, hI.r06]; rfl
    · rw [G _ by_omega by_omega by_omega by_omega by_omega by_omega by_omega
        by_omega]; rfl
    · rw [G _ by_omega by_omega by_omega by_omega by_omega by_omega by_omega
        by_omega, hI.r19]; rfl
    · rw [G _ by_omega by_omega by_omega by_omega by_omega by_omega by_omega
        by_omega, hI.r20]
    · rw [G _ by_omega by_omega by_omega by_omega by_omega by_omega by_omega
        by_omega, hI.r23]
    · rw [G _ by_omega by_omega by_omega by_omega by_omega by_omega by_omega
        by_omega, hI.r24]
    · show c₅.nreg 80041 = c₅.nmem ztwj + 2
      rw [f41, mem5 _ (by have := hareas.1; omega)]
    · show LB + 3 * (K + R) ≤ c₅.nreg ALLOC
      zunji; omega
    · show c₅.nreg ALLOC + ztnd * R + 2 ≤ E.W
      zunji
      have : ztnd * R ≤ ztnd * E.Kc := Nat.mul_le_mul_left _ by_omega
      have hBr2 : 21 * E.Kc + 40 + ztnd * E.Kc ≤ E.Br := by unfold DrvEnv.Br; omega
      omega
  obtain ⟨c', k', ex, hQ⟩ := hrest c₅ _ hgood RFA by_omega
    (by rw [G _ by_omega by_omega by_omega by_omega by_omega by_omega by_omega
      by_omega, hI.r02])
    (by rw [G _ by_omega by_omega by_omega by_omega by_omega by_omega by_omega
      by_omega, hI.r10])
    (by rw [G _ by_omega by_omega by_omega by_omega by_omega by_omega by_omega
      by_omega, hI.r11])
    (by rw [G _ by_omega by_omega by_omega by_omega by_omega by_omega by_omega
      by_omega, hI.r21])
    (by rw [G _ by_omega by_omega by_omega by_omega by_omega by_omega by_omega
      by_omega, hI.r22])
    f17
    (G _ by_omega by_omega by_omega by_omega by_omega by_omega by_omega by_omega)
  exact ⟨c', _, .seq e₁ ztgxd, by
    have : k₁ + (k₂ + (k₃ + (k₄ + (k₅ + k')))) = k₁ + ztwqm + k' := by_ring
    zvmwk; exact hQ⟩
theorem clog_mul_mono {a b : ℕ} (h : a ≤ b) :
    a * ztqaq + 1 ≤ b * ztqar + 1 := by
  have := Nat.clog_mono_right 2 h
  have : a * ztqaq ≤ b * ztqar := Nat.mul_le_mul h by_omega
  omega
set_option maxHeartbeats 16000000 in
/-- **One round.** -/
theorem round_step {E : DrvEnv} (hE : DrvGood E) {t : ℕ} {c : Config} (hI : OutI E t c)
    (ht : t < E.d0 + 1) :
    ∃ c' k, Exec E.P E.W ztkec c c' k ∧ OutI E ztbx c' ∧
      RF dBands E.A₀ c c' k ∧ k ≤ E.Br := by
  obtain ⟨N, hcur⟩ := hI.cur
  obtain ⟨reg, hRC, hCS, hAO, hRO, -⟩ := hcur.nf.2.2.2
  have hregs : NFRegs E.M _ N reg := zteyk
  zuclv
  have hRK := Gran.nRegions_eq hcur.nf hM
  have hKc := size_le_Kc by_omega hcur.size
  zugnc
  have hroom' : c.nreg ALLOC + E.Br + 2 ≤ E.W := by
    have : ztyyd :=
      Nat.le_mul_of_pos_left _ by_omega
    omega
  unfold roundBody
  refine phaseA hE hI ht hcur hregs _
    (fun c' k => OutI E _ c' ∧ RF dBands E.A₀ c c' k ∧ k ≤ E.Br) ?_
  intro c₅ k₅ hgood RF₅ hk₅ q02 q10 q11 q21 q22 q17 q12
  -- the region loop
  obtain ⟨c₆, k₆, newL, e₆, I₆, h40, RF₆, hk₆⟩ := reg_exec hgood
  have hNew : NewOK E.M zti N reg E.D newL := ⟨by
    have := I₆.hfst; rw [h40] at this; tauto, I₆.hgood⟩
  set L := oldL N ++ newL.map Prod.snd with hLd
  have hlenNew : newL.length ≤ N.nRegions := by
    have := congrArg List.length hNew.fst
    zubus
    zugxg
  have hLlen : L.length = N.nChords + newL.length := by
    simp [hLd, oldL, NF.nChords]
  have hok := round_list_ok hM hcur.nf hregs hNew
  zujb
  -- registers after the loop
  have reg6 := I₆.regs
  -- build: arguments
  obtain ⟨c₇, k₇, e₇, hk₇, b0, b1, b2, R₇, rr₇, m₇, rm₇, o₇⟩ := bargs_exec (P := E.P) c₆ w₆
  zubgp
  have A₇ : ztfky := R₇ _ by_decide by_decide by_decide
  have x0 : c₇.nreg 40000 = E.MD := by
    rw [b0, reg6 _ by_omega by_omega by_omega by_omega by_omega by_omega
      by_omega, hgood.r00]; rfl
  have x1 : c₇.nreg 40001 = c.nreg ALLOC := by
    grind
  have x2 : c₇.nreg 40002 = L.length := by rw [b2, I₆.cnt, hLlen]; rfl
  -- memory below `A₀` agrees with the initial one
  have RF56 := RF₅.trans RF₆
  have lowc : ztkod := fun a ha => by
    rw [m₇, RF56.2.2.1 a ha, hI.low a ha]
  have hA0₇ : ztukm := by
    zupaj; exact le_trans hI.alloc RF56.2.2.2.2.2.1
  obtain ⟨hMD₇, hwf₇⟩ := Gran.desc_agree' hE.hwf hE.hMD lowc
  have hlist₇ : ChordListAt c₇.nmem ztm L := by zungk; exact I₆.list
  have hLB₇ : c.nreg ALLOC + 3 * L.length ≤ c₇.nreg ALLOC := by
    rw [A₇, hLlen]
    have h1 := hgood.alloc
    have h2 := I₆.alloc
    change c.nreg ALLOC + 3 * ztnnc ≤ c₅.nreg ALLOC at h1
    omega
  -- cost facts
  have hLK : L.length ≤ 2 * E.Kc := by_omega
  have hcl := clog_mul_mono hLK
  have hA7le : c₇.nreg ALLOC ≤ c.nreg ALLOC + zttrj := by
    zupaj; exact RF56.2.2.2.2.2.2
  have hRKc : N.nRegions ≤ E.Kc := by_omega
  have hBfR : ztnd * N.nRegions ≤ ztnd * E.Kc := Nat.mul_le_mul_left _ hRKc
  have hk56 : k₅ + k₆ ≤ 22 + 15 * E.Kc + 6 * E.Kc + ztnd * E.Kc := by
    change k₆ ≤ ztnd * N.nRegions + 2 at hk₆
    omega
  have hκB : E.κB * ztbma ≤
      E.κB * ztxjz := Nat.mul_le_mul_left _ hcl
  have hBrdef : E.Br = 40 + 21 * E.Kc + ztnd * E.Kc +
      E.κB * ztxjz := rfl
  -- build
  have z0 : rd c₇ bBuild 0 = E.MD := x0
  have z1 : rd c₇ bBuild 1 = c.nreg ALLOC := x1
  have z2 : rd c₇ bBuild 2 = L.length := x2
  have p1 : ModelDescWF E.P (c₇.nreg ALLOC) c₇.nmem ztrwl := by
    rw [z0]; exact hwf₇.mono hA0₇
  have p2 : ModelDescAt c₇.nmem ztrwl zti E.M := by_grind
  have p3 : rd c₇ bBuild 1 + 3 * L.length ≤ c₇.nreg ALLOC := by_omega
  have p4 : ChordListAt c₇.nmem (rd c₇ bBuild 1) L := by_grind
  obtain ⟨c₈, k₈, e₈, hk₈, post₈, F₈⟩ := hE.hB E.P E.W c₇ w₇
    ⟨hE.hG, hE.hWh, p1, E.M, L, p2, hE.hGM, z2, p3, p4, hok⟩
    (by
      grind)
  beta_reduce at hk₈
  rw [z2] at hk₈
  obtain ⟨N', g₈, hNW₈, hNF₈, hmap₈, -⟩ := post₈ E.M L p2 z2 p4
  zujai
  -- handle and counter
  obtain ⟨c₉, k₉, e₉, hk₉, h12, R₉, rr₉, m₉, rm₉, o₉⟩ := copy1_exec' (P := E.P) c₈ w₈ 80012 40003
  zujaj
  have r8 := fun q h1 h2 =>
    F₈.1 q ztcmc ztu
  have y10 : c₉.nreg 80010 = t := by
    rw [R₉ _ by_decide, r8 _ by_omega by_omega, R₇ _ by_decide by_decide by_decide,
      reg6 _ by_omega by_omega by_omega by_omega by_omega by_omega by_omega, q10]
  have y20 : c₉.nreg 80020 = 1 := by
    rw [R₉ _ by_decide, r8 _ by_omega by_omega, R₇ _ by_decide by_decide by_decide,
      reg6 _ by_omega by_omega by_omega by_omega by_omega by_omega by_omega,
      hgood.r20]
  have hd0Kc : E.d0 + 1 ≤ E.Kc := by
    unfold DrvEnv.Kc
    have := Nat.lt_two_pow_self (n := E.d0 + 1)
    nlinarith
  obtain ⟨c₁₀, k₁₀, e₁₀, hk₁₀, h10, R₁₀, rr₁₀, m₁₀, rm₁₀, o₁₀⟩ := incr_exec (P := E.P) c₉ w₉
    by_omega
  rw [y10, y20] at h10
  -- fixed registers
  have Y : ∀ q, 80000 ≤ q → q < 81000 → q ≠ 80040 → q ≠ 80041 → q ≠ 80042 → q ≠ 80018 →
      q ≠ 80043 → q ≠ 80012 → q ≠ 80010 → c₁₀.nreg q = c₅.nreg q := by
    intro q h1 h2 h3 h4 h5 h6 h7 h8 h9
    rw [R₁₀ q h9, R₉ q h8, r8 q h1 by_omega, R₇ q by_omega by_omega by_omega,
      reg6 q h1 h2 h3 h4 h5 h6 h7]
  -- frames
  have RF₇ : RF dBands E.A₀ c₆ c₇ k₇ := rf_of_regs' (fun r hr => R₇ r
    ztwmm ztwmm
    ztwmm) rr₇ m₇ rm₇ o₇
  have RF₈ : RF dBands E.A₀ c₇ c₈ k₈ := RF.of_frame (F₈.mono by_decide le_rfl) hA0₇
  have RF₉ : RF dBands E.A₀ c₈ c₉ k₉ := rf_of_regs (fun r hr => R₉ r by_omega) rr₉ m₉ rm₉ o₉
  have RF₁₀ : RF dBands E.A₀ c₉ c₁₀ k₁₀ := rf_of_regs (fun r hr => R₁₀ r by_omega)
    rr₁₀ m₁₀ rm₁₀ o₁₀
  have RFall := RF56.trans (RF₇.trans ztqcj)
  have hktot : k₅ + k₆ + ztjzt ≤ E.Br := by_omega
  -- the new family
  have hF' : N'.F E.M zti = N.F E.M zti ∪ newSet E.M zti newL := by
    rw [Gran.F_of_map hmap₈, round_lset]
  have hSa : N.F E.M _ ⊆ E.M.Adm := hcur.nf.1.2.1
  have hSf : (N.F E.M _).Finite := hcur.nf.1.1
  have hdata := round_data hM hcur.nf hregs hNew
  have hdeg' := round_degLe hM hSa hSf hdata hcur.deg (round_all hcur.nf hregs hNew)
  have hN'len : N'.nChords = L.length := by
    unfold NF.nChords; rw [← hmap₈, List.length_map]
  have e₆' : Exec E.P E.W ztqvo c₅ c₆ k₆ := e₆
  refine ⟨c₁₀, k₆ + (ztock + k₁₀),
    .seq e₆' (.seq ztncq e₁₀), ?_, by_grind,
    by omega⟩
  · have e5 : ∀ q, 80000 ≤ q → q ≤ 80024 → q ≠ 80018 → q ≠ 80012 → q ≠ 80010 →
        c₁₀.nreg q = c₅.nreg q := fun q h1 h2 h3 h4 h5 =>
      Y q h1 by_omega by_omega by_omega by_omega h3 by_omega h4 h5
    have hA10 : ztsgu := by
      rw [R₁₀ _ by_decide, R₉ _ by_decide]
    have hmem10 : c₁₀.nmem = c₈.nmem := by_grind
    have hH10 : c₁₀.nreg 80012 = rd c₈ bBuild 3 := by rw [R₁₀ _ by_decide, h12]; rfl
    have E5 := e5
    have v00 : c₁₀.nreg 80000 = E.MD := (E5 _ by_omega by_omega by_omega by_omega
      by_omega).trans hgood.r00
    have v02 := (E5 _ by_omega by_omega by_omega by_omega
      by_omega).trans q02
    have v03 : c₁₀.nreg 80003 = E.D := (E5 _ by_omega by_omega by_omega by_omega
      by_omega).trans hgood.r03
    have v04 : c₁₀.nreg 80004 = E.γ := (E5 _ by_omega by_omega by_omega by_omega
      by_omega).trans hgood.r04
    have v06 : c₁₀.nreg 80006 = E.ctx := (E5 _ by_omega by_omega by_omega by_omega
      by_omega).trans hgood.r06
    have v11 := (E5 _ by_omega by_omega by_omega by_omega
      by_omega).trans q11
    have v19 : c₁₀.nreg 80019 = E.d0 + E.D := (E5 _ by_omega by_omega by_omega
      by_omega by_omega).trans hgood.r19
    have v20 := (E5 _ by_omega by_omega by_omega by_omega
      by_omega).trans hgood.r20
    have v21 := (E5 _ by_omega by_omega by_omega by_omega
      by_omega).trans q21
    have v22 := (E5 _ by_omega by_omega by_omega by_omega
      by_omega).trans q22
    have v23 := (E5 _ by_omega by_omega by_omega by_omega
      by_omega).trans hgood.r23
    have v24 := (E5 _ by_omega by_omega by_omega by_omega
      by_omega).trans hgood.r24
    have vlow : ∀ a, a < E.A₀ → c₁₀.nmem a = E.m₀ a := fun a ha => by
      rw [RFall.2.2.1 a ha, hI.low a ha]
    refine ⟨e₁₀.wb_right, v00, v02, v03, v04, v06, h10, v11, v19, v20, v21, v22, v23, v24,
      ⟨N', ?_⟩, vlow, le_trans hI.alloc RFall.2.2.2.2.2.1, by_omega, ?_⟩
    · refine ⟨by_grind, hNF₈, ?_, ?_, ?_, ?_, fun _ => ?_⟩
      · rw [hF']; exact hcur.sub.trans Set.subset_union_left
      · zudtz
        exact Model.DegLe.mono _ hdeg' (max_le by_omega by_omega)
      · zudtz
        exact semigranular_mono hM Set.subset_union_left zttcy
          ztvty hcur.sg
      · rw [hN'len, hLlen, pow_succ]
        have := hcur.size
        nlinarith
      omega
    · have h1 := RFall.2.2.2.2.2.2
      have h2 : ztgdn * ztbgq = ztzbp * ztbgq + ztbgq := by
        rw [show E.d0 + 1 - t = ztzbp + 1 by omega, Nat.add_mul, Nat.one_mul]
      omega
end
end Restore
end Chazelle.Core
namespace Chazelle.Core
namespace Restore
open Machine Machine.Stmt Programs
open Chazelle.Chain (sideInArc sidePt)
open Chazelle.Geometry (lerp)
@[expose] public section
variable {M : Model}

/-- **A good model has a counted walk edge.** -/
theorem exists_counted (hG : GoodModel M) : ∃ p, p < M.W.n ∧ M.counted p := by
  zudfb
  · refine ⟨6, ?_, ?_⟩
    · show 6 < (C.sideWalk C.sideBeta).n
      rw [C.sideWalk_n]; omega
    · show 6 ≤ 6 ∧ 6 < 2 * C.m + 6
      have := C.one_le; omega
  · refine ⟨0, ?_, trivial⟩
    show 0 < (interiorWalk Q).n
    zugcj

/-- **A semigranularity bound of a chord family of a good model is positive.** -/
theorem one_le_gamma (hG : GoodModel M) {Q : Polygon} {S : Set ztf} {γ : ℕ}
    (hS : M.ChordFamily Q S) (h : M.Semigranular S γ) : 1 ≤ γ := by
  have hM := walkAx_of_goodModel hG
  obtain ⟨p₀, hp₀, hc₀⟩ := exists_counted hG
  by_contra hγ
  have hγ0 : γ = 0 := by_omega
  subst hγ0
  rcases S.eq_empty_or_nonempty with rfl | hne
  · have hD : M.D ∈ M.regions ∅ := by
      show M.D ∈ Chazelle.Chain.regionsIn M.D ∅
      rw [Chazelle.Chain.regionsIn_empty hM.preconn hM.nonempty]; rfl
    have h1 := h M.D hD
    rw [Gran.weight_empty hM hD] at h1
    have : 1 ≤ M.size := by
      zujpy
      rw [Nat.one_le_iff_ne_zero]
      zubww
      rw [Set.ncard_eq_zero (hs := (Set.finite_lt_nat M.W.n).subset fun p hp => hp.1)] at h0
      exact (Set.eq_empty_iff_forall_notMem.1 h0) p₀ ⟨hp₀, hc₀⟩
    omega
  · exact hM.not_semigranular_zero hS.2.1 hS.1 hne hp₀ hc₀ h
variable (Q : Polygon)
theorem key00 : M.key Q ztbqw = 0 := by zunpm
theorem key10 : M.key Q ⟨1, 0⟩ = 1 := by zunpm

/-- The subarc from key `0` to key `1` meets at most one counted edge. -/
theorem arcWt01 : M.arcWt ztxvi ztnms ≤ 1 := by
  zukxf
  zuiqa
  calc _ ≤ ({0} : Set ℕ).ncard := by
        refine Set.ncard_le_ncard ?_ (Set.finite_singleton 0)
        rintro p ⟨-, -, t, ht0, ht1, hin⟩
        simp only [sideInArc, zero_lt_one, ite_true] at hin
        have : (p : ℝ) < 1 := by_grind
        simp_all
    _ = 1 := Set.ncard_singleton 0
theorem properPos0 (n : ℕ) (e : ℕ) : ProperPos M Q n ztjy :=
  ⟨by_rfl, by_positivity, by_simp⟩

/-- The points of the subarc from key `0` to key `1` lie on the segment of the first walk edge. -/
theorem arcSet01_sub {x : Point} (hn : 2 ≤ M.W.n)
    (hx : x ∈ M.arcSet 0 1) : ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ x = lerp (M.W.vtx 0) (M.W.vtx 1) s := by
  obtain ⟨p, t, hp, ht0, ht1, hk, rfl⟩ := hx
  have hwb : ztxrr := fun q hq => by
    show M.W.vtx ztxls = _; zuost
  have hkey : (p : ℝ) + t ≤ 1 := by
    rcases hk with h | h | h
    · simp only [sideInArc, zero_lt_one, ite_true] at h; grind
    · linarith
    simp_all
  have hp1 : p ≤ 1 := by
    have : (p : ℝ) ≤ 1 := by_linarith
    simp_all
  rcases Nat.lt_or_ge p 1 with h0 | h1
  · have : ztidy := by_omega
    zumo
    refine ztezc
    tauto
  · have : p = 1 := by_omega
    zumo
    zukfz
    zucfb
    refine ⟨1, by_norm_num, le_rfl, ?_⟩
    rw [Geometry.lerp_zero, Geometry.lerp_one]; rfl

/-- **The walk vertex `2` is not on the first walk edge** of a good model. -/
theorem vtx2_not_mem (hG : GoodModel M) (Q : Polygon) :
    M.pos Q ztkin ∉ M.arcSet ztxvi ztnms := by
  zukxf
  have hpos : M.pos Q ztkin = M.W.vtx 2 := by
    simp [Model.pos, Model.param, Geometry.lerp, Model.wa]
  zudul
  zuetb
  rcases hG with ⟨C, -, rfl⟩ | ⟨Q', hQ', rfl⟩
  · have hn : 2 ≤ (chainModel C).W.n := by
      show 2 ≤ (C.sideWalk C.sideBeta).n; rw [C.sideWalk_n]; omega
    obtain ⟨s, hs0, hs1, he⟩ := arcSet01_sub hn hx
    have e2 : ztwsl := rfl
    zuffb

    rw [e2, e0, e1] at he
    zukhf
    simp only [Geometry.lerp_snd, Chain.slitTop, sub_self, mul_zero, add_zero] at hy
    have := C.radius_pos
    linarith
  · have hsimp := (FactsInterior.interiorWalk_spec hQ').1
    have hn3 : 3 ≤ (interiorWalk Q').n := Jordan.simple_three_le hsimp
    obtain ⟨s, hs0, hs1, he⟩ := arcSet01_sub (by show 2 ≤ (interiorWalk Q').n; omega) hx
    set W := interiorWalk Q' with hWd
    have hv : ∀ q, q < W.n → sidePt W q 0 = W.vtx q := fun q _ => by
      zufdr
    have hs01 : ∀ s : ℝ, lerp ztvdz ztvea s = sidePt W 0 s := fun s => by
      unfold sidePt; zvmyc
    zukmg
    · have := FactsInterior.pos_unique hsimp (p := 2) (p' := 0) (t := 0) (t' := s)
        by_omega by_omega le_rfl by_norm_num hs0 hs1
        (by rw [hv 2 by_omega, ← hs01]; exact he)
      omega
    · have := FactsInterior.pos_unique hsimp (p := 2) (p' := 1) (t := 0) (t' := 0)
        by_omega by_omega le_rfl by_norm_num le_rfl by_norm_num
        (by
          change W.vtx 2 = lerp ztvdz ztvea 1 at he
          rw [hv 2 by_omega, hv 1 by_omega, he, Geometry.lerp_one])
      omega

/-- The configuration `c` with the inputs of an oracle query in band `b`: model `MD`, subarc
`⟨0,0⟩ … ⟨1,0⟩`, origin the walk vertex `2`, weight bound `γ`, context `g`. -/
def setQ (c : Config) (b MD γ g : ℕ) : Config :=
  { c with nreg := fun r =>
      if r = bandReg b 0 then MD else if r = bandReg b 3 then 1 else
      if r = bandReg b 5 then 2 else if r = bandReg b 6 then 2 else
      if r = bandReg b 9 then γ else if r = bandReg b 13 then g else
      if bandReg b 0 ≤ r ∧ r ≤ bandReg b 13 then 0 else c.nreg r }
theorem setQ_wb {W : ℕ} {c : Config} (hw : WordsBounded W c) {b MD γ g : ℕ} (h2 : 2 ≤ W)
    (hMD : MD ≤ W) (hγ : γ ≤ W) (hg : g ≤ W) : WordsBounded W (setQ c b MD γ g) := by
  refine ⟨fun r => ?_, hw.2⟩
  simp only [setQ]
  split_ifs <;> first | assumption | omega | exact hw.1 r
theorem setQ_alloc (c : Config) {b MD γ g : ℕ} (hb : 1 ≤ b) :
    (setQ c b MD γ g).nreg ALLOC = c.nreg ALLOC := by
  unfold setQ
  zubi
  split_ifs with h1 h2 h3 h4 h5 h6 h7 <;>
    first | rfl | (exfalso; simp only [bandReg, ALLOC] at *; omega)

/-- **The oracle costs are positive** in the context of `RestoreSpec`. -/
theorem oracle_pos {sh cu : Stmt} {Bs Bc : Finset ℕ} {F G H : ℕ → ℕ} {X : MemCtx}
    {Ok : Polygon → Model → Prop} (hsh : ShooterOK sh Bs F X Ok) (hcu : CutterOK cu Bc G H X Ok)
    {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c) (hG : GoodEnv P)
    (hWh : hostWords P.n ≤ W) {MD γ g : ℕ} (hX : X.holds P c.nmem g ztm)
    (hcap : γ ≤ X.cap P c.nmem g) (hwf : ModelDescWF P ztm c.nmem MD)
    (hreg : c.nmem MD = 0 → ∀ H C, ChainDescAt c.nmem ztki zta H C →
      HostRegular (Qof P).n H)
    (hMD : ModelDescAt c.nmem MD zta M) (hGM : GoodModel M) (hOk : Ok P M) (hγ : 1 ≤ γ)
    (hMDW : MD ≤ W) (hγW : γ ≤ W) (hgW : g ≤ W) : 1 ≤ F γ ∧ 1 ≤ G γ := by
  have h2 : zteht := le_trans ztdmm hWh
  have hn2 : 2 < M.W.n := by
    rcases hGM with ⟨C, -, rfl⟩ | ⟨Q, hQ, rfl⟩
    · show 2 < (C.sideWalk C.sideBeta).n; rw [C.sideWalk_n]; omega
    · show 2 < (interiorWalk Q).n
      zugcj
  constructor
  · set cS := setQ c bShoot MD γ g with hcS
    have r0 : rd cS bShoot 0 = MD := by_rfl
    have r1 : rd cS bShoot 1 = 0 := by_rfl
    have r2 : rd cS bShoot 2 = 0 := by_rfl
    have r3 : rd cS bShoot 3 = 1 := by_rfl
    have r4 : rd cS bShoot 4 = 0 := by_rfl
    have r9 : rd cS bShoot 9 = γ := by_rfl
    have r13 : rd cS bShoot 13 = g := by_rfl
    have hwS : WordsBounded (W + F γ) cS :=
      Machine.WordsBounded.mono ztpdo by_omega
    have hA : cS.nreg ALLOC = c.nreg ALLOC := setQ_alloc c by_decide
    have hO : OriginIn cS ztbpu (.walk ztkin) :=
      ⟨by_rfl, by_rfl,
       by rfl⟩
    zuixg
    have := shooter_cost_pos hsh (W := W + F γ) hwS ⟨hG, by_omega,
      by tauto, by_tauto,
      by tauto, by_tauto, M, by_tauto, hOk,
      by rw [r1, r2]; exact properPos0 _ _ _, by zuomu; exact properPos0 _ _ _,
      by omega, by_omega, Or.inl r2, Or.inl r4,
      by zunmn; exact (arcWt01 _).trans hγ,
      .walk ztkin, ⟨hn2, Nat.zero_le _⟩, hO, Or.inl ⟨2, rfl⟩,
      by rw [r1, r2, r3, r4]; exact vtx2_not_mem hGM _⟩
      by_simp_all
    simp_all
  · set cC := setQ c bCut MD γ g with hcC
    have r0 : rd cC bCut 0 = MD := by_rfl
    have r1 : rd cC bCut 1 = 0 := by_rfl
    have r2 : rd cC bCut 2 = 0 := by_rfl
    have r3 : rd cC bCut 3 = 1 := by_rfl
    have r4 : rd cC bCut 4 = 0 := by_rfl
    have r9 : rd cC bCut 9 = γ := by_rfl
    have r13 : rd cC bCut 13 = g := by_rfl
    have hwC : WordsBounded (W + G γ) cC :=
      Machine.WordsBounded.mono ztpdo by_omega
    have hA : cC.nreg ALLOC = c.nreg ALLOC := setQ_alloc c by_decide
    zuixg
    have := cutter_cost_pos hcu (W := W + G γ) hwC ⟨hG, by_omega,
      by tauto, by_tauto,
      by tauto, M, by_tauto, hOk,
      by rw [r1, r2]; exact properPos0 _ _ _, by zuomu; exact properPos0 _ _ _,
      by omega, by_omega, Or.inl r2, Or.inl r4,
      by zunmn; exact (arcWt01 _).trans hγ⟩
      by_simp_all
    simp_all
end
end Restore
end Chazelle.Core
namespace Chazelle.Core
namespace Restore
open Machine Machine.Stmt Programs
@[expose] public section
def RestoreSpecLocal : Prop :=
  ∃ (mk : Stmt → Stmt → Stmt) (κ cR : ℕ → ℕ → ℕ), ∀ (sh cu : Stmt)
    (Bs Bc : Finset ℕ) (F G H : ℕ → ℕ) (X : MemCtx) (Ok : Polygon → Model → Prop),
    CapLocal X → X.Halves → ztcxi →
    Bs ⊆ oracleBands → Bc ⊆ oracleBands → ShooterOK sh Bs F X Ok → CutterOK cu Bc G H X Ok →
    Meets ztdvk zttyt
      (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧
        X.holds P c.nmem ztiab ztm ∧
        rd c bRestore 4 ≤ X.cap P c.nmem ztiab ∧ 4 ≤ rd c bRestore 3 ∧
        ModelDescWF P ztm c.nmem ztcdq ∧
        (c.nmem ztcdq = 0 → ∀ H C,
          ChainDescAt c.nmem ztfig zta H C → HostRegular (Qof P).n H) ∧
        (c.nmem ztcdq = 0 → ∀ H C,
          ChainDescAt c.nmem ztfig zta H C → C.P.Simple) ∧
        ∃ M N, ModelDescAt c.nmem ztcdq zta M ∧ GoodModel M ∧ Ok P M ∧
          M.FullDegLe zta ztdad ∧
          NFWithin c.nmem ztdac ztm N ∧ IsNF M zta N ∧
          M.DegLe ztwiv ztefw ∧
          M.Semigranular ztwiv ztbrm)
      (fun P c c' => ∀ M N, ModelDescAt c.nmem ztcdq zta M →
        NFAt c.nmem ztdac N →
        ∃ N', c.nreg ALLOC ≤ rd c' bRestore 5 ∧
          NFWithin c'.nmem ztrvq ztdo N' ∧ IsNF M zta N' ∧
          N.F M zta ⊆ N'.F M zta ∧ M.DegLe ztxvm ztdad ∧
          M.Semigranular ztxvm ztbrm ∧
          N'.nChords ≤ cR ztefw ztdad * zthbn)
      (fun _ c => κ ztefw ztdad * ztxnh *
        F ztbrm * G ztbrm *
        (H ztbrm + Nat.clog 2 ztbrm +
          Nat.clog 2 ztxnh + 1))

/-! ## The round loop -/

/-- **All rounds.** -/
theorem rounds_exec {E : DrvEnv} (hE : DrvGood E) {c : Config} (hI : OutI E 0 c) :
    ∃ c' k, Exec E.P E.W (.whileLtN 80010 80011 ztkec) c c' k ∧
      OutI E ztfnl c' ∧ RF dBands E.A₀ c c' k ∧ k ≤ ztbgq * ztfnl + 2 := by
  obtain ⟨c', k, e, ⟨t, I'⟩, hx, RFl, hk⟩ := whileLtN_frame (P := E.P) (W := E.W)
    (a := 80010) (b := 80011) (body := roundBody E.sF E.sB) (B := dBands) (A₀ := E.A₀)
    (fun c => ∃ t, OutI E t c) (fun c => E.d0 + 1 - c.nreg 80010) E.Br
    ztdnu
    (fun c ⟨t, I⟩ ht => by
      rw [I.r10, I.r11] at ht
      zucxk
      exact ztfdc) ⟨0, hI⟩
  have ht : t = E.d0 + 1 := by
    rw [I'.r10, I'.r11] at hx; have := I'.t_le; omega
  zucfb
  zuhja

/-! ## Arithmetic of the cost -/
theorem clog_two_pow_mul (j x : ℕ) : Nat.clog 2 (2 ^ j * x) ≤ j + Nat.clog 2 x := by
  zudwq
  zujlg
  exact Nat.mul_le_mul_left _ (Nat.le_pow_clog by_norm_num x)

/-- The constant of the round bound. -/
def C1 (κf : ℕ → ℕ) (κB d0 D : ℕ) : ℕ :=
  40 + 21 * 2 ^ ztcmy + (κf (d0 + D) + 22) * 2 ^ ztcmy +
    κB * (2 * 2 ^ ztcmy * (d0 + 3) + 1)

/-- The constant of the cost bound. -/
def κRestore (κf : ℕ → ℕ) (κB : ℕ) (d0 D : ℕ) : ℕ :=
  ztcmy * zthac + d0 + D + 20
set_option maxHeartbeats 4000000 in
/-- **The round bound is linear.** -/
theorem Br_le (E : DrvEnv) (hF : 1 ≤ E.F E.γ) (hG : 1 ≤ E.G E.γ) :
    E.Br ≤ C1 E.κf E.κB E.d0 E.D * ztbjj * (E.F E.γ * E.G E.γ *
      ztxrx) := by
  set T := 2 ^ ztfnl with hT
  zuinv
  set A := E.F E.γ * E.G E.γ * (E.Hc E.γ + Nat.clog 2 E.γ + Nat.clog 2 K1 + 1) with hA
  set A0 := E.F E.γ * E.G E.γ * ztdyl with hA0
  set L := Nat.clog 2 K1 with hL
  have hFG : 1 ≤ E.F E.γ * E.G E.γ := Nat.one_le_iff_ne_zero.2 by_positivity
  have hA1 : 1 ≤ A := by
    grind
  have hA0A : A0 ≤ A := by
    grind
  have hLA : L + 1 ≤ A := by
    zugum
    calc L + 1 ≤ 1 * ztkpz := by_omega
      _ ≤ E.F E.γ * E.G E.γ * ztkpz := Nat.mul_le_mul_right _ hFG
  have hKc : E.Kc = T * K1 := rfl
  have hBf : E.Bf = E.κf ztjig * A0 + 20 := by
    unfold DrvEnv.Bf costF; grind
  have hcl : Nat.clog 2 (2 * E.Kc) ≤ E.d0 + 2 + L := by
    have : 2 * E.Kc = 2 ^ (E.d0 + 2) * K1 := by_grind
    zvmwk; exact clog_two_pow_mul _ _
  have hBr : E.Br = 40 + 21 * E.Kc + ztnd * E.Kc +
      E.κB * ztxjz := rfl
  have hK1p : 1 ≤ K1 := by_omega
  have hTp : 1 ≤ T := Nat.one_le_two_pow
  -- the four terms
  have t1 : 40 ≤ 40 * K1 * A := by_nlinarith
  have t2 : 21 * E.Kc ≤ 21 * T * K1 * A := by rw [hKc]; nlinarith
  have t3 : ztnd * E.Kc ≤ ztzjv * T * K1 * A := by
    rw [hBf, hKc]
    grind
  have t4 : 2 * E.Kc * ztlfj + 1 ≤
      ztjfc * K1 * A := by
    zummp
    have h1 : 2 * ztbmh * (Nat.clog 2 (2 * ztbmh) + 1) ≤
        2 * ztbmh * ztpxj := Nat.mul_le_mul_left _ by_grind
    have h2 : E.d0 + 3 + L ≤ ztswy * A := by_nlinarith
    have h3 : 2 * ztbmh * ztpxj ≤ 2 * ztbmh * (ztswy * A) :=
      Nat.mul_le_mul_left _ h2
    nlinarith
  have t4' := Nat.mul_le_mul_left E.κB t4
  have hC : C1 E.κf E.κB E.d0 E.D * ztbjj * (E.F E.γ * E.G E.γ *
      ztxrx) =
      40 * K1 * A + 21 * T * K1 * A + ztzjv * T * K1 * A +
        E.κB * (ztjfc * K1 * A) := by
    unfold C1; grind
  grind
set_option maxHeartbeats 8000000 in
/-- **WP-E: restoring conformality**, from the splitting step (`FindSpec`) and the construction
of normal forms, for memory contexts with a local capacity. -/
theorem restoreSpecLocal_of_find (hB : BuildNFSpec) (hF : FindSpec) : RestoreSpecLocal := by
  obtain ⟨sB, κB, hsB⟩ := Gran.buildOK_of hB
  obtain ⟨mkF, κf, hmkF⟩ := hF
  refine ⟨fun sh cu => restoreStmt (mkF sh cu) sB, κRestore κf κB, fun d0 _ => 2 ^ ztcmy, ?_⟩
  intro sh cu Bs Bc F G H X Ok hloc hhalf hOkM hBs hBc hsh hcu P W c hw pre hroom
  obtain ⟨hGE, hWh, hX, hcap, hD4, hwf, hreg, hsimp, M, N, hMD, hGM, hOk, hfull, hNW, hNF, hdeg, hsg⟩ := pre
  zubmr
  have e0 : rd c bRestore 0 = c.nreg 80000 := rfl
  have e1 : rd c bRestore 1 = c.nreg 80001 := rfl
  have e2 : rd c bRestore 2 = c.nreg 80002 := rfl
  have e3 : rd c bRestore 3 = c.nreg 80003 := rfl
  have e4 : rd c bRestore 4 = c.nreg 80004 := rfl
  have e6 : rd c bRestore 6 = c.nreg 80006 := rfl
  zvokq at hwf hMD hreg hsimp
  zuelk

  zvnak at hfull hD4 hroom
  rw [e4] at hsg hcap hroom
  rw [e6] at hX hcap
  rw [e0, e1, e2, e3, e4]
  set MD := c.nreg 80000 with hMDd
  set NFH := c.nreg 80001 with hNFHd
  set d0 := c.nreg 80002 with hd0d
  set D := c.nreg 80003 with hDd
  set γ := c.nreg 80004 with hγd
  set g := c.nreg 80006 with hgd
  zucvx

  have hγ1 := one_le_gamma hGM hNF.1 hsg
  obtain ⟨hF1, hG1⟩ := oracle_pos hsh hcu hw hGE hWh hX hcap hwf hreg hMD hGM hOk hγ1
    zthyb zthyb zthyb
  -- the driver data
  set E : DrvEnv := ⟨P, W, M, c.nreg ALLOC, c.nmem, MD, d0, D, γ, g, mkF sh cu, sB, κf, κB, F, G,
    H, X, Ok, N.F M zta, K⟩ with hEd
  have hE : DrvGood E := ⟨hmkF sh cu Bs Bc F G H X Ok oracleBands subset_rfl by_decide hloc hhalf
    by_grind
    hBs hBc hsh hcu, hsB, hGE, hWh, hX,
    fun m hm => by
      show γ ≤ X.cap P m g
      rw [hloc P c.nmem m g _ hm hX]; omega,
    hwf, hMD, hreg, hsimp, hGM, hOk, hfull⟩
  -- cost bounds
  set A := F γ * G γ * ztxry with hAd
  have hFG : 1 ≤ F γ * G γ := Nat.one_le_iff_ne_zero.2 by_positivity
  have hA1 : 1 ≤ A := by_grind
  have hBr : E.Br ≤ C1 κf κB d0 D * ztbr * A := Br_le E hF1 hG1
  have hcost : κRestore κf κB d0 D * ztbr * F γ * G γ *
      ztxry = κRestore κf κB d0 D * ztbr * A := by
    grind
  zuexw
  have hK1A : 1 ≤ ztbr * A := by_grind
  have hbig : ztbgq * ztfnl + 20 + d0 + D ≤ κRestore κf κB d0 D * ztbr * A := by
    have h1 : ztbgq * ztcmy ≤ ztxva * ztcmy :=
      Nat.mul_le_mul_right _ by_omega
    have h2 : κRestore κf κB d0 D * ztbr * A =
        ztcmy * zthac * ztxyr + ztqlu * ztxyr := by
      unfold κRestore; ring
    have h3 : ztxva * ztcmy ≤
        ztcmy * zthac * ztxyr := by_nlinarith
    have h4 : d0 + D + 20 ≤ ztqlu * ztxyr := Nat.le_mul_of_pos_right _ hK1A
    grind
  -- initialisation
  have hn3 := Jordan.simple_three_le hGE.1
  zudof
  zueqh
  obtain ⟨c₁, k₁, e₁, hk₁, i20, i21, i22, i23, i24, i12, i10, i11, i19, R₁, rr₁, m₁, rm₁, o₁⟩ :=
    init_exec (P := P) c hw hW5 by_omega by_omega
  zud
  zuhdp
  have hI0 : OutI E 0 c₁ := by
    refine ⟨w₁, by_grind, by_grind,
      by grind, by_grind,
      by grind, i10, i11, i19, i20, i21, i22, i23, i24, ⟨N, ?_⟩,
      by grind, by rw [A₁], by_omega, ?_⟩
    · refine ⟨by_grind, hNF, subset_rfl, ?_, hsg, by_grind, fun h => ?_⟩
      · exact Model.DegLe.mono _ hdeg by_grind
      · omega
    grind
  -- the rounds
  zudef
  obtain ⟨N₂, hcur₂⟩ := I₂.cur
  -- the output
  obtain ⟨c₃, k₃, e₃, hk₃, h05, R₃, rr₃, m₃, rm₃, o₃⟩ := copy1_exec' (P := P) c₂ I₂.wb 80005 80012
  have RF₁ : RF dBands ztm c c₁ k₁ :=
    rf_of_regs by_grind rr₁ m₁ rm₁ o₁
  have RF₃ : RF dBands ztm c₂ c₃ k₃ :=
    rf_of_regs by_grind rr₃ m₃ rm₃ o₃
  zulha
  refine ⟨c₃, k₁ + zttl, .seq e₁ ztcr, ?_, ?_, RFall.to_frame⟩
  · grind
  · intro M' N' hM' hN'
    have hMM := NFLoc.modelDesc_unique hMD hM'
    subst hMM
    have hch := NFLoc.nfAt_chords_eq hNW.nfAt hN'
    have hFeq : N'.F M _ = N.F M zta := Gran.F_congr hch
    have hA3 : ztbox := R₃ _ by_decide
    have hKN' : N'.nChords = K := by
      show N'.chords.length = N.chords.length; rw [hch]
    refine ⟨N₂, ?_, ?_, hcur₂.nf, by rw [hFeq]; exact hcur₂.sub, ?_, hcur₂.sg, ?_⟩
    · show c.nreg ALLOC ≤ c₃.nreg 80005
      rw [h05]; exact hcur₂.fresh by_omega
    · show NFWithin c₃.nmem (c₃.nreg 80005) _ N₂
      rw [h05, m₃, hA3]; exact hcur₂.nw
    · exact Model.DegLe.mono _ hcur₂.deg by_grind
    · have hs := hcur₂.size
      grind
end
end Restore
@[expose] public section
theorem restoreSpec_of_find (hB : BuildNFSpec) (hF : Restore.FindSpec) : RestoreSpec := by
  obtain ⟨mk, κ, cR, h⟩ := Restore.restoreSpecLocal_of_find hB hF
  exact ⟨mk, κ, cR, fun sh cu Bs Bc F G H X Ok hloc hhalf hOkM hBs hBc hsh hcu =>
    h sh cu Bs Bc F G H X Ok hloc hhalf hOkM hBs hBc hsh hcu⟩
end
namespace MergeAsm
open Machine Machine.Stmt Programs SignK
@[expose] public section
def MB : Finset ℕ := mergeBands ∪ oracleBands
theorem frame_band {b : ℕ} {c c' : Config} (h : FrameB (inBand b) c c') (hb : b ∈ MB)
    (hb0 : b ≠ 0) (k : ℕ) : Frame MB c c' k :=
  NFLoc.frame_of_frameB h (fun r hr => by
    simp only [inBand, decide_eq_true_eq] at hr
    refine ⟨hr ▸ hb, fun h => ?_⟩
    zvmwc at hr; tauto) k
theorem ftr {c c₁ c₂ : Config} {k₁ k₂ : ℕ} (h₁ : Frame MB c c₁ k₁)
    (h₂ : Frame MB c₁ c₂ k₂) : Frame MB c c₂ ztbct :=
  (h₁.trans h₂).mono by_simp le_rfl
theorem holds_frame {X : MemCtx} {P : Polygon} {g : ℕ} {B : Finset ℕ} {c c' : Config} {k : ℕ}
    (hX : X.holds P c.nmem g ztm) (hf : Frame B c c' k) :
    X.holds P c'.nmem g ztdo :=
  X.mono _ _ _ _ _ hf.2.2.2.2.2.1 ztfow
theorem cap_frame {X : MemCtx} (hloc : X.CapLocal) {P : Polygon} {g : ℕ} {B : Finset ℕ}
    {c c' : Config} {k : ℕ} (hX : X.holds P c.nmem g ztm) (hf : Frame B c c' k) :
    X.cap P c'.nmem g = X.cap P c.nmem g :=
  hloc P c.nmem c'.nmem g _ ztnym hX

/-- The frame of the descriptor copy. -/
theorem descS_frame {c c' : Config} {A : ℕ} (hA : c.nreg ALLOC = A) (hA' : c'.nreg ALLOC = A + 6)
    (hm : ∀ a, (a < A ∨ A + 6 ≤ a) → c'.nmem a = c.nmem a)
    (hr : ∀ r, ztofh → r ≠ ALLOC → c'.nreg r = c.nreg r)
    (hrr : c'.rreg = c.rreg) (hrm : c'.rmem = c.rmem) (ho : c'.output = c.output) :
    Frame MB c c' 27 := by
  refine ⟨fun r hb hra => hr r ?_ hra, fun r _ => by zvnhk, fun a ha => hm a by_omega,
    fun a _ => by zvnmc, ho, by_omega, by_omega⟩
  zubq

  apply hb
  zugkq
  zuvs

/-! ## The constant -/

/-- The largest value of `f` on `0 … n`. -/
def supTo (f : ℕ → ℕ) (n : ℕ) : ℕ := (Finset.range ztkk).sup f
theorem le_supTo {f : ℕ → ℕ} {n d : ℕ} (h : d ≤ n) : f d ≤ supTo f n :=
  Finset.le_sup (f := f) (Finset.mem_range.2 by_omega)

/-- The constant of Lemma 2.3 in the form `K₁ + K₂ + 1 ≤ β (m + 1)`. -/
def βf (c23 : ℕ → ℕ) (D : ℕ) : ℕ := 16 * c23 D + 1

/-- **The constant of the merge.** -/
def κM (κF capF : ℕ → ℕ) (κR cR : ℕ → ℕ → ℕ) (κG c23 : ℕ → ℕ) (D : ℕ) : ℕ :=
  κF D * (βf c23 D + 2) + 8 * (βf c23 D + 7) * supTo ztpbh zthvn +
    κG D * (8 * supTo ztijl zthvn *
      (8 * supTo ztijl zthvn * βf c23 D + 1) + 1) + 123

/-! ## Oracle positivity -/

/-- The configuration `c` with a model descriptor of the chain at `bw` written at the allocator
(used only to apply `Restore.oracle_pos`). -/
def withDesc (c : Config) (bw : ℕ) : Config :=
  { c with
    nreg := upd c.nreg ALLOC zthve
    nmem := fun a => if a = c.nreg ALLOC then 0
      else if c.nreg ALLOC < a ∧ a < c.nreg ALLOC + 6 then c.nmem (bw + (a - c.nreg ALLOC - 1))
      else c.nmem a }
theorem oracle_pos_merge {sh cu : Stmt} {Bs Bc : Finset ℕ} {F G H : ℕ → ℕ} {X : MemCtx}
    {Ok : Polygon → Model → Prop} (hloc : X.CapLocal) (hsh : ShooterOK sh Bs F X Ok)
    (hcu : CutterOK cu Bc G H X Ok) {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c)
    (hG : GoodEnv P) (hWh : hostWords P.n ≤ W) {g γ bw : ℕ}
    (hX : X.holds P c.nmem g ztm) (hcap : γ ≤ X.cap P c.nmem g) (hγ : 1 ≤ γ)
    (hγW : γ ≤ W + 6) (hgW : g ≤ W) {Hs : Host} {C : Chain}
    (hwf : ChainWF P ztm c.nmem bw) (hC : ChainDescAt c.nmem bw zta Hs C)
    (hP : C.P.Simple) (hOk : Ok P ztc) (hreg : HostRegular (Qof P).n Hs) :
    1 ≤ F γ ∧ 1 ≤ G γ := by
  obtain ⟨A, hAd⟩ : ztgbe := zths
  rw [hAd] at hwf hX
  set ĉ := withDesc c bw
  have hA : ĉ.nreg ALLOC = A + 6 := by simp [ĉ, withDesc, hAd]
  have hAW : ztpio := hAd ▸ hw.1 ALLOC
  have hmem : ∀ a, ĉ.nmem a = if a = A then 0 else if A < a ∧ a < A + 6 then
      c.nmem ztlgk else c.nmem a := fun a => by simp only [ĉ, withDesc, hAd]
  have he : ∀ a, a < A → ĉ.nmem a = c.nmem a := fun a ha => by
    grind
  have hbA := hwf.1
  have hw' : WordsBounded (W + 6) ĉ := by
    refine ⟨fun r => ?_, fun a => ?_⟩
    · simp only [ĉ, withDesc]
      by_cases hr : r = ALLOC
      · subst hr; zumwv; omega
      · simp only [upd_other _ _ _ hr]; have := hw.1 r; omega
    · zujjj
      split_ifs
      · omega
      · have := hw.2 ztlgk; omega
      · have := hw.2 a; omega
  have h0 : ĉ.nmem A = 0 := by_grind
  have hc : ∀ j, j < 5 → ĉ.nmem ztcsp = c.nmem ztctz := fun j hj => by
    grind
  obtain ⟨hMD, hMWF⟩ := modelDesc_copy hwf hC le_rfl he h0 hc (E' := A + 6) le_rfl
  have hCd : ChainDescAt ĉ.nmem ztbo zta Hs C := by
    obtain ⟨-, -, hEb, -⟩ := hwf.2 Hs C hC
    exact chainDescAt_copy hC hEb he hc
  have hreg' : ĉ.nmem A = 0 → ∀ H' C', ChainDescAt ĉ.nmem ztbo zta H' C' →
      HostRegular (Qof P).n H' := fun _ H' C' h' => by
    rw [NFLoc.hostAt_unique h'.1 hCd.1]; omega
  have hX' : X.holds P ĉ.nmem g (ĉ.nreg ALLOC) := by
    zugum
    exact X.mono _ _ _ _ _ by_omega (X.local_ _ _ _ _ _ ztkvx hX)
  have hcap' : γ ≤ X.cap P ĉ.nmem g := by
    rw [hloc P c.nmem ĉ.nmem g _ he hX]; omega
  exact Restore.oracle_pos hsh hcu hw' hG by_omega hX' hcap' by_grind hreg' hMD
    ztxgi hOk hγ by_omega hγW by_omega
theorem keepF {B : Finset ℕ} {c c' : Config} {k : ℕ} (hf : Frame B c c' k) (r : ℕ)
    (hr : bandOf r ∉ B) (hA : r ≠ ALLOC) : c'.nreg r = c.nreg r := hf.1 r hr hA
set_option maxHeartbeats 8000000 in
/-- **WP-F: Lemma 3.5.** -/
theorem mergeSpec_of (hF : FuseSpec) (hR : RestoreSpec) (hG : GranularizeSpec) : MergeSpec := by
  obtain ⟨fMk, κF, capF, hFu⟩ := hF
  obtain ⟨rMk, κR, cR, hRe⟩ := hR
  obtain ⟨gS, κG, hGr⟩ := hG
  obtain ⟨c23, h23⟩ := lemma23
  refine ⟨mergeMk fMk rMk gS, κM κF capF κR cR κG c23, ?_⟩
  intro sh cu Bs Bc F G H X Ok hloc hhalf hOkM hFm hGm hHm hBs hBc hsh hcu
  have hFuse := hFu sh Bs F X Ok hloc hBs hsh
  have hRes := hRe sh cu Bs Bc F G H X Ok hloc hhalf hOkM hBs hBc hsh hcu
  zubgq
  obtain ⟨hGE, hWh, hX, hcap, hD4, hγ, hJWF, Hs, J, N₁, N₂, hJ, hPs, hSG, hOk1, hOk2,
    hOkw, hFull, hN1, hN2, ⟨γ₁, hγ₁, hc1⟩, ⟨γ₂, hγ₂, hc2⟩⟩ := hpre
  simp only [fuseLoss] at hcap hγ hroom
  -- names
  obtain ⟨γ₀, hγ₀⟩ : ∃ x, rd c bMerge 5 = x := zths
  obtain ⟨γt, hγt⟩ : ∃ x, rd c bMerge 6 = x := zths
  obtain ⟨D, hD⟩ : ∃ x, rd c bMerge 7 = x := zths
  obtain ⟨g, hg⟩ : ∃ x, rd c bMerge 9 = x := zths
  obtain ⟨bw, hbw⟩ : ∃ x, rd c bMerge 2 = x := zths
  obtain ⟨A0, hA0⟩ : ztcgh := zths
  rw [hγ₀] at hcap hγ hγ₁ hγ₂ hroom
  rw [hγt] at hγ
  rw [hD] at hD4 hFull hc1 hc2 hroom
  rw [hg, hA0] at hX
  rw [hg] at hcap
  rw [hbw] at hJ hJWF hroom
  have hK1 : ztplu := hN1.nfAt.1
  have hK2 : ztplv := hN2.nfAt.1
  have hm : ztunk := hJ.2.2.2.2.2.1
  rw [hK1, hK2, hm] at hroom
  have hwfw : ChainWF P A0 c.nmem bw := by zunvv; exact hJWF.2.2.1
  have hbA := hwfw.1
  have hmn := chain_m_le hwfw hJ.2.2
  have hγtW : γt ≤ W := hγt ▸ hw.1 _
  have hgW : g ≤ W := hg ▸ hw.1 _
  have hA0W := by_omega
  have hnW : ztixx := by unfold hostWords at hWh; omega
  -- Lemma 2.3 and the oracle costs
  have hK1b := nChords_le_canonical h23 hPs hc1
  have hK2b := nChords_le_canonical h23 hPs hc2
  set β := βf c23 D with hβ
  set m := J.whole.m with hmdef
  set S := N₁.nChords + N₂.nChords + 1 with hSdef
  have hS : S ≤ β * ztbl := by
    have := S_le hK1b hK2b
    tauto
  have hregW : HostRegular (Qof P).n Hs := by
    zunht; exact hJWF.2.2.2 Hs hJ.2.2.1
  obtain ⟨hF1, hG1⟩ := oracle_pos_merge hloc hsh hcu hw hGE hWh (hA0 ▸ hX)
    hcap by_omega by_omega hgW (hA0 ▸ hwfw) hJ.2.2 hPs hOkw hregW
  set Fq := F ztbfd
  set Gq := G ztbfd
  set Hq := H ztbfd
  zudvq
  set Y := Fq * Gq * ztgdz with hY
  have hY1 : 1 ≤ Y := by
    have : 1 * 1 * 1 ≤ Fq * Gq * ztgdz := by gcongr; omega
    omega
  set kr := supTo ztpbh zthvn
  set cr := supTo ztijl zthvn
  set PF := κF D * zthlo * S * Y
  set PR := 8 * zteww * kr * S * Y
  set PG := κG D * (8 * cr * (8 * cr * β + 1) + 1) * S * Y
  set SY := S * Y with hSYdef
  have hT : κM κF capF κR cR κG c23 D * S * Fq * Gq * ztgdz =
      PF + PR + PG + 123 * SY := by
    simp only [κM, PF, PR, PG, hY, kr, cr, hβ, hSYdef]; ring
  zugdl
  have hSY : S ≤ SY := Nat.le_mul_of_pos_right _ hY1
  -- 1. the arguments of the fusion
  obtain ⟨c1, k1, e1, hk1, f0, f1, f2, f3, f4, f5, f6, f8, fr1⟩ := setF_exec (P := P) c hw
  have F1 := frame_band fr1 by_decide by_decide k1
  have m1 := fr1.2.2.1
  have a1 : ztupc := by zunvv; exact fr1.1 ALLOC by_decide
  -- 2. the fusion
  have hpreF : GoodEnv P ∧ hostWords P.n ≤ W ∧
      X.holds P c1.nmem ztrvw zterf ∧
      rd c1 bFuse 5 ≤ X.cap P c1.nmem ztrvw ∧
      JunctionWF P zterf c1.nmem ztrvt ztrvu ztrvv ∧
      ∃ H J N₁ N₂, JunctionAt c1.nmem ztrvt ztrvu ztrvv zta H J ∧
        J.P.Simple ∧ SharedGeneric J ∧
        Ok P ztbw ∧ Ok P ztj ∧ Ok P ztbm ∧
        NFWithin c1.nmem (rd c1 bFuse 3) zterf N₁ ∧
        NFWithin c1.nmem (rd c1 bFuse 4) zterf N₂ ∧
        IsNF ztbw zta N₁ ∧ IsNF ztj zta N₂ ∧
        (chainModel J.left).DegLe ztwjx ztlsq ∧
        (chainModel J.right).DegLe ztwis ztlsq ∧
        (chainModel J.left).Semigranular ztwjx ztlsp ∧
        (chainModel J.right).Semigranular ztwis ztlsp := by
    rw [m1, a1, f0, f1, f2, f3, f4, f5, f6, f8, hγ₀, hD, hg, hbw]
    refine ⟨hGE, hWh, hX, by_omega, ?_, Hs, J, N₁, N₂, hJ, hPs, hSG, hOk1, hOk2, hOkw,
      hA0 ▸ hN1, hA0 ▸ hN2, hc1.1, hc2.1, hc1.2.1, hc2.2.1,
      hc1.2.2.1.semigranular_of_le _ hγ₁, hc2.2.2.1.semigranular_of_le _ hγ₂⟩
    zunvv; omega
  have hcostF : κF ztlsq * ztghq *
      (F ztlsp + Nat.clog 2 ztghq + 1)
      ≤ PF := by
    rw [m1, f3, f4, f5, f6, hK1, hK2, hγ₀, hD]
    exact fuse_le hS (hFm by_omega) hF1 hG1
  obtain ⟨c2, k2, e2, hk2, postF, frF⟩ := hFuse P W c1 e1.wb_right hpreF (by
    rw [a1]; beta_reduce; omega)
  have hk2' := hk2.trans hcostF
  have F2 : Frame MB c1 c2 k2 := frF.mono by_decide le_rfl
  obtain ⟨Nf, hNfA, hNfW, hNf, -, hNfK, hNfD, hNfS⟩ := postF Hs J N₁ N₂
    (by zunmj; exact hJ) (by zuolk; exact hN1.nfAt)
    (by zuoll; exact hN2.nfAt)
  rw [f6, hD] at hNfD
  rw [f5, hγ₀] at hNfS
  simp only [fuseLoss] at hNfS
  have hKf : Nf.nChords + 1 ≤ 8 * S := by zunre; omega
  set Hf := rd c2 bFuse 7 with hHf
  -- 3. the model descriptor
  have a2 : A0 ≤ c2.nreg ALLOC := by zuose; exact frF.2.2.2.2.2.1
  have a2' : c2.nreg ALLOC ≤ A0 + k2 := by zuose; exact frF.2.2.2.2.2.2
  have r2 : ∀ r, bandOf r = bMerge → c2.nreg r = c.nreg r := fun r hr => by
    rw [keepF frF r ztcmf ztdgs,
      fr1.1 r ztljt]
  have mem2 : ∀ a, a < A0 → c2.nmem a = c.nmem a := fun a ha => by
    rw [frF.2.2.1 a by_omega, m1]
  obtain ⟨A, hA⟩ : ∃ x, c2.nreg ALLOC = x := zths
  obtain ⟨c3, k3, e3, hk3, v10, a3, v20, v21, h3A, h3c, m3, r3, rr3, rm3, o3⟩ :=
    descS_exec (P := P) c2 e2.wb_right hA (bw := bw) ((r2 _ by_decide).trans hbw)
      by_omega by_omega
  have F3 := hk3 ▸ descS_frame hA a3 m3 r3 rr3 rm3 o3
  have mem3 : ∀ a, a < A0 → c3.nmem a = c.nmem a := fun a ha => by
    zugwc
  -- the fused normal form at `c3`
  have hNf3 : NFWithin c3.nmem Hf _ Nf := hNfW.frame F3
  have hH3 : rd c3 bFuse 7 = Hf := r3 _ ztbuo by_decide
  obtain ⟨hHb, -, hRb, -, -, -⟩ := Gran.nf_areas hNf3
  have hRn :=
    Gran.nRegions_eq hNf (walkAx_of_goodModel (Or.inl ztkit))
  have hR0 := hRb 0 by_omega
  have hRl := hRb (Nf.nRegions - 1) by_omega
  -- 4. the maximum-degree loop
  obtain ⟨c4, k4, e4, hk4, v34, v31, v30, v32, m4, r4, fr4⟩ := mdInit_exec (P := P) c3
    e3.wb_right hH3 by_omega by_omega
  have hNfA3 := hNf3.nfAt
  have hR : c3.nmem _ = Nf.nRegions := hNfA3.2.2.1
  have hlens := lens_of_degLe hNf hNfD
  obtain ⟨c5, k5, e5, hk5, hall, hcap5, m5, r5⟩ := mdLoop_exec (P := P)
    (base := c3.nmem (Hf + 5) + 2) (R := Nf.nRegions) (Cap := capF D)
    (L := fun r => (Nf.region r).chords.length) by_omega by_omega hlens Nf.nRegions c4
    e4.wb_right ztlim ztlim
    by_omega (fun r hr => by
      rw [m4, show c3.nmem _ + 2 + 5 * r = c3.nmem _ + 5 * r + 2 by ring]
      exact (hNfA3.2.2.2.2.2.2.2.1 r hr).2.1) by_omega by_omega
    by_omega ztjwk
  have fr5 := exec_frameB e5 wr_mdLoop
  obtain ⟨d₀, hd₀⟩ : ∃ x, c5.nreg 100032 = x := zths
  rw [hd₀] at hall hcap5
  have hDeg0 : (chainModel J.whole).DegLe _ d₀ :=
    degLe_of_lens hNf hall
  -- 5. `γ_R`
  have r45 : ∀ r, bandOf r ≠ bMerge → c5.nreg r = c3.nreg r := fun r hr => by
    rw [fr5.1 r ztnuw, fr4.1 r ztnuw]
  have r35 : ∀ r, r < 100030 → c5.nreg r = c3.nreg r := fun r hr => by
    rw [r5 r by_omega by_omega by_omega by_omega, r4 r hr]
  have mem5 : c5.nmem = c3.nmem := by zuojq
  have hmW : 2 * m ≤ W := by_omega
  obtain ⟨c6, k6, e6, hk6, v45, fr6, r6⟩ := gamS_exec (P := P) c5 e5.wb_right
    (by rw [r35 _ by_decide]; omega)
    (by show c5.nreg 100005 = γ₀; rw [r35 _ by_decide, r3 _ by_omega by_decide,
      r2 _ by_decide]; exact hγ₀)
    (by show c5.nmem (c5.nreg 100002 + 2) = m
        rw [r35 _ by_decide, r3 _ by_omega by_decide, r2 _ by_decide, mem5,
          show c.nreg 100002 = bw from hbw, mem3 _ by_omega]; exact hm)
    by_omega hmW
    (by show c5.nreg 100002 + 2 ≤ W
        rw [r35 _ by_decide, r3 _ by_omega by_decide, r2 _ by_decide,
          show c.nreg 100002 = bw from hbw]; omega)
  set γR := min γ₀ _ + 1 with hγR
  have r56 : ∀ r, r < 100030 → c6.nreg r = c3.nreg r := fun r hr => by
    rw [r6 r by_omega]; exact r35 r hr
  -- 6. restoration
  obtain ⟨c7, k7, e7, hk7, s0, s1, s2, s3, s4, s6, fr7⟩ := setR_exec (P := P) c6 e6.wb_right
  have r3c : ∀ r, bandOf r = bMerge → r < 100010 → c3.nreg r = c.nreg r := fun r hr hr' => by
    rw [r3 r ztvcc ztdgs, r2 r hr]
  rw [r56 _ by_decide, v10] at s0
  rw [show rd c6 bFuse 7 = c6.nreg 70007 from rfl, r56 _ by_decide,
    show c3.nreg 70007 = rd c3 bFuse 7 from rfl, hH3] at s1
  rw [r6 _ by_decide, hd₀] at s2
  rw [show rd c6 bMerge 7 = c6.nreg 100007 from rfl, r56 _ by_decide,
    r3c _ by_decide by_decide, show c.nreg 100007 = rd c bMerge 7 from rfl, hD] at s3
  rw [v45] at s4
  rw [show rd c6 bMerge 9 = c6.nreg 100009 from rfl, r56 _ by_decide,
    r3c _ by_decide by_decide, show c.nreg 100009 = rd c bMerge 9 from rfl, hg] at s6
  have F4 := frame_band fr4 by_decide by_decide k4
  have F5 := frame_band fr5 by_decide by_decide k5
  have F6 := frame_band fr6 by_decide by_decide k6
  have F7 := frame_band fr7 by_decide by_decide k7
  have mem7 : c7.nmem = c3.nmem := by rw [fr7.2.2.1, fr6.2.2.1, mem5]
  have a7 : c7.nreg ALLOC = A + 6 := by
    rw [fr7.1 ALLOC by_decide, fr6.1 ALLOC by_decide, fr5.1 ALLOC by_decide,
      fr4.1 ALLOC by_decide, a3]
  have Fc7 : Frame MB c c7 _ :=
    ftr F1 (ftr F2 ztzvs)
  have hX0 : X.holds P c.nmem g ztm := by rw [hA0]; exact hX
  have hold7 := holds_frame hX0 Fc7
  have cap7 := cap_frame hloc hX0 Fc7
  have mem7c : ∀ a, a < A0 → c7.nmem a = c.nmem a := fun a ha => by zuoyr; exact mem3 a ha
  have hcopy7 : ∀ j, j < 5 → c7.nmem _ = c.nmem _ := fun j hj => by
    rw [mem7, h3c j hj, mem2 _ by_omega]
  obtain ⟨hMD7, hMWF7⟩ := modelDesc_copy hwfw hJ.2.2 by_omega mem7c zthey
    hcopy7 (E' := c7.nreg ALLOC) by_omega
  have hNf7 : NFWithin c7.nmem Hf _ Nf := hNf3.frame ztesc
  have hKf7 := hNf7.nfAt.1
  have hγRle : γR ≤ γ₀ + 1 := by_omega
  have hγRm : γR ≤ 8 * ztbl := by rw [hγR]; have := min_le_right γ₀ ztdk; omega
  have hpreR : GoodEnv P ∧ hostWords P.n ≤ W ∧
      X.holds P c7.nmem ztrwc ztqjm ∧
      rd c7 bRestore 4 ≤ X.cap P c7.nmem ztrwc ∧ 4 ≤ rd c7 bRestore 3 ∧
      ModelDescWF P ztqjm c7.nmem ztiag ∧
      (c7.nmem ztiag = 0 → ∀ H C,
        ChainDescAt c7.nmem ztpdj zta H C → HostRegular (Qof P).n H) ∧
      (c7.nmem ztiag = 0 → ∀ H C,
        ChainDescAt c7.nmem ztpdj zta H C → C.P.Simple) ∧
      ∃ M N, ModelDescAt c7.nmem ztiag zta M ∧ GoodModel M ∧ Ok P M ∧
        M.FullDegLe zta ztrwb ∧
        NFWithin c7.nmem (rd c7 bRestore 1) ztqjm N ∧ IsNF M zta N ∧
        M.DegLe ztwiv ztrwa ∧
        M.Semigranular ztwiv ztfug := by
    rw [s0, s1, s2, s3, s4, s6, cap7]
    refine ⟨hGE, hWh, hold7, by_omega, hD4, hMWF7, fun _ H' C' h' => ?_, fun _ H' C' h' => ?_,
      chainModel J.whole, Nf,
      hMD7,
      Or.inl ztkit, hOkw, hFull, hNf7, hNf, hDeg0,
      semigranular_min_chain' hNfS⟩
    zucdn

    · rw [NFLoc.hostAt_unique h'.1 hCd7.1]; exact hregW
    · zucdn

      rw [h'.2.1, NFLoc.hostAt_unique h'.1 hCd7.1, ← hCd7.2.1]; exact hPs
  have hcostR : κR ztrwa ztrwb * ztllv *
      F ztfug * G ztfug *
      (H ztfug + Nat.clog 2 ztfug +
        Nat.clog 2 ztllv + 1) ≤ PR := by
    rw [s1, s2, s3, s4, hKf7]
    refine (restore_le hS hKf hγRm (hFm hγRle) (hGm hγRle) (hHm hγRle)).trans ?_
    have  := le_supTo (f := fun d => κR d D) hcap5
    show 8 * zteww * κR d₀ D * S * Y ≤ 8 * zteww * kr * S * Y
    gcongr
  obtain ⟨c8, k8, e8, hk8, postR, frR⟩ := hRes P W c7 e7.wb_right hpreR (by
    rw [a7]; beta_reduce; omega)
  have hk8' := hk8.trans hcostR
  have F8 : Frame MB c7 c8 k8 := frR.mono by_decide le_rfl
  obtain ⟨Nr, -, hNrW, hNr, -, hNrD, hNrS, hNrK⟩ := postR ztbm Nf
    ztnuk (by zunsu; exact hNf7.nfAt)
  rw [s3] at hNrD
  rw [s4] at hNrS
  rw [s2, s3] at hNrK
  -- 7. the arguments of granularity enforcement
  obtain ⟨c9, k9, e9, hk9, g0, g1, g2, g3, fr9⟩ := setG_exec (P := P) c8 e8.wb_right
  have r78 : ∀ r, bandOf r = bMerge → c8.nreg r = c7.nreg r := fun r hr =>
    keepF frR r ztcmf ztdgs
  have r7 : ∀ r, bandOf r = bMerge → r < 100030 → c7.nreg r = c3.nreg r := fun r hr hr' => by
    rw [fr7.1 r ztljt, r56 r hr']
  rw [r78 _ by_decide, r7 _ by_decide by_decide, v10] at g0
  rw [show rd c8 bMerge 7 = c8.nreg 100007 from rfl, r78 _ by_decide,
    r7 _ by_decide by_decide, r3c _ by_decide by_decide,
    show c.nreg 100007 = rd c bMerge 7 from rfl, hD] at g2
  rw [show rd c8 bMerge 6 = c8.nreg 100006 from rfl, r78 _ by_decide,
    r7 _ by_decide by_decide, r3c _ by_decide by_decide,
    show c.nreg 100006 = rd c bMerge 6 from rfl, hγt] at g3
  have F9 := frame_band fr9 by_decide by_decide k9
  have mem9 := fr9.2.2.1
  have a9 := fr9.1 ALLOC by_decide
  have a8 := frR.2.2.2.2.2.2
  have he79 : ∀ a, a < c7.nreg ALLOC → c9.nmem a = c7.nmem a := fun a ha => by
    rw [mem9]; exact frR.2.2.1 a ha
  obtain ⟨-, hwhbound, -⟩ := hwfw.2 Hs J.whole hJ.2.2
  have hdesc7 : ∀ (H' : Host) (C' : Chain), ChainDescAt c.nmem bw _ H' C' →
      ChainDescAt c7.nmem _ _ H' C' := fun H' C' hC' => by
    obtain ⟨-, -, hb', -⟩ := hwfw.2 H' C' hC'
    exact chainDescAt_copy hC' by_omega mem7c hcopy7
  obtain ⟨hMD9, hMWF9, -, -⟩ := modelDesc_agree hMWF7 (by zuoyr; exact h3A)
    (hdesc7 Hs J.whole hJ.2.2) he79
  have hNr9 : NFWithin c9.nmem _ _ Nr := hNrW.frame F9
  have hKr9 : c9.nmem _ = Nr.nChords := hNr9.nfAt.1
  have hpreG : GoodEnv P ∧ hostWords P.n ≤ W ∧ 1 ≤ rd c9 bGran 2 ∧
      ModelDescWF P ztvkq c9.nmem ztrwd ∧
      ∃ M N, ModelDescAt c9.nmem ztrwd zta M ∧ GoodModel M ∧
        NFWithin c9.nmem ztlss ztvkq N ∧ IsNF M zta N ∧
        M.DegLe ztwiv ztrwe ∧
        M.Semigranular ztwiv (rd c9 bGran 3) := by
    rw [g0, g1, g2, g3]
    exact ⟨hGE, hWh, by_omega, hMWF9.mono (by zuoys; exact frR.2.2.2.2.2.1), chainModel J.whole,
      Nr, hMD9, Or.inl ztkit, hNr9, hNr, hNrD,
      hNrS.mono _ by_omega⟩
  have hcostG : κG ztrwe *
      (c9.nmem ztlss * (Nat.clog 2 (c9.nmem ztlss) + 1) + 1) ≤ PG := by
    rw [g1, g2, hKr9]
    refine gran_le hS ?_ hF1 hG1 by_omega
    have  := le_supTo (f := fun d => cR d D) hcap5
    calc Nr.nChords ≤ cR d₀ D * (Nf.nChords + 1) := hNrK
      _ ≤ cr * ztnhs := Nat.mul_le_mul this hKf
      _ = 8 * cr * S := by_ring
  obtain ⟨c10, k10, e10, hk10, postG, frG⟩ := hGr P W c9 e9.wb_right hpreG (by
    zuoys; beta_reduce; have := hcostG; omega)
  have hk10' := hk10.trans hcostG
  have F10 : Frame MB c9 c10 k10 := frG.mono by_decide le_rfl
  -- 8. the output
  obtain ⟨c11, k11, e11, hk11, o8, fr11⟩ := outS_exec (P := P) c10 e10.wb_right
  have F11 : Frame MB c10 c11 k11 :=
    NFLoc.frame_of_frameB fr11 (fun r hr => by
      simp only [beq_iff_eq] at hr; subst hr; decide) k11
  have ex : Exec P W (mergeMk fMk rMk gS sh cu) c c11
      _ :=
    .seq e1 (.seq e2 (.seq e3 (.seq e4 (.seq e5 (.seq e6 (.seq e7 (.seq e8 (.seq e9
      ztspx))))))))
  have Fall : Frame MB c c11
      _ :=
    ftr F1 (ftr F2 (ftr F3 (ftr F4 (ftr F5 (ftr F6 (ftr F7 (ftr F8 (ftr F9 (ftr F10 F11)))))))))
  refine ⟨c11, _, ex, ?_, ?_, Fall⟩
  · -- the cost
    show _ ≤ κM κF capF κR cR κG c23 _ *
      (c.nmem _ + c.nmem _ + 1) * F _ *
        G _ *
        (H _ + Nat.clog 2 _ + 1)
    rw [hD, hK1, hK2, hγ₀, hbw, hm]
    show _ ≤ κM κF capF κR cR κG c23 D * S * Fq * Gq * ztgdz
    zujik
    have h5 : k5 ≤ 56 * S + 2 := by_omega
    omega
  · -- the postcondition
    intro Hs' J' N₁' N₂' hJ' hN1' hN2'
    rw [hbw] at hJ'
    obtain ⟨Nf', -, hNfW', -, -, -, -, -⟩ := postF Hs' J' N₁' N₂'
      (by zunmj; omega) (by zuolk; omega)
      (by zuoll; omega)
    have hNf7' : NFWithin c7.nmem Hf _ Nf' :=
      hNfW'.frame ztzvs
    obtain ⟨hMD7', -⟩ := modelDesc_copy hwfw hJ'.2.2 by_omega mem7c
      zthey hcopy7 (E' := c7.nreg ALLOC) by_omega
    obtain ⟨Nr', -, hNrW', -⟩ := postR _ Nf' ztnuk
      (by zunsu; exact hNf7'.nfAt)
    obtain ⟨hMD9', -, -, -⟩ := modelDesc_agree hMWF7 zthey
      (hdesc7 Hs' J'.whole hJ'.2.2) he79
    obtain ⟨N'', hN''A, hN''W, -, hN''⟩ := postG _ Nr' (by rw [g0]; omega)
      (by rw [g1, mem9]; exact hNrW'.nfAt)
    rw [g2, g3] at hN''
    have a10 := frG.2.2.2.2.2.1
    have a11 := fr11.1 ALLOC by_decide
    have c9A : c.nreg ALLOC ≤ c9.nreg ALLOC := by
      have := (ftr F1 (ftr F2 (ftr F3 (ftr F4 (ftr F5 (ftr F6 (ftr F7 (ftr F8 F9)))))))).2.2.2.2.2.1
      omega
    refine ⟨N'', ?_, ?_, by rw [hγt, hD]; omega⟩
    · omega
    · rw [o8, fr11.2.2.1, a11]; omega
