module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.DownPhaseDrvBSig
public import Chazelle.Core.DownPhaseDrvBGeo

/-!
# Down-phase base (D9), RAM: the corner test at a host point

For the corner `a → v → b` of three host points held in the register triples `212060`, `212063`,
`212066`, `cornerS` runs nine sign tests (heights and abscissae of the neighbours against `v`, one
orientation) and decides `emitG a v b σ` for both directions: the bit `212084` for `σ = 1`
(direction code `0`), the bit `212085` for `σ = -1` (code `1`).

* `emD`: the decision on the nine bits; `emD_iff`: it is `emitG`;
* **`cornerS_exec`**: at most `2300` steps; writes the kernel registers and `212071 … 212085`.

Constants: `212000 = 1`, `212001 = 0`.
-/

namespace Chazelle.Core

namespace DrvB

open Machine Machine.Stmt Programs SignK WalkKey

@[expose] public section

/-! ## The decision on the bits -/

/-- **The corner decision on the nine bits**, for the direction codes `0` and `1`:
`A1 = [a.y < v.y]`, `A2 = [v.y < a.y]`, `B1 = [b.y < v.y]`, `B2 = [v.y < b.y]`, `D = [0 < det a v b]`,
`X1 = [v.x < a.x]`, `X2 = [a.x < v.x]`, `X3 = [b.x < v.x]`, `X4 = [v.x < b.x]`. -/
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
  have e1 : A1 = decide (a.2 < v.2) := Bool.eq_iff_iff.2 (by simpa using hA1)
  have e2 : A2 = decide (v.2 < a.2) := Bool.eq_iff_iff.2 (by simpa using hA2)
  have e3 : B1 = decide (b.2 < v.2) := Bool.eq_iff_iff.2 (by simpa using hB1)
  have e4 : B2 = decide (v.2 < b.2) := Bool.eq_iff_iff.2 (by simpa using hB2)
  have e5 : D = decide (0 < det a v b) := Bool.eq_iff_iff.2 (by simpa using hD)
  have e6 : X1 = decide (v.1 < a.1) := Bool.eq_iff_iff.2 (by simpa using hX1)
  have e7 : X2 = decide (a.1 < v.1) := Bool.eq_iff_iff.2 (by simpa using hX2)
  have e8 : X3 = decide (b.1 < v.1) := Bool.eq_iff_iff.2 (by simpa using hX3)
  have e9 : X4 = decide (v.1 < b.1) := Bool.eq_iff_iff.2 (by simpa using hX4)
  subst e1 e2 e3 e4 e5 e6 e7 e8 e9
  have h1 : (1 : ℝ) ≠ -1 := by norm_num
  have h2 : (-1 : ℝ) ≠ 1 := by norm_num
  unfold emD emitG Brute.emitR
  rcases lt_trichotomy a.2 v.2 with ha | ha | ha <;>
    rcases lt_trichotomy b.2 v.2 with hb | hb | hb
  · simp [ha, hb, not_lt.2 ha.le, not_lt.2 hb.le, ha.ne, hb.ne]
  · simp [ha, hb, not_lt.2 ha.le, ha.ne, h1]
  · simp [ha, hb, not_lt.2 ha.le, not_lt.2 hb.le, ha.ne, hb.ne', h2]
  · simp [ha, hb, not_lt.2 hb.le, hb.ne, h2]
  · simp [ha, hb]
  · simp [ha, hb, not_lt.2 hb.le, hb.ne', h1]
  · simp [ha, hb, not_lt.2 ha.le, not_lt.2 hb.le, ha.ne', hb.ne, h2]
  · simp [ha, hb, not_lt.2 ha.le, ha.ne', h2]
  · simp [ha, hb, not_lt.2 ha.le, not_lt.2 hb.le, ha.ne', hb.ne']

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
        (.ifLtN 212072 212074 (block [.copyN 212084 212073, .subN 212085 212000 212073])
          (.ifLtN 212074 212072 (block [.copyN 212084 212073, .subN 212085 212000 212073])
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
  aesop (add simp [Brute.Bt, Bcor, Bool.or_eq_true, decide_eq_true_eq]) (add safe (by omega))

theorem wr_decideS : wr (fun r => decide (212082 ≤ r ∧ r ≤ 212085)) decideS = true := by decide

set_option maxHeartbeats 4000000 in
/-- **The nine tests.** -/
theorem testsS_exec (hG : GoodEnv P) (hW : P.n + 3 ≤ W) (c : Config) (hw : WordsBounded W c)
    {sa sv sb : SymPt} (ia : SymPtIn c 212060 sa) (iv : SymPtIn c 212063 sv)
    (ib : SymPtIn c 212066 sb) (la : sa.Lt P.n) (lv : sv.Lt P.n) (lb : sb.Lt P.n) :
    ∃ c' k, Exec P W testsS c c' k ∧ k ≤ 9 * 245 ∧ FrameB Bcor c c' ∧
      (∀ r, 212071 ≤ r → r ≤ 212079 → c'.nreg r ≤ 1) ∧
      (c'.nreg 212071 = 1 ↔ (sa.eval (Qof P)).2 < (sv.eval (Qof P)).2) ∧
      (c'.nreg 212072 = 1 ↔ (sv.eval (Qof P)).2 < (sa.eval (Qof P)).2) ∧
      (c'.nreg 212073 = 1 ↔ (sb.eval (Qof P)).2 < (sv.eval (Qof P)).2) ∧
      (c'.nreg 212074 = 1 ↔ (sv.eval (Qof P)).2 < (sb.eval (Qof P)).2) ∧
      (c'.nreg 212075 = 1 ↔ 0 < det (sa.eval (Qof P)) (sv.eval (Qof P)) (sb.eval (Qof P))) ∧
      (c'.nreg 212076 = 1 ↔ (sv.eval (Qof P)).1 < (sa.eval (Qof P)).1) ∧
      (c'.nreg 212077 = 1 ↔ (sa.eval (Qof P)).1 < (sv.eval (Qof P)).1) ∧
      (c'.nreg 212078 = 1 ↔ (sb.eval (Qof P)).1 < (sv.eval (Qof P)).1) ∧
      (c'.nreg 212079 = 1 ↔ (sv.eval (Qof P)).1 < (sb.eval (Qof P)).1) := by
  have oa : OutK 212060 := Or.inr (by norm_num)
  have ov : OutK 212063 := Or.inr (by norm_num)
  have ob : OutK 212066 := Or.inr (by norm_num)
  -- a test keeps the three triples and the earlier bits
  have keep : ∀ {d : ℕ} {c₁ c₂ : Config}, 212071 ≤ d → d ≤ 212079 → FrameB (Brute.Bt d) c₁ c₂ →
      ∀ r, (r < 10000 ∨ 10500 ≤ r) → r ≠ d → c₂.nreg r = c₁.nreg r := by
    intro d c₁ c₂ _ _ f r hr hrd
    refine f.1 r ?_
    core_grind
  have tr : ∀ {c₁ c₂ : Config} {x : ℕ} {s : SymPt}, SymPtIn c₁ x s → x = 212060 ∨ x = 212063 ∨
      x = 212066 → (∀ r, 212060 ≤ r → r < 212069 → c₂.nreg r = c₁.nreg r) → SymPtIn c₂ x s := by
    intro c₁ c₂ x s h hx hr
    exact symPtIn_of_eq h fun j h1 h2 => hr j (by omega) (by omega)
  obtain ⟨c₁, k₁, e₁, hk₁, f₁, b₁, t₁⟩ := tstR_exec (P := P) hG hW (op := 1) (by norm_num)
    (d := 212071) oa ov ov c hw ia iv iv la lv lv
  have g₁ := keep (by norm_num) (by norm_num) f₁
  have tr₁ : ∀ {x : ℕ} {s : SymPt}, SymPtIn c x s → x = 212060 ∨ x = 212063 ∨ x = 212066 →
      SymPtIn c₁ x s := fun h hx => tr h hx fun r h1 h2 => g₁ r (by omega) (by omega)
  obtain ⟨c₂, k₂, e₂, hk₂, f₂, b₂, t₂⟩ := tstR_exec (P := P) hG hW (op := 1) (by norm_num)
    (d := 212072) ov oa ov c₁ e₁.wb_right (tr₁ iv (by norm_num)) (tr₁ ia (by norm_num))
    (tr₁ iv (by norm_num)) lv la lv
  have g₂ := keep (by norm_num) (by norm_num) f₂
  have tr₂ : ∀ {x : ℕ} {s : SymPt}, SymPtIn c x s → x = 212060 ∨ x = 212063 ∨ x = 212066 →
      SymPtIn c₂ x s := fun h hx => tr (tr₁ h hx) hx fun r h1 h2 => g₂ r (by omega) (by omega)
  obtain ⟨c₃, k₃, e₃, hk₃, f₃, b₃, t₃⟩ := tstR_exec (P := P) hG hW (op := 1) (by norm_num)
    (d := 212073) ob ov ov c₂ e₂.wb_right (tr₂ ib (by norm_num)) (tr₂ iv (by norm_num))
    (tr₂ iv (by norm_num)) lb lv lv
  have g₃ := keep (by norm_num) (by norm_num) f₃
  have tr₃ : ∀ {x : ℕ} {s : SymPt}, SymPtIn c x s → x = 212060 ∨ x = 212063 ∨ x = 212066 →
      SymPtIn c₃ x s := fun h hx => tr (tr₂ h hx) hx fun r h1 h2 => g₃ r (by omega) (by omega)
  obtain ⟨c₄, k₄, e₄, hk₄, f₄, b₄, t₄⟩ := tstR_exec (P := P) hG hW (op := 1) (by norm_num)
    (d := 212074) ov ob ov c₃ e₃.wb_right (tr₃ iv (by norm_num)) (tr₃ ib (by norm_num))
    (tr₃ iv (by norm_num)) lv lb lv
  have g₄ := keep (by norm_num) (by norm_num) f₄
  have tr₄ : ∀ {x : ℕ} {s : SymPt}, SymPtIn c x s → x = 212060 ∨ x = 212063 ∨ x = 212066 →
      SymPtIn c₄ x s := fun h hx => tr (tr₃ h hx) hx fun r h1 h2 => g₄ r (by omega) (by omega)
  obtain ⟨c₅, k₅, e₅, hk₅, f₅, b₅, t₅⟩ := tstR_exec (P := P) hG hW (op := 2) (by norm_num)
    (d := 212075) oa ov ob c₄ e₄.wb_right (tr₄ ia (by norm_num)) (tr₄ iv (by norm_num))
    (tr₄ ib (by norm_num)) la lv lb
  have g₅ := keep (by norm_num) (by norm_num) f₅
  have tr₅ : ∀ {x : ℕ} {s : SymPt}, SymPtIn c x s → x = 212060 ∨ x = 212063 ∨ x = 212066 →
      SymPtIn c₅ x s := fun h hx => tr (tr₄ h hx) hx fun r h1 h2 => g₅ r (by omega) (by omega)
  obtain ⟨c₆, k₆, e₆, hk₆, f₆, b₆, t₆⟩ := tstR_exec (P := P) hG hW (op := 0) (by norm_num)
    (d := 212076) ov oa ov c₅ e₅.wb_right (tr₅ iv (by norm_num)) (tr₅ ia (by norm_num))
    (tr₅ iv (by norm_num)) lv la lv
  have g₆ := keep (by norm_num) (by norm_num) f₆
  have tr₆ : ∀ {x : ℕ} {s : SymPt}, SymPtIn c x s → x = 212060 ∨ x = 212063 ∨ x = 212066 →
      SymPtIn c₆ x s := fun h hx => tr (tr₅ h hx) hx fun r h1 h2 => g₆ r (by omega) (by omega)
  obtain ⟨c₇, k₇, e₇, hk₇, f₇, b₇, t₇⟩ := tstR_exec (P := P) hG hW (op := 0) (by norm_num)
    (d := 212077) oa ov ov c₆ e₆.wb_right (tr₆ ia (by norm_num)) (tr₆ iv (by norm_num))
    (tr₆ iv (by norm_num)) la lv lv
  have g₇ := keep (by norm_num) (by norm_num) f₇
  have tr₇ : ∀ {x : ℕ} {s : SymPt}, SymPtIn c x s → x = 212060 ∨ x = 212063 ∨ x = 212066 →
      SymPtIn c₇ x s := fun h hx => tr (tr₆ h hx) hx fun r h1 h2 => g₇ r (by omega) (by omega)
  obtain ⟨c₈, k₈, e₈, hk₈, f₈, b₈, t₈⟩ := tstR_exec (P := P) hG hW (op := 0) (by norm_num)
    (d := 212078) ob ov ov c₇ e₇.wb_right (tr₇ ib (by norm_num)) (tr₇ iv (by norm_num))
    (tr₇ iv (by norm_num)) lb lv lv
  have g₈ := keep (by norm_num) (by norm_num) f₈
  have tr₈ : ∀ {x : ℕ} {s : SymPt}, SymPtIn c x s → x = 212060 ∨ x = 212063 ∨ x = 212066 →
      SymPtIn c₈ x s := fun h hx => tr (tr₇ h hx) hx fun r h1 h2 => g₈ r (by omega) (by omega)
  obtain ⟨c₉, k₉, e₉, hk₉, f₉, b₉, t₉⟩ := tstR_exec (P := P) hG hW (op := 0) (by norm_num)
    (d := 212079) ov ob ov c₈ e₈.wb_right (tr₈ iv (by norm_num)) (tr₈ ib (by norm_num))
    (tr₈ iv (by norm_num)) lv lb lv
  have g₉ := keep (by norm_num) (by norm_num) f₉
  -- the bits survive the later tests
  have v1 : c₉.nreg 212071 = c₁.nreg 212071 := by
    rw [g₉ _ (by norm_num) (by norm_num), g₈ _ (by norm_num) (by norm_num),
      g₇ _ (by norm_num) (by norm_num), g₆ _ (by norm_num) (by norm_num),
      g₅ _ (by norm_num) (by norm_num), g₄ _ (by norm_num) (by norm_num),
      g₃ _ (by norm_num) (by norm_num), g₂ _ (by norm_num) (by norm_num)]
  have v2 : c₉.nreg 212072 = c₂.nreg 212072 := by
    rw [g₉ _ (by norm_num) (by norm_num), g₈ _ (by norm_num) (by norm_num),
      g₇ _ (by norm_num) (by norm_num), g₆ _ (by norm_num) (by norm_num),
      g₅ _ (by norm_num) (by norm_num), g₄ _ (by norm_num) (by norm_num),
      g₃ _ (by norm_num) (by norm_num)]
  have v3 : c₉.nreg 212073 = c₃.nreg 212073 := by
    rw [g₉ _ (by norm_num) (by norm_num), g₈ _ (by norm_num) (by norm_num),
      g₇ _ (by norm_num) (by norm_num), g₆ _ (by norm_num) (by norm_num),
      g₅ _ (by norm_num) (by norm_num), g₄ _ (by norm_num) (by norm_num)]
  have v4 : c₉.nreg 212074 = c₄.nreg 212074 := by
    rw [g₉ _ (by norm_num) (by norm_num), g₈ _ (by norm_num) (by norm_num),
      g₇ _ (by norm_num) (by norm_num), g₆ _ (by norm_num) (by norm_num),
      g₅ _ (by norm_num) (by norm_num)]
  have v5 : c₉.nreg 212075 = c₅.nreg 212075 := by
    rw [g₉ _ (by norm_num) (by norm_num), g₈ _ (by norm_num) (by norm_num),
      g₇ _ (by norm_num) (by norm_num), g₆ _ (by norm_num) (by norm_num)]
  have v6 : c₉.nreg 212076 = c₆.nreg 212076 := by
    rw [g₉ _ (by norm_num) (by norm_num), g₈ _ (by norm_num) (by norm_num),
      g₇ _ (by norm_num) (by norm_num)]
  have v7 : c₉.nreg 212077 = c₇.nreg 212077 := by
    rw [g₉ _ (by norm_num) (by norm_num), g₈ _ (by norm_num) (by norm_num)]
  have v8 : c₉.nreg 212078 = c₈.nreg 212078 := by
    grind
  have hf : FrameB Bcor c c₉ := by
    have hh : ∀ {d : ℕ} {c₁ c₂ : Config}, 212071 ≤ d ∧ d ≤ 212085 → FrameB (Brute.Bt d) c₁ c₂ →
        FrameB Bcor c₁ c₂ := fun hd f => fbMono f (bt_cor hd)
    exact fbTrans (fbTrans (fbTrans (fbTrans (fbTrans (fbTrans (fbTrans (fbTrans
      (hh (by norm_num) f₁) (hh (by norm_num) f₂)) (hh (by norm_num) f₃)) (hh (by norm_num) f₄))
      (hh (by norm_num) f₅)) (hh (by norm_num) f₆)) (hh (by norm_num) f₇)) (hh (by norm_num) f₈))
      (hh (by norm_num) f₉)
  refine ⟨c₉, k₁ + (k₂ + (k₃ + (k₄ + (k₅ + (k₆ + (k₇ + (k₈ + k₉))))))),
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ (.seq e₇ (.seq e₈ e₉))))))),
    by omega, hf, ?_, by rw [v1]; exact t₁, by rw [v2]; exact t₂, by rw [v3]; exact t₃,
    by rw [v4]; exact t₄, by rw [v5]; exact t₅, by rw [v6]; exact t₆, by rw [v7]; exact t₇,
    by rw [v8]; exact t₈, t₉⟩
  intro r h1 h2
  interval_cases r
  · omega
  · omega
  · omega
  · omega
  all_goals omega

section
variable (b : Bool)
include b
/-- The value of a bit. -/
def bv : ℕ := if b then 1 else 0

theorem bv_le : bv b ≤ 1 := by core_grind

theorem bv_eq_one : bv b = 1 ↔ b = true := by simp_all [bv] <;> omega_nf


end

/-- A test bit as a Boolean. -/
theorem bv_of_bit {n : ℕ} (h : n ≤ 1) : n = bv (decide (n = 1)) := by
  unfold bv; by_cases h1 : n = 1 <;> simp [h1]; omega

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
    · rw [h1, h2]; have := bv_le A1; have := bv_le A2; omega
    · config_simp; rw [h3, h4]; have := bv_le B1; have := bv_le B2; omega
    · cases A1 <;> cases A2 <;> cases B1 <;> cases B2 <;>
        simp only [bv, ite_true, ite_false, Bool.false_eq_true] at h1 h2 h3 h4 ⊢ <;>
        (repeat (first
          | refine spec_ifLtN_true (by config_simp; simp only [h1, h2, h3, h4, c1]; omega) ?_
          | refine spec_ifLtN_false (by config_simp; simp only [h1, h2, h3, h4, c1]; omega) ?_)) <;>
        (try unfold setE) <;> exec_block <;> (try omega) <;>
        refine ⟨by omega, ?_, ?_⟩ <;> config_simp <;>
        (try simp only [c0, h5, h6, h7, h8, h9]) <;>
        cases D <;> cases X1 <;> cases X2 <;> cases X3 <;> cases X4 <;> simp [emD, bv, h3]
  exact ⟨c', k, ex, hk, q1, q2, exec_frameB ex wr_decideS⟩

theorem bcor_dec (r : ℕ) (h : decide (212082 ≤ r ∧ r ≤ 212085) = true) : Bcor r = true := by
  simp_all [Bcor, Bool.or_eq_true, decide_eq_true_eq] <;> omega_nf

set_option maxHeartbeats 2000000 in
/-- **The corner test** (at most `2300` steps). -/
theorem cornerS_exec (hG : GoodEnv P) (hW : P.n + 3 ≤ W) (c : Config) (hw : WordsBounded W c)
    {sa sv sb : SymPt} (ia : SymPtIn c 212060 sa) (iv : SymPtIn c 212063 sv)
    (ib : SymPtIn c 212066 sb) (la : sa.Lt P.n) (lv : sv.Lt P.n) (lb : sb.Lt P.n)
    (c0 : c.nreg 212000 = 1) (c1 : c.nreg 212001 = 0) :
    ∃ c' k, Exec P W cornerS c c' k ∧ k ≤ 2300 ∧ FrameB Bcor c c' ∧
      c'.nreg 212084 ≤ 1 ∧ c'.nreg 212085 ≤ 1 ∧
      (c'.nreg 212084 = 1 ↔ emitG (sa.eval (Qof P)) (sv.eval (Qof P)) (sb.eval (Qof P)) 1) ∧
      (c'.nreg 212085 = 1 ↔ emitG (sa.eval (Qof P)) (sv.eval (Qof P)) (sb.eval (Qof P)) (-1)) := by
  obtain ⟨c₁, k₁, e₁, hk₁, f₁, hb, t1, t2, t3, t4, t5, t6, t7, t8, t9⟩ :=
    testsS_exec (P := P) hG hW c hw ia iv ib la lv lb
  have c0' : c₁.nreg 212000 = 1 := by rw [f₁.1 _ (by decide), c0]
  have c1' : c₁.nreg 212001 = 0 := by rw [f₁.1 _ (by decide), c1]
  obtain ⟨c₂, k₂, e₂, hk₂, q1, q2, f₂⟩ := decideS_exec (P := P) c₁ e₁.wb_right (by omega) c0' c1'
    (bv_of_bit (hb 212071 (by norm_num) (by norm_num)))
    (bv_of_bit (hb 212072 (by norm_num) (by norm_num)))
    (bv_of_bit (hb 212073 (by norm_num) (by norm_num)))
    (bv_of_bit (hb 212074 (by norm_num) (by norm_num)))
    (bv_of_bit (hb 212075 (by norm_num) (by norm_num)))
    (bv_of_bit (hb 212076 (by norm_num) (by norm_num)))
    (bv_of_bit (hb 212077 (by norm_num) (by norm_num)))
    (bv_of_bit (hb 212078 (by norm_num) (by norm_num)))
    (bv_of_bit (hb 212079 (by norm_num) (by norm_num)))
  obtain ⟨m1, m2⟩ := emD_iff (a := sa.eval (Qof P)) (v := sv.eval (Qof P)) (b := sb.eval (Qof P))
    (A1 := decide (c₁.nreg 212071 = 1)) (A2 := decide (c₁.nreg 212072 = 1))
    (B1 := decide (c₁.nreg 212073 = 1)) (B2 := decide (c₁.nreg 212074 = 1))
    (D := decide (c₁.nreg 212075 = 1)) (X1 := decide (c₁.nreg 212076 = 1))
    (X2 := decide (c₁.nreg 212077 = 1)) (X3 := decide (c₁.nreg 212078 = 1))
    (X4 := decide (c₁.nreg 212079 = 1))
    (by simp_all) (by simp_all)
    (by simp_all) (by simp_all)
    (by simp_all) (by simp_all)
    (by simp_all) (by simp_all)
    (by simp_all)
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by omega, fbTrans f₁ (fbMono f₂ bcor_dec),
    by rw [q1]; exact bv_le _, by rw [q2]; exact bv_le _, ?_, ?_⟩
  all_goals (grind [bv_eq_one])

end exec

end

end DrvB

end Chazelle.Core
