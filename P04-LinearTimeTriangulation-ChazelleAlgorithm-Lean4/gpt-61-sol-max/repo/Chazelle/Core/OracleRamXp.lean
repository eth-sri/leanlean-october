module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.OracleRamClus

/-!
# Lemma 3.6 (WP-H), RAM part 8: the abscissa of a chord endpoint

A chord endpoint is stored as a walk position `(w, h + 1)`.  Its abscissa is `-r` on the left
side of the box (`w = 1`, class `0`), `r` on the right side (`w = 3`, class `2`), and otherwise
(class `1`) the abscissa of a symbolic point of `Q`: the point of the chain edge of the tour edge
`w` at the height of `h`, or the top vertex (for the slit edges).

`xpS` computes the class (register `120122`) and the symbolic point (`120123 …`) from `w`
(`120120`) and `h` (`120121`).  Main result: `xpS_exec`.
-/

namespace Chazelle.Core

namespace OracleR

open Machine Machine.Stmt Programs SignK WalkKey
open OracleQ

@[expose] public section

/-- The class of the endpoint on walk edge `w`: `0` left box side, `2` right box side, `1`
otherwise. -/
def xpClass (w : ℕ) : ℕ := if w = 1 then 0 else if w = 3 then 2 else 1

open Classical in
/-- The symbolic point with the abscissa of the endpoint `(w, h + 1)` (class `1`). -/
noncomputable def xpSym (C : Chain) (V : QV) (n w h : ℕ) : SymPt :=
  if 6 ≤ w ∧ w < 2 * V.m + 6 then .onEdge (eIdx n V.s (tci C (w - 6))) h else .vtx V.tv

/-- The vertex part. -/
def xpVtx : Stmt := block [.constN 120123 0, .copyN 120124 120022]

/-- The edge part: the chain edge of the tour edge `w - 6`, its edge of `Q`, and the height. -/
def xpEdge : Stmt :=
  .seq (block [.subN 120127 120120 120028, .addN 120127 120127 120021])
    (.seq (modSub 120127 120019)
      (.seq (.ifLtN 120127 120016 (.instr (.copyN 120126 120127))
          (block [.subN 120126 120019 120011, .subN 120126 120126 120127]))
        (.seq (.instr (.addN 120126 120126 120015))
          (.seq (modSub 120126 120010)
            (block [.constN 120123 1, .copyN 120124 120126, .copyN 120125 120121])))))

/-- **The class and symbolic point of the endpoint** `(w, h + 1)`. -/
def xpS : Stmt :=
  ifEq 120120 120011 (.instr (.constN 120122 0))
    (.seq (.instr (.constN 120126 3))
      (ifEq 120120 120126 (.instr (.constN 120122 2))
        (.seq (.instr (.constN 120122 1))
          (.ifLtN 120120 120028 xpVtx (.ifLtN 120120 120029 xpEdge xpVtx)))))

/-- The registers written by `xpS`. -/
def BX (r : ℕ) : Bool := decide (120122 ≤ r ∧ r ≤ 120127)

theorem wr_xpS : wr BX xpS = true := by decide

theorem xpSym_lt {C : Chain} {V : QV} {n w h : ℕ} (hn : 0 < n) (htv : V.tv < n) (hh : h < n) :
    (xpSym C V n w h).Lt n := by
  unfold xpSym
  split_ifs
  · exact ⟨Nat.mod_lt _ hn, hh⟩
  · exact htv

section
variable {P : Polygon} {W : ℕ}
theorem xpVtx_exec (c : Config) (hw : WordsBounded W c) (hW : 1 ≤ W) :
    ∃ c' k, Exec P W xpVtx c c' k ∧ k = 2 ∧ c'.nreg 120123 = 0 ∧ c'.nreg 120124 = c.nreg 120022 ∧
      (∀ r, r ≠ 120123 → r ≠ 120124 → c'.nreg r = c.nreg r) := by
  unfold xpVtx
  exec_block
  all_goals simp_all

theorem xpEdge_exec (hW : 4 * P.n + 8 ≤ W) {C : Chain} {V : QV}
    (hv : QVOK P C V) (c : Config) (hw : WordsBounded W c) (hq : QConst P V c)
    (h6 : 6 ≤ c.nreg 120120) (hE : c.nreg 120120 < 2 * V.m + 6) :
    ∃ c' k, Exec P W xpEdge c c' k ∧ k ≤ 20 ∧ c'.nreg 120123 = 1 ∧
      c'.nreg 120124 = eIdx P.n V.s (tci C (c.nreg 120120 - 6)) ∧
      c'.nreg 120125 = c.nreg 120121 ∧
      (∀ r, r < 120123 ∨ 120127 < r → c'.nreg r = c.nreg r) := by
  have hmn : C.m < P.n := by
    have := C.m_lt; rw [hv.CQ, show (Qof P).n = P.n from shear_n _ _] at this; exact this
  
  have hsS : V.sS ≤ 2 * C.m := by rw [hv.sS]; exact C.sideS_lt C.sideBeta
  obtain ⟨w, hwdef⟩ : ∃ w, c.nreg 120120 = w := ⟨_, rfl⟩
  rw [hwdef] at h6 hE ⊢
  obtain ⟨c₁, k₁, e₁, hk₁, v₁, r₁⟩ : ∃ c₁ k₁, Exec P W
      (block [.subN 120127 120120 120028, .addN 120127 120127 120021]) c c₁ k₁ ∧ k₁ = 2 ∧
      c₁.nreg 120127 = w - 6 + V.sS ∧ (∀ r, r ≠ 120127 → c₁.nreg r = c.nreg r) := by
    exec_block
    · config_simp; ram_grind
    · refine ⟨rfl, ?_, fun r hr => ?_⟩
      · config_simp; ram_grind
      simp_all
  obtain ⟨c₂, k₂, e₂, hk₂, v₂, r₂, -⟩ := modSub_exec (P := P) (r := 120127) (nr := 120019)
    (by decide) c₁ e₁.wb_right (by ram_grind)
  rw [v₁, r₁ _ (by decide), hq.twoM, hv.m] at v₂
  have htj : c₂.nreg 120127 = tj C (w - 6) := by
    rw [v₂]; unfold tj; rw [← hv.sS, Nat.add_comm]
  have R₂ : ∀ r, r ≠ 120127 → c₂.nreg r = c.nreg r := fun r h => (r₂ r h).trans (r₁ r h)
  
  obtain ⟨c₃, k₃, e₃, hk₃, v₃, r₃⟩ : ∃ c₃ k₃, Exec P W
      (.ifLtN 120127 120016 (.instr (.copyN 120126 120127))
        (block [.subN 120126 120019 120011, .subN 120126 120126 120127])) c₂ c₃ k₃ ∧ k₃ ≤ 4 ∧
      c₃.nreg 120126 = tci C (w - 6) ∧ (∀ r, r ≠ 120126 → c₃.nreg r = c₂.nreg r) := by
    have hm2 : c₂.nreg 120016 = C.m := by rw [R₂ _ (by decide), hq.m, hv.m]
    by_cases hlt : tj C (w - 6) < C.m
    · refine ⟨_, _, .ifLtN_true (by omega) (Exec.copyN e₂.wb_right _ _),
        by omega, ?_, fun r hr => ?_⟩
      · config_simp; grind [tci]
      · config_simp; upd_solve
    · have w₂ := e₂.wb_right
      obtain ⟨c₃, k₃, e₃, hk₃, v₃, r₃⟩ : ∃ c₃ k₃, Exec P W
          (block [.subN 120126 120019 120011, .subN 120126 120126 120127]) c₂ c₃ k₃ ∧ k₃ = 2 ∧
          c₃.nreg 120126 = 2 * C.m - 1 - tj C (w - 6) ∧
          (∀ r, r ≠ 120126 → c₃.nreg r = c₂.nreg r) := by
        exec_block
        refine ⟨rfl, ?_, fun r hr => ?_⟩
        · config_simp
          rw [R₂ _ (by decide), R₂ _ (by decide), hq.twoM, hq.one, htj, hv.m]
        · config_simp; upd_solve
      refine ⟨c₃, _, .ifLtN_false (by omega) e₃, by omega, ?_, r₃⟩
      grind [tci]
  have hci := tci_lt C (w - 6)
  obtain ⟨c₄, e₄, v₄, r₄, -⟩ := add_exec (P := P) e₃.wb_right 120126 120126 120015 (by
    rw [v₃, r₃ _ (by decide), R₂ _ (by decide), hq.s]; have := hv.s_lt; omega)
  rw [v₃, r₃ _ (by decide), R₂ _ (by decide), hq.s] at v₄
  obtain ⟨c₅, k₅, e₅, hk₅, v₅, r₅, -⟩ := modSub_exec (P := P) (r := 120126) (nr := 120010)
    (by decide) c₄ e₄.wb_right (by
      rw [v₄, r₄ _ (by decide), r₃ _ (by decide), R₂ _ (by decide), hq.n]
      have := hv.s_lt; omega)
  rw [v₄, r₄ _ (by decide), r₃ _ (by decide), R₂ _ (by decide), hq.n] at v₅
  obtain ⟨c₆, k₆, e₆, hk₆, v₆⟩ : ∃ c₆ k₆, Exec P W
      (block [.constN 120123 1, .copyN 120124 120126, .copyN 120125 120121]) c₅ c₆ k₆ ∧ k₆ = 3 ∧
      (c₆.nreg 120123 = 1 ∧ c₆.nreg 120124 = c₅.nreg 120126 ∧ c₆.nreg 120125 = c₅.nreg 120121 ∧
        ∀ r, r ≠ 120123 → r ≠ 120124 → r ≠ 120125 → c₆.nreg r = c₅.nreg r) := by
    have w₅ := e₅.wb_right
    exec_block
    · omega
    · exact ⟨rfl, by config_simp, by config_simp, by config_simp,
        fun r h1 h2 h3 => by config_simp; upd_solve⟩
  obtain ⟨x123, x124, x125, r₆⟩ := v₆
  have R : ∀ r, (r < 120123 ∨ 120127 < r) → c₆.nreg r = c.nreg r := fun r hr => by
    rw [r₆ r (by omega) (by omega) (by omega), r₅ r (by omega), r₄ r (by omega), r₃ r (by omega),
      R₂ r (by omega)]
  refine ⟨c₆, _, .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ e₆)))), by omega, x123, ?_, ?_, R⟩
  · rw [x124, v₅]; unfold eIdx; grind
  · rw [x125, r₅ _ (by decide), r₄ _ (by decide), r₃ _ (by decide), R₂ _ (by decide)]


end

open Classical in
/-- **The class and symbolic point of the endpoint** `(w, h + 1)` (`w` in `120120`, `h` in
`120121`). -/
theorem xpS_exec {P : Polygon} {W : ℕ} (hW : 4 * P.n + 8 ≤ W) {C : Chain} {V : QV}
    (hv : QVOK P C V) (c : Config) (hw : WordsBounded W c) (hq : QConst P V c) :
    ∃ c' k, Exec P W xpS c c' k ∧ k ≤ 40 ∧ FrameB BX c c' ∧
      c'.nreg 120122 = xpClass (c.nreg 120120) ∧
      (xpClass (c.nreg 120120) = 1 →
        SymPtIn c' 120123 (xpSym C V P.n (c.nreg 120120) (c.nreg 120121))) := by
  suffices H : ∃ c' k, Exec P W xpS c c' k ∧ k ≤ 40 ∧
      c'.nreg 120122 = xpClass (c.nreg 120120) ∧
      (xpClass (c.nreg 120120) = 1 →
        SymPtIn c' 120123 (xpSym C V P.n (c.nreg 120120) (c.nreg 120121))) by
    obtain ⟨c', k, ex, hk, h1, h2⟩ := H
    exact ⟨c', k, ex, hk, exec_frameB ex wr_xpS, h1, h2⟩
  obtain ⟨w, hwdef⟩ : ∃ w, c.nreg 120120 = w := ⟨_, rfl⟩
  rw [hwdef]
  by_cases h1 : w = 1
  · obtain ⟨c₁, e₁, v₁, -⟩ := const_exec (P := P) hw 120122 0 (by omega)
    refine ⟨c₁, _, ifEq_eq_exec (by ram_grind) e₁, by omega, ?_, ?_⟩
    all_goals (simp_all [xpClass])
  obtain ⟨c₁, e₁, v₁, r₁⟩ := const_exec (P := P) hw 120126 3 (by omega)
  by_cases h3 : w = 3
  · obtain ⟨c₂, e₂, v₂, -⟩ := const_exec (P := P) e₁.wb_right 120122 2 (by omega)
    obtain ⟨k', ex', hk'⟩ := ifEq_ne_exec (a := 120120) (b := 120011)
      (S := .instr (.constN 120122 0))
      (by ram_grind)
      (.seq e₁ (ifEq_eq_exec (a := 120120) (b := 120126)
        (T := .seq (.instr (.constN 120122 1)) _)
        (by simp_all) e₂))
    refine ⟨c₂, k', ex', by omega, ?_, ?_⟩
    all_goals (simp_all [xpClass])
  have hcl : xpClass w = 1 := by simp_all [xpClass]
  rw [hcl]
  obtain ⟨c₂, e₂, v₂, r₂⟩ := const_exec (P := P) e₁.wb_right 120122 1 (by omega)
  have hq₂ : QConst P V c₂ := hq.congr fun r h1' h2' => by
    grind
  have x120 : c₂.nreg 120120 = w := by simp_all
  have x121 : c₂.nreg 120121 = c.nreg 120121 := by simp_all
  -- the class-1 part
  obtain ⟨c₃, k₃, e₃, hk₃, v₃, s₃⟩ : ∃ c₃ k₃, Exec P W
      (.ifLtN 120120 120028 xpVtx (.ifLtN 120120 120029 xpEdge xpVtx)) c₂ c₃ k₃ ∧ k₃ ≤ 23 ∧
      c₃.nreg 120122 = 1 ∧ SymPtIn c₃ 120123 (xpSym C V P.n w (c.nreg 120121)) := by
    have vtxcase : ¬ (6 ≤ w ∧ w < 2 * V.m + 6) → ∀ (d : Config), WordsBounded W d →
        d.nreg 120122 = 1 → d.nreg 120022 = V.tv → ∃ d' k, Exec P W xpVtx d d' k ∧ k = 2 ∧
          d'.nreg 120122 = 1 ∧ SymPtIn d' 120123 (xpSym C V P.n w (c.nreg 120121)) := by
      intro hn d hd h22 htv
      obtain ⟨d', k, ex, hk, a1, a2, a3⟩ := xpVtx_exec (P := P) d hd (by omega)
      refine ⟨d', k, ex, hk, by simp_all, ?_⟩
      grind [Chazelle.Core.SymPtIn, xpSym]
    by_cases h6 : w < 6
    · obtain ⟨d', k, ex, hk, a, b⟩ := vtxcase (by omega) c₂ e₂.wb_right v₂ hq₂.tv
      exact ⟨d', _, .ifLtN_true (by rw [x120, hq₂.six]; exact h6) ex, by omega, a, b⟩
    by_cases hE : w < 2 * V.m + 6
    · obtain ⟨d', k, ex, hk, a1, a2, a3, a4⟩ := xpEdge_exec (P := P) hW hv c₂ e₂.wb_right hq₂
        (by omega) (by omega)
      refine ⟨d', _, .ifLtN_false (by rw [x120, hq₂.six]; exact h6)
        (.ifLtN_true (by rw [x120, hq₂.tEnd]; exact hE) ex), by omega,
        by grind, ?_⟩
      grind [Chazelle.Core.SymPtIn, xpSym]
    · obtain ⟨d', k, ex, hk, a, b⟩ := vtxcase (by omega) c₂ e₂.wb_right v₂ hq₂.tv
      exact ⟨d', _, .ifLtN_false (by rw [x120, hq₂.six]; exact h6)
        (.ifLtN_false (by rw [x120, hq₂.tEnd]; exact hE) ex), by omega, a, b⟩
  obtain ⟨k₄, ex₄, hk₄⟩ := ifEq_ne_exec (a := 120120) (b := 120126)
    (S := .instr (.constN 120122 2))
    (show c₁.nreg 120120 ≠ c₁.nreg 120126 by simp_all)
    (.seq e₂ e₃)
  obtain ⟨k', ex', hk'⟩ := ifEq_ne_exec (a := 120120) (b := 120011)
    (S := .instr (.constN 120122 0)) (by rw [hwdef, hq.one]; exact h1) (.seq e₁ ex₄)
  exact ⟨c₃, k', ex', by omega, v₃, fun _ => s₃⟩

/-! ## Comparisons of an endpoint -/

/-- Decide by the class: `v0` for class `0`, `S1` for class `1`, `v2` for class `2` (bit in
`120128`). -/
def clsDec (v0 v2 : ℕ) (S1 : Stmt) : Stmt :=
  .ifLtN 120122 120011 (.instr (.constN 120128 v0))
    (.ifLtN 120122 120048 S1 (.instr (.constN 120128 v2)))

/-- The endpoint is ahead of the origin (rightwards): `z.1 < x`. -/
def gtZ1 : Stmt :=
  .ifLtN 120025 120048
    (.seq (sgnS 0 (.regs 120025) (.regs 120123) (.vtx 120022)) (.instr (.copyN 120128 10010)))
    (.instr (.copyN 120128 120024))

/-- The endpoint is ahead of the origin (leftwards): `x < z.1`. -/
def ltZ1 : Stmt :=
  .ifLtN 120025 120048
    (.seq (sgnS 0 (.regs 120123) (.regs 120025) (.vtx 120022)) (.instr (.copyN 120128 10010)))
    (.instr (.subN 120128 120011 120024))

/-- The endpoint comes before the hit `120051` (rightwards): `x < x_D`. -/
def ltD1 : Stmt :=
  .seq (sgnS 0 (.regs 120123) (.edge 120051 120023) (.vtx 120022)) (.instr (.copyN 120128 10010))

/-- The endpoint comes before the hit `120051` (leftwards): `x_D < x`. -/
def gtD1 : Stmt :=
  .seq (sgnS 0 (.edge 120051 120023) (.regs 120123) (.vtx 120022)) (.instr (.copyN 120128 10010))

/-- **`z.1 < x`** for the endpoint `(w, h + 1)`. -/
def gtZS : Stmt := .seq xpS (clsDec 0 1 gtZ1)
/-- **`x < z.1`** for the endpoint `(w, h + 1)`. -/
def ltZS : Stmt := .seq xpS (clsDec 1 0 ltZ1)
/-- **`x < x_D`** for the endpoint `(w, h + 1)`. -/
def ltDS : Stmt := .seq xpS (clsDec 1 0 ltD1)
/-- **`x_D < x`** for the endpoint `(w, h + 1)`. -/
def gtDS : Stmt := .seq xpS (clsDec 0 1 gtD1)

/-- The registers written by the comparisons. -/
def BX2 (r : ℕ) : Bool := Bk r || decide (120122 ≤ r ∧ r ≤ 120128)

theorem wr_gtZS : wr BX2 gtZS = true := by decide
theorem wr_ltZS : wr BX2 ltZS = true := by decide
theorem wr_ltDS : wr BX2 ltDS = true := by decide
theorem wr_gtDS : wr BX2 gtDS = true := by decide

section Sem
variable (P : Polygon) (C : Chain) (V : QV)

section
variable (w h : ℕ)
include w h
/-- The abscissa of the class-`1` endpoint `(w, h + 1)`. -/
noncomputable def xpX : ℝ := ((xpSym C V P.n w h).eval (Qof P)).1

/-- **`z.1 < x`** in the sense of the program (the box sides are `∓∞`; a box origin is on the
side the ray comes from). -/
def EndGtZ : Prop :=
  xpClass w = 2 ∨ (xpClass w = 1 ∧
    match V.zo with
    | none => V.σb = 1
    | some z => z.1 < xpX P C V w h)

/-- **`x < z.1`** in the sense of the program. -/
def EndLtZ : Prop :=
  xpClass w = 0 ∨ (xpClass w = 1 ∧
    match V.zo with
    | none => V.σb ≠ 1
    | some z => xpX P C V w h < z.1)


end

/-- **`x < x_D`** in the sense of the program (`x_D` the point of edge `eD`). -/
def EndLtD (eD w h : ℕ) : Prop :=
  xpClass w = 0 ∨ (xpClass w = 1 ∧ xpX P C V w h < xe (Qof P) eD V.hz)

/-- **`x_D < x`** in the sense of the program. -/
def EndGtD (eD w h : ℕ) : Prop :=
  xpClass w = 2 ∨ (xpClass w = 1 ∧ xe (Qof P) eD V.hz < xpX P C V w h)

end Sem

/-! ### Execution of the comparisons -/

theorem xpClass_le (w : ℕ) : xpClass w ≤ 2 := by core_grind

section
variable {P : Polygon} {W : ℕ}
/-- **Deciding by the class.** -/
theorem clsDec_exec (hW : 3 ≤ W) {v0 v2 : ℕ} (hv0 : v0 ≤ 1) (hv2 : v2 ≤ 1)
    {S1 : Stmt} {K1 : ℕ} {R1 : Prop} (c : Config) (hw : WordsBounded W c) (hone : c.nreg 120011 = 1)
    (htwo : c.nreg 120048 = 2) (hcl : c.nreg 120122 ≤ 2)
    (hS1 : c.nreg 120122 = 1 → ∃ c' k, Exec P W S1 c c' k ∧ k ≤ K1 ∧ c'.nreg 120128 ≤ 1 ∧
      (c'.nreg 120128 = 1 ↔ R1)) :
    ∃ c' k, Exec P W (clsDec v0 v2 S1) c c' k ∧ k ≤ K1 + 5 ∧ c'.nreg 120128 ≤ 1 ∧
      (c'.nreg 120128 = 1 ↔ (c.nreg 120122 = 0 ∧ v0 = 1) ∨ (c.nreg 120122 = 1 ∧ R1) ∨
        (c.nreg 120122 = 2 ∧ v2 = 1)) := by
  unfold clsDec
  by_cases h0 : c.nreg 120122 < 1
  · obtain ⟨c₁, e₁, v₁, -⟩ := const_exec (P := P) hw 120128 v0 (by omega)
    refine ⟨c₁, _, .ifLtN_true (by omega) e₁, by omega, by omega, ?_⟩
    omega
  by_cases h1 : c.nreg 120122 < 2
  · obtain ⟨c₁, k₁, e₁, hk₁, b₁, v₁⟩ := hS1 (by omega)
    refine ⟨c₁, _, .ifLtN_false (by omega) (.ifLtN_true (by omega) e₁),
      by omega, b₁, ?_⟩
    grind
  · obtain ⟨c₁, e₁, v₁, -⟩ := const_exec (P := P) hw 120128 v2 (by omega)
    refine ⟨c₁, _, .ifLtN_false (by omega) (.ifLtN_false (by omega) e₁),
      by omega, by omega, ?_⟩
    omega

/-- The class-`1` point and the constants after `xpS`. -/
theorem after_xp (hW : 4 * P.n + 8 ≤ W) {C : Chain} {V : QV}
    (hv : QVOK P C V) (c : Config) (hw : WordsBounded W c) (hq : QConst P V c) :
    ∃ c₁ k₁, Exec P W xpS c c₁ k₁ ∧ k₁ ≤ 40 ∧ FrameB BX c c₁ ∧ QConst P V c₁ ∧
      c₁.nreg 120122 = xpClass (c.nreg 120120) ∧
      (xpClass (c.nreg 120120) = 1 →
        SymPtIn c₁ 120123 (xpSym C V P.n (c.nreg 120120) (c.nreg 120121))) := by
  obtain ⟨c₁, k₁, e₁, hk₁, f₁, v₁, s₁⟩ := xpS_exec (P := P) hW hv c hw hq
  exact ⟨c₁, k₁, e₁, hk₁, f₁, hq.frame f₁ fun r h1 h2 => by
    simp only [BX, decide_eq_false_iff_not, not_and, not_le]; omega, v₁, s₁⟩


end

section
variable {P : Polygon} {W : ℕ} (hG : GoodEnv P) (hW : 4 * P.n + 8 ≤ W) {C : Chain} {V : QV} (hv : QVOK P C V) (htv : V.tv < P.n) (c : Config) (hw : WordsBounded W c) (hq : QConst P V c) (hh : c.nreg 120121 < P.n)
include hG hW hv htv hw hq hh
/-- **`z.1 < x`.** -/
theorem gtZS_exec :
    ∃ c' k, Exec P W gtZS c c' k ∧ k ≤ 300 ∧ FrameB BX2 c c' ∧ c'.nreg 120128 ≤ 1 ∧
      (c'.nreg 120128 = 1 ↔ EndGtZ P C V (c.nreg 120120) (c.nreg 120121)) := by
  obtain ⟨c₁, k₁, e₁, hk₁, f₁, hq₁, v₁, s₁⟩ := after_xp (P := P) hW hv c hw hq
  have hn : 0 < P.n := by omega
  obtain ⟨c₂, k₂, e₂, hk₂, b₂, v₂⟩ := clsDec_exec (P := P) (v0 := 0) (v2 := 1) (S1 := gtZ1)
    (K1 := 250) (R1 := match V.zo with
      | none => V.σb = 1
      | some z => z.1 < xpX P C V (c.nreg 120120) (c.nreg 120121)) (by omega) (by norm_num)
    (by norm_num) c₁ e₁.wb_right hq₁.one hq₁.two (by rw [v₁]; exact xpClass_le _) (by
      intro hc1
      rw [v₁] at hc1
      have hpt := s₁ hc1
      have hl := xpSym_lt (C := C) (V := V) (w := c.nreg 120120) hn htv hh
      rcases hq₁.org with ⟨hk2, hzo⟩ | ⟨hk2, p, hp, hpin, hzo⟩
      · obtain ⟨c₂, e₂, v₂, -⟩ := copy_exec (P := P) e₁.wb_right 120128 120024
        refine ⟨c₂, _, .ifLtN_false (by rw [hk2, hq₁.two]; omega) e₂, by omega, ?_, ?_⟩
        · rw [v₂, hq₁.σb]; exact hv.σb_le
        · rw [v₂, hq₁.σb, hzo]
      · obtain ⟨c₂, k₂, e₂, hk₂, -, b₂, g₂⟩ := sgnS_exec (P := P) hG (by omega) 0 (by norm_num)
          (.regs 120025) (.regs 120123) (.vtx 120022) c₁ e₁.wb_right (by decide) (by decide)
          (by decide) hpin hpt rfl hp hl (by rw [hq₁.tv]; exact htv)
        obtain ⟨c₃, e₃, v₃, -⟩ := copy_exec (P := P) e₂.wb_right 120128 10010
        refine ⟨c₃, _, .ifLtN_true (by rw [hq₁.two]; exact hk2) (.seq e₂ e₃), by omega,
          by omega, ?_⟩
        rw [v₃, g₂, hzo]
        simp only [SignTest]
        rfl)
  refine ⟨c₂, _, .seq e₁ e₂, by omega, exec_frameB (.seq e₁ e₂) wr_gtZS, b₂, ?_⟩
  grind [EndGtZ]

/-- **`x < z.1`.** -/
theorem ltZS_exec :
    ∃ c' k, Exec P W ltZS c c' k ∧ k ≤ 300 ∧ FrameB BX2 c c' ∧ c'.nreg 120128 ≤ 1 ∧
      (c'.nreg 120128 = 1 ↔ EndLtZ P C V (c.nreg 120120) (c.nreg 120121)) := by
  obtain ⟨c₁, k₁, e₁, hk₁, f₁, hq₁, v₁, s₁⟩ := after_xp (P := P) hW hv c hw hq
  have hn : 0 < P.n := by omega
  obtain ⟨c₂, k₂, e₂, hk₂, b₂, v₂⟩ := clsDec_exec (P := P) (v0 := 1) (v2 := 0) (S1 := ltZ1)
    (K1 := 250) (R1 := match V.zo with
      | none => V.σb ≠ 1
      | some z => xpX P C V (c.nreg 120120) (c.nreg 120121) < z.1) (by omega) (by norm_num)
    (by norm_num) c₁ e₁.wb_right hq₁.one hq₁.two (by rw [v₁]; exact xpClass_le _) (by
      intro hc1
      rw [v₁] at hc1
      have hpt := s₁ hc1
      have hl := xpSym_lt (C := C) (V := V) (w := c.nreg 120120) hn htv hh
      rcases hq₁.org with ⟨hk2, hzo⟩ | ⟨hk2, p, hp, hpin, hzo⟩
      · have w₁ := e₁.wb_right
        obtain ⟨c₂, e₂, v₂, -⟩ : ∃ c₂, Exec P W (.instr (.subN 120128 120011 120024)) c₁ c₂ 1 ∧
            c₂.nreg 120128 = c₁.nreg 120011 - c₁.nreg 120024 ∧ True :=
          ⟨_, Exec.subN w₁ _ _ _, by config_simp, trivial⟩
        have hσ := hv.σb_le
        refine ⟨c₂, _, .ifLtN_false (by rw [hk2, hq₁.two]; omega) e₂, by omega, ?_, ?_⟩
        · rw [v₂, hq₁.one]; omega
        · rw [v₂, hq₁.one, hq₁.σb, hzo]; omega
      · obtain ⟨c₂, k₂, e₂, hk₂, -, b₂, g₂⟩ := sgnS_exec (P := P) hG (by omega) 0 (by norm_num)
          (.regs 120123) (.regs 120025) (.vtx 120022) c₁ e₁.wb_right (by decide) (by decide)
          (by decide) hpt hpin rfl hl hp (by rw [hq₁.tv]; exact htv)
        obtain ⟨c₃, e₃, v₃, -⟩ := copy_exec (P := P) e₂.wb_right 120128 10010
        refine ⟨c₃, _, .ifLtN_true (by rw [hq₁.two]; exact hk2) (.seq e₂ e₃), by omega,
          by omega, ?_⟩
        rw [v₃, g₂, hzo]
        simp only [SignTest]
        rfl)
  refine ⟨c₂, _, .seq e₁ e₂, by omega, exec_frameB (.seq e₁ e₂) wr_ltZS, b₂, ?_⟩
  ram_grind

section
variable (heD : c.nreg 120051 < P.n)
include heD
/-- **`x < x_D`.** -/
theorem ltDS_exec :
    ∃ c' k, Exec P W ltDS c c' k ∧ k ≤ 300 ∧ FrameB BX2 c c' ∧ c'.nreg 120128 ≤ 1 ∧
      (c'.nreg 120128 = 1 ↔ EndLtD P C V (c.nreg 120051) (c.nreg 120120) (c.nreg 120121)) := by
  obtain ⟨c₁, k₁, e₁, hk₁, f₁, hq₁, v₁, s₁⟩ := after_xp (P := P) hW hv c hw hq
  have hn : 0 < P.n := by omega
  have x51 : c₁.nreg 120051 = c.nreg 120051 := f₁.1 _ (by decide)
  obtain ⟨c₂, k₂, e₂, hk₂, b₂, v₂⟩ := clsDec_exec (P := P) (v0 := 1) (v2 := 0) (S1 := ltD1)
    (K1 := 250) (R1 := xpX P C V (c.nreg 120120) (c.nreg 120121) <
      xe (Qof P) (c.nreg 120051) V.hz) (by omega) (by norm_num)
    (by norm_num) c₁ e₁.wb_right hq₁.one hq₁.two (by rw [v₁]; exact xpClass_le _) (by
      intro hc1
      rw [v₁] at hc1
      have hpt := s₁ hc1
      have hl := xpSym_lt (C := C) (V := V) (w := c.nreg 120120) hn htv hh
      obtain ⟨c₂, k₂, e₂, hk₂, -, b₂, g₂⟩ := sgnS_exec (P := P) hG (by omega) 0 (by norm_num)
        (.regs 120123) (.edge 120051 120023) (.vtx 120022) c₁ e₁.wb_right (by decide) (by decide)
        (by decide) hpt rfl rfl hl (show (SymPt.onEdge _ _).Lt P.n from
          ⟨by omega, by rw [hq₁.hz]; exact hv.hz_lt⟩) (by rw [hq₁.tv]; exact htv)
      obtain ⟨c₃, e₃, v₃, -⟩ := copy_exec (P := P) e₂.wb_right 120128 10010
      refine ⟨c₃, _, .seq e₂ e₃, by omega, by omega, ?_⟩
      rw [v₃, g₂]
      simp only [SignTest, SymPt.eval, xpX, xe, x51, hq₁.hz])
  refine ⟨c₂, _, .seq e₁ e₂, by omega, exec_frameB (.seq e₁ e₂) wr_ltDS, b₂, ?_⟩
  ram_grind

/-- **`x_D < x`.** -/
theorem gtDS_exec :
    ∃ c' k, Exec P W gtDS c c' k ∧ k ≤ 300 ∧ FrameB BX2 c c' ∧ c'.nreg 120128 ≤ 1 ∧
      (c'.nreg 120128 = 1 ↔ EndGtD P C V (c.nreg 120051) (c.nreg 120120) (c.nreg 120121)) := by
  obtain ⟨c₁, k₁, e₁, hk₁, f₁, hq₁, v₁, s₁⟩ := after_xp (P := P) hW hv c hw hq
  have hn : 0 < P.n := by omega
  have x51 : c₁.nreg 120051 = c.nreg 120051 := f₁.1 _ (by decide)
  obtain ⟨c₂, k₂, e₂, hk₂, b₂, v₂⟩ := clsDec_exec (P := P) (v0 := 0) (v2 := 1) (S1 := gtD1)
    (K1 := 250) (R1 := xe (Qof P) (c.nreg 120051) V.hz <
      xpX P C V (c.nreg 120120) (c.nreg 120121)) (by omega) (by norm_num)
    (by norm_num) c₁ e₁.wb_right hq₁.one hq₁.two (by rw [v₁]; exact xpClass_le _) (by
      intro hc1
      rw [v₁] at hc1
      have hpt := s₁ hc1
      have hl := xpSym_lt (C := C) (V := V) (w := c.nreg 120120) hn htv hh
      obtain ⟨c₂, k₂, e₂, hk₂, -, b₂, g₂⟩ := sgnS_exec (P := P) hG (by omega) 0 (by norm_num)
        (.edge 120051 120023) (.regs 120123) (.vtx 120022) c₁ e₁.wb_right (by decide) (by decide)
        (by decide) rfl hpt rfl (show (SymPt.onEdge _ _).Lt P.n from
          ⟨by omega, by rw [hq₁.hz]; exact hv.hz_lt⟩) hl (by rw [hq₁.tv]; exact htv)
      obtain ⟨c₃, e₃, v₃, -⟩ := copy_exec (P := P) e₂.wb_right 120128 10010
      refine ⟨c₃, _, .seq e₂ e₃, by omega, by omega, ?_⟩
      rw [v₃, g₂]
      simp only [SignTest, SymPt.eval, xpX, xe, x51, hq₁.hz])
  refine ⟨c₂, _, .seq e₁ e₂, by omega, exec_frameB (.seq e₁ e₂) wr_gtDS, b₂, ?_⟩
  grind [EndGtD]



end

end

end

end OracleR

end Chazelle.Core
