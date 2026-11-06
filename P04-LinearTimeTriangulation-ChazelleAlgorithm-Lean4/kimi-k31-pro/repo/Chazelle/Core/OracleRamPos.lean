module

public import Chazelle.Core.OracleRamLoc
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics
public import Chazelle.SimpTactics
public import Chazelle.ConfigTactics

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

/-! ## The chain edge of a tour edge -/

/-- `120181 := tci (120180 - 6)` (scratch `120182`). -/
def tciS : Stmt :=
  .seq (block [.subN 120182 120180 120028, .addN 120182 120182 120021])
    (.seq (modSub 120182 120019)
      (.ifLtN 120182 120016 (.instr (.copyN 120181 120182))
        (block [.subN 120181 120019 120011, .subN 120181 120181 120182])))

theorem tciS_exec {P : Polygon} {W : ℕ} (hW : 4 * P.n + 8 ≤ W) {C : Chain} {V : QV}
    (hv : QVOK P C V) (c : Config) (hw : WordsBounded W c) (hq : QConst P V c)
    (h6 : 6 ≤ c.nreg 120180) (hE : c.nreg 120180 < 2 * V.m + 6) :
    ∃ c' k, Exec P W tciS c c' k ∧ k ≤ 9 ∧ c'.nreg 120181 = tci C (c.nreg 120180 - 6) ∧
      (∀ r, r ≠ 120181 → r ≠ 120182 → c'.nreg r = c.nreg r) := by
  have hmn : C.m < P.n := by
    have := C.m_lt; rw [hv.CQ, show (Qof P).n = P.n from shear_n _ _] at this; exact this
  have hm1 := C.one_le
  have hsS : V.sS ≤ 2 * C.m := by rw [hv.sS]; exact C.sideS_lt C.sideBeta
  obtain ⟨w, hwdef⟩ : ∃ w, c.nreg 120180 = w := ⟨_, rfl⟩
  rw [hwdef] at h6 hE ⊢
  obtain ⟨c₁, k₁, e₁, hk₁, v₁, r₁⟩ : ∃ c₁ k₁, Exec P W
      (block [.subN 120182 120180 120028, .addN 120182 120182 120021]) c c₁ k₁ ∧ k₁ = 2 ∧
      c₁.nreg 120182 = w - 6 + V.sS ∧ (∀ r, r ≠ 120182 → c₁.nreg r = c.nreg r) := by
    exec_block
    · config_simp; rw [hq.six, hq.sS, hwdef]; rwo [hv.m] at hE
    · refine ⟨rfl, ?_, fun r hr => ?_⟩
      · config_simp; rw [hq.six, hq.sS, hwdef]
      · config_simp; upd_solve
  obtain ⟨c₂, k₂, e₂, hk₂, v₂, r₂, -⟩ := modSub_exec (P := P) (r := 120182) (nr := 120019)
    (by decide) c₁ e₁.wb_right (by rw [v₁, r₁ _ (by decide), hq.twoM, hv.m]; rwo [hv.m] at hE)
  rw [v₁, r₁ _ (by decide), hq.twoM, hv.m] at v₂
  have htj : c₂.nreg 120182 = tj C (w - 6) := by
    rw [v₂]; unfold tj; rw [← hv.sS, Nat.add_comm]
  have R₂ : ∀ r, r ≠ 120182 → c₂.nreg r = c.nreg r := fun r h => (r₂ r h).trans (r₁ r h)
  have hu := tj_lt C (w - 6)
  have hm2 : c₂.nreg 120016 = C.m := by rw [R₂ _ (by decide), hq.m, hv.m]
  by_cases hlt : tj C (w - 6) < C.m
  · refine ⟨_, _, .seq e₁ (.seq e₂ (.ifLtN_true (by rwx [htj, hm2])
      (Exec.copyN e₂.wb_right _ _))), by omega, ?_, fun r h1 h2 => ?_⟩
    · config_simp; rw [htj]; unfold tci; rw [ite_eq_left hlt]
    · config_simp; rw [Machine.upd_other _ _ _ h1]; exact R₂ r h2
  · have w₂ := e₂.wb_right
    obtain ⟨c₃, k₃, e₃, hk₃, v₃, r₃⟩ : ∃ c₃ k₃, Exec P W
        (block [.subN 120181 120019 120011, .subN 120181 120181 120182]) c₂ c₃ k₃ ∧ k₃ = 2 ∧
        c₃.nreg 120181 = 2 * C.m - 1 - tj C (w - 6) ∧
        (∀ r, r ≠ 120181 → c₃.nreg r = c₂.nreg r) := by
      exec_block
      refine ⟨rfl, ?_, fun r hr => ?_⟩
      · config_simp
        rw [R₂ _ (by decide), R₂ _ (by decide), hq.twoM, hq.one, htj, hv.m]
      · config_simp; upd_solve
    refine ⟨c₃, _, .seq e₁ (.seq e₂ (.ifLtN_false (by rwx [htj, hm2]) e₃)), by omega,
      ?_, fun r h1 h2 => by rw [r₃ r h1]; exact R₂ r h2⟩
    rw [v₃]; unfold tci; rw [ite_eq_right hlt]

/-! ## The choice of the stopping point -/

/-- Use the hit on `D*`. -/
def useD : Stmt := block [.constN 120150 0, .copyN 120151 120052]

/-- Use the near end of the chord. -/
def useCh : Stmt :=
  .ifLtN 120141 120028 (.instr (.copyN 120152 120141))
    (.ifLtN 120141 120029
      (.seq (.instr (.copyN 120180 120141)) (.seq tciS (block [.constN 120150 0, .copyN 120151 120181])))
      (ifEq 120141 120029
        (.seq (.instr (.subN 120180 120029 120011)) (.seq tciS (block [.constN 120150 0,
          .copyN 120151 120181])))
        (.instr (.copyN 120152 120141))))

/-- **The choice of the stopping point.** -/
def tchS : Stmt :=
  .seq (.instr (.constN 120150 1))
    (.seq (.ifLtN 120024 120011 (.instr (.constN 120152 1)) (.instr (.constN 120152 3)))
      (.ifLtN 120012 120140
        (.ifLtN 120012 120050
          (.seq (block [.copyN 120120 120141, .copyN 120121 120023])
            (.seq (.ifLtN 120024 120011 gtDS ltDS) (.ifLtN 120012 120128 useCh useD)))
          useCh)
        (.ifLtN 120012 120050 useD .skip)))

/-- The registers written by `tchS`. -/
def BT (r : ℕ) : Bool :=
  BX2 r || decide (120120 ≤ r ∧ r ≤ 120121) || decide (120150 ≤ r ∧ r ≤ 120152) ||
    decide (120180 ≤ r ∧ r ≤ 120182)

theorem wr_tchS : wr BT tchS = true := by decide

section Sel
variable (C : Chain) (V : QV)

open Classical in
/-- The stopping point at the near end `w` of the chord: a point of a chain edge (mode `0`) or
the walk position itself (mode `1`). -/
noncomputable def chordSel (w : ℕ) : ℕ × ℕ :=
  if 6 ≤ w ∧ w < 2 * V.m + 6 then (0, tci C (w - 6))
  else if w = 2 * V.m + 6 then (0, tci C (2 * V.m - 1)) else (1, w)

/-- The stopping point on the side of the box. -/
def boxSel : ℕ × ℕ := (1, if V.σb = 1 then 3 else 1)

open Classical in
/-- **The stopping point**: the near end of the chord if it exists and comes before the hit on
`D*` (`cb`), else the hit on `D*`, else the side of the box. -/
noncomputable def selOf (bestD : Option ℕ) (found : Prop) (w : ℕ) (cb : Prop) : ℕ × ℕ :=
  if found ∧ (bestD = none ∨ cb) then chordSel C V w
  else match bestD with
    | some cD => (0, cD)
    | none => boxSel V

end Sel

/-- The selected stopping point held in the registers. -/
def SelIn (c : Config) (sel : ℕ × ℕ) : Prop :=
  c.nreg 120150 = sel.1 ∧ (sel.1 = 0 → c.nreg 120151 = sel.2) ∧ (sel.1 = 1 → c.nreg 120152 = sel.2)

theorem useD_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) (hW : 1 ≤ W) :
    ∃ c' k, Exec P W useD c c' k ∧ k = 2 ∧ SelIn c' (0, c.nreg 120052) ∧
      (∀ r, r ≠ 120150 → r ≠ 120151 → c'.nreg r = c.nreg r) := by
  unfold useD
  exec_block
  · omega
  · exact ⟨rfl, ⟨by config_simp, fun _ => by config_simp, fun h => absurd h (by norm_num)⟩,
      fun r h1 h2 => by config_simp; upd_solve⟩

theorem useCh_exec {P : Polygon} {W : ℕ} (hW : 4 * P.n + 8 ≤ W) {C : Chain} {V : QV}
    (hv : QVOK P C V) (c : Config) (hw : WordsBounded W c) (hq : QConst P V c)
    (h150 : c.nreg 120150 = 1) :
    ∃ c' k, Exec P W useCh c c' k ∧ k ≤ 20 ∧ SelIn c' (chordSel C V (c.nreg 120141)) ∧
      (∀ r, (r < 120150 ∨ 120152 < r) → r < 120180 ∨ 120182 < r → c'.nreg r = c.nreg r) := by
  have hm1 := C.one_le
  obtain ⟨w, hwdef⟩ : ∃ w, c.nreg 120141 = w := ⟨_, rfl⟩
  rw [hwdef]
  unfold useCh
  by_cases h6 : w < 6
  · refine ⟨_, _, .ifLtN_true (by rwx [hwdef, hq.six]) (Exec.copyN hw _ _), by omega,
      ⟨?_, ?_, ?_⟩, fun r h1 h2 => ?_⟩
    · config_simp; rw [h150]; unfold chordSel; rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    · intro h; unfold chordSel at h; rw [ite_eq_right (by omega), ite_eq_right (by omega)] at h
      exact absurd h (by norm_num)
    · intro _; config_simp; rw [hwdef]; unfold chordSel
      rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    · config_simp; upd_solve
  have mid : ∀ (w' : ℕ), 6 ≤ w' → w' < 2 * V.m + 6 → ∀ (d : Config), WordsBounded W d →
      QConst P V d → d.nreg 120180 = w' →
      ∃ d' k, Exec P W (.seq tciS (block [.constN 120150 0, .copyN 120151 120181])) d d' k ∧
        k ≤ 11 ∧ d'.nreg 120150 = 0 ∧ d'.nreg 120151 = tci C (w' - 6) ∧
        (∀ r, r ≠ 120150 → r ≠ 120151 → r ≠ 120181 → r ≠ 120182 → d'.nreg r = d.nreg r) := by
    intro w' h1 h2 d hd hqd h180
    obtain ⟨d₁, k₁, e₁, hk₁, v₁, r₁⟩ := tciS_exec (P := P) hW hv d hd hqd (by rwx [h180])
      (by rwx [h180])
    rw [h180] at v₁
    have w₁ := e₁.wb_right
    obtain ⟨d₂, k₂, e₂, hk₂, v₂⟩ : ∃ d₂ k₂, Exec P W (block [.constN 120150 0, .copyN 120151 120181])
        d₁ d₂ k₂ ∧ k₂ = 2 ∧ (d₂.nreg 120150 = 0 ∧ d₂.nreg 120151 = d₁.nreg 120181 ∧
          ∀ r, r ≠ 120150 → r ≠ 120151 → d₂.nreg r = d₁.nreg r) := by
      exec_block
      · omega
      · exact ⟨rfl, by config_simp, by config_simp, fun r h1 h2 => by config_simp; upd_solve⟩
    obtain ⟨a1, a2, a3⟩ := v₂
    exact ⟨d₂, _, .seq e₁ e₂, by omega, a1, by rw [a2, v₁], fun r h1 h2 h3 h4 => by
      rw [a3 r h1 h2, r₁ r h3 h4]⟩
  by_cases hE : w < 2 * V.m + 6
  · obtain ⟨c₁, e₁, v₁, r₁⟩ := copy_exec (P := P) hw 120180 120141
    rw [hwdef] at v₁
    obtain ⟨d', k, ex, hk, a1, a2, a3⟩ := mid w (by omega) hE c₁ e₁.wb_right
      (hq.congr fun r h1 h2 => r₁ r (by omega)) v₁
    refine ⟨d', _, .ifLtN_false (by rwx [hwdef, hq.six])
      (.ifLtN_true (by rwx [hwdef, hq.tEnd]) (.seq e₁ ex)), by omega, ⟨?_, ?_, ?_⟩,
      fun r h1 h2 => ?_⟩
    · rw [a1]; unfold chordSel; rw [ite_eq_left ⟨by omega, hE⟩]
    · intro _; rw [a2]; unfold chordSel; rw [ite_eq_left ⟨by omega, hE⟩]
    · intro h; unfold chordSel at h; rw [ite_eq_left ⟨by omega, hE⟩] at h; exact absurd h (by norm_num)
    · rw [a3 r (by omega) (by omega) (by omega) (by omega), r₁ r (by omega)]
  by_cases hT : w = 2 * V.m + 6
  · have w₀ := hw
    obtain ⟨c₁, e₁, v₁⟩ : ∃ c₁, Exec P W (.instr (.subN 120180 120029 120011)) c c₁ 1 ∧
        c₁.nreg 120180 = 2 * V.m + 5 ∧ ∀ r, r ≠ 120180 → c₁.nreg r = c.nreg r :=
      ⟨_, Exec.subN hw _ _ _, by config_simp; rwo [hq.tEnd, hq.one], fun r hr => by
        config_simp; upd_solve⟩
    obtain ⟨d', k, ex, hk, a1, a2, a3⟩ := mid (2 * V.m + 5) (by rwo [hv.m]) (by omega) c₁
      e₁.wb_right
      (hq.congr fun r h1 h2 => v₁.2 r (by omega)) v₁.1
    have hq12 : c.nreg 120141 = c.nreg 120029 := by rw [hwdef, hq.tEnd, hT]
    refine ⟨d', _, .ifLtN_false (by rwx [hwdef, hq.six])
      (.ifLtN_false (by rwx [hwdef, hq.tEnd]) (ifEq_eq_exec hq12 (.seq e₁ ex))), by omega,
      ⟨?_, ?_, ?_⟩, fun r h1 h2 => ?_⟩
    · rw [a1]; unfold chordSel; rw [ite_eq_right (by omega), ite_eq_left (by rw [hv.m] at hT ⊢; exact hT)]
    · intro _; rw [a2]; unfold chordSel
      rw [ite_eq_right (by omega), ite_eq_left (by rw [hv.m] at hT ⊢; exact hT), hv.m]
      congr 1
    · intro h; unfold chordSel at h
      rw [ite_eq_right (by omega), ite_eq_left (by rw [hv.m] at hT ⊢; exact hT)] at h
      exact absurd h (by norm_num)
    · rw [a3 r (by omega) (by omega) (by omega) (by omega), v₁.2 r (by omega)]
  · have hq12 : c.nreg 120141 ≠ c.nreg 120029 := by rwx [hwdef, hq.tEnd]
    obtain ⟨k', ex', hk'⟩ := ifEq_ne_exec (a := 120141) (b := 120029)
      (S := .seq (.instr (.subN 120180 120029 120011)) (.seq tciS (block [.constN 120150 0,
        .copyN 120151 120181]))) hq12 (Exec.copyN hw 120152 120141 (P := P))
    refine ⟨_, _, .ifLtN_false (by rwx [hwdef, hq.six])
      (.ifLtN_false (by rwx [hwdef, hq.tEnd]) ex'), by omega, ⟨?_, ?_, ?_⟩,
      fun r h1 h2 => ?_⟩
    · config_simp; rw [h150]; unfold chordSel
      rw [ite_eq_right (by omega), ite_eq_right (by rw [hv.m] at hT ⊢; exact hT)]
    · intro h; unfold chordSel at h
      rw [ite_eq_right (by omega), ite_eq_right (by rw [hv.m] at hT ⊢; exact hT)] at h
      exact absurd h (by norm_num)
    · intro _; config_simp; rw [hwdef]; unfold chordSel
      rw [ite_eq_right (by omega), ite_eq_right (by rw [hv.m] at hT ⊢; exact hT)]
    · config_simp; upd_solve

open Classical in
/-- **The choice of the stopping point.** -/
theorem tchS_exec {P : Polygon} {W : ℕ} (hG : GoodEnv P) (hW : 8 * P.n + 32 ≤ W) {C : Chain}
    {V : QV} (hv : QVOK P C V) (htv : V.tv < P.n) (c : Config) (hw : WordsBounded W c)
    (hq : QConst P V c) (hf : c.nreg 120140 ≤ 1) (hb : BestOK P.n V.s V.m c) :
    ∃ c' k, Exec P W tchS c c' k ∧ k ≤ 340 ∧ FrameB BT c c' ∧
      SelIn c' (selOf C V (bestOf c) (c.nreg 120140 = 1) (c.nreg 120141)
        (if V.σb = 1 then EndLtD P C V (c.nreg 120051) (c.nreg 120141) V.hz
          else EndGtD P C V (c.nreg 120051) (c.nreg 120141) V.hz)) := by
  suffices H : ∃ c' k, Exec P W tchS c c' k ∧ k ≤ 340 ∧
      SelIn c' (selOf C V (bestOf c) (c.nreg 120140 = 1) (c.nreg 120141)
        (if V.σb = 1 then EndLtD P C V (c.nreg 120051) (c.nreg 120141) V.hz
          else EndGtD P C V (c.nreg 120051) (c.nreg 120141) V.hz)) by
    obtain ⟨c', k, ex, hk, hs⟩ := H
    exact ⟨c', k, ex, hk, exec_frameB ex wr_tchS, hs⟩
  obtain ⟨c₁, e₁, v₁, r₁⟩ := const_exec (P := P) hw 120150 1 (by omega)
  -- the side of the box
  obtain ⟨c₂, k₂, e₂, hk₂, v₂, v150, r₂⟩ : ∃ c₂ k₂, Exec P W (.ifLtN 120024 120011
      (.instr (.constN 120152 1)) (.instr (.constN 120152 3))) c₁ c₂ k₂ ∧ k₂ ≤ 3 ∧
      c₂.nreg 120152 = (boxSel V).2 ∧ c₂.nreg 120150 = 1 ∧
      (∀ r, r ≠ 120152 → r ≠ 120150 → c₂.nreg r = c.nreg r) := by
    have x24 : c₁.nreg 120024 = V.σb := (r₁ _ (by decide)).trans hq.σb
    have x11 : c₁.nreg 120011 = 1 := (r₁ _ (by decide)).trans hq.one
    by_cases hσ : V.σb < 1
    · obtain ⟨c₂, e₂, v₂, r₂⟩ := const_exec (P := P) e₁.wb_right 120152 1 (by omega)
      refine ⟨c₂, _, .ifLtN_true (by rw [x24, x11]; exact hσ) e₂, by omega, ?_, ?_, ?_⟩
      · rw [v₂]; unfold boxSel; rw [ite_eq_right (by omega)]
      · rw [r₂ _ (by decide), v₁]
      · intro r h1 h2; rw [r₂ r h1, r₁ r h2]
    · obtain ⟨c₂, e₂, v₂, r₂⟩ := const_exec (P := P) e₁.wb_right 120152 3 (by omega)
      refine ⟨c₂, _, .ifLtN_false (by rw [x24, x11]; exact hσ) e₂, by omega, ?_, ?_, ?_⟩
      · rw [v₂]; unfold boxSel; rw [ite_eq_left (by have := hv.σb_le; omega)]
      · rw [r₂ _ (by decide), v₁]
      · intro r h1 h2; rw [r₂ r h1, r₁ r h2]
  have hq₂ : QConst P V c₂ := hq.congr fun r h1 h2 => r₂ r (by omega) (by omega)
  have w₂ := e₂.wb_right
  have x140 : c₂.nreg 120140 = c.nreg 120140 := r₂ _ (by decide) (by decide)
  have x50 : c₂.nreg 120050 = c.nreg 120050 := r₂ _ (by decide) (by decide)
  have x141 : c₂.nreg 120141 = c.nreg 120141 := r₂ _ (by decide) (by decide)
  have x52 : c₂.nreg 120052 = c.nreg 120052 := r₂ _ (by decide) (by decide)
  have hbo : bestOf c = if c.nreg 120050 = 1 then some (c.nreg 120052) else none := rfl
  set CB := (if V.σb = 1 then EndLtD P C V (c.nreg 120051) (c.nreg 120141) V.hz
    else EndGtD P C V (c.nreg 120051) (c.nreg 120141) V.hz) with hCB
  have hb1 := hb.1
  by_cases hF : c.nreg 120140 = 1
  · by_cases hD : c.nreg 120050 = 1
    · -- both: compare
      obtain ⟨c₃, k₃, e₃, hk₃, v₃⟩ : ∃ c₃ k₃, Exec P W (block [.copyN 120120 120141,
          .copyN 120121 120023]) c₂ c₃ k₃ ∧ k₃ = 2 ∧ (c₃.nreg 120120 = c.nreg 120141 ∧
            c₃.nreg 120121 = V.hz ∧ ∀ r, r ≠ 120120 → r ≠ 120121 → c₃.nreg r = c₂.nreg r) := by
        exec_block
        exact ⟨rfl, by config_simp; exact x141, by config_simp; exact hq₂.hz,
          fun r h1 h2 => by config_simp; upd_solve⟩
      obtain ⟨x120, x121, r₃⟩ := v₃
      have hq₃ : QConst P V c₃ := hq₂.congr fun r h1 h2 => r₃ r (by omega) (by omega)
      have heD : c₃.nreg 120051 < P.n := by
        rw [r₃ _ (by decide) (by decide), r₂ _ (by decide) (by decide), (hb.2 hD).1]
        exact Nat.mod_lt _ (by have := hv.s_lt; omega)
      have x51 : c₃.nreg 120051 = c.nreg 120051 := by
        rw [r₃ _ (by decide) (by decide), r₂ _ (by decide) (by decide)]
      obtain ⟨c₄, k₄, e₄, hk₄, f₄, b₄, g₄⟩ : ∃ c₄ k₄, Exec P W (.ifLtN 120024 120011 gtDS ltDS)
          c₃ c₄ k₄ ∧ k₄ ≤ 302 ∧ FrameB BX2 c₃ c₄ ∧ c₄.nreg 120128 ≤ 1 ∧ (c₄.nreg 120128 = 1 ↔ CB) := by
        by_cases hσ : V.σb < 1
        · obtain ⟨c₄, k₄, e₄, hk₄, f₄, b₄, g₄⟩ := gtDS_exec (P := P) hG (by omega) hv htv c₃
            e₃.wb_right hq₃ (by rw [x121]; exact hv.hz_lt) heD
          rw [x51, x120, x121] at g₄
          refine ⟨c₄, _, .ifLtN_true (by rw [hq₃.σb, hq₃.one]; exact hσ) e₄, by omega, f₄, b₄, ?_⟩
          rw [g₄, hCB, ite_eq_right (by omega)]
        · obtain ⟨c₄, k₄, e₄, hk₄, f₄, b₄, g₄⟩ := ltDS_exec (P := P) hG (by omega) hv htv c₃
            e₃.wb_right hq₃ (by rw [x121]; exact hv.hz_lt) heD
          rw [x51, x120, x121] at g₄
          refine ⟨c₄, _, .ifLtN_false (by rw [hq₃.σb, hq₃.one]; exact hσ) e₄, by omega, f₄, b₄, ?_⟩
          rw [g₄, hCB, ite_eq_left (by have := hv.σb_le; omega)]
      have hq₄ : QConst P V c₄ := hq₃.frame f₄ fun r h1 h2 => by
        sio only [BX2, Bk, Bool.or_eq_false_iff, decide_eq_false_iff_not]
      have R₄ : ∀ r, BX2 r = false → r ≠ 120120 → r ≠ 120121 → c₄.nreg r = c₂.nreg r :=
        fun r h1 h2 h3 => (f₄.1 r h1).trans (r₃ r h2 h3)
      by_cases hc : c₄.nreg 120128 = 1
      · obtain ⟨c₅, k₅, e₅, hk₅, s₅, -⟩ := useCh_exec (P := P) (by omega) hv c₄ e₄.wb_right hq₄
          (by rw [R₄ _ (by decide) (by decide) (by decide), v150])
        rw [R₄ _ (by decide) (by decide) (by decide), x141] at s₅
        refine ⟨c₅, _, .seq e₁ (.seq e₂ (.ifLtN_true (by rwo [hq₂.zero, x140])
          (.ifLtN_true (by rwo [hq₂.zero, x50]) (.seq e₃ (.seq e₄
            (.ifLtN_true (by rwo [hq₄.zero]) e₅)))))), by omega, ?_⟩
        unfold selOf; rwx [ite_eq_left ⟨hF, Or.inr (g₄.1 hc)⟩]
      · have hdc : ¬ CB := fun h => hc (g₄.2 h)
        obtain ⟨c₅, k₅, e₅, hk₅, s₅, -⟩ := useD_exec (P := P) c₄ e₄.wb_right (by omega)
        rw [R₄ _ (by decide) (by decide) (by decide), x52] at s₅
        refine ⟨c₅, _, .seq e₁ (.seq e₂ (.ifLtN_true (by rwo [hq₂.zero, x140])
          (.ifLtN_true (by rwo [hq₂.zero, x50]) (.seq e₃ (.seq e₄
            (.ifLtN_false (by rwo [hq₄.zero]) e₅)))))), by omega, ?_⟩
        unfold selOf
        rw [ite_eq_right (fun h => by
          rcases h.2 with h' | h'
          · rw [hbo, ite_eq_left hD] at h'; exact absurd h' (by simp)
          · exact hdc h'), hbo, ite_eq_left hD]
        exact s₅
    · -- only the chord
      obtain ⟨c₅, k₅, e₅, hk₅, s₅, -⟩ := useCh_exec (P := P) (by omega) hv c₂ w₂ hq₂ v150
      rw [x141] at s₅
      refine ⟨c₅, _, .seq e₁ (.seq e₂ (.ifLtN_true (by rwo [hq₂.zero, x140])
        (.ifLtN_false (by rwo [hq₂.zero, x50]) e₅))), by omega, ?_⟩
      unfold selOf; rw [ite_eq_left ⟨hF, Or.inl (by rw [hbo, ite_eq_right hD])⟩]; exact s₅
  · by_cases hD : c.nreg 120050 = 1
    · obtain ⟨c₅, k₅, e₅, hk₅, s₅, -⟩ := useD_exec (P := P) c₂ w₂ (by omega)
      rw [x52] at s₅
      refine ⟨c₅, _, .seq e₁ (.seq e₂ (.ifLtN_false (by rwo [hq₂.zero, x140])
        (.ifLtN_true (by rwo [hq₂.zero, x50]) e₅))), by omega, ?_⟩
      unfold selOf; rwx [ite_eq_right (fun h => hF h.1), hbo, ite_eq_left hD]
    · refine ⟨c₂, _, .seq e₁ (.seq e₂ (.ifLtN_false (by rwo [hq₂.zero, x140])
        (.ifLtN_false (by rwo [hq₂.zero, x50]) (.skip w₂)))), by omega, ?_⟩
      unfold selOf; rw [ite_eq_right (fun h => hF h.1), hbo, ite_eq_right hD]
      exact ⟨v150, fun h => absurd h (by ufn boxSel), fun _ => v₂⟩

/-! ## The walk positions of the stopping point -/

section PosDef
variable (V : QV) (n : ℕ)

/-- The walk edge of the stopping point on the tour edge of chain edge `c` running forward. -/
def wAOf (c : ℕ) : ℕ :=
  (c + 2 * V.m - V.sS) % (2 * V.m) + 6 + (if V.hz = (V.s + c + 1) % n then 1 else 0)

/-- The walk edge of the stopping point on the tour edge of chain edge `c` running backward. -/
def wBOf (c : ℕ) : ℕ :=
  (2 * V.m - 1 - c + 2 * V.m - V.sS) % (2 * V.m) + 6 + (if V.hz = (V.s + c) % n then 1 else 0)

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

theorem wr_posS : wr BPo posS = true := by decide

theorem endS_exec {P : Polygon} {W : ℕ} (hW : 8 * P.n + 32 ≤ W) {C : Chain} {V : QV}
    (hv : QVOK P C V) (c : Config) (hw : WordsBounded W c) (hq : QConst P V c) {rd : ℕ}
    (hrd : rd = 120160 ∨ rd = 120161) (δ : Bool) {x cc : ℕ} (hx : c.nreg 120184 = x)
    (hx4 : x < 2 * (2 * V.m)) (hc : c.nreg 120151 = cc) (hcm : cc < V.m) :
    ∃ c' k, Exec P W (endS rd δ) c c' k ∧ k ≤ 16 ∧
      c'.nreg rd = x % (2 * V.m) + 6 + (if V.hz = (V.s + cc + (if δ then 1 else 0)) % P.n then 1 else 0) ∧
      (∀ r, r ≠ rd → r ≠ 120184 → r ≠ 120185 → c'.nreg r = c.nreg r) := by
  have hmn : V.m < P.n := by
    rw [hv.m]; have := C.m_lt; rw [hv.CQ, show (Qof P).n = P.n from shear_n _ _] at this; exact this
  have hm1 : 1 ≤ V.m := by rw [hv.m]; exact C.one_le
  have hs := hv.s_lt
  have hn : 0 < P.n := by omega
  unfold endS
  obtain ⟨c₁, k₁, e₁, hk₁, v₁, r₁, -⟩ := modSub_exec (P := P) (r := 120184) (nr := 120019)
    (by decide) c hw (by rwx [hx, hq.twoM])
  rw [hx, hq.twoM] at v₁
  have hq₁ : QConst P V c₁ := hq.congr fun r h1 h2 => r₁ r (by omega)
  have hr1 : rd ≠ 120184 ∧ rd ≠ 120185 ∧ rd ≠ 120015 ∧ rd ≠ 120151 ∧ rd ≠ 120011 ∧
      rd ≠ 120028 ∧ rd ≠ 120010 ∧ rd ≠ 120023 := by
    rcases hrd with rfl | rfl <;> decide
  obtain ⟨c₂, k₂, e₂, hk₂, v₂, v₂', r₂⟩ : ∃ c₂ k₂, Exec P W (block ([.addN rd 120184 120028,
      .addN 120185 120015 120151] ++ (if δ then [.addN 120185 120185 120011] else []))) c₁ c₂ k₂ ∧
      k₂ ≤ 3 ∧ c₂.nreg rd = x % (2 * V.m) + 6 ∧
      c₂.nreg 120185 = V.s + cc + (if δ then 1 else 0) ∧
      (∀ r, r ≠ rd → r ≠ 120185 → c₂.nreg r = c₁.nreg r) := by
    have hxm : x % (2 * V.m) < 2 * V.m := Nat.mod_lt _ (by omega)
    have h151 : c₁.nreg 120151 = cc := by rw [r₁ _ (by decide), hc]
    have w₁ := e₁.wb_right
    clear hw
    have q6 := hq₁.six
    have qs := hq₁.s
    have q1 := hq₁.one
    have hrd' := hr1
    cases δ
    · simp only [List.append_nil, Bool.false_eq_true, ite_false]
      exec_block
      · omega
      · config_simp; ((try simp only [Machine.upd_apply]); (repeat' split_ifs) <;> omega)
      · refine ⟨by omega, ?_, ?_, fun r h1 h2 => ?_⟩ <;>
          (config_simp; ((try simp only [Machine.upd_apply]); (repeat' split_ifs) <;>
            first | omega))
    · simp only [List.cons_append, List.nil_append, ite_true]
      exec_block
      · omega
      · config_simp; ((try simp only [Machine.upd_apply]); (repeat' split_ifs) <;> omega)
      · config_simp; ((try simp only [Machine.upd_apply]); (repeat' split_ifs) <;> omega)
      · refine ⟨by omega, ?_, ?_, fun r h1 h2 => ?_⟩ <;>
          (config_simp; ((try simp only [Machine.upd_apply]); (repeat' split_ifs) <;>
            first | omega))
  have hq₂ : QConst P V c₂ := hq₁.congr fun r h1 h2 => r₂ r (by omega) (by omega)
  obtain ⟨c₃, k₃, e₃, hk₃, v₃, r₃, -⟩ := modSub_exec (P := P) (r := 120185) (nr := 120010)
    (by decide) c₂ e₂.wb_right (by rw [v₂', hq₂.n]; cases δ <;> simp <;> omega)
  rw [v₂', hq₂.n] at v₃
  have x23 : c₃.nreg 120023 = V.hz := (r₃ _ (by decide)).trans hq₂.hz
  have xrd : c₃.nreg rd = x % (2 * V.m) + 6 := (r₃ _ (by omega)).trans v₂
  by_cases heq : V.hz = (V.s + cc + (if δ then 1 else 0)) % P.n
  · have hq12 : c₃.nreg 120023 = c₃.nreg 120185 := by rw [x23, v₃, heq]
    obtain ⟨c₄, e₄, v₄, r₄, -⟩ := add_exec (P := P) e₃.wb_right rd rd 120011 (by
      rw [xrd, (r₃ _ (by decide)).trans hq₂.one]
      have : x % (2 * V.m) < 2 * V.m := Nat.mod_lt _ (by omega)
      omega)
    refine ⟨c₄, _, .seq e₁ (.seq e₂ (.seq e₃ (ifEq_eq_exec hq12 e₄))), by omega, ?_,
      fun r h1 h2 h3 => ?_⟩
    · rw [v₄, xrd, (r₃ _ (by decide)).trans hq₂.one, ite_eq_left heq]
    · rw [r₄ r h1, r₃ r h3, r₂ r h1 h3, r₁ r h2]
  · have hq12 : c₃.nreg 120023 ≠ c₃.nreg 120185 := by rwx [x23, v₃]
    obtain ⟨k', ex', hk'⟩ := ifEq_ne_exec (S := .instr (.addN rd rd 120011)) hq12
      (.skip e₃.wb_right)
    refine ⟨c₃, _, .seq e₁ (.seq e₂ (.seq e₃ ex')), by omega, ?_, fun r h1 h2 h3 => ?_⟩
    · rw [xrd, ite_eq_right heq]
    · rw [r₃ r h3, r₂ r h1 h3, r₁ r h2]

/-- **The walk positions of the stopping point.** -/
theorem posS_exec {P : Polygon} {W : ℕ} (hW : 8 * P.n + 32 ≤ W) {C : Chain} {V : QV}
    (hv : QVOK P C V) (c : Config) (hw : WordsBounded W c) (hq : QConst P V c) {sel : ℕ × ℕ}
    (hs : SelIn c sel) (hsel : sel.1 = 0 ∨ sel.1 = 1) (hcm : sel.1 = 0 → sel.2 < V.m) :
    ∃ c' k, Exec P W posS c c' k ∧ k ≤ 60 ∧ FrameB BPo c c' ∧
      (c'.nreg 120160, c'.nreg 120161, c'.nreg 120162, c'.nreg 120163) = posOf V P.n sel := by
  suffices H : ∃ c' k, Exec P W posS c c' k ∧ k ≤ 60 ∧
      (c'.nreg 120160, c'.nreg 120161, c'.nreg 120162, c'.nreg 120163) = posOf V P.n sel by
    obtain ⟨c', k, ex, hk, h⟩ := H
    exact ⟨c', k, ex, hk, exec_frameB ex wr_posS, h⟩
  have hsS : V.sS ≤ 2 * V.m := by rw [hv.sS, hv.m]; exact C.sideS_lt C.sideBeta
  have hm1 : 1 ≤ V.m := by rw [hv.m]; exact C.one_le
  have hmn : V.m < P.n := by
    rw [hv.m]; have := C.m_lt; rw [hv.CQ, show (Qof P).n = P.n from shear_n _ _] at this; exact this
  rcases hsel with h0 | h1
  · obtain ⟨cc, hcc⟩ : ∃ cc, sel.2 = cc := ⟨_, rfl⟩
    have hccm := hcm h0
    rw [hcc] at hccm
    have x151 : c.nreg 120151 = cc := by rw [hs.2.1 h0, hcc]
    have x150 : c.nreg 120150 = 0 := by rw [hs.1, h0]
    -- the forward tour edge
    obtain ⟨c₁, k₁, e₁, hk₁, v₁, r₁⟩ : ∃ c₁ k₁, Exec P W (block [.addN 120184 120151 120019,
        .subN 120184 120184 120021]) c c₁ k₁ ∧ k₁ = 2 ∧ c₁.nreg 120184 = cc + 2 * V.m - V.sS ∧
        (∀ r, r ≠ 120184 → c₁.nreg r = c.nreg r) := by
      exec_block
      · rwo [x151, hq.twoM]
      · refine ⟨rfl, ?_, fun r hr => by config_simp; upd_solve⟩
        config_simp; rw [x151, hq.twoM, hq.sS]
    have hq₁ : QConst P V c₁ := hq.congr fun r h1 h2 => r₁ r (by omega)
    obtain ⟨c₂, k₂, e₂, hk₂, v₂, r₂⟩ := endS_exec (P := P) hW hv c₁ e₁.wb_right hq₁ (Or.inl rfl) true
      v₁ (by omega) (by rw [r₁ _ (by decide), x151]) hccm
    have hq₂ : QConst P V c₂ := hq₁.congr fun r h1 h2 => r₂ r (by omega) (by omega) (by omega)
    -- the backward tour edge
    obtain ⟨c₃, k₃, e₃, hk₃, v₃, r₃⟩ : ∃ c₃ k₃, Exec P W (block [.subN 120184 120019 120011,
        .subN 120184 120184 120151, .addN 120184 120184 120019, .subN 120184 120184 120021]) c₂ c₃ k₃ ∧
        k₃ = 4 ∧ c₃.nreg 120184 = 2 * V.m - 1 - cc + 2 * V.m - V.sS ∧
        (∀ r, r ≠ 120184 → c₃.nreg r = c₂.nreg r) := by
      have x151' : c₂.nreg 120151 = cc := by
        rw [r₂ _ (by decide) (by decide) (by decide), r₁ _ (by decide), x151]
      have q2 := hq₂.twoM
      have q1 := hq₂.one
      have q21 := hq₂.sS
      have w₂ := e₂.wb_right
      clear hw
      exec_block
      · cso
      · refine ⟨rfl, ?_, fun r hr => by config_simp; upd_solve⟩
        cso
    have hq₃ : QConst P V c₃ := hq₂.congr fun r h1 h2 => r₃ r (by omega)
    obtain ⟨c₄, k₄, e₄, hk₄, v₄, r₄⟩ := endS_exec (P := P) hW hv c₃ e₃.wb_right hq₃ (Or.inr rfl) false
      v₃ (by omega) (by rw [r₃ _ (by decide), r₂ _ (by decide) (by decide) (by decide),
        r₁ _ (by decide), x151]) hccm
    have hq₄ : QConst P V c₄ := hq₃.congr fun r h1 h2 => r₄ r (by omega) (by omega) (by omega)
    have x160 : c₄.nreg 120160 = wAOf V P.n cc := by
      rw [r₄ _ (by decide) (by decide) (by decide), r₃ _ (by decide), v₂]; ufs wAOf
    have x161 : c₄.nreg 120161 = wBOf V P.n cc := by rw [v₄]; ufs wBOf
    have ex₀ : Exec P W (.seq (block [.addN 120184 120151 120019, .subN 120184 120184 120021])
        (.seq (endS 120160 true) (.seq (block [.subN 120184 120019 120011, .subN 120184 120184 120151,
          .addN 120184 120184 120019, .subN 120184 120184 120021]) (endS 120161 false)))) c c₄
        (k₁ + (k₂ + (k₃ + k₄))) := .seq e₁ (.seq e₂ (.seq e₃ e₄))
    have w₄ := e₄.wb_right
    by_cases htv : V.hz = V.tv
    · have hq12 : c₄.nreg 120023 = c₄.nreg 120022 := by rw [hq₄.hz, hq₄.tv, htv]
      obtain ⟨c₅, k₅, e₅, hk₅, v₅⟩ : ∃ c₅ k₅, Exec P W (block [.copyN 120162 120028,
          .copyN 120163 120029]) c₄ c₅ k₅ ∧ k₅ = 2 ∧ (c₅.nreg 120160 = c₄.nreg 120160 ∧
            c₅.nreg 120161 = c₄.nreg 120161 ∧ c₅.nreg 120162 = 6 ∧
            c₅.nreg 120163 = 2 * V.m + 6) := by
        exec_block
        exact ⟨rfl, by config_simp, by config_simp, by config_simp; exact hq₄.six,
          by config_simp; exact hq₄.tEnd⟩
      obtain ⟨a0, a1, a2, a3⟩ := v₅
      refine ⟨c₅, _, .ifLtN_true (by rwo [x150, hq.one]) (.seq e₁ (.seq e₂ (.seq e₃ (.seq e₄
        (ifEq_eq_exec hq12 e₅))))), by omega, ?_⟩
      unfold posOf; rw [ite_eq_left h0, hcc, a0, a1, a2, a3, x160, x161, ite_eq_left htv,
        ite_eq_left htv]
    · have hq12 : c₄.nreg 120023 ≠ c₄.nreg 120022 := by rwx [hq₄.hz, hq₄.tv]
      obtain ⟨c₅, k₅, e₅, hk₅, v₅⟩ : ∃ c₅ k₅, Exec P W (block [.copyN 120162 120160,
          .copyN 120163 120161]) c₄ c₅ k₅ ∧ k₅ = 2 ∧ (c₅.nreg 120160 = c₄.nreg 120160 ∧
            c₅.nreg 120161 = c₄.nreg 120161 ∧ c₅.nreg 120162 = c₄.nreg 120160 ∧
            c₅.nreg 120163 = c₄.nreg 120161) := by
        exec_block
        exact ⟨rfl, by config_simp, by config_simp, by config_simp, by config_simp⟩
      obtain ⟨a0, a1, a2, a3⟩ := v₅
      obtain ⟨k', ex', hk'⟩ := ifEq_ne_exec (S := block [.copyN 120162 120028, .copyN 120163 120029])
        hq12 e₅
      refine ⟨c₅, _, .ifLtN_true (by rwo [x150, hq.one]) (.seq e₁ (.seq e₂ (.seq e₃ (.seq e₄
        ex')))), by omega, ?_⟩
      unfold posOf; rw [ite_eq_left h0, hcc, a0, a1, a2, a3, x160, x161, ite_eq_right htv,
        ite_eq_right htv]
  · have x150 : c.nreg 120150 = 1 := by rw [hs.1, h1]
    have x152  := hs.2.2 h1
    obtain ⟨c₁, k₁, e₁, hk₁, v₁⟩ : ∃ c₁ k₁, Exec P W (block [.copyN 120160 120152,
        .copyN 120161 120152, .copyN 120162 120152, .copyN 120163 120152]) c c₁ k₁ ∧ k₁ = 4 ∧
        (c₁.nreg 120160 = sel.2 ∧ c₁.nreg 120161 = sel.2 ∧ c₁.nreg 120162 = sel.2 ∧
          c₁.nreg 120163 = sel.2) := by
      exec_block
      exact ⟨rfl, by config_simp; exact x152, by config_simp; exact x152,
        by config_simp; exact x152, by config_simp; exact x152⟩
    obtain ⟨a0, a1, a2, a3⟩ := v₁
    refine ⟨c₁, _, .ifLtN_false (by rwo [x150, hq.one]) e₁, by omega, ?_⟩
    unfold posOf; rw [ite_eq_right (by omega), a0, a1, a2, a3]

end

end OracleR

end Chazelle.Core
