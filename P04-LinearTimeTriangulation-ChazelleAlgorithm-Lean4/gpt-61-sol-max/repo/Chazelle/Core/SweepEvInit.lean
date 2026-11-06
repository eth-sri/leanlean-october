module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.SweepEvTasks2

/-!
# The sweep (WP-D), stages 2–3: the initialisation, part 1 (the register constants)

The initialisation `initE` of `sweepEvSpec`'s program (task `InitTask`, `SweepEvTasks2.lean`)
starts with `initRA`: a straight-line block `regA` and four tests `stmtB`, which set from the
stage-0 registers (`St0S`: `sw 21`, `sw 33 … 35`, `sw 40 … 49`, `sw 90 … 93`)

* the constants `Consts` (`sw 610 … 616`);
* the constants of the map `MapK` (`sw 652 … 658`, `660`) and `cGW = gW` (`sw 659`);
* the constants of the classification `OrgK` except the top of `C₁` (`sw 640 … 644`).

Scratch: `sw 700 … 704`.  The block lemma `exec_regB` runs a straight-line register block
without the scratch condition of `SweepIo.IRS.block` (the initialisation writes fixed registers).

Main lemma: `initRA_exec`.
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep

@[expose] public section

/-! ## Straight-line register blocks -/

/-- The word-bound side condition of a register instruction. -/
def okWI (W : ℕ) (f : ℕ → ℕ) : Instr → Prop
  | .constN _ k => k ≤ W
  | .copyN _ _ => True
  | .addN _ a b => f a + f b ≤ W
  | .subN _ _ _ => True
  | .loadN _ _ => True
  | _ => False

/-- The side conditions of a register block along its run. -/
def okW (W : ℕ) (m : ℕ → ℕ) : List Instr → (ℕ → ℕ) → Prop
  | [], _ => True
  | i :: l, f => okWI W f i ∧ okW W m l (regI m i f)

section
variable {P : Polygon} {W : ℕ}
theorem exec_regI {c : Config} (hw : WordsBounded W c) {i : Instr}
    (hi : okWI W c.nreg i) : Exec P W (.instr i) c { c with nreg := regI c.nmem i c.nreg } 1 := by
  cases i with
  | constN r k => exact Exec.constN hw r k hi
  | copyN r a => exact Exec.copyN hw r a
  | addN r a b => exact Exec.addN hw r a b hi
  | subN r a b => exact Exec.subN hw r a b
  | loadN r a => exact Exec.loadN hw r a
  | _ => ram_grind

/-- **A straight-line register block** runs to `regB`. -/
theorem exec_regB : ∀ (l : List Instr) {c : Config}, WordsBounded W c →
    okW W c.nmem l c.nreg → Exec P W (block l) c { c with nreg := regB c.nmem l c.nreg } l.length
  | [], _, hw, _ => Exec.block_nil hw
  | i :: l, _, hw, ⟨hi, hl⟩ => by
    have e1 := exec_regI (P := P) hw hi
    exact Exec.block_cons e1 (exec_regB l e1.wb_right hl)

/-! ## The block `regA` -/


end

def iL : ℕ := sw 700
def iT : ℕ := sw 701
def iG : ℕ := sw 702
def iO : ℕ := sw 703
def iB : ℕ := sw 704

/-- The constants, the copies, `Lst`, `E₁`, `gW + Lst`, `sw 45 + n - gW`, and the words `m`,
`topIdx`, `sideBeta` of the descriptor of `C₂`. -/
def regA : List Instr :=
  [.constN K0 0, .constN K1 1, .constN K6 6, .constN K4 4, .constN K5 5, .constN K2 2,
    .constN K3 3, .copyN cGW (sw 40), .copyN cN1 (sw 33), .copyN cNW (sw 35), .copyN cLL (sw 47),
    .copyN cLD (sw 49), .addN cLE (sw 47) (sw 49), .subN c2m (sw 34) (sw 92),
    .subN c2m6 (sw 34) (sw 91), .addN iL (sw 42) (sw 43), .subN iT (sw 35) iL,
    .addN cE1 iT (sw 49), .addN iG (sw 40) iL, .addN iO (sw 45) (sw 35), .subN iO iO (sw 40),
    .addN iT (sw 21) K2, .loadN cm iT, .addN iT (sw 21) K3, .loadN cTop iT,
    .addN iT (sw 21) K4, .loadN iB iT]

set_option maxRecDepth 20000 in
theorem regA_ok {W : ℕ} (m f : ℕ → ℕ) (hW : 6 ≤ W) (h1 : f (sw 47) + f (sw 49) ≤ W)
    (h2 : f (sw 42) + f (sw 43) ≤ W) (h3 : f (sw 35) - (f (sw 42) + f (sw 43)) + f (sw 49) ≤ W)
    (h4 : f (sw 40) + (f (sw 42) + f (sw 43)) ≤ W) (h5 : f (sw 45) + f (sw 35) ≤ W)
    (h6 : f (sw 21) + 4 ≤ W) : okW W m regA f := by
  simp only [sw, Nat.reduceAdd] at *
  simp only [regA, okW, okWI, regI, K0, K1, K2, K3, K4, K5, K6, cGW, cN1, cNW, cLL, cLD, cLE, c2m,
    c2m6, iL, iT, cE1, iG, iO, cm, cTop, iB, sw, Machine.upd_same, ne_eq, Machine.upd_other,
    Nat.reduceAdd, Nat.reduceEqDiff, not_false_eq_true, and_true, true_and]
  omega

set_option maxRecDepth 20000 in
theorem regA_val (m f : ℕ → ℕ) :
    regB m regA f K0 = 0 ∧ regB m regA f K1 = 1 ∧ regB m regA f K6 = 6 ∧
    regB m regA f K4 = 4 ∧ regB m regA f K5 = 5 ∧ regB m regA f K2 = 2 ∧
    regB m regA f K3 = 3 ∧ regB m regA f cGW = f (sw 40) ∧ regB m regA f cN1 = f (sw 33) ∧
    regB m regA f cNW = f (sw 35) ∧ regB m regA f cLL = f (sw 47) ∧
    regB m regA f cLD = f (sw 49) ∧ regB m regA f cLE = f (sw 47) + f (sw 49) ∧
    regB m regA f c2m = f (sw 34) - f (sw 92) ∧ regB m regA f c2m6 = f (sw 34) - f (sw 91) ∧
    regB m regA f iL = f (sw 42) + f (sw 43) ∧
    regB m regA f cE1 = f (sw 35) - (f (sw 42) + f (sw 43)) + f (sw 49) ∧
    regB m regA f iG = f (sw 40) + (f (sw 42) + f (sw 43)) ∧
    regB m regA f iO = f (sw 45) + f (sw 35) - f (sw 40) ∧
    regB m regA f cm = m (f (sw 21) + 2) ∧ regB m regA f cTop = m (f (sw 21) + 3) ∧
    regB m regA f iB = m (f (sw 21) + 4) := by
  simp only [regA, regB, regI, K0, K1, K2, K3, K4, K5, K6, cGW, cN1, cNW, cLL, cLD, cLE, c2m,
    c2m6, iL, iT, cE1, iG, iO, cm, cTop, iB, sw, Machine.upd_same, ne_eq, Machine.upd_other,
    Nat.reduceAdd, Nat.reduceEqDiff, not_false_eq_true, and_true]

theorem regA_other (m f : ℕ → ℕ) {r : ℕ} (hr : r < sw 610 ∨ sw 705 ≤ r) :
    regB m regA f r = f r := by
  apply regB_other
  intro i hi
  simp only [regA, List.mem_cons, List.not_mem_nil, or_false] at hi
  simp only [sw] at hr
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp only [dstI, K0, K1, K2, K3, K4, K5, K6, cGW, cN1, cNW, cLL, cLD, cLE, c2m, c2m6, iL, iT,
    cE1, iG, iO, cm, cTop, iB, sw] <;> omega

/-! ## The tests -/

/-- `cGL := (gW + Lst) mod n` (one conditional subtraction). -/
def glS : Stmt := .ifLtN iG (sw 35) (.instr (.copyN cGL iG)) (.instr (.subN cGL iG (sw 35)))

/-- `iO := lOff = (sw 45 + n - gW) mod n`. -/
def offS : Stmt := .ifLtN iO (sw 35) .skip (.instr (.subN iO iO (sw 35)))

/-- `cB1 := b₁`. -/
def b1S : Stmt := .ifLtN iL iO (.instr (.subN cB1 (sw 33) (sw 91))) (.instr (.copyN cB1 (sw 46)))

/-- `cS := sideS` of `C₂` from the orientation bit. -/
def sideSS : Stmt :=
  .ifLtN iB K1 (.instr (.subN cS c2m cTop))
    (.ifLtN K1 iB (.instr (.subN cS c2m cTop)) (.instr (.copyN cS cTop)))

/-- The tests. -/
def stmtB : Stmt := .seq glS (.seq offS (.seq b1S sideSS))

/-- **The first part of the initialisation.** -/
def initRA : Stmt := .seq (block regA) stmtB

/-- A conditional register update (two branches). -/
theorem exec_ite_upd {P : Polygon} {W : ℕ} {c : Config} {a b r : ℕ}
    {i j : Instr} {u v : ℕ}
    (hi : Exec P W (.instr i) c { c with nreg := upd c.nreg r u } 1)
    (hj : Exec P W (.instr j) c { c with nreg := upd c.nreg r v } 1) :
    Exec P W (.ifLtN a b (.instr i) (.instr j)) c
      { c with nreg := upd c.nreg r (if c.nreg a < c.nreg b then u else v) }
      (if c.nreg a < c.nreg b then 2 else 3) := by
  by_cases h : c.nreg a < c.nreg b
  · simp only [h, ↓reduceIte]; exact .ifLtN_true h hi
  · simp only [h, ↓reduceIte]; exact .ifLtN_false h hj

section
variable {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c)
include hw
theorem glS_exec :
    ∃ k, Exec P W glS c { c with nreg := upd c.nreg cGL (if c.nreg iG < c.nreg (sw 35) then c.nreg iG else c.nreg iG - c.nreg (sw 35)) } k ∧
      k ≤ 3 := by
  refine ⟨_, exec_ite_upd (Exec.copyN hw _ _) (Exec.subN hw _ _ _), by grind⟩

theorem offS_exec :
    ∃ k, Exec P W offS c { c with nreg := upd c.nreg iO (if c.nreg iO < c.nreg (sw 35) then c.nreg iO else c.nreg iO - c.nreg (sw 35)) } k ∧
      k ≤ 3 := by
  by_cases h : c.nreg iO < c.nreg (sw 35)
  · refine ⟨1, ?_, by omega⟩
    rw [ite_eq_left h, upd_eq_self]
    exact .ifLtN_true h (.skip hw)
  · refine ⟨3, ?_, le_rfl⟩
    rw [ite_eq_right h]
    exact .ifLtN_false h (Exec.subN hw _ _ _)

theorem b1S_exec :
    ∃ k, Exec P W b1S c { c with nreg := upd c.nreg cB1 (if c.nreg iL < c.nreg iO then c.nreg (sw 33) - c.nreg (sw 91) else c.nreg (sw 46)) } k ∧
      k ≤ 3 :=
  ⟨_, exec_ite_upd (Exec.subN hw _ _ _) (Exec.copyN hw _ _), by grind⟩

theorem sideSS_exec :
    ∃ k, Exec P W sideSS c { c with nreg := upd c.nreg cS (if c.nreg iB = c.nreg K1 then c.nreg cTop else c.nreg c2m - c.nreg cTop) } k ∧ k ≤ 5 := by
  unfold sideSS
  by_cases h1 : c.nreg iB < c.nreg K1
  · refine ⟨2, ?_, by omega⟩
    rw [ite_eq_right (by omega)]
    exact .ifLtN_true h1 (Exec.subN hw _ _ _)
  · by_cases h2 : c.nreg K1 < c.nreg iB
    · refine ⟨4, ?_, by omega⟩
      rw [ite_eq_right (by omega)]
      exact .ifLtN_false h1 (.ifLtN_true h2 (Exec.subN hw _ _ _))
    · refine ⟨5, ?_, le_rfl⟩
      rw [ite_eq_left (by omega)]
      exact .ifLtN_false h1 (.ifLtN_false h2 (Exec.copyN hw _ _))

/-! ## The first part, at the register level -/


end

/-- The register values after `initRA`. -/
def fIA (m f : ℕ → ℕ) : ℕ → ℕ :=
  let R := regB m regA f
  let R₁ := upd R cGL (if R iG < R (sw 35) then R iG else R iG - R (sw 35))
  let R₂ := upd R₁ iO (if R₁ iO < R₁ (sw 35) then R₁ iO else R₁ iO - R₁ (sw 35))
  let R₃ := upd R₂ cB1 (if R₂ iL < R₂ iO then R₂ (sw 33) - R₂ (sw 91) else R₂ (sw 46))
  upd R₃ cS (if R₃ iB = R₃ K1 then R₃ cTop else R₃ c2m - R₃ cTop)

theorem initRA_exec_regs {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c)
    (hok : okW W c.nmem regA c.nreg) :
    ∃ k, Exec P W initRA c { c with nreg := fIA c.nmem c.nreg } k ∧ k ≤ 41 := by
  have e₀ := exec_regB (P := P) regA hw hok
  set c₁ : Config := { c with nreg := regB c.nmem regA c.nreg } with hc₁
  obtain ⟨k₁, e₁, hk₁⟩ := glS_exec (P := P) e₀.wb_right
  obtain ⟨k₂, e₂, hk₂⟩ := offS_exec (P := P) e₁.wb_right
  obtain ⟨k₃, e₃, hk₃⟩ := b1S_exec (P := P) e₂.wb_right
  obtain ⟨k₄, e₄, hk₄⟩ := sideSS_exec (P := P) e₃.wb_right
  exact ⟨_, .seq e₀ (.seq e₁ (.seq e₂ (.seq e₃ e₄))), by simp only [regA] at *; simp; omega⟩

set_option maxRecDepth 20000 in
/-- The values of `fIA`. -/
theorem fIA_val (m f : ℕ → ℕ) :
    fIA m f K0 = 0 ∧ fIA m f K1 = 1 ∧ fIA m f K6 = 6 ∧ fIA m f K4 = 4 ∧ fIA m f K5 = 5 ∧
    fIA m f K2 = 2 ∧ fIA m f K3 = 3 ∧ fIA m f cGW = f (sw 40) ∧ fIA m f cN1 = f (sw 33) ∧
    fIA m f cNW = f (sw 35) ∧ fIA m f cLL = f (sw 47) ∧ fIA m f cLD = f (sw 49) ∧
    fIA m f cLE = f (sw 47) + f (sw 49) ∧ fIA m f c2m = f (sw 34) - f (sw 92) ∧
    fIA m f c2m6 = f (sw 34) - f (sw 91) ∧
    fIA m f cE1 = f (sw 35) - (f (sw 42) + f (sw 43)) + f (sw 49) ∧
    fIA m f cGL = (if f (sw 40) + (f (sw 42) + f (sw 43)) < f (sw 35)
      then f (sw 40) + (f (sw 42) + f (sw 43))
      else f (sw 40) + (f (sw 42) + f (sw 43)) - f (sw 35)) ∧
    fIA m f cB1 = (if f (sw 42) + f (sw 43) <
        (if f (sw 45) + f (sw 35) - f (sw 40) < f (sw 35) then f (sw 45) + f (sw 35) - f (sw 40)
          else f (sw 45) + f (sw 35) - f (sw 40) - f (sw 35))
      then f (sw 33) - f (sw 91) else f (sw 46)) ∧
    fIA m f cm = m (f (sw 21) + 2) ∧ fIA m f cTop = m (f (sw 21) + 3) ∧
    fIA m f cS = (if m (f (sw 21) + 4) = 1 then m (f (sw 21) + 3)
      else (f (sw 34) - f (sw 92)) - m (f (sw 21) + 3)) := by
  have hv := regA_val m f
  have o : ∀ q, q < sw 610 ∨ sw 705 ≤ q → regB m regA f q = f q := fun q hq => regA_other m f hq
  have o35 := o (sw 35) (by omega_nf)
  have o33 := o (sw 33) (by omega_nf)
  have o91 := o (sw 91) (by omega_nf)
  have o46 := o (sw 46) (by omega_nf)
  obtain ⟨v0, v1, v6, v4, v5, v2, v3, vgw, vn1, vnw, vll, vld, vle, v2m, v2m6, vL, vE, vG, vO', vm,
    vt, vB⟩ := hv
  simp only [fIA]
  simp only [K0, K1, K2, K3, K4, K5, K6, cGW, cN1, cNW, cLL, cLD, cLE, c2m, c2m6, iL, cE1, iG,
    iO, cm, cTop, iB, cGL, cB1, cS, sw, Nat.reduceAdd] at *
  simp only [Machine.upd_same, ne_eq, Machine.upd_other, Nat.reduceEqDiff, not_false_eq_true,
    o35, o33, o91, o46, v0, v1, v6, v4, v5, v2, v3, vgw, vn1, vnw, vll, vld, vle, v2m, v2m6, vL, vE,
    vG, vO', vm, vt, vB, true_and]
  grind

/-! ## The first part, for the junction -/

/-- One conditional subtraction is the remainder below `2 n`. -/
theorem ite_sub_mod {x n : ℕ} (h : x < 2 * n) : (if x < n then x else x - n) = x % n := by
  split_ifs with h'
  · exact (Nat.mod_eq_of_lt h').symm
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

section
variable (J : Merge.Junction)
theorem rlen_le : Lst J ≤ 2 * J.m₂ + 7 := by
  grind [Lst_rlen, rlen]

theorem lL1_le : lL1 J ≤ 2 * J.m₁ + 7 := by
  grind [lL1]

theorem lδ_le : lδ J ≤ 7 := by
  grind [lδ]


end

set_option maxRecDepth 20000 in
/-- **The first part of the initialisation**: the constants, `MapK`, `cGW` and the constants of
the classification except the top of `C₁`, from the stage-0 state.  Only `sw 610 … 704` change. -/
theorem initRA_exec {P : Polygon} {W : ℕ} {c : Config} {H : Host} {J : Merge.Junction}
    (hw : WordsBounded W c) (h0 : St0S P c H J) (hWn : 2 * (chainModel J.whole).W.n ≤ W) :
    ∃ c' k, Exec P W initRA c c' k ∧ k ≤ 41 ∧ c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧
      c'.rmem = c.rmem ∧ c'.output = c.output ∧
      (∀ r, (r < sw 610 ∨ sw 705 ≤ r) → c'.nreg r = c.nreg r) ∧
      Consts c' ∧ MapK J c' ∧ c'.nreg cGW = gW J ∧ c'.nreg c2m = 2 * J.right.m ∧
      c'.nreg cm = J.right.m ∧ c'.nreg cTop = J.right.topIdx ∧
      c'.nreg cS = J.right.sideS J.right.sideBeta ∧ c'.nreg c2m6 = 2 * J.right.m + 6 := by
  obtain ⟨h90, h91, h92, h93, -, -, -, -, d21, w21, -, -, hR, hL, h33, h34, h35, -⟩ := h0
  have r0 : c.nreg (sw 40) = 6 + tpos J.whole J.m₁ := by grind [cstR]
  have r2 : c.nreg (sw 42) = rL1 J := by grind [cstR]
  have r3 : c.nreg (sw 43) = rL2 J := by grind [cstR]
  have l0 : c.nreg (sw 45) = 6 + tpos J.whole (J.m₁ + 2 * J.m₂) := by
    grind [cstL]
  have l1 : c.nreg (sw 46) = 6 + tpos J.left J.m₁ := by grind [cstL]
  have l2 : c.nreg (sw 47) = lL1 J := by grind [cstL]
  have l4 : c.nreg (sw 49) = lδ J := by simpa [cstL] using hL 4 (by norm_num)
  have hn : (chainModel J.whole).W.n = 2 * J.whole.m + 7 := cm_n _
  have hn₁ : (chainModel J.left).W.n = 2 * J.left.m + 7 := cm_n _
  have hm : J.whole.m = J.m₁ + J.m₂ := rfl
  
  have hm₂ : J.right.m = J.m₂ := rfl
  have t0 := tpos_lt J.whole J.m₁
  have t1 := tpos_lt J.whole (J.m₁ + 2 * J.m₂)
  have hLst : Lst J = rL1 J + rL2 J := rfl
  have hLs := rlen_le J
  have hll := lL1_le J
  have hld := lδ_le J
  have one₁ := J.one_le_m₁
  have hd21 : c.nreg (sw 21) + 5 ≤ c.nreg ALLOC := w21.1
  have hAW := hw.1 ALLOC
  have hok : okW W c.nmem regA c.nreg := regA_ok _ _ (by omega)
    (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)
  obtain ⟨k, ex, hk⟩ := initRA_exec_regs (P := P) hw hok
  obtain ⟨v0, v1, v6, v4, v5, v2, v3, vgw, vn1, vnw, vll, vld, vle, v2m, v2m6, vE, vG, vB1, vm,
    vt, vS⟩ := fIA_val c.nmem c.nreg
  have hHm : c.nmem (c.nreg (sw 21) + 2) = J.right.m := d21.2.2.2.1
  have hHt : c.nmem (c.nreg (sw 21) + 3) = J.right.topIdx := d21.2.2.2.2.1
  have hHb : c.nmem (c.nreg (sw 21) + 4) = 1 ↔ J.right.sideBeta = true := d21.2.2.2.2.2
  refine ⟨_, k, ex, hk, rfl, rfl, rfl, rfl, fun r hr => ?_, ⟨v0, v1, v6, v4, v5, v2, v3⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [fIA]
    simp only [cGL, iO, cB1, cS, sw] at hr ⊢
    rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega), upd_other _ _ _ (by omega),
      upd_other _ _ _ (by omega)]
    exact regA_other _ _ (by omega_nf)
  · -- b₁
    show fIA c.nmem c.nreg cB1 = b₁ J
    rw [vB1, r2, r3, l0, h35, r0, h33, h91, l1, ← hLst]
    unfold b₁
    have hO : (if 6 + tpos J.whole (J.m₁ + 2 * J.m₂) + (2 * J.whole.m + 7) -
          (6 + tpos J.whole J.m₁) < 2 * J.whole.m + 7
        then 6 + tpos J.whole (J.m₁ + 2 * J.m₂) + (2 * J.whole.m + 7) - (6 + tpos J.whole J.m₁)
        else 6 + tpos J.whole (J.m₁ + 2 * J.m₂) + (2 * J.whole.m + 7) - (6 + tpos J.whole J.m₁) -
          (2 * J.whole.m + 7)) = lOff J := by
      rw [ite_sub_mod (by omega)]
      unfold lOff dOf
      rw [hn]
    grind
  · ram_simp
  · grind [E₁]
  · ram_simp
  · ram_simp
  · show fIA c.nmem c.nreg cGL = _
    rw [vG, r0, r2, r3, h35, ite_sub_mod (by omega), hn, hLst]
    rfl
  · ram_simp
  · ram_simp
  · show fIA c.nmem c.nreg cGW = _
    rw [vgw, r0]; rfl
  · grind
  · ram_simp
  · ram_simp
  · grind [Chain.sideS]
  grind

end

end SweepEv

end Chazelle.Core
