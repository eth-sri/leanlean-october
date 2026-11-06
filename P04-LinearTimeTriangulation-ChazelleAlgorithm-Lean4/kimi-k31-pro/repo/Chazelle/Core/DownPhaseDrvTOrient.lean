module

public import Chazelle.Final.RamOrient
public import Chazelle.Core.DownPhaseDrvTList
public import Chazelle.Core.NFBuildMain
public import Chazelle.Rwx
public import Chazelle.UnfoldTactics
public import Chazelle.ConfigTactics
set_option maxHeartbeats 2000000

/-!
# Down-phase transition (D2), RAM part 1: the `LeftInside` bit

`orientT` computes the orientation bit of the interior model of `Q = Qof P` into register
`190001` (band `bTrans = 19`): `1` iff `Mountain.LeftInside Q`.  It runs the final stage's
orientation program `Final.orientStmt` (the corner sign at a lexicographically lowest vertex,
`Final.orientStmt_exec`), whose registers lie in band `0`; they are saved in band `19` before
and restored after (`saveO`, `restO`), so that the net effect is confined to band `19`
(`orientT_exec`).
-/

namespace Chazelle.Core

namespace DrvT

open Machine Machine.Stmt Programs BuildRam

@[expose] public section

/-! ## The program -/

/-- Save the natural registers `230 … 236`. -/
def saveN : Stmt := block [.copyN 190230 230, .copyN 190231 231, .copyN 190232 232,
  .copyN 190233 233, .copyN 190234 234, .copyN 190235 235, .copyN 190236 236]

/-- Save the real registers `100`, `230 … 243`. -/
def saveR : Stmt := block [.copyR 190100 100, .copyR 190230 230, .copyR 190231 231,
  .copyR 190232 232, .copyR 190233 233, .copyR 190234 234, .copyR 190235 235,
  .copyR 190236 236, .copyR 190237 237, .copyR 190238 238, .copyR 190239 239,
  .copyR 190240 240, .copyR 190241 241, .copyR 190242 242, .copyR 190243 243]

/-- Restore the natural registers. -/
def restN : Stmt := block [.copyN 230 190230, .copyN 231 190231, .copyN 232 190232,
  .copyN 233 190233, .copyN 234 190234, .copyN 235 190235, .copyN 236 190236]

/-- Restore the real registers. -/
def restR : Stmt := block [.copyR 100 190100, .copyR 230 190230, .copyR 231 190231,
  .copyR 232 190232, .copyR 233 190233, .copyR 234 190234, .copyR 235 190235,
  .copyR 236 190236, .copyR 237 190237, .copyR 238 190238, .copyR 239 190239,
  .copyR 240 190240, .copyR 241 190241, .copyR 242 190242, .copyR 243 190243]

/-- The bit: `190001 := (0 < orient Q)`. -/
def bitO : Stmt := .seq (block [.constR 190300 0, .constN 190001 0])
  (.ifLtR 190300 100 (.instr (.constN 190001 1)) .skip)

/-- **The `LeftInside` bit** into register `190001`. -/
def orientT : Stmt :=
  .seq saveN (.seq saveR (.seq Final.orientStmt (.seq bitO (.seq restN restR))))

/-- The registers of band `19`. -/
def B19 (r : ℕ) : Bool := decide (190000 ≤ r ∧ r < 200000)

/-- The registers of the bit. -/
def Bbit (r : ℕ) : Bool := decide (r = 190001 ∨ r = 190300)

/-- The natural registers restored. -/
def BrN (r : ℕ) : Bool := decide (230 ≤ r ∧ r ≤ 236)

/-- The real registers restored. -/
def BrR (r : ℕ) : Bool := decide (r = 100 ∨ (230 ≤ r ∧ r ≤ 243))

theorem wrM_saveN : wrM B19 saveN = true := by decide
theorem wrM_saveR : wrM B19 saveR = true := by decide
theorem wrM_bitO : wrM Bbit bitO = true := by decide
theorem wrM_restN : wrM BrN restN = true := by decide
theorem wrM_restR : wrM BrR restR = true := by decide

section exec

variable {P : Polygon} {W : ℕ}

theorem saveN_exec (c : Config) (hw : WordsBounded W c) :
    ∃ c' k, Exec P W saveN c c' k ∧ k = 7 ∧
      (∀ i, 230 ≤ i → i ≤ 236 → c'.nreg (190000 + i) = c.nreg i) ∧
      FrameM B19 c c' ∧ c'.rreg = c.rreg ∧ c'.nmem = c.nmem := by
  obtain ⟨c', k, e, hk, h1, h2, hm⟩ : ∃ c' k, Exec P W saveN c c' k ∧ k = 7 ∧
      (∀ i, 230 ≤ i → i ≤ 236 → c'.nreg (190000 + i) = c.nreg i) ∧
      c'.rreg = c.rreg ∧ c'.nmem = c.nmem := by
    unfold saveN
    exec_block
    refine ⟨rfl, fun i h1 h2 => ?_, rfl, rfl⟩
    interval_cases i <;> config_simp
  exact ⟨c', k, e, hk, h1, exec_frameM e wrM_saveN, h2, hm⟩

theorem saveR_exec (c : Config) (hw : WordsBounded W c) :
    ∃ c' k, Exec P W saveR c c' k ∧ k = 15 ∧
      (∀ i, (i = 100 ∨ (230 ≤ i ∧ i ≤ 243)) → c'.rreg (190000 + i) = c.rreg i) ∧
      FrameM B19 c c' ∧ c'.nreg = c.nreg ∧ c'.nmem = c.nmem := by
  obtain ⟨c', k, e, hk, h1, h2, hm⟩ : ∃ c' k, Exec P W saveR c c' k ∧ k = 15 ∧
      (∀ i, (i = 100 ∨ (230 ≤ i ∧ i ≤ 243)) → c'.rreg (190000 + i) = c.rreg i) ∧
      c'.nreg = c.nreg ∧ c'.nmem = c.nmem := by
    unfold saveR
    exec_block
    refine ⟨rfl, fun i hi => ?_, rfl, rfl⟩
    rcases hi with rfl | ⟨h1, h2⟩
    · config_simp
    · interval_cases i <;> config_simp
  exact ⟨c', k, e, hk, h1, exec_frameM e wrM_saveR, h2, hm⟩

theorem restN_exec (c : Config) (hw : WordsBounded W c) :
    ∃ c' k, Exec P W restN c c' k ∧ k = 7 ∧
      (∀ i, 230 ≤ i → i ≤ 236 → c'.nreg i = c.nreg (190000 + i)) ∧
      FrameM BrN c c' ∧ c'.rreg = c.rreg ∧ c'.nmem = c.nmem := by
  obtain ⟨c', k, e, hk, h1, h2, hm⟩ : ∃ c' k, Exec P W restN c c' k ∧ k = 7 ∧
      (∀ i, 230 ≤ i → i ≤ 236 → c'.nreg i = c.nreg (190000 + i)) ∧
      c'.rreg = c.rreg ∧ c'.nmem = c.nmem := by
    unfold restN
    exec_block
    refine ⟨rfl, fun i h1 h2 => ?_, rfl, rfl⟩
    interval_cases i <;> config_simp
  exact ⟨c', k, e, hk, h1, exec_frameM e wrM_restN, h2, hm⟩

theorem restR_exec (c : Config) (hw : WordsBounded W c) :
    ∃ c' k, Exec P W restR c c' k ∧ k = 15 ∧
      (∀ i, (i = 100 ∨ (230 ≤ i ∧ i ≤ 243)) → c'.rreg i = c.rreg (190000 + i)) ∧
      FrameM BrR c c' ∧ c'.nreg = c.nreg ∧ c'.nmem = c.nmem := by
  obtain ⟨c', k, e, hk, h1, h2, hm⟩ : ∃ c' k, Exec P W restR c c' k ∧ k = 15 ∧
      (∀ i, (i = 100 ∨ (230 ≤ i ∧ i ≤ 243)) → c'.rreg i = c.rreg (190000 + i)) ∧
      c'.nreg = c.nreg ∧ c'.nmem = c.nmem := by
    unfold restR
    exec_block
    refine ⟨rfl, fun i hi => ?_, rfl, rfl⟩
    rcases hi with rfl | ⟨h1, h2⟩
    · config_simp
    · interval_cases i <;> config_simp
  exact ⟨c', k, e, hk, h1, exec_frameM e wrM_restR, h2, hm⟩

theorem bitO_exec (c : Config) (hw : WordsBounded W c) (hW : 1 ≤ W) :
    ∃ c' k, Exec P W bitO c c' k ∧ k ≤ 4 ∧ c'.nreg 190001 ≤ 1 ∧
      (c'.nreg 190001 = 1 ↔ 0 < c.rreg 100) ∧ c'.rreg 100 = c.rreg 100 ∧
      FrameM Bbit c c' ∧ c'.nmem = c.nmem := by
  obtain ⟨c', k, e, hk, h1, h2, h3, hm⟩ : ∃ c' k, Exec P W bitO c c' k ∧ k ≤ 4 ∧
      c'.nreg 190001 ≤ 1 ∧ (c'.nreg 190001 = 1 ↔ 0 < c.rreg 100) ∧ c'.rreg 100 = c.rreg 100 ∧
      c'.nmem = c.nmem := by
    unfold bitO
    refine spec_seq ?_
    exec_block
    · omega
    by_cases h : (0 : ℝ) < c.rreg 100
    · refine spec_ifLtR_true (by config_simp; simpa using h) ?_
      refine spec_instr (Exec.constN ‹WordsBounded _ _› _ _ hW) fun _ => ?_
      refine ⟨by omega, by cso, by config_simp; simp [h], by config_simp,
        rfl⟩
    · refine spec_ifLtR_false (by config_simp; simpa using h) ?_
      refine spec_skip ‹WordsBounded _ _› ?_
      refine ⟨by omega, by cso, by config_simp; simp [h],
        by config_simp, rfl⟩
  exact ⟨c', k, e, hk, h1, h2, h3, exec_frameM e wrM_bitO, hm⟩

/-- **The `LeftInside` bit.** -/
theorem orientT_exec (hG : GoodEnv P) (hW : P.n + 3 ≤ W) (c : Config) (hw : WordsBounded W c) :
    ∃ c' k, Exec P W orientT c c' k ∧ k ≤ 14 * P.n + 120 ∧
      c'.nreg 190001 ≤ 1 ∧ (c'.nreg 190001 = 1 ↔ Mountain.LeftInside (Qof P)) ∧
      FrameM B19 c c' ∧ c'.nmem = c.nmem := by
  have hQ  := (shearInvariance (epsOf P) P).1 hG.1
  obtain ⟨c₀, k₀, e₀, hk₀, s1, F₀, rr₀, m₀⟩ := saveN_exec (P := P) c hw
  obtain ⟨c₁, k₁, e₁, hk₁, s2, F₁, nr₁, m₁⟩ := saveR_exec (P := P) c₀ e₀.wb_right
  obtain ⟨c₂, k₂, e₂, hk₂, ho, f2n, f2r, m₂, rm₂, o₂⟩ :=
    Final.orientStmt_exec (shearRel_Qof hG.2) hQ c₁ e₁.wb_right (by omega)
  obtain ⟨c₃, k₃, e₃, hk₃, b1, b2, b3, F₃, m₃⟩ := bitO_exec (P := P) c₂ e₂.wb_right (by omega)
  obtain ⟨c₄, k₄, e₄, hk₄, r1, F₄, rr₄, m₄⟩ := restN_exec (P := P) c₃ e₃.wb_right
  obtain ⟨c₅, k₅, e₅, hk₅, r2, F₅, nr₅, m₅⟩ := restR_exec (P := P) c₄ e₄.wb_right
  refine ⟨c₅, k₀ + (k₁ + (k₂ + (k₃ + (k₄ + k₅)))),
    .seq e₀ (.seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ e₅)))), by omega, ?_, ?_,
    ⟨fun r hr => ?_, fun r hr => ?_, ?_, ?_⟩, by rw [m₅, m₄, m₃, m₂, m₁, m₀]⟩
  · rwx [nr₅, F₄.1 _ (by decide)]
  · rw [nr₅, F₄.1 _ (by decide), b2, ho]
    unfold Mountain.orient
    split_ifs with h <;> simp [h]
  · -- natural registers outside band `19`
    unfold B19 at hr
    simp [decide_eq_false_iff_not, not_and, not_lt] at hr
    rw [nr₅]
    by_cases hres : 230 ≤ r ∧ r ≤ 236
    · rw [r1 r hres.1 hres.2, F₃.1 (190000 + r) (by ufs Bbit; omega),
        f2n (190000 + r) (by omega), nr₁, s1 r hres.1 hres.2]
    · rw [F₄.1 r (by ufs BrN; omega), F₃.1 r (by ufs Bbit; omega),
        f2n r (by omega), nr₁, F₀.1 r (by ufs B19; omega)]
  · -- real registers outside band `19`
    unfold B19 at hr
    simp [decide_eq_false_iff_not, not_and, not_lt] at hr
    by_cases hres : r = 100 ∨ (230 ≤ r ∧ r ≤ 243)
    · rw [r2 r hres, rr₄, F₃.2.1 (190000 + r) (by ufs Bbit; omega),
        f2r (190000 + r) (by omega) (by omega), s2 r hres, rr₀]
    · rw [F₅.2.1 r (by ufs BrR; omega), rr₄, F₃.2.1 r (by ufs Bbit; omega),
        f2r r (by omega) (by omega), F₁.2.1 r (by ufs B19; omega), rr₀]
  · rw [F₅.2.2.1, F₄.2.2.1, F₃.2.2.1, rm₂, F₁.2.2.1, F₀.2.2.1]
  · rw [F₅.2.2.2, F₄.2.2.2, F₃.2.2.2, o₂, F₁.2.2.2, F₀.2.2.2]

end exec

end

end DrvT

end Chazelle.Core
