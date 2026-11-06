module

public import Chazelle.Golf

public import Chazelle.Core.DownPhaseDrvRLib

/-!
# Down-phase driver (RAM side): padding

`padS src` runs exactly `3 (r9999 - r_src) + 4` steps and changes only the scratch registers
`210068`, `210069`.  Appended to a part of the driver that allocates from the address saved in
`src`, it makes the step count at least the allocated size (the last conjunct of `Frame`).
-/

namespace Chazelle.Core

namespace DrvR

open Machine Machine.Stmt

@[expose] public section

/-- The padding loop: count `r210068` up to the allocation pointer. -/
def padLoop : Stmt := .whileLtN 210068 9999 (.instr (.addN 210068 210068 210069))

/-- **Padding** from the allocation pointer saved in register `src`. -/
def padS (src : ℕ) : Stmt :=
  .seq (.instr (.copyN 210068 src)) (.seq (.instr (.constN 210069 1)) padLoop)

section exec

variable {P : Polygon} {W : ℕ}

theorem padLoop_exec : ∀ (d : ℕ) (c : Config), WordsBounded W c → c.nreg 210069 = 1 →
    c.nreg 210068 ≤ c.nreg 9999 → c.nreg 9999 - c.nreg 210068 = d →
    Exec P W padLoop c { c with nreg := upd c.nreg 210068 (c.nreg 9999) } (3 * d + 2)
  | 0, c, hw, _, hle, hd => by
    have h : c.nreg 210068 = c.nreg 9999 := ⋄
    refine Exec.cast (k := 2) ((Exec.whileLtN_false (⋄) hw).cast_end ?_) (by omega)
    Ξ ← h, upd_eq_self
  | d + 1, c, hw, h69, hle, hd => by
    have e := Exec.addN (P := P) hw 210068 210068 210069 (by rw [h69]; have := hw.1 9999; omega)
    have h1 : (upd c.nreg 210068 (c.nreg 210068 + c.nreg 210069)) 210069 = 1 := by
      rw [upd_other _ _ _ (⌖), h69]
    have h2 : (upd c.nreg 210068 (c.nreg 210068 + c.nreg 210069)) 9999 = c.nreg 9999 :=
      upd_other _ _ _ (⌖)
    have h3 : (upd c.nreg 210068 (c.nreg 210068 + c.nreg 210069)) 210068 = c.nreg 210068 + 1 := by
      Ξ upd_same, h69
    have e' := padLoop_exec d _ e.wb_right h1 (by dsimp only; rw [h2, h3]; omega)
      (by dsimp only; rw [h2, h3]; omega)
    refine ((Exec.whileLtN_true (⋄) e e').cast (by ring)).cast_end ?_
    ϴ h2, upd_upd_same

/-- **The padding**: exactly `3 (r9999 - r_src) + 4` steps, only `210068`, `210069` written. -/
theorem padS_exec {src : ℕ} {c : Config} (hw : WordsBounded W c) (hs : c.nreg src ≤ c.nreg 9999)
    (hW : 1 ≤ W) :
    ∃ c', Exec P W (padS src) c c' (3 * (c.nreg 9999 - c.nreg src) + 4) ∧
      (∀ r, r ≠ 210068 → r ≠ 210069 → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧
      c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output ∧ WordsBounded W c' := by
  have e₁ := Exec.copyN (P := P) hw 210068 src
  have e₂ := Exec.constN (P := P) e₁.wb_right 210069 1 hW
  have a68 : (upd (upd c.nreg 210068 (c.nreg src)) 210069 1) 210068 = c.nreg src := by
    rw [upd_other _ _ _ (⌖), upd_same]
  have a69 : (upd (upd c.nreg 210068 (c.nreg src)) 210069 1) 210069 = 1 := upd_same _ _ _
  have aA : (upd (upd c.nreg 210068 (c.nreg src)) 210069 1) 9999 = c.nreg 9999 := by
    rw [upd_other _ _ _ (⌖), upd_other _ _ _ (by decide)]
  have e₃ := padLoop_exec (P := P) _ _ e₂.wb_right a69 (by dsimp only; rw [a68, aA]; exact hs) rfl
  refine ⟨_, (Exec.seq e₁ (Exec.seq e₂ e₃)).cast (by dsimp only; rw [a68, aA]; ring),
    fun r h1 h2 => ?_, rfl, rfl, rfl, rfl, e₃.wb_right⟩
  ϴ upd_other _ _ _ h1, upd_other _ _ _ h2

end exec

end

end DrvR

end Chazelle.Core
