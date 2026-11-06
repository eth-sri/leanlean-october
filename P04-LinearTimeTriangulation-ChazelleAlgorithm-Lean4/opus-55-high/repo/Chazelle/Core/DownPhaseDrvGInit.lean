module

public import Chazelle.Core.DownPhaseDrvGLoop

/-!
# Down-phase driver, region procedure (D5), part 9: the setup

`rgInit0_exec` (the planner's arguments), `rgPadLoop_exec` (the padding after the leaf table, exact
cost), `rgInit1_exec` (constants, host data of the merge steps, loop state, three spare words of
the allocator).
-/

namespace Chazelle.Core

namespace DrvG

open Machine Machine.Stmt Programs BuildRam DrvR

@[expose] public section

section exec

variable {P : Polygon} {W : ℕ}

theorem rgInit0_exec (c : Config) (hw : WordsBounded W c) :
    ∃ c' k, Exec P W rgInit0 c c' k ∧ k = 2 ∧ c'.nreg 219000 = c.nreg 219200 ∧
      c'.nreg 219002 = c.nreg 219203 ∧ c'.nmem = c.nmem ∧
      FrameM (fun q => decide (q = 219000 ∨ q = 219002)) c c' ∧ c'.rreg = c.rreg := by
  obtain ⟨c', k, ex, hk, h1, h2, hm⟩ : ∃ c' k, Exec P W rgInit0 c c' k ∧ k = 2 ∧
      c'.nreg 219000 = c.nreg 219200 ∧ c'.nreg 219002 = c.nreg 219203 ∧ c'.nmem = c.nmem := by
    unfold rgInit0
    exec_block
    refine ⟨rfl, ?_, ?_, rfl⟩ <;> config_simp
  exact ⟨c', k, ex, hk, h1, h2, hm, exec_frameM ex (by decide),
    funext fun r => exec_frameM2 ex (BN := fun q => decide (q = 219000 ∨ q = 219002))
      (BR := fun _ => false) (by decide) r rfl⟩

/-- **The padding loop** runs exactly `3 (r9999 - r219250) + 2` steps. -/
theorem rgPadLoop_exec : ∀ (m : ℕ) (c : Config), WordsBounded W c → c.nreg 219251 = 1 →
    c.nreg 219250 ≤ c.nreg 9999 → c.nreg 9999 - c.nreg 219250 = m →
    Exec P W (.whileLtN 219250 9999 (block [.addN 219250 219250 219251])) c
      { c with nreg := upd c.nreg 219250 (c.nreg 9999) } (3 * m + 2)
  | 0, c, hw, _, hle, hd => by
    have h : c.nreg 219250 = c.nreg 9999 := by omega
    refine ((Exec.whileLtN_false (by omega) hw).cast_end ?_)
    rw [← h, upd_eq_self]
  | m + 1, c, hw, h51, hle, hd => by
    have e := Exec.addN (P := P) hw 219250 219250 219251 (by rw [h51]; have := hw.1 9999; omega)
    have h1 : (upd c.nreg 219250 (c.nreg 219250 + c.nreg 219251)) 219251 = 1 := by
      rw [upd_other _ _ _ (by decide), h51]
    have h2 : (upd c.nreg 219250 (c.nreg 219250 + c.nreg 219251)) 9999 = c.nreg 9999 :=
      upd_other _ _ _ (by decide)
    have h3 : (upd c.nreg 219250 (c.nreg 219250 + c.nreg 219251)) 219250 = c.nreg 219250 + 1 := by
      rw [upd_same, h51]
    have e' := rgPadLoop_exec m _ e.wb_right h1 (by dsimp only; rw [h2, h3]; omega)
      (by dsimp only; rw [h2, h3]; omega)
    refine ((Exec.whileLtN_true (by omega) (Exec.seq e (.skip e.wb_right)) e').cast
      (by ring)).cast_end ?_
    simp only [h2, upd_upd_same]

/-- **The padding**: exactly `3 (r9999 - r219003) + 4` steps. -/
theorem rgPad_exec (c : Config) (hw : WordsBounded W c) (hs : c.nreg 219003 ≤ c.nreg 9999)
    (hW : 1 ≤ W) :
    ∃ c', Exec P W rgPad c c' (3 * (c.nreg 9999 - c.nreg 219003) + 4) ∧
      (∀ r, r ≠ 219250 → r ≠ 219251 → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧
      c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have e₁ := Exec.copyN (P := P) hw 219250 219003
  have e₂ := Exec.constN (P := P) e₁.wb_right 219251 1 hW
  have a50 : (upd (upd c.nreg 219250 (c.nreg 219003)) 219251 1) 219250 = c.nreg 219003 := by
    rw [upd_other _ _ _ (by decide), upd_same]
  have a51 : (upd (upd c.nreg 219250 (c.nreg 219003)) 219251 1) 219251 = 1 := upd_same _ _ _
  have aA : (upd (upd c.nreg 219250 (c.nreg 219003)) 219251 1) 9999 = c.nreg 9999 := by
    rw [upd_other _ _ _ (by decide), upd_other _ _ _ (by decide)]
  have e₃ := rgPadLoop_exec (P := P) _ _ e₂.wb_right a51 (by dsimp only; rw [a50, aA]; exact hs)
    rfl
  refine ⟨_, (Exec.seq (Exec.seq e₁ (Exec.seq e₂ (.skip e₂.wb_right))) e₃).cast
    (by dsimp only; rw [a50, aA]; ring), fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
  simp only [upd_other _ _ _ h1, upd_other _ _ _ h2]

/-- The registers `rgInit1` writes. -/
def Bi1 (q : ℕ) : Bool :=
  decide (219140 ≤ q ∧ q ≤ 219146) || decide (219100 ≤ q ∧ q ≤ 219107) ||
    decide (219220 ≤ q ∧ q ≤ 219231) || decide (q = 9999)

set_option maxHeartbeats 1000000 in
theorem rgInit1_exec (c : Config) (hw : WordsBounded W c) {HB NP T Hl : ℕ}
    (h00 : c.nreg 219200 = HB) (h01 : c.nreg 219201 = NP) (h03 : c.nreg 219003 = T)
    (hHl : c.nmem HB = Hl) (hW : c.nreg 9999 + 130 ≤ W) :
    ∃ c' k, Exec P W rgInit1 c c' k ∧ k = 20 ∧ MgConst c' ∧ c'.nreg 219100 = HB ∧
      c'.nreg 219101 = NP ∧ c'.nreg 219103 = 130 ∧ c'.nreg 219104 = c.nreg 219205 ∧
      c'.nreg 219107 = Hl ∧ c'.nreg 219230 = 1 ∧ c'.nreg 219231 = 3 ∧ c'.nreg 219220 = 0 ∧
      c'.nreg 219221 = 0 ∧ c'.nreg 219222 = 0 ∧ c'.nreg 219223 = NP - 1 ∧ c'.nreg 219224 = T ∧
      c'.nreg 9999 = c.nreg 9999 + 3 ∧ c'.nmem = c.nmem ∧ FrameM Bi1 c c' ∧ c'.rreg = c.rreg := by
  obtain ⟨c', k, ex, hk, h40, h41, h42, h43, h44, h45, h46, a00, a01, a03, a04, a07, a30, a31,
      a20, a21, a22, a23, a24, aA, hm⟩ : ∃ c' k, Exec P W rgInit1 c c' k ∧ k = 20 ∧
      c'.nreg 219140 = 0 ∧ c'.nreg 219141 = 1 ∧ c'.nreg 219142 = 2 ∧ c'.nreg 219143 = 3 ∧
      c'.nreg 219144 = 4 ∧ c'.nreg 219145 = 5 ∧ c'.nreg 219146 = 6 ∧ c'.nreg 219100 = HB ∧
      c'.nreg 219101 = NP ∧ c'.nreg 219103 = 130 ∧ c'.nreg 219104 = c.nreg 219205 ∧
      c'.nreg 219107 = Hl ∧ c'.nreg 219230 = 1 ∧ c'.nreg 219231 = 3 ∧ c'.nreg 219220 = 0 ∧
      c'.nreg 219221 = 0 ∧ c'.nreg 219222 = 0 ∧ c'.nreg 219223 = NP - 1 ∧ c'.nreg 219224 = T ∧
      c'.nreg 9999 = c.nreg 9999 + 3 ∧ c'.nmem = c.nmem := by
    unfold rgInit1
    exec_block
    all_goals try (config_simp; (try simp only [h00, h01, h03, hHl]); omega)
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      rfl⟩ <;> config_simp <;> (try simp only [h00, h01, h03, hHl])
  exact ⟨c', k, ex, hk, ⟨h40, h41, h42, h43, h44, h45, h46⟩, a00, a01, a03, a04, a07, a30, a31,
    a20, a21, a22, a23, a24, aA, hm, exec_frameM ex (by decide),
    funext fun r => exec_frameM2 ex (BN := Bi1) (BR := fun _ => false) (by decide) r rfl⟩

end exec

end

end DrvG

end Chazelle.Core
