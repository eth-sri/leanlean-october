module

public import Chazelle.Core.RestoreTIntLeft
public import Chazelle.Core.RestoreTChainLeft

/-!
# WP-E, the candidate test on the RAM, part 20: the sector test of both models

`gLeft`: `leftSec` for a chain model, `iLeft` for the interior model (`gLeft_ok`:
`LeftOK gLeft 20000`).
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Machine Machine.Stmt Programs SweepPrim NFLoc SignK

variable {P : Polygon} {W : ℕ} {M : Model} {N : NF} {c₀ c : Config}

theorem wr_fixBit : wr (fun q => q == 50210) fixBit = true := by_d

/-- The edge case of the interior sector test. -/
theorem iLeft_ok_edge (hE : TGood P W M N c₀) (hI : TInv W c₀ c) (hv : c₀.nreg 83006 ≠ 0)
    (hroom : c.nreg ALLOC + 5300 ≤ W) :
    ∃ c' k, Exec P W (.seq tTurnN fixBit) c c' k ∧ k ≤ 5300 ∧
      BitIs c' 50210 (LeftB M P (xOf c₀) (c₀.nreg 83008)) ∧ TStep W c₀ c c' k := by
  obtain ⟨c₁, k₁, e₁, hk₁, t₁, s₁⟩ := turn_ok.1 P W M N c₀ c hE hI by_o
  have hI₁ := s₁.1
  have h23 := hI₁.h23
  have hw₁ := hI₁.hw
  have hW1 : 1 ≤ W := by have := hw₁.1 83023; omega
  have hpos : 0 < M.param (Qof P) (xOf c₀) := by
    rcases hE.hxc with h | h
    · exact absurd h hv
    · exact h
  have hleft := left_inside_iff (σb := c₀.nreg 83008) hpos hE.hxp.2.1
  unfold fixBit
  by_cases h2 : c₁.nreg 83023 < c₁.nreg 50210
  · have e₂ := Exec.constN (P := P) hw₁ 50210 0 by_o
    have ex := Exec.seq e₁ (Exec.ifLtN_true (e := .skip) h2 e₂)
    have f₂ :=
      exec_frameB (Exec.ifLtN_true (e := .skip) h2 e₂) wr_fixBit
    refine ⟨_, _, ex, by_o, ⟨by simp [upd], ?_⟩, s₁.trans (hI₁.stepB e₂.wb_right f₂
      (fun r hr => Restore.primReg (by simp only [beq_iff_eq] at hr; omega)) _)⟩
    simp only [upd_eq, zero_ne_one, false_iff]
    rw [hleft]; intro h; have := t₁.2 h; omega
  · have ex := Exec.seq e₁ (Exec.ifLtN_false (t := .instr (.constN 50210 0)) h2 (.skip hw₁))
    refine ⟨_, _, ex, by_o, ⟨by_o, ?_⟩, s₁.mono by_o⟩
    rwa [hleft]

/-- **The sector test of both models.** -/
def gLeft : Stmt := .ifLtN 83021 83023 tLeft iLeft

theorem gLeft_ok : LeftOK gLeft 20000 := by
  intro P W M N c₀ c hE hI hroom
  have h21 := hI.h21
  have h23 := hI.h23
  rcases hE.kind with ⟨h0, C, hM⟩ | ⟨h1, hMi, hbit⟩
  · obtain ⟨c', k, ex, hk, b, s⟩ := tLeft_exec hE hI hM by_o
    exact ⟨c', k + 1, .ifLtN_true (by rw [h21, h23, h0]; omega) ex, by_o, b,
      s.mono by_o⟩
  · have i6 := hI.hin 83006 by_n by_n
    by_cases hv : c.nreg 83006 < c.nreg 83023
    · obtain ⟨c', k, ex, hk, b, s⟩ := iLeft_ok_vertex hE hI hMi hbit by_o by_o
      exact ⟨c', k + 1 + 2, .ifLtN_false (by rw [h21, h23, h1]; omega) (.ifLtN_true hv ex),
        by_o, b, s.mono by_o⟩
    · obtain ⟨c', k, ex, hk, b, s⟩ := iLeft_ok_edge hE hI by_o by_o
      exact ⟨c', k + 2 + 2, .ifLtN_false (by rw [h21, h23, h1]; omega) (.ifLtN_false hv ex),
        by_o, b, s.mono by_o⟩

end

end Restore

end Chazelle.Core
