module

public import Chazelle.Programs.RamSimp

public import Chazelle.Core.RestoreTOps

/-!
# WP-E, the candidate test on the RAM, part 9: composing run steps

`RS P W c₀ s c K Q`: from `c`, the statement `s` runs in at most `K` steps to a configuration
satisfying the run invariant and `Q`, within the relative frame of the run.  The combinators
(`RS.seq`, `RS.ifT`, `RS.ifF`, `RS.while`, …) compose such facts; `RS.reg` covers one register
instruction on a scratch register of band `bRestore` (`Scr`), `RS.op` a step of a model
operation (`TStep`).
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Machine Machine.Stmt Programs SweepPrim

/-- **A run step**: `s` runs from `c` in at most `K` steps to a configuration of the run
satisfying `Q`. -/
abbrev RS (P : Polygon) (W : ℕ) (c₀ : Config) (s : Stmt) (c : Config) (K : ℕ)
    (Q : Config → Prop) : Prop :=
  RunSpec (TInv W c₀) (RF dBands (c₀.nreg ALLOC)) P W s c K Q

theorem bit01 {c : Config} {r : ℕ} {p : Prop} (h : BitIs c r p) :
    (c.nreg r = 0 ∧ ¬ p) ∨ (c.nreg r = 1 ∧ p) := by
  obtain ⟨h1, h2⟩ := h
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 h1 with h | h
  · simp_all <;> omega
  · tauto

theorem upd_eq {f : ℕ → ℕ} {r v : ℕ} : upd f r v r = v := by simp [upd]

theorem upd_ne {f : ℕ → ℕ} {r v q : ℕ} (h : q ≠ r) : upd f r v q = f q := by simp [upd, h]

variable {P : Polygon} {W : ℕ} {c₀ c : Config}

theorem RS.mono {s : Stmt} {K K' : ℕ} {Q Q' : Config → Prop} (h : RS P W c₀ s c K Q)
    (hK : K ≤ K') (hQ : ∀ c', Q c' → Q' c') : RS P W c₀ s c K' Q' :=
  RunSpec.mono h hK hQ

theorem RS.seq {s t : Stmt} {K₁ K₂ : ℕ} {Q₁ Q₂ : Config → Prop} (h₁ : RS P W c₀ s c K₁ Q₁)
    (h₂ : ∀ c₁, TInv W c₀ c₁ → c₁.nreg ALLOC ≤ c.nreg ALLOC + K₁ → Q₁ c₁ →
      RS P W c₀ t c₁ K₂ Q₂) : RS P W c₀ (.seq s t) c (K₁ + K₂) Q₂ :=
  RunSpec.seq h₁ (fun d hi _ ha hq => h₂ d hi ha hq)

theorem RS.ifT {a b : ℕ} {t e : Stmt} {K : ℕ} {Q : Config → Prop}
    (ht : c.nreg a < c.nreg b) (h : RS P W c₀ t c K Q) : RS P W c₀ (.ifLtN a b t e) c (K + 2) Q :=
  RunSpec.ifT ht h

theorem RS.ifF {a b : ℕ} {t e : Stmt} {K : ℕ} {Q : Config → Prop}
    (ht : ¬ c.nreg a < c.nreg b) (h : RS P W c₀ e c K Q) :
    RS P W c₀ (.ifLtN a b t e) c (K + 2) Q :=
  RunSpec.ifF ht h

theorem RS.skip {K : ℕ} {Q : Config → Prop} (hI : TInv W c₀ c) (hq : Q c) :
    RS P W c₀ .skip c K Q :=
  RunSpec.skip hI.hw hI hq

/-- **A step of a model operation.** -/
theorem RS.op {s : Stmt} {K : ℕ} {Q : Config → Prop}
    (h : ∃ c' k, Exec P W s c c' k ∧ k ≤ K ∧ Q c' ∧ TStep W c₀ c c' k) :
    RS P W c₀ s c K (fun c' => Q c' ∧ ∀ q, 80000 ≤ q → q < 90000 → c'.nreg q = c.nreg q) := by
  obtain ⟨c', k, ex, hk, hq, hI, hrf, h8⟩ := h
  exact ⟨c', k, ex, hk, hI, hrf, hq, h8⟩

/-- A scratch or output register of the test (band `bRestore` from `83010` on, off the constants
`83020 … 83023`). -/
@[ram_layout] def Scr (r : ℕ) : Prop := 83010 ≤ r ∧ r < 90000 ∧ (r < 83020 ∨ 83024 ≤ r)

/-- **One register instruction** on a scratch register. -/
theorem RS.reg {i : Instr} {r v : ℕ} (hI : TInv W c₀ c) (hr : Scr r)
    (hex : Exec P W (.instr i) c { c with nreg := upd c.nreg r v } 1) :
    RS P W c₀ (.instr i) c 1 (fun c' => c'.nreg = upd c.nreg r v) := by
  unfold Scr at hr
  obtain ⟨hI', hrf⟩ := hI.regs (c' := { c with nreg := upd c.nreg r v }) (k := 1) hex.wb_right
    (fun q hq => by simp only [upd]; split_ifs with h <;> [omega; rfl]) rfl rfl rfl rfl
  exact ⟨_, 1, hex, le_rfl, hI', hrf, rfl⟩

theorem RS.const (hI : TInv W c₀ c) {r v : ℕ} (hr : Scr r) (hv : v ≤ W) :
    RS P W c₀ (.instr (.constN r v)) c 1 (fun c' => c'.nreg = upd c.nreg r v) :=
  RS.reg hI hr (Exec.constN hI.hw r v hv)

theorem RS.copy (hI : TInv W c₀ c) {r a : ℕ} (hr : Scr r) :
    RS P W c₀ (.instr (.copyN r a)) c 1 (fun c' => c'.nreg = upd c.nreg r (c.nreg a)) :=
  RS.reg hI hr (Exec.copyN hI.hw r a)

theorem RS.add (hI : TInv W c₀ c) {r a b : ℕ} (hr : Scr r) (hab : c.nreg a + c.nreg b ≤ W) :
    RS P W c₀ (.instr (.addN r a b)) c 1 (fun c' => c'.nreg = upd c.nreg r (c.nreg a + c.nreg b)) :=
  RS.reg hI hr (Exec.addN hI.hw r a b hab)

/-- **A loop**: an invariant `I` and a measure `μ`; each iteration costs at most `Kb` and lowers
`μ`.  The allocator must leave room for all iterations. -/
theorem RS.while {a b : ℕ} {body : Stmt} (I : Config → Prop) (μ : Config → ℕ) (Kb : ℕ)
    (hpos : ∀ c, I c → c.nreg a < c.nreg b → 0 < μ c)
    (hbody : ∀ c, TInv W c₀ c → I c → c.nreg a < c.nreg b → c.nreg ALLOC + Kb ≤ W →
      RS P W c₀ body c Kb (fun c' => I c' ∧ μ c' < μ c))
    (hI : TInv W c₀ c) (hc : I c) (hroom : c.nreg ALLOC + (Kb + 2) * μ c ≤ W) :
    RS P W c₀ (.whileLtN a b body) c ((Kb + 2) * μ c + 2)
      (fun c' => I c' ∧ ¬ c'.nreg a < c'.nreg b) :=
  RunSpec.whileN I μ Kb (fun _ h => h.hw) hpos hbody hI hc hroom

end

end Restore

end Chazelle.Core
