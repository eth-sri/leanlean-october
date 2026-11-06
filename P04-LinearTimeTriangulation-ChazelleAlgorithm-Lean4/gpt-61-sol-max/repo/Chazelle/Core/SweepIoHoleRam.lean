module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.RestoreTHoleMath

/-!
# The sweep RAM (WP-D), answers: small register programs for the holes (copied from WP-E)

Register-only building blocks with exact effects (`Out`: only the listed registers change):
a conditional subtraction (`condSub`), the tour step of a tour position (`candS`, `candIdx`),
the wrap of a walk index (`nxtS`), and the lemma turning such an execution into a run step.
-/

namespace Chazelle.Core

namespace SweepIo

@[expose] public section

open Machine Machine.Stmt Programs SweepPrim SignK

variable {P : Polygon} {W : ℕ} {c : Config}

/-- **Only the registers `L` change** (and nothing else of the configuration). -/
def Out (c c' : Config) (L : List ℕ) : Prop :=
  (∀ r, r ∉ L → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧ c'.nmem = c.nmem ∧
    c'.rmem = c.rmem ∧ c'.output = c.output

theorem Out.refl (c : Config) (L : List ℕ) : Out c c L :=
  ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩

theorem Out.trans {c c₁ c₂ : Config} {L₁ L₂ : List ℕ} (h₁ : Out c c₁ L₁) (h₂ : Out c₁ c₂ L₂) :
    Out c c₂ (L₁ ++ L₂) :=
  ⟨fun r hr => by
    ram_grind, h₂.2.1.trans h₁.2.1, h₂.2.2.1.trans h₁.2.2.1,
    h₂.2.2.2.1.trans h₁.2.2.2.1, h₂.2.2.2.2.trans h₁.2.2.2.2⟩

theorem Out.mono {c c' : Config} {L L' : List ℕ} (h : Out c c' L) (hL : ∀ r ∈ L, r ∈ L') :
    Out c c' L' := by core_grind

/-- One register instruction. -/
theorem out_instr {i : Instr} {r v : ℕ}
    (hex : Exec P W (.instr i) c { c with nreg := upd c.nreg r v } 1) :
    ∃ c', Exec P W (.instr i) c c' 1 ∧ c'.nreg r = v ∧ Out c c' [r] :=
  ⟨_, hex, by simp, fun q hq => by simp_all,
    rfl, rfl, rfl, rfl⟩

/-! ## A conditional subtraction -/

/-- `dst := a < b ? a : a - b`. -/
def condSub (dst a b : ℕ) : Stmt := .ifLtN a b (.instr (.copyN dst a)) (.instr (.subN dst a b))

theorem condSub_exec (hw : WordsBounded W c) (dst a b : ℕ) :
    ∃ c', ∃ k ≤ 3, Exec P W (condSub dst a b) c c' k ∧
      c'.nreg dst = (if c.nreg a < c.nreg b then c.nreg a else c.nreg a - c.nreg b) ∧
      Out c c' [dst] := by
  unfold condSub
  by_cases h : c.nreg a < c.nreg b
  · obtain ⟨c', e, v, o⟩ := out_instr (P := P) (Exec.copyN hw dst a)
    exact ⟨c', _, by omega, .ifLtN_true h e, by simp_all, o⟩
  · obtain ⟨c', e, v, o⟩ := out_instr (P := P) (Exec.subN hw dst a b)
    exact ⟨c', _, by omega, .ifLtN_false h e, by simp_all, o⟩

/-! ## The tour step of a tour position -/

/-- `dst := candIdx m S j` for `j` in `jr`, `S` in `sr`, `2m` in `mr` (`t` scratch). -/
def candS (dst jr sr mr : ℕ) : Stmt :=
  .ifLtN jr sr (.seq (.instr (.subN dst mr sr)) (.instr (.addN dst dst jr)))
    (.instr (.subN dst jr sr))

theorem candS_exec (hw : WordsBounded W c) {dst jr sr mr : ℕ} (hd1 : dst ≠ jr) (_hd2 : dst ≠ sr)
    (_hd3 : dst ≠ mr) {m S j : ℕ} (hj : c.nreg jr = j) (hs : c.nreg sr = S)
    (hm : c.nreg mr = 2 * m) (hS : S ≤ 2 * m) (hW : 2 * m ≤ W) (_hjm : j ≤ 2 * m) :
    ∃ c', ∃ k ≤ 4, Exec P W (candS dst jr sr mr) c c' k ∧ c'.nreg dst = candIdx m S j ∧
      Out c c' [dst] := by
  unfold candS
  by_cases h : c.nreg jr < c.nreg sr
  · obtain ⟨c₁, e₁, v₁, o₁⟩ := out_instr (P := P) (Exec.subN hw dst mr sr)
    obtain ⟨c₂, e₂, v₂, o₂⟩ := out_instr (P := P) (Exec.addN e₁.wb_right dst dst jr
      (by ram_grind))
    refine ⟨c₂, _, by omega, .ifLtN_true h (.seq e₁ e₂), ?_, (o₁.trans o₂).mono (by simp)⟩
    rw [v₂, v₁, o₁.1 jr (by grind), hm, hs, hj]
    core_grind
  · obtain ⟨c₁, e₁, v₁, o₁⟩ := out_instr (P := P) (Exec.subN hw dst jr sr)
    refine ⟨c₁, _, by omega, .ifLtN_false h e₁, ?_, o₁⟩
    simp_all [candIdx] <;> omega_nf

/-! ## Wrapping a walk index -/

/-- `r := r < n ? r : 0` (`n` in `nr`). -/
def nxtS (r nr : ℕ) : Stmt := .ifLtN r nr .skip (.instr (.constN r 0))

theorem nxtS_exec (hw : WordsBounded W c) (r nr : ℕ) :
    ∃ c', ∃ k ≤ 3, Exec P W (nxtS r nr) c c' k ∧
      c'.nreg r = (if c.nreg r < c.nreg nr then c.nreg r else 0) ∧ Out c c' [r] := by
  unfold nxtS
  by_cases h : c.nreg r < c.nreg nr
  · exact ⟨c, _, by omega, .ifLtN_true h (.skip hw), by simp_all, Out.refl _ _⟩
  · obtain ⟨c', e, v, o⟩ := out_instr (P := P) (Exec.constN hw r 0 (Nat.zero_le _))
    exact ⟨c', _, by omega, .ifLtN_false h e, by simp_all, o⟩

/-- The wrap of `q + 1` below `n` is `(q + 1) % n`. -/
theorem wrap_succ {q n : ℕ} (hq : q < n) : (if q + 1 < n then q + 1 else 0) = (q + 1) % n := by
  split_ifs with h
  · exact (Nat.mod_eq_of_lt h).symm
  grind [Nat.mod_self]

end

end SweepIo

end Chazelle.Core
