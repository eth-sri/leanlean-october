module

public import Chazelle.Machine.FrameFields

meta import Chazelle.Programs.RamEval

public import Chazelle.Core.DownPhaseDrvPCost

/-!
# Down-phase pieces (D4), part 9: the sub-procedures and the program

The contracts of the sub-procedures as named predicates (`L41M`, `BruteM`, `BuildM`, `GranM`:
the `Meets` judgements of `Lemma41Spec`, `BruteSpec`, `BuildNFSpec`, `GranularizeSpec` for a
given program and constant), the program `pieceS sL sB sBd sG` of a piece, and the grade loop
`clogS` (`218019 := ⌈log₂ m⌉`, `clogS_exec`).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Chazelle.Core

namespace DrvP

open Machine Machine.Stmt Programs

@[expose] public section

/-! ## The program -/

/-- The empty list of a connector. -/
def connS : Stmt := block [.constN 218016 0, .constN 218017 0]

/-- `218019 := ⌈log₂ m⌉` (`218023 = 2^218019`). -/
def clogS : Stmt := .seq (block [.constN 218019 0, .constN 218023 1])
  (.whileLtN 218023 218002 (block [.addN 218023 218023 218023, .addN 218019 218019 218021]))

/-- Lemma 4.1 on the leaf, at grade `⌈log₂ m⌉`. -/
def l41Call (sL : Stmt) : Stmt := .seq clogS (.seq (block [.copyN 160000 218008,
  .copyN 160001 218004, .copyN 160002 218002, .copyN 160003 218019])
  (.seq sL (block [.copyN 218015 160004])))

/-- Brute force on the leaf (`γ' = 1` for one edge, else `2`). -/
def bruteCall (sB : Stmt) : Stmt :=
  .seq (.ifLtN 218021 218002 (block [.constN 180002 2]) (block [.constN 180002 1]))
    (.seq (block [.copyN 180000 218004, .copyN 180001 218002])
      (.seq sB (block [.copyN 218015 180003])))

/-- The normal form of a leaf, then its wall filter. -/
def leafS (sL sB : Stmt) : Stmt := .seq (.ifLtN 218002 218022 (bruteCall sB) (l41Call sL)) dropS

/-- The chord list of a piece. -/
def listS (sL sB : Stmt) : Stmt := .ifLtN 218003 218021 connS (leafS sL sB)

/-- The build of the normal form from the list. -/
def buildS (sBd : Stmt) : Stmt := .seq (block [.copyN 40000 218010, .copyN 40001 218016,
  .copyN 40002 218017]) (.seq sBd (block [.copyN 218018 40003]))

/-- The granularity enforcement (cap `4`, target `γ`). -/
def granS (sG : Stmt) : Stmt := .seq (block [.copyN 90000 218010, .copyN 90001 218018,
  .constN 90002 4, .copyN 90003 218007]) (.seq sG (block [.copyN 218011 90004]))

/-- The top offset. -/
def topS : Stmt := .ifLtN 218002 218022 scanS gTop

/-- The descriptor part: count, top, bit, descriptor. -/
def frontS : Stmt := .seq cntS (.seq topS (.seq betaS descS))

/-- **The procedure of a piece.** -/
def pieceS (sL sB sBd sG : Stmt) : Stmt :=
  .seq frontS (.seq (listS sL sB) (.seq (buildS sBd) (granS sG)))

/-! ## The grade loop -/

section exec

variable {P : Polygon} {W : ℕ}

/-- **The grade** `⌈log₂ m⌉`. -/
theorem clogS_exec (c : Config) (hw : WordsBounded W c) {m : ℕ} (h02 : c.nreg 218002 = m)
    (hm : 1 ≤ m) (h21 : c.nreg 218021 = 1) (hmW : 2 * m ≤ W) :
    ∃ c' k, Exec P W clogS c c' k ∧ k ≤ 4 * Nat.clog 2 m + 4 ∧
      c'.nreg 218019 = Nat.clog 2 m ∧
      (∀ r, r ≠ 218019 → r ≠ 218023 → c'.nreg r = c.nreg r) ∧ Machine.NatRegFrame c c' := by
  obtain ⟨c₁, k₁, e₁, hk₁, v19, v23, r₁, m₁⟩ : ∃ c₁ k₁, Exec P W
      (block [.constN 218019 0, .constN 218023 1]) c c₁ k₁ ∧ k₁ = 2 ∧ c₁.nreg 218019 = 0 ∧
      c₁.nreg 218023 = 1 ∧ (∀ r, r ≠ 218019 → r ≠ 218023 → c₁.nreg r = c.nreg r) ∧
      Machine.NatRegFrame c c₁ := by
    ram_exec
  let I : Config → Prop := fun d => WordsBounded W d ∧ d.nreg 218023 = 2 ^ d.nreg 218019 ∧
    (1 ≤ d.nreg 218019 → 2 ^ (d.nreg 218019 - 1) < m) ∧
    (∀ r, r ≠ 218019 → r ≠ 218023 → d.nreg r = c.nreg r) ∧ d.nmem = c.nmem ∧
    d.rreg = c.rreg ∧ d.rmem = c.rmem ∧ d.output = c.output
  have hI₁ : I c₁ := ⟨e₁.wb_right, by rw [v23, v19]; rfl, by rw [v19]; omega, r₁, m₁⟩
  obtain ⟨c₂, k₂, e₂, ⟨w₂, p₂, l₂, r₂, m₂, rr₂, rm₂, o₂⟩, hx₂, hk₂⟩ :=
    Exec.whileLtN_bounded (P := P) (W := W) (a := 218023) (b := 218002)
    (body := block [.addN 218023 218023 218023, .addN 218019 218019 218021]) I
    (fun d => Nat.clog 2 m - d.nreg 218019) 2 (fun d hd => hd.1) (fun d ⟨wd, pd, ld, rd', md, rrd, rmd, od⟩ ht => by
      have h2 : d.nreg 218002 = m := by frame_finish
      have h21' : d.nreg 218021 = 1 := by frame_finish
      rw [h2] at ht
      have hw := wd
      obtain ⟨d', k, e, hk, v23', v19', r', m'⟩ : ∃ d' k, Exec P W
          (block [.addN 218023 218023 218023, .addN 218019 218019 218021]) d d' k ∧ k = 2 ∧
          d'.nreg 218023 = 2 * d.nreg 218023 ∧ d'.nreg 218019 = d.nreg 218019 + 1 ∧
          (∀ r, r ≠ 218019 → r ≠ 218023 → d'.nreg r = d.nreg r) ∧
          (Machine.NatRegFrame d d') := by
        exec_block
        · config_simp; omega
        · config_simp; rw [h21']
          have : d.nreg 218019 < 2 ^ d.nreg 218019 := Nat.lt_two_pow_self
          omega
        refine ⟨rfl, by config_simp; ring, by config_simp; rw [h21'], fun r h1 h2 => ?_,
          rfl, rfl, rfl, rfl⟩
        simp only [Config.nreg_mk, upd, ite_eq_right h1, ite_eq_right h2]
      obtain ⟨m'', rr'', rm'', o''⟩ := m'
      refine ⟨d', k, e, ⟨e.wb_right, ?_, ?_, fun r h1 h2 => (r' r h1 h2).trans (rd' r h1 h2),
        m''.trans md, rr''.trans rrd, rm''.trans rmd, o''.trans od⟩, by omega, ?_⟩
      · rw [v23', v19', pd, pow_succ]; ring
      · intro _; rw [v19', Nat.add_sub_cancel, ← pd]; exact ht
      · rw [v19']
        rw [pd] at ht
        have : d.nreg 218019 < Nat.clog 2 m := by
          by_contra hc
          push Not at hc
          have h3 : m ≤ 2 ^ Nat.clog 2 m := Nat.le_pow_clog (by norm_num) m
          have h4 : 2 ^ Nat.clog 2 m ≤ 2 ^ d.nreg 218019 := Nat.pow_le_pow_right (by norm_num) hc
          omega
        omega) hI₁
  have h2 : c₂.nreg 218002 = m := by frame_finish
  rw [h2, p₂] at hx₂
  have hg : c₂.nreg 218019 = Nat.clog 2 m := by
    apply le_antisymm
    · by_contra hlt
      push Not at hlt
      have := l₂ (by omega)
      have h3 : m ≤ 2 ^ Nat.clog 2 m := Nat.le_pow_clog (by norm_num) m
      have h4 : 2 ^ Nat.clog 2 m ≤ 2 ^ (c₂.nreg 218019 - 1) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    · exact Nat.clog_le_of_le_pow (by omega)
  have hk₂' : k₂ ≤ 4 * Nat.clog 2 m + 2 := by
    rw [v19, Nat.sub_zero] at hk₂; omega
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by omega, hg, r₂, m₂, rr₂, rm₂, o₂⟩

end exec

end

end DrvP

end Chazelle.Core
