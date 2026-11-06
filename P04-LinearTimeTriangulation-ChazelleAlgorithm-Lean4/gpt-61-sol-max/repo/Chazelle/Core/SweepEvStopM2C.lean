module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.SweepEvStopTasks3
public import Chazelle.Core.SweepEvStopRC
public import Chazelle.Core.SweepEvGen
public import Chazelle.Core.SweepIoRec

/-!
# The sweep (WP-D), stage 2: the candidate of `C₂` of a stop origin (task M2, part 1)

`m2cS sh` (shared and top codes): `callArr` in the walk of `C₂` from the origin's position
`(oPE, oPH)` for the reversed direction (flag `m2F`, arrival `(pE2, pH2)`); without arrival the
empty result; otherwise the local hit from the arrival (`lhSave`).  `m2cW sh` (wall codes): the
local hit from `(oPE, oPH)` (the end of the chord record, an attachment of it: `m2c_wall_left`).
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep SweepStop
open Chazelle.Visibility (rayPt)
open Chazelle.Chain (SideAttach sidePt sideLeft)
open Chazelle.Merge (FreeAt)

@[expose] public section

/-! ## Mathematics -/

/-- **The end of a chord record looks along the chord**: at the position of the end `1 - b` of
chord `k`, the direction `dirOf b` (towards the other end) is in the left sector. -/
theorem m2c_wall_left {C : Chain} {Q : Polygon} {N : NF} (hN : IsNF (chainModel C) Q N) {k b : ℕ}
    (hk : k < N.nChords) (hb : b ≤ 1) :
    sideLeft (chainModel C).W (endPos N k (1 - b)).edge
      ((chainModel C).param Q (endPos N k (1 - b)))
      (rayPt ((chainModel C).pos Q (endPos N k (1 - b))) (dirOf b) 1) := by
  obtain ⟨y, l, r, hlr, heq, hl, hr, -⟩ := rec_ends hN hk
  have hA := hN.2.2.1 k hk
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hb with rfl | rfl
  · have he : endPos N k (1 - 0) = (N.chord k).rpos := by aesop
    rw [he, dirOf_zero]
    have := sideLeft_of_attach hA.2 (Or.inr rfl) (show (0 : ℝ) < r - l by linarith)
      (fun s hs0 hs => by
        show rayPt ((chainModel C).pos Q (N.chord k).rpos) (-1) s ∈ _
        rw [hr, heq]
        refine ⟨by simp [rayPt], ?_, ?_⟩ <;> simp [rayPt] <;> linarith)
    exact this
  · have he : endPos N k (1 - 1) = (N.chord k).lpos := by aesop
    rw [he, dirOf_one]
    have := sideLeft_of_attach hA.1 (Or.inl rfl) (show (0 : ℝ) < r - l by linarith)
      (fun s hs0 hs => by
        show rayPt ((chainModel C).pos Q (N.chord k).lpos) 1 s ∈ _
        rw [hl, heq]
        refine ⟨by simp [rayPt], ?_, ?_⟩ <;> simp [rayPt] <;> linarith)
    exact this

/-! ## The program -/

/-- Set the local hit's input from the position `(e, h)` and the direction code `oB`. -/
def m2cSet (e h : ℕ) : List Instr := [.copyN lE e, .copyN lH h, .copyN lD oB]

section
variable (sh : Stmt)
include sh
/-- **Shared and top codes.** -/
def m2cS : Stmt :=
  .seq (callArr (sw 21) oPE oPH oB m2F)
    (.ifLtN m2F K1 (noRes r2F)
      (.seq (block (m2cSet pE2 pH2)) (lhSave sh gMD2 gCD2 (sw 4) (sw 34) r2F)))

/-- **Wall codes.** -/
def m2cW : Stmt :=
  .seq (block (m2cSet oPE oPH)) (lhSave sh gMD2 gCD2 (sw 4) (sw 34) r2F)

/-- **The candidate of `C₂`.** -/
def m2c : Stmt :=
  .ifLtN oKd K1 (m2cS sh) (.ifLtN K1 oKd (m2cS sh) (m2cW sh))


end

variable {P : Polygon} {W : ℕ} {c₀ c : Config}

section
variable (m f : ℕ → ℕ)
theorem m2cSet_val {e h : ℕ} (_he : e ≠ lE ∧ e ≠ lH) (hh : h ≠ lE) :
    regB m (m2cSet e h) f lE = f e ∧ regB m (m2cSet e h) f lH = f h ∧
      regB m (m2cSet e h) f lD = f oB ∧
      (∀ q, q ≠ lE → q ≠ lH → q ≠ lD → regB m (m2cSet e h) f q = f q) := by
  simp_all [lE, lH, sw, lD, oB, m2cSet, regB, regI, upd] <;> omega_nf

theorem m2cSet_ok (e h : ℕ) : okB W m (m2cSet e h) f :=
  ⟨iscr_sw (by omega_nf) (by omega_nf),
    iscr_sw (by omega_nf) (by omega_nf),
    iscr_sw (by omega_nf) (by omega_nf), trivial⟩


end

/-- The cost of a branch. -/
def m2cK (T Fg D : ℕ) : ℕ := 35007 + (3 + (lhRunK T Fg D + 7) + 2)

theorem m2cK_le (T Fg D : ℕ) : m2cK T Fg D + 4 ≤ (κGen D + 40000) * (Fg + T + 1) := by
  have h1 : lhRunK T Fg D + 7 ≤ genK Fg D T := by omega_nf
  have h2 := genK_le Fg D T
  have h3 : (κGen D + 40000) * (Fg + T + 1) = κGen D * (Fg + T + 1) + 40000 * (Fg + T + 1) := by
    ring
  simp_all [m2cK] <;> omega_nf

end

end SweepEv

end Chazelle.Core
