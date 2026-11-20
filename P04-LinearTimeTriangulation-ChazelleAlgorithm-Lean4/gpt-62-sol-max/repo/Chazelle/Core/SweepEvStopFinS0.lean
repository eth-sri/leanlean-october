module

public import Chazelle.Programs.RamSimp

public import Chazelle.Core.SweepEvStopTasks3

/-!
# The sweep (WP-D), stage 2, the finish of a stop origin: contract of the stretch labels

`StrLabTask`: from a stretch attachment `(slfSE, slfSH)` of the walk of `C` of a stop chord without a
parent (offset in `(0, Lst)`), the regions `frA`, `frB` of `N₂` faced just after / just before the
counterpart position in the walk of `C₂` (the hypotheses of the second part of `LabTask`).
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep SweepStop
open Chazelle.Chain (SideAttach)

@[expose] public section

@[ram_layout] def slfSE : ℕ := sw 4116
@[ram_layout] def slfSH : ℕ := sw 4117

/-- The registers the stretch labels may write. -/
def StrR (r : ℕ) : Prop :=
  FRR r ∨ (sw 4096 ≤ r ∧ r < sw 4100) ∨ (sw 4110 ≤ r ∧ r < sw 4200)

/-- **Task SL: the stretch labels.** -/
def StrLabSpec (sl : Stmt) (κ : ℕ → ℕ) : Prop :=
  ∀ (sh : Stmt) (Bs : Finset ℕ) (F : ℕ → ℕ) (X : MemCtx)
    (Ok : Polygon → Model → Prop) (P : Polygon) (W : ℕ) (c₀ c : Config) (J : Merge.Junction)
    (N₁ N₂ : NF), EvEnv sh Bs F X Ok P W c₀ J N₁ N₂ → IInv W c₀ c →
      c.nreg slfSE < J.wholeModel.W.n →
      ProperPos J.wholeModel (Qof P) P.n ⟨c.nreg slfSE, c.nreg slfSH⟩ →
      |(J.wholeModel.pos (Qof P) ⟨c.nreg slfSE, c.nreg slfSH⟩).2| < J.whole.radius →
      (∃ e, e ∈ F₂plus J (N₂.F J.rightModel (Qof P)) ∧
        (∀ c ∈ N₂.F J.rightModel (Qof P), ¬ e ⊆ c) ∧
        SideAttach J.wholeModel.W e (c.nreg slfSE)
          (J.wholeModel.param (Qof P) ⟨c.nreg slfSE, c.nreg slfSH⟩)) →
      0 < oW J (c.nreg slfSE + J.wholeModel.param (Qof P) ⟨c.nreg slfSE, c.nreg slfSH⟩) →
      oW J (c.nreg slfSE + J.wholeModel.param (Qof P) ⟨c.nreg slfSE, c.nreg slfSH⟩) < Lst J →
      c.nreg ALLOC + κ (c₀.nreg (sw 6)) * (c₀.nreg TLR + 1) ≤ W →
      IRS P W c₀ sl c (κ (c₀.nreg (sw 6)) * (c₀.nreg TLR + 1)) (fun c' =>
        c'.nreg frA < N₂.nRegions ∧ c'.nreg frB < N₂.nRegions ∧
        (∃ d, d < Lst J ∧
          (J.wholeModel.param (Qof P) ⟨c.nreg slfSE, c.nreg slfSH⟩ = 0 → d ≠ 0) ∧
          c.nreg slfSE = (gW J + d) % J.wholeModel.W.n ∧
          AfterFaces J.rightModel (cpA J d)
            (J.wholeModel.param (Qof P) ⟨c.nreg slfSE, c.nreg slfSH⟩)
            (regOf J.rightModel (Qof P) N₂ (c'.nreg frA)) ∧
          (0 < J.wholeModel.param (Qof P) ⟨c.nreg slfSE, c.nreg slfSH⟩ →
            BeforeFaces J.rightModel (cpA J d)
              (J.wholeModel.param (Qof P) ⟨c.nreg slfSE, c.nreg slfSH⟩)
              (regOf J.rightModel (Qof P) N₂ (c'.nreg frB))) ∧
          (J.wholeModel.param (Qof P) ⟨c.nreg slfSE, c.nreg slfSH⟩ = 0 →
            BeforeFaces J.rightModel (cpB J d) 0
              (regOf J.rightModel (Qof P) N₂ (c'.nreg frB)))) ∧
        (MemEqBelow (c.nreg ALLOC) c'.nmem c.nmem) ∧ c.nreg ALLOC ≤ c'.nreg ALLOC ∧
        (∀ r, bandOf r ∉ oracleBands → ¬ StrR r → r ≠ ALLOC → c'.nreg r = c.nreg r))

def StrLabTask : Prop := ∃ sl κ, StrLabSpec sl κ

end

end SweepEv

end Chazelle.Core
