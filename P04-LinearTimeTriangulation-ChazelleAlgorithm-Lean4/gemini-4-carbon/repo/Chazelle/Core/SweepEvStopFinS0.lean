module

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

def slfSE : ℕ := sw 4116
def slfSH : ℕ := sw 4117

/-- The registers the stretch labels may write. -/
def StrR (r : ℕ) : Prop :=
  FRR r ∨ (sw 4096 ≤ r ∧ r < sw 4100) ∨ (sw 4110 ≤ r ∧ r < sw 4200)

/-- **Task SL: the stretch labels.** -/
def StrLabTask : Prop :=
  ∃ (sl : Stmt) (κ : ℕ → ℕ), ∀ (sh : Stmt) (Bs : Finset ℕ) (F : ℕ → ℕ) (X : MemCtx)
    (Ok : Polygon → Model → Prop) (P : Polygon) (W : ℕ) (c₀ c : Config) (J : Merge.Junction)
    (N₁ N₂ : NF), EvEnv sh Bs F X Ok P W c₀ J N₁ N₂ → IInv W c₀ c →
      c.nreg slfSE < (chainModel J.whole).W.n →
      ProperPos (chainModel J.whole) (Qof P) P.n ⟨c.nreg slfSE, c.nreg slfSH⟩ →
      |((chainModel J.whole).pos (Qof P) ⟨c.nreg slfSE, c.nreg slfSH⟩).2| < J.whole.radius →
      (∃ e, e ∈ F₂plus J (N₂.F (chainModel J.right) (Qof P)) ∧
        (∀ c ∈ N₂.F (chainModel J.right) (Qof P), ¬ e ⊆ c) ∧
        SideAttach (chainModel J.whole).W e (c.nreg slfSE)
          ((chainModel J.whole).param (Qof P) ⟨c.nreg slfSE, c.nreg slfSH⟩)) →
      0 < oW J (c.nreg slfSE + (chainModel J.whole).param (Qof P) ⟨c.nreg slfSE, c.nreg slfSH⟩) →
      oW J (c.nreg slfSE + (chainModel J.whole).param (Qof P) ⟨c.nreg slfSE, c.nreg slfSH⟩) < Lst J →
      c.nreg ALLOC + κ (c₀.nreg (sw 6)) * (c₀.nreg TLR + 1) ≤ W →
      IRS P W c₀ sl c (κ (c₀.nreg (sw 6)) * (c₀.nreg TLR + 1)) (fun c' =>
        c'.nreg frA < N₂.nRegions ∧ c'.nreg frB < N₂.nRegions ∧
        (∃ d, d < Lst J ∧
          ((chainModel J.whole).param (Qof P) ⟨c.nreg slfSE, c.nreg slfSH⟩ = 0 → d ≠ 0) ∧
          c.nreg slfSE = (gW J + d) % (chainModel J.whole).W.n ∧
          AfterFaces (chainModel J.right) (cpA J d)
            ((chainModel J.whole).param (Qof P) ⟨c.nreg slfSE, c.nreg slfSH⟩)
            (regOf (chainModel J.right) (Qof P) N₂ (c'.nreg frA)) ∧
          (0 < (chainModel J.whole).param (Qof P) ⟨c.nreg slfSE, c.nreg slfSH⟩ →
            BeforeFaces (chainModel J.right) (cpA J d)
              ((chainModel J.whole).param (Qof P) ⟨c.nreg slfSE, c.nreg slfSH⟩)
              (regOf (chainModel J.right) (Qof P) N₂ (c'.nreg frB))) ∧
          ((chainModel J.whole).param (Qof P) ⟨c.nreg slfSE, c.nreg slfSH⟩ = 0 →
            BeforeFaces (chainModel J.right) (cpB J d) 0
              (regOf (chainModel J.right) (Qof P) N₂ (c'.nreg frB)))) ∧
        (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) ∧ c.nreg ALLOC ≤ c'.nreg ALLOC ∧
        (∀ r, bandOf r ∉ oracleBands → ¬ StrR r → r ≠ ALLOC → c'.nreg r = c.nreg r))

end

end SweepEv

end Chazelle.Core
