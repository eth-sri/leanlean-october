module

public import Chazelle.Core.SweepIoSpec

/-!
# The sweep RAM (WP-D), answers: the table step of a side-1 query (contract)

`TabStepSpec`: for a regular endpoint query `j = qJ` (index below `2 K₂`, origin `z` a point of
`C₂` other than the shared vertex and the top of `C₂`, direction `endDir j`), a program `tabB`
reads the endpoint table entry `j` (three words `(f, e, h)` at `rd c₀ bSweep 302 + 3 j`) and, if
the flag is `1`, offers the position `(e, h)` of the walk of `C` (descriptor `sw 2`) with tag `2`
to the accumulator.  Afterwards the first hit of `C` is a candidate, or it equals the first hit
of `C₂` (`TabOK`, from `AEnv.hout`).  Constant cost.
-/

namespace Chazelle.Core

namespace SweepIo

open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed Sweep
open Chazelle.Visibility (rayPt)
open Chazelle.Merge (FreeAt)

@[expose] public section

/-- **The table step of a regular endpoint query of side `1`.** -/
def TabStepSpec : Prop :=
  ∃ (tabB : Stmt) (κT : ℕ), ∀ (P : Polygon) (W : ℕ) (X : MemCtx) (Ok : Polygon → Model → Prop)
    (J : Merge.Junction) (H : Host) (N₁ N₂ : NF) (E : ℕ) (c₀ c : Config) (L : Set ℝ)
    (z : Point),
    AEnv P W X Ok J H N₁ N₂ E c₀ → IInv W c₀ c →
    c.nreg qJ < 2 * N₂.nChords → endOrigin J (Qof P) N₂ (c.nreg qJ) = z →
    endDir (c.nreg qJ) = dirOf (c.nreg qD) →
    z ∈ J.right.set → z ≠ J.shared → z ≠ J.right.top →
    AccOK P accA (ModB J (c.nreg bL) (c.nreg bR)) J.whole.radius z (dirOf (c.nreg qD)) L c →
    c.nreg ALLOC + κT ≤ W →
    IRS P W c₀ tabB c κT
      (fun c' =>
        (∃ L', AccOK P accA (ModB J (c.nreg bL) (c.nreg bR)) J.whole.radius z
            (dirOf (c.nreg qD)) L' c' ∧ L ⊆ L' ∧
          (∀ τ ∈ L', τ ∈ L ∨ (0 < τ ∧ OnCB J.whole (rayPt z (dirOf (c.nreg qD)) τ))) ∧
          (J.whole.hitParam z (dirOf (c.nreg qD)) ∈ L' ∨
            J.whole.hitParam z (dirOf (c.nreg qD)) = J.right.hitParam z (dirOf (c.nreg qD)))) ∧
        CandFr c c')

end

end SweepIo

end Chazelle.Core
