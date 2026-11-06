module

public import Chazelle.Core.SweepIoCand1L

/-!
# The sweep RAM (WP-D), answers: the shared-vertex step of a side-1 query (contract)

`ShrStepSpec`: for a side-1 query at the shared vertex `J.shared` (height code `qH` naming its
height, direction code `qD` free for `C`), a program `shrB sh` computes the arrival position of
the shared vertex in the walk of the model of `C₁` (`callArr` on the chain descriptor `sw 20` at
the vertex position `(sw 46, K0)` — `sw 46 = cstL J 1 = 6 + tpos J.left J.m₁` — with the direction
code `qD`) and runs the local hit in the model of `C₁` there (`Cand1.lhsL_irs` at `(p, qH)`,
tag `0`).  The arrival exists since the direction is free for `C₁` (`freeAt_left_of`,
`freeAt_iff_arr`); `Cand1.lhGeo_arr` gives `LHGeo`.  Afterwards the first hit of `C₁` is a
candidate; every new candidate is a point of `C₁` or of the box at a positive parameter.
-/

namespace Chazelle.Core

namespace SweepIo

open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed Sweep
open Chazelle.Visibility (rayPt)
open Chazelle.Merge (FreeAt)

@[expose] public section

/-- **The shared-vertex step of a side-1 query.** -/
def ShrStepSpec : Prop :=
  ∃ (shrB : Stmt → Stmt) (κS : ℕ), ∀ (sh : Stmt) (Bs : Finset ℕ) (F : ℕ → ℕ) (X : MemCtx)
    (Ok : Polygon → Model → Prop), ShooterOK sh Bs F X Ok → Bs ⊆ oracleBands → X.CapLocal →
    ∀ (P : Polygon) (W : ℕ) (c₀ c : Config) (J : Merge.Junction) (H : Host) (N₁ N₂ : NF)
      (E : ℕ) (L : Set ℝ),
      AEnv P W X Ok J H N₁ N₂ E c₀ → IInv W c₀ c →
      1 ≤ c.nreg qH → c.nreg qH ≤ P.n → ((Qof P).vtx (c.nreg qH - 1)).2 = J.shared.2 →
      FreeAt J.whole J.shared (dirOf (c.nreg qD)) → c.nreg bL = 1 →
      AccOK P accA (ModB J (c.nreg bL) (c.nreg bR)) J.whole.radius J.shared
        (dirOf (c.nreg qD)) L c →
      c.nreg ALLOC + (κS + Cand1.lhsK (c₀.nreg TLR) (F (c₀.nreg (sw 5))) (c₀.nreg (sw 6))) ≤ W →
      IRS P W c₀ (shrB sh) c
        (κS + Cand1.lhsK (c₀.nreg TLR) (F (c₀.nreg (sw 5))) (c₀.nreg (sw 6)))
        (fun c' =>
          (∃ L', AccOK P accA (ModB J (c.nreg bL) (c.nreg bR)) J.whole.radius J.shared
              (dirOf (c.nreg qD)) L' c' ∧ L ⊆ L' ∧
            (∀ τ ∈ L', τ ∈ L ∨ (0 < τ ∧ OnCB J.left (rayPt J.shared (dirOf (c.nreg qD)) τ))) ∧
            J.left.hitParam J.shared (dirOf (c.nreg qD)) ∈ L') ∧
          CandFr c c')

end

end SweepIo

end Chazelle.Core
