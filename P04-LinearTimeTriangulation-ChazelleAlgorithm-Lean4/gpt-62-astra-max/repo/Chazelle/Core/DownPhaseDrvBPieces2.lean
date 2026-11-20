module

public import Chazelle.Core.DownPhaseDrvBEnv

/-!
# Down-phase base (D9): the contract of one region of the region loop

`RegStepSpec s κR`: the statement `s` processes region `r` of the region loop: from the state
`RSt E r` (fixed registers `BRegs`, `r216006 = 5`, region counter `r212014 = r`, region record
pointer `r216031 = RP r`, `MX = r212018` bounding the points of the regions `< r` and at most
`S₀`, the output `OutSt` of the tagged records `TL r`, the allocator above the reserved area)
to `RSt E (r + 1)`, in `κR (S₀ + 1) (Cm + 1)` steps, within the relative frame
`Restore.RF DrvR.drvBands B₂`, keeping the registers `FixB`, `212013` and `216006`.

The region loop (`RegLoopSpec`) is then: an initialisation establishing `RSt E 0` from
`RegPre`, the loop `whileLtN 212014 212013 s` (`r212013 = K + 1`), and `RegPost` from
`RSt E (K + 1)` (with `DrvB.bktMath`).
-/

namespace Chazelle.Core

namespace DrvB

open Machine Machine.Stmt

@[expose] public section

/-- **The state of the region loop before region `r`.** -/
structure RSt (E : BEnv) (r : ℕ) (c : Config) : Prop where
  wb : WordsBounded E.W c
  regs : BRegs E c
  c6 : c.nreg 216006 = 5
  r14 : c.nreg 212014 = r
  p31 : c.nreg 216031 = E.RP r
  mx : ∀ r', r' < r → (E.pts r').length ≤ c.nreg 212018
  mxS : c.nreg 212018 ≤ E.S₀
  out : OutSt E c (E.TL r)
  alloc : E.B₂ + 10 * E.P.n ≤ c.nreg ALLOC

/-- **The contract of one region of the region loop.** -/
def RegStepSpec (s : Stmt) (κR : ℕ) : Prop :=
  ∀ (E : BEnv), BGood E → ∀ (r : ℕ) (c : Config), r < E.K + 1 → RSt E r c →
    c.nreg ALLOC + κR * (E.S₀ + 1) * (E.Cm + 1) ≤ E.W →
    ∃ c' k, Exec E.P E.W s c c' k ∧ k ≤ κR * (E.S₀ + 1) * (E.Cm + 1) ∧ RSt E (r + 1) c' ∧
      Restore.RF DrvR.drvBands E.B₂ c c' k ∧
      (∀ q, (FixB q ∨ q = 212013 ∨ q = 216006) → c'.nreg q = c.nreg q)

end

end DrvB

end Chazelle.Core
