/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.FourPoint.ThreePointFiniteCorrelation
import DOZZ.FourPoint.BPZ.DegenerateFourPointBPZ
import Batteries.Tactic.Alias

/-! The statement `DOZZ.degenerateFourPoint_BPZ`,
proved by `DOZZ.Proofs.degenerateFourPoint_BPZ`. -/

public section


namespace DOZZ

/-- For either degenerate insertion, the literal reduced function `T` satisfies the Wirtinger form
of the Gauss equation with the parameters of [KRV, (defabcfirst)]. The two values of `χ` are kept in
the same statement; the Seiberg sum is the one for `(-χ, α₁, α₂, α₃)`. -/
alias degenerateFourPoint_BPZ := DOZZ.Proofs.degenerateFourPoint_BPZ

end DOZZ
