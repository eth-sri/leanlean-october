module

public import Chazelle.Core.SweepEvStopFin3

/-!
# The sweep (WP-D), stage 2, the finish of a stop origin: contract of the emission (RAM)

`slfEmits`: emit the raw record of `A₀ = (oF0 + 1, oF0 + 2)` (code `dc = oB`) unless its offset is
`< Lst` (bit `slfO`), then that of `A₁ = (a1F + 1, a1F + 2)` (code `dc = 1 - oB`, register
`slfDc`) unless its offset is `< Lst` (bit `slfO + 4`).  Contract `SlfEmitsSpec`: from the
attachments, the offset bits and the auxiliary data (`AuxOK` of the words `slfA, slfN, slfL0,
slfL1, oPar`, given an attachment on the `C₁` part), the post `OrgOut`.
(`orig_attach`, `attach_two`; the words of a record by `slfEmit_irs`.)
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep SweepStop
open Chazelle.Chain (SideAttach)

@[expose] public section

def slfDc : ℕ := sw 4067

/-- **The emission of the raw records.** -/
def slfEmits : Stmt :=
  .seq (block [.subN slfDc K1 oB])
    (.seq (.ifLtN K0 slfO .skip (slfEmit (oF0 + 1) (oF0 + 2) oB))
      (.ifLtN K0 (slfO + 4) .skip (slfEmit (a1F + 1) (a1F + 2) slfDc)))

/-- **The contract of the emission.** -/
def SlfEmitsSpec : Prop :=
  ∀ (sh : Stmt) (Bs : Finset ℕ) (F : ℕ → ℕ) (X : MemCtx)
    (Ok : Polygon → Model → Prop) (P : Polygon) (W : ℕ) (c₀ c : Config) (J : Merge.Junction)
    (N₁ N₂ : NF), EvEnv sh Bs F X Ok P W c₀ J N₁ N₂ → IInv W c₀ c →
      OrgD P J N₂ (c.nreg oKd) (c.nreg oKk) (c.nreg oB) →
      Arrival (chainModel J.whole).W (stOrig J (Qof P) N₂ (c.nreg oKd) (c.nreg oKk) (c.nreg oB))
        (-dirOf (c.nreg oB)) (c.nreg (oF0 + 1))
        ((chainModel J.whole).param (Qof P) ⟨c.nreg (oF0 + 1), c.nreg (oF0 + 2)⟩) →
      PosW P J (c.nreg (oF0 + 1)) (c.nreg (oF0 + 2)) →
      Arrival (chainModel J.whole).W
        (farPt J.whole (stOrig J (Qof P) N₂ (c.nreg oKd) (c.nreg oKk) (c.nreg oB))
          (dirOf (c.nreg oB))) (dirOf (c.nreg oB)) (c.nreg (a1F + 1))
        ((chainModel J.whole).param (Qof P) ⟨c.nreg (a1F + 1), c.nreg (a1F + 2)⟩) →
      PosW P J (c.nreg (a1F + 1)) (c.nreg (a1F + 2)) →
      BitIs c slfO (slfOff P J c (oF0 + 1) (oF0 + 2) < Lst J) →
      BitIs c (slfO + 4) (slfOff P J c (a1F + 1) (a1F + 2) < Lst J) →
      ((∃ (q : ℕ) (s : ℝ), SideAttach (chainModel J.whole).W
          (stopSet J (Qof P) N₂ (c.nreg oKd) (c.nreg oKk) (c.nreg oB)) q s ∧
          (Lst J : ℝ) ≤ oW J (q + s)) →
        AuxOK P J N₂ (stopSet J (Qof P) N₂ (c.nreg oKd) (c.nreg oKk) (c.nreg oB))
          (c.nreg slfA, c.nreg slfN, c.nreg slfL0, c.nreg slfL1, c.nreg oPar)) →
      c₀.nreg ALLOC ≤ c.nreg gRB → c.nreg gRB + 11 * (c.nreg gRC + 2) ≤ c.nreg ALLOC →
      c.nreg ALLOC + 100 ≤ W →
      IRS P W c₀ slfEmits c 100 (OrgOut P J N₂ (c.nreg oKd) (c.nreg oKk) (c.nreg oB) c)

end

end SweepEv

end Chazelle.Core
