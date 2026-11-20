module

public import Chazelle.Core.SweepIoS0CandMath2

/-!
# The sweep RAM (WP-D), answers: the binary search in the event log (contract)

`LSearchSpec`: a statement `lsearch` that finds, for a target walk position `x = (xE, xH)` of the
walk of `C` (registers `lsxE = sw 4020`, `lsxH = sw 4021`), the number `t` of log records (base
`rd 300`, count `E = rd 301`, seven words per record, key `(e, h)` in the first two words) whose
key has an offset (from the base held in `sw 40`) smaller than that of `x`, given that this
predicate is downward closed in the record index.  Binary search with the table of powers
(`TBR`, `TLR`, `E < 2 ^ TLR`) and the primitive `offCmp` (`callOff` with the chain descriptor
`sw 2` of `C`).  Result in `lsI = sw 4000`; writes only `sw 4000 … sw 4019`, the oracle bands and
the allocator.  Cost `κ (TLR + 1)`.
-/

namespace Chazelle.Core

namespace SweepIo

namespace S0C

open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed Sweep

@[expose] public section

/-- The result register of the search. -/
def lsI : ℕ := sw 4000
/-- The target position. -/
def lsxE : ℕ := sw 4020
def lsxH : ℕ := sw 4021

/-- The registers the search may write (outside the oracle bands, besides the allocator). -/
def LSet (r : ℕ) : Prop := sw 4000 ≤ r ∧ r ≤ sw 4019

/-- **The predicate of the search**: the key of log record `j` (in memory `m` at base `AL`) has
a smaller offset from `G` than the target `x`. -/
def lsPr (P : Polygon) (J : Merge.Junction) (m : ℕ → ℕ) (AL G : ℕ) (x : WPos) (j : ℕ) : Prop :=
  off (chainModel J.whole).W.n G
      ((chainModel J.whole).key (Qof P) ⟨m (AL + 7 * j), m (AL + 7 * j + 1)⟩) <
    off (chainModel J.whole).W.n G ((chainModel J.whole).key (Qof P) x)

/-- **The contract of the binary search in the log.** -/
def LSearchSpec : Prop :=
  ∃ (lsearch : Stmt) (κ : ℕ), ∀ (P : Polygon) (W : ℕ) (J : Merge.Junction) (c₀ c : Config),
    IInv W c₀ c → Consts c₀ → ChainCtx P W c (sw 2) J.whole →
    (∀ j, j < c.nreg TLR → c.nmem (c.nreg TBR + j) = 2 ^ j) →
    c.nreg TBR + c.nreg TLR ≤ c.nreg ALLOC →
    c.nreg (sw 301) < 2 ^ c.nreg TLR →
    c.nreg (sw 300) + 7 * c.nreg (sw 301) ≤ c.nreg ALLOC →
    c.nreg (sw 40) < (chainModel J.whole).W.n →
    (∀ j, j < c.nreg (sw 301) → SweepEv.PosW P J (c.nmem (c.nreg (sw 300) + 7 * j))
      (c.nmem (c.nreg (sw 300) + 7 * j + 1))) →
    SweepEv.PosW P J (c.nreg lsxE) (c.nreg lsxH) →
    (∀ i j, i ≤ j → j < c.nreg (sw 301) →
      lsPr P J c.nmem (c.nreg (sw 300)) (c.nreg (sw 40)) ⟨c.nreg lsxE, c.nreg lsxH⟩ j →
      lsPr P J c.nmem (c.nreg (sw 300)) (c.nreg (sw 40)) ⟨c.nreg lsxE, c.nreg lsxH⟩ i) →
    c.nreg ALLOC + κ * (c.nreg TLR + 1) ≤ W →
    IRS P W c₀ lsearch c (κ * (c.nreg TLR + 1)) (fun c' =>
      c'.nreg lsI ≤ c.nreg (sw 301) ∧
      (∀ j, j < c'.nreg lsI →
        lsPr P J c.nmem (c.nreg (sw 300)) (c.nreg (sw 40)) ⟨c.nreg lsxE, c.nreg lsxH⟩ j) ∧
      (∀ j, c'.nreg lsI ≤ j → j < c.nreg (sw 301) →
        ¬ lsPr P J c.nmem (c.nreg (sw 300)) (c.nreg (sw 40)) ⟨c.nreg lsxE, c.nreg lsxH⟩ j) ∧
      (∀ r, bandOf r ∉ oracleBands → ¬ LSet r → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c.nreg ALLOC ≤ c'.nreg ALLOC ∧ (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a))

end

end S0C

end SweepIo

end Chazelle.Core
