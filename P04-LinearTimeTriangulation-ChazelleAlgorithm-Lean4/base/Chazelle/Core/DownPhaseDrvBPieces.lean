module

public import Chazelle.Core.DownPhaseDrvBEnv

/-!
# Down-phase base (D9): contracts of two pieces of the region loop

Two self-contained pieces of `DrvB.RegLoopSpec` (the rest is the region loop of the base case):

* **`ExpSpec`** (RAM): the expansion of a host block (`HostAt`, layout of `SpecRam`) into the
  point array of the walk-order points `wlist li (H.pts n)` (`PtArrB`: three words per point,
  kind `0` vertex / `1` edge point, then the indices).
* **`BktMathSpec`** (mathematics): the splice preconditions of the region-loop output (`RegPost`
  fields `len`, `bkle`, `bkmono`, `bcnt`) from the bucket invariant of the tagged records
  (`DrvD.BktOK` for `K > 0`, buckets `0` for `K = 0`) and a bound `MX` on the points of a region.
-/

namespace Chazelle.Core

namespace DrvB

open Machine Machine.Stmt
open BuildNF (codeLe)
open BuildRam (FrameM)

@[expose] public section

/-- A symbolic point at `a` in memory (kind `0` vertex, `1` edge point, then its indices). -/
def PtAtB (m : ℕ → ℕ) (a : ℕ) : SymPt → Prop
  | .vtx i => m a = 0 ∧ m (a + 1) = i
  | .onEdge e h => m a = 1 ∧ m (a + 1) = e ∧ m (a + 2) = h

/-- **The point array** at `PA`: point `k` of `l` at `PA + 3 k`. -/
def PtArrB (m : ℕ → ℕ) (PA : ℕ) (l : List SymPt) : Prop :=
  ∀ k, k < l.length → PtAtB m (PA + 3 * k) (l.getD k (.vtx 0))

/-- **The expansion of a host block** (RAM): the host `H` at `HB = r212022` (`HostAt`, well
formed, `r212021 = H.length` items, `r212016 = (H.pts n).length` points) is expanded into the
point array of `wlist li (H.pts n)` at `PA = r212015` (`li` the bit in `r212011`; `r212010 = n`,
constants `r212000 = 1`, `r212001 = 0`, `r212002 = 2`).  The host block lies below `PA`, the
array fits below `W`.  Only the memory `[PA, PA + 3 NP)` and the registers
`212023 … 212031` are written; cost `κ (NP + |H| + 1)`. -/
def ExpSpec : Prop :=
  ∃ (s : Stmt) (κ : ℕ), ∀ (P : Polygon) (W : ℕ) (c : Config) (H : Host) (li : Bool),
    WordsBounded W c → HostAt c.nmem (c.nreg 212022) H → HostWF P.n H →
    c.nreg 212021 = H.length → c.nreg 212016 = (H.pts P.n).length →
    c.nreg 212011 = (if li then 1 else 0) → c.nreg 212010 = P.n →
    c.nreg 212000 = 1 → c.nreg 212001 = 0 → c.nreg 212002 = 2 →
    c.nreg 212022 + 3 * H.length + 1 ≤ c.nreg 212015 →
    c.nreg 212015 + 3 * (H.pts P.n).length ≤ W →
    ∃ c' k, Exec P W s c c' k ∧ k ≤ κ * ((H.pts P.n).length + H.length + 1) ∧
      PtArrB c'.nmem (c.nreg 212015) (wlist li (H.pts P.n)) ∧
      (∀ a, (a < c.nreg 212015 ∨ c.nreg 212015 + 3 * (H.pts P.n).length ≤ a) →
        c'.nmem a = c.nmem a) ∧
      FrameM (fun r => decide (212023 ≤ r ∧ r ≤ 212031)) c c'

/-- **The splice preconditions of the region-loop output** (mathematics): for the data of the
region loop (`BEnv`, `BGood`), buckets `bk` of the tagged records `TL (K + 1)` (`DrvD.BktOK` for
`K > 0`, `0` for `K = 0`) and a bound `MX` on the points of every region: the new chords
`newLB` number at most `2 n`, the buckets are at most the number of arcs, ordered by the event
comparator, and hold at most `4 MX` codes each. -/
def BktMathSpec : Prop :=
  ∀ (E : BEnv), BGood E → ∀ (bk : ℕ → ℕ) (MX : ℕ),
    (0 < E.K → DrvD.BktOK E.I E.Q E.N (E.TL (E.K + 1)) bk) →
    (E.K = 0 → ∀ q, q < 2 * (E.TL (E.K + 1)).length → bk q = 0) →
    (∀ r, r < E.K + 1 → (E.pts r).length ≤ MX) →
    (newLB E.li E.Q E.L E.E).length ≤ 2 * E.P.n ∧
    (∀ q, q < 2 * (newLB E.li E.Q E.L E.E).length → bk q ≤ E.N.arcs.length) ∧
    (∀ q q', q < 2 * (newLB E.li E.Q E.L E.E).length →
      q' < 2 * (newLB E.li E.Q E.L E.E).length → bk q < bk q' →
      codeLe E.I E.Q (E.L ++ newLB E.li E.Q E.L E.E) (2 * E.L.length + q) (2 * E.L.length + q')) ∧
    (∀ b, DrvR.bcnt bk (2 * (newLB E.li E.Q E.L E.E).length) b ≤ 4 * MX)

end

end DrvB

end Chazelle.Core
