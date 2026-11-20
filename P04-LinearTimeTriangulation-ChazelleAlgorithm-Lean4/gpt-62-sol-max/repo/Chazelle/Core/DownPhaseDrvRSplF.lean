module

public import Chazelle.Core.DownPhaseDrvRSplE

/-!
# Down-phase driver (RAM side): the splice as a `Meets` judgement

**`splice_meets`**: for a program `sB` meeting `BuildNFSortedSpec` (`SortedMeets`), the splice
`splS sB` adds the new chords `L₂` (registers `210020`, `210021` of `bDownDrv`, with the bucket
of every new event code at `r210022`, buckets `≤ r210023`, of at most `r210024` codes each, and
ordered by the event comparator) to the chord list `L` (`210002`, `210003`) with its sorted event
list `E` (`210004`), and writes the normal form of the result (`210005`), in
`κ (K + K₂ + A + 1) (⌈log₂ Mb⌉ + 1)` steps.
-/

namespace Chazelle.Core

namespace DrvR

open Machine Machine.Stmt Programs SortL BuildRam SignK
open BuildNF (codeLe)

@[expose] public section

/-- The bucket of new event code `2K + q`. -/
def bkOf (c : Config) (q : ℕ) : ℕ := c.nmem (rd c bDownDrv 22 + q)

/-- **The precondition of the splice.** -/
def SplPre (P : Polygon) (W : ℕ) (c : Config) : Prop :=
  GoodEnv P ∧ hostWords P.n ≤ W ∧ ModelDescWF P (c.nreg ALLOC) c.nmem (rd c bDownDrv 1) ∧
  ∃ (M : Model) (L L₂ : List (ℕ × ℕ × ℕ)) (E : List ℕ),
    ModelDescAt c.nmem (rd c bDownDrv 1) (Qof P) M ∧ GoodModel M ∧
    rd c bDownDrv 3 = L.length ∧ rd c bDownDrv 2 + 3 * L.length ≤ c.nreg ALLOC ∧
    ChordListAt c.nmem (rd c bDownDrv 2) L ∧
    rd c bDownDrv 21 = L₂.length ∧ rd c bDownDrv 20 + 3 * L₂.length ≤ c.nreg ALLOC ∧
    ChordListAt c.nmem (rd c bDownDrv 20) L₂ ∧
    ChordTriplesOK M (Qof P) (L ++ L₂) ∧
    rd c bDownDrv 4 + 2 * L.length ≤ c.nreg ALLOC ∧
    seg c.nmem (rd c bDownDrv 4) (2 * L.length) = E ∧
    E.Perm (List.range (2 * L.length)) ∧ E.Pairwise (codeLe M (Qof P) L) ∧
    rd c bDownDrv 22 + 2 * L₂.length ≤ c.nreg ALLOC ∧
    (∀ q, q < 2 * L₂.length → bkOf c q ≤ rd c bDownDrv 23) ∧
    (∀ q q', q < 2 * L₂.length → q' < 2 * L₂.length → bkOf c q < bkOf c q' →
      codeLe M (Qof P) (L ++ L₂) (2 * L.length + q) (2 * L.length + q')) ∧
    (∀ b, bcnt (bkOf c) (2 * L₂.length) b ≤ rd c bDownDrv 24)

/-- **The postcondition of the splice.** -/
def SplPost (P : Polygon) (c c' : Config) : Prop :=
  (∀ r, (210000 ≤ r ∧ r < 210002 ∨ 210006 ≤ r ∧ r < 210025 ∨ 210074 ≤ r ∧ r < 220000) →
    c'.nreg r = c.nreg r) ∧
  ∀ (M : Model) (L L₂ : List (ℕ × ℕ × ℕ)), ModelDescAt c.nmem (rd c bDownDrv 1) (Qof P) M →
    rd c bDownDrv 3 = L.length → ChordListAt c.nmem (rd c bDownDrv 2) L →
    rd c bDownDrv 21 = L₂.length → ChordListAt c.nmem (rd c bDownDrv 20) L₂ →
    rd c' bDownDrv 3 = L.length + L₂.length ∧
    c.nreg ALLOC ≤ rd c' bDownDrv 2 ∧
    rd c' bDownDrv 2 + 3 * (L.length + L₂.length) ≤ c'.nreg ALLOC ∧
    ChordListAt c'.nmem (rd c' bDownDrv 2) (L ++ L₂) ∧
    c.nreg ALLOC ≤ rd c' bDownDrv 4 ∧
    rd c' bDownDrv 4 + 2 * (L.length + L₂.length) ≤ c'.nreg ALLOC ∧
    (seg c'.nmem (rd c' bDownDrv 4) (2 * (L.length + L₂.length))).Perm
      (List.range (2 * (L.length + L₂.length))) ∧
    (seg c'.nmem (rd c' bDownDrv 4) (2 * (L.length + L₂.length))).Pairwise
      (codeLe M (Qof P) (L ++ L₂)) ∧
    c.nreg ALLOC ≤ rd c' bDownDrv 5 ∧
    NFWithin c'.nmem (rd c' bDownDrv 5) (c'.nreg ALLOC)
      (BuildNF.buildNF M (Qof P) (L ++ L₂)
        (seg c'.nmem (rd c' bDownDrv 4) (2 * (L.length + L₂.length))))

/-- The cost constant of the splice. -/
def κSpl (κB : ℕ) : ℕ := 120000 + κB

/-- **The cost of the splice.** -/
def splCost (κB : ℕ) (c : Config) : ℕ :=
  κSpl κB * (rd c bDownDrv 3 + rd c bDownDrv 21 + rd c bDownDrv 23 + 1) *
    (Nat.clog 2 (rd c bDownDrv 24) + 1)

end

end DrvR

end Chazelle.Core
