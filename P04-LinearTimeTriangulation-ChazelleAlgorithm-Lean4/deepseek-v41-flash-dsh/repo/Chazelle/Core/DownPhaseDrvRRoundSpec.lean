module

public import Chazelle.Core.DownPhaseDrvRInv

/-!
# Down-phase driver: the contract of the restoration rounds (D8)

After the main step of a level (regions, leaves, merges, extraction, splice) the interior family
has degree at most `d₀ = D_H + 4`; the level ends with restoration rounds that bring the degree
back to `4` (design `docs/design-downphase-driver.md` §4.3).  **`RoundsSpec X F G H`** is their
contract, for interior oracles of costs `F`, `G`, `H` on the context `X`.

The state is the memory part of the level invariant (`StateAt`, registers `1 … 5` of `bDownDrv`,
as in `InvAt`): the interior model descriptor, the chord list `L`, its sorted event list `E` and
the normal form `buildNF I Q L E`, all robust below the allocator.

Registers (band `bDownDrv`): inputs `216000` the degree bound `d₀ ≥ 4`, `216001` the
semigranularity `γ` (`1 ≤ γ ≤ n - 1`, so the oracles serve it); `216000 … 216999` are reserved
for the rounds.  The rounds keep register `0`, register `1` and the registers `211000 … 215999`
and `217000 … 219999` of `bDownDrv` (the level driver's), and write only `drvBands`.

Post: a new state `(L', E')` whose family contains the old one, with degree `≤ 4`, still
`γ`-semigranular, and `K' + 1 ≤ 2^{d₀} (K + 1)` (`DownMath.round_ncard` per round).
Cost `κ d₀ · (K + 1) · F γ · G γ · (H γ + ⌈log₂ γ⌉ + 1)`.
-/

namespace Chazelle.Core

namespace DrvR

open Machine
open BuildNF (codeLe)
open SortL (seg)

@[expose] public section

/-- **The memory part of the level state** (registers `1 … 5` of `bDownDrv`, as in `InvAt`): the
interior model descriptor, the chord list `L`, its `codeLe`-sorted event list `E` and the normal
form `buildNF I Q L E`, all robust below the allocator; the triples are valid. -/
def StateAt (P : Polygon) (c : Config) (L : List (ℕ × ℕ × ℕ)) (E : List ℕ) : Prop :=
  rd c bDownDrv 1 + 6 ≤ c.nreg ALLOC ∧
    Robust (c.nreg ALLOC) c.nmem
      (fun m => ModelDescAt m (rd c bDownDrv 1) (Qof P) (interiorModel (Qof P))) ∧
    rd c bDownDrv 3 = L.length ∧
    rd c bDownDrv 2 + 3 * L.length ≤ c.nreg ALLOC ∧
    Robust (c.nreg ALLOC) c.nmem (fun m => ChordListAt m (rd c bDownDrv 2) L) ∧
    rd c bDownDrv 4 + 2 * L.length ≤ c.nreg ALLOC ∧
    Robust (c.nreg ALLOC) c.nmem (fun m => seg m (rd c bDownDrv 4) (2 * L.length) = E) ∧
    ChordTriplesOK (interiorModel (Qof P)) (Qof P) L ∧
    E.Perm (List.range (2 * L.length)) ∧
    E.Pairwise (codeLe (interiorModel (Qof P)) (Qof P) L) ∧
    NFWithin c.nmem (rd c bDownDrv 5) (c.nreg ALLOC)
      (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E)

/-- **The contract of the restoration rounds (D8)**, for interior oracles of costs `F`, `G`, `H`
on the context `X`. -/
def RoundsSpec (X : MemCtx) (F G H : ℕ → ℕ) : Prop :=
  ∃ (s : Stmt) (κ : ℕ → ℕ), Meets s drvBands
    (fun P W c => EnvD X P W c ∧ 4 ≤ c.nreg 216000 ∧ 1 ≤ c.nreg 216001 ∧
      c.nreg 216001 ≤ P.n - 1 ∧
      ∃ (L : List (ℕ × ℕ × ℕ)) (E : List ℕ), StateAt P c L E ∧
        (interiorModel (Qof P)).DegLe
          ((BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E).F (interiorModel (Qof P))
            (Qof P)) (c.nreg 216000) ∧
        (interiorModel (Qof P)).Semigranular
          ((BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E).F (interiorModel (Qof P))
            (Qof P)) (c.nreg 216001))
    (fun P c c' =>
      (∀ r, (r = 210000 ∨ r = 210001 ∨ 211000 ≤ r ∧ r < 216000 ∨ 217000 ≤ r ∧ r < 220000) →
        c'.nreg r = c.nreg r) ∧
      ∀ (L : List (ℕ × ℕ × ℕ)) (E : List ℕ), StateAt P c L E →
        ∃ (L' : List (ℕ × ℕ × ℕ)) (E' : List ℕ), StateAt P c' L' E' ∧
          (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E).F (interiorModel (Qof P)) (Qof P) ⊆
            (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L' E').F (interiorModel (Qof P))
              (Qof P) ∧
          (interiorModel (Qof P)).DegLe
            ((BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L' E').F (interiorModel (Qof P))
              (Qof P)) 4 ∧
          (interiorModel (Qof P)).Semigranular
            ((BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L' E').F (interiorModel (Qof P))
              (Qof P)) (c.nreg 216001) ∧
          L'.length + 1 ≤ 2 ^ c.nreg 216000 * (L.length + 1))
    (fun _ c => κ (c.nreg 216000) * (rd c bDownDrv 3 + 1) * F (c.nreg 216001) *
      G (c.nreg 216001) * (H (c.nreg 216001) + Nat.clog 2 (c.nreg 216001) + 1))

end

end DrvR

end Chazelle.Core
