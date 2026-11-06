module

public import Chazelle.Core.DownPhaseDrvRObl

/-!
# Down-phase driver: the contract of the host RAM (D3a)

**`HostRamSpec`**: a procedure that writes the host description `regHost li n N r` of region `r`
of the current interior normal form `N = buildNF I Q L E` (the description of
`DownPhaseDrvRObl`, about which `HostR1Spec` speaks) into fresh memory, as a `HostAt` block.  The
base case (D9) and the level body both call it once per region.

Registers (a reserved part of band `bDownDrv`, `215000 … 215999`):

* inputs: `215000` the handle of `N` (`NFAt`), `215001` the region `r`, `215002` the bit `li`
  (`1` iff `LeftInside (Qof P)`);
* outputs: `215010` the host handle `HB` (fresh: at or above the allocator on entry), `215011` the
  number of items, `215012` the number of host points (`(H.pts n).length`).

The procedure writes only the registers `215000 … 215999` of band `bDownDrv` (and the allocator),
the memory only at or above the allocator on entry (`Frame`), and costs a constant (the region has
at most `4` exit chords and `5` arcs, degree `≤ 4`).
-/

namespace Chazelle.Core

namespace DrvR

@[expose] public section

open Machine

/-- **The contract of the host RAM (D3a).**  For region `r` (register `215001`) of the normal form
`N = buildNF I Q L E` at the handle in register `215000` (valid sorted input, at least one chord,
degree `≤ 4`), with the `LeftInside` bit in register `215002`: a fresh `HostAt` block of
`regHost li n N r` at the handle in register `215010`, its item count in `215011` and its point
count in `215012`. -/
def HostRamSpec : Prop :=
  ∃ (s : Stmt) (κ : ℕ), Meets s {bDownDrv}
    (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧ c.nreg 215002 ≤ 1 ∧
      (c.nreg 215002 = 1 ↔ Mountain.LeftInside (Qof P)) ∧
      ∃ (L : List (ℕ × ℕ × ℕ)) (E : List ℕ), L ≠ [] ∧
        ChordTriplesOK (interiorModel (Qof P)) (Qof P) L ∧ E.Perm (List.range (2 * L.length)) ∧
        E.Pairwise (BuildNF.codeLe (interiorModel (Qof P)) (Qof P) L) ∧
        (interiorModel (Qof P)).DegLe
          ((BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E).F (interiorModel (Qof P))
            (Qof P)) 4 ∧
        NFWithin c.nmem (c.nreg 215000) (c.nreg ALLOC)
          (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E) ∧
        c.nreg 215001 < (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E).nRegions)
    (fun P c c' =>
      (∀ q, bandOf q = bDownDrv → (q < 215000 ∨ 216000 ≤ q) → c'.nreg q = c.nreg q) ∧
      ∀ (L : List (ℕ × ℕ × ℕ)) (E : List ℕ), L ≠ [] →
        ChordTriplesOK (interiorModel (Qof P)) (Qof P) L → E.Perm (List.range (2 * L.length)) →
        E.Pairwise (BuildNF.codeLe (interiorModel (Qof P)) (Qof P) L) →
        NFAt c.nmem (c.nreg 215000) (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E) →
        let H := regHost (decide (c.nreg 215002 = 1)) (Qof P).n
          (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E) (c.nreg 215001)
        c.nreg ALLOC ≤ c'.nreg 215010 ∧ c'.nreg 215010 + 3 * H.length + 1 ≤ c'.nreg ALLOC ∧
          HostAt c'.nmem (c'.nreg 215010) H ∧ c'.nreg 215011 = H.length ∧
          c'.nreg 215012 = (H.pts (Qof P).n).length)
    (fun _ _ => κ)

end

end DrvR

end Chazelle.Core
