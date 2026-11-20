module

public import Chazelle.Core.DownPhaseDrvRHostSpec

/-!
# Down-phase driver: the contract of the extraction (D6)

In one level, after the merges, region `r` of the current interior normal form
`N = buildNF I Q L E` has a canonical normal form `N_R` in the chain model of its host chain
`C = ⟨H.poly Q, 0, #points - 1⟩`, `H = regHost li n N r` (`HostRamSpec`).  The extraction keeps
the chords of `N_R` that meet the region (`Extract.kept`) and writes them as interior chord
triples, with the bucket of each end for the splice (design §4.2 (f), (g)).

**`keyBkt Q N x`**: the bucket of a walk position: twice the number of arc starts of `N` with a
smaller key, plus one if some arc start has the same key.  It is monotone in the key, so
buckets are ordered like `codeLe` (the splice's requirement, `SplPre`).

**`ExtractRamSpec`**.  Registers (band `bDownDrv`, `217000 … 217999` reserved): inputs `217000`
the handle of `N`, `217001` the region `r`, `217002` the bit `li`, `217003` the host handle
`HB` (`HostAt`), `217004` the number of host points, `217005` the model descriptor of `C`
(`m MD = 0`, the chain descriptor of `C` itself, with its top index and orientation bit, at
`MD + 1`), `217006` the handle of `N_R`; outputs (fresh memory)
`217010` the triple list `Lx` (three words per triple), `217011` its length, `217012` the bucket
list (two words per triple: the buckets of the left and of the right end).
-/

namespace Chazelle.Core

namespace DrvR

@[expose] public section

open Machine

/-- **The bucket of a walk position** for the splice into `N`: `2 · #{arc starts with a smaller
key} + [some arc start has the same key]`. -/
noncomputable def keyBkt (Q : Polygon) (N : NF) (x : WPos) : ℕ := by
  classical
  exact 2 * ((List.range N.arcs.length).filter fun j =>
      decide ((interiorModel Q).key Q (N.arc j).s < (interiorModel Q).key Q x)).length +
    if ∃ j, j < N.arcs.length ∧ (interiorModel Q).key Q (N.arc j).s = (interiorModel Q).key Q x
    then 1 else 0

/-- The position lies on the closure of arc `j` of `N` (cyclically, by keys). -/
def OnArcKey (Q : Polygon) (N : NF) (j : ℕ) (x : WPos) : Prop :=
  (interiorModel Q).key Q x = (interiorModel Q).key Q (N.arc j).s ∨
    (interiorModel Q).key Q x = (interiorModel Q).key Q (N.arc j).e ∨
    Chazelle.Chain.sideInArc ((interiorModel Q).key Q (N.arc j).s)
      ((interiorModel Q).key Q (N.arc j).e) ((interiorModel Q).key Q x)

/-- The two end positions of a chord triple (`q` even: left end). -/
def endPos (Lx : List (ℕ × ℕ × ℕ)) (q : ℕ) : WPos :=
  if q % 2 = 0 then (recOf (Lx.getD (q / 2) (0, 0, 0))).lpos
  else (recOf (Lx.getD (q / 2) (0, 0, 0))).rpos

/-- **The contract of the extraction (D6).** -/
def ExtractRamSpec : Prop :=
  ∃ (s : Stmt) (κ : ℕ), Meets s {bDownDrv, bSign, bLocate, bBuild, bSort}
    (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧ c.nreg 217002 ≤ 1 ∧
      (c.nreg 217002 = 1 ↔ Mountain.LeftInside (Qof P)) ∧
      ∃ (L : List (ℕ × ℕ × ℕ)) (E : List ℕ) (C : Chain) (NR : NF), L ≠ [] ∧
        ChordTriplesOK (interiorModel (Qof P)) (Qof P) L ∧ E.Perm (List.range (2 * L.length)) ∧
        E.Pairwise (BuildNF.codeLe (interiorModel (Qof P)) (Qof P) L) ∧
        (interiorModel (Qof P)).DegLe
          ((BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E).F (interiorModel (Qof P))
            (Qof P)) 4 ∧
        NFWithin c.nmem (c.nreg 217000) (c.nreg ALLOC)
          (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E) ∧
        c.nreg 217001 < (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E).nRegions ∧
        Robust (c.nreg ALLOC) c.nmem (fun m => HostAt m (c.nreg 217003)
          (regHost (decide (c.nreg 217002 = 1)) (Qof P).n
            (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E) (c.nreg 217001))) ∧
        c.nreg 217003 + 3 * (regHost (decide (c.nreg 217002 = 1)) (Qof P).n
            (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E) (c.nreg 217001)).length + 1 ≤
          c.nreg ALLOC ∧
        c.nreg 217004 = ((regHost (decide (c.nreg 217002 = 1)) (Qof P).n
          (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E) (c.nreg 217001)).pts
            (Qof P).n).length ∧
        C.P = (regHost (decide (c.nreg 217002 = 1)) (Qof P).n
          (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E) (c.nreg 217001)).poly (Qof P) ∧
        C.s = 0 ∧ C.m + 1 = C.P.n ∧
        ModelDescWF P (c.nreg ALLOC) c.nmem (c.nreg 217005) ∧
        Robust (c.nreg ALLOC) c.nmem (fun m => ModelDescAt m (c.nreg 217005) (Qof P)
          (chainModel C)) ∧
        Robust (c.nreg ALLOC) c.nmem (fun m => ChainDescAt m (c.nreg 217005 + 1) (Qof P)
          (regHost (decide (c.nreg 217002 = 1)) (Qof P).n
            (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E) (c.nreg 217001)) C) ∧
        NFWithin c.nmem (c.nreg 217006) (c.nreg ALLOC) NR ∧ IsNF (chainModel C) (Qof P) NR)
    (fun P c c' =>
      (∀ q, bandOf q = bDownDrv → (q < 217000 ∨ 218000 ≤ q) → c'.nreg q = c.nreg q) ∧
      ∀ (L : List (ℕ × ℕ × ℕ)) (E : List ℕ) (C : Chain) (NR : NF) (reg : ℕ → Set Point),
        L ≠ [] → ChordTriplesOK (interiorModel (Qof P)) (Qof P) L →
        E.Perm (List.range (2 * L.length)) →
        E.Pairwise (BuildNF.codeLe (interiorModel (Qof P)) (Qof P) L) →
        NFAt c.nmem (c.nreg 217000) (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E) →
        Restore.NFRegs (interiorModel (Qof P)) (Qof P)
          (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E) reg →
        C.P = (regHost (decide (c.nreg 217002 = 1)) (Qof P).n
          (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E) (c.nreg 217001)).poly (Qof P) →
        C.s = 0 → C.m + 1 = C.P.n → NFAt c.nmem (c.nreg 217006) NR →
        IsNF (chainModel C) (Qof P) NR →
        ∃ Lx : List (ℕ × ℕ × ℕ),
          c.nreg ALLOC ≤ c'.nreg 217010 ∧ c'.nreg 217010 + 3 * Lx.length ≤ c'.nreg ALLOC ∧
          c.nreg ALLOC ≤ c'.nreg 217012 ∧ c'.nreg 217012 + 2 * Lx.length ≤ c'.nreg ALLOC ∧
          c'.nreg 217011 = Lx.length ∧ ChordListAt c'.nmem (c'.nreg 217010) Lx ∧
          {x | ∃ y ∈ Lx, x = (recOf y).toSet (interiorModel (Qof P)) (Qof P)} =
            Extract.kept (reg (c.nreg 217001)) (NR.F (chainModel C) (Qof P)) ∧
          (Lx.map fun y => (recOf y).toSet (interiorModel (Qof P)) (Qof P)).Nodup ∧
          (∀ y ∈ Lx, (recOf y).Attached (interiorModel (Qof P)) (Qof P) ∧ y.1 < (Qof P).n) ∧
          ∀ q, q < 2 * Lx.length →
            c'.nmem (c'.nreg 217012 + q) = keyBkt (Qof P)
              (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E) (endPos Lx q) ∧
            ∃ j ∈ ((BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E).region
                (c.nreg 217001)).arcs,
              OnArcKey (Qof P) (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E) j
                (endPos Lx q))
    (fun _ c => κ * (c.nmem (c.nreg 217006) + 1))

end

end DrvR

end Chazelle.Core
