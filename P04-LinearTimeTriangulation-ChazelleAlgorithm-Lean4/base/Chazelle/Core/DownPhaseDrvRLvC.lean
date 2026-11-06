module

public import Chazelle.Core.DownPhaseDrvRLvB
public import Chazelle.Core.DownPhaseDrvRRoundSpec

/-!
# Down-phase driver (RAM side): one level, the contracts of the components for one program

`HostMeets`, `RegMeets`, `ExtMeets`, `RoundMeets`: the `Meets` statements of `HostRamSpec`,
`RegionSpec`, `ExtractRamSpec`, `RoundsSpec` for a fixed program (definitionally the bodies of the
contracts; `*_of` unpack the contracts).
-/

namespace Chazelle.Core

namespace DrvR

open Machine

@[expose] public section

/-- The `Meets` statement of `HostRamSpec` for one program. -/
def HostMeets (s : Stmt) (κ : ℕ) : Prop :=
  Meets s {bDownDrv}
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

theorem hostMeets_of (h : HostRamSpec) : ∃ s κ, HostMeets s κ := h

/-- The `Meets` statement of `RegionSpec` for one program. -/
def RegMeets (O : OracleIface) (s : Stmt) (κ : ℕ) : Prop :=
  Meets s drvBands
    (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧
      (gradeCtx O).holds P c.nmem (c.nreg 219205) (c.nreg ALLOC) ∧
      7 ≤ c.nreg 219202 ∧ c.nreg 219202 ≤ c.nmem (c.nreg 219205) ∧
      c.nreg 219203 = 2 ^ c.nreg 219202 ∧
      2 * gradeGran (c.nreg 219202) ≤ c.nreg 219204 ∧ 128 ≤ c.nreg 219204 ∧
      c.nreg 219204 ≤ 4096 * 2 ^ Cost.ceilBeta (c.nreg 219202) ∧
      c.nreg 219204 + 129 ≤ (gradeCtx O).cap P c.nmem (c.nreg 219205) ∧
      ∃ H : Host, Robust (c.nreg ALLOC) c.nmem (fun m => HostAt m (c.nreg 219200) H) ∧
        c.nreg 219200 + 3 * H.length + 1 ≤ c.nreg ALLOC ∧
        H.length ≤ 20 ∧ HostWF (Qof P).n H ∧ HostRegular (Qof P).n H ∧
        (H.poly (Qof P)).Simple ∧
        c.nreg 219201 = (H.pts (Qof P).n).length ∧ 3 ≤ c.nreg 219201 ∧
        ∀ a ℓ, HostItem.run a ℓ ∈ H → ℓ ≤ 2 * c.nreg 219203)
    (fun P c c' =>
      (∀ q, bandOf q = bDownDrv → (q < 218000 ∨ 220000 ≤ q) → c'.nreg q = c.nreg q) ∧
      c.nreg ALLOC ≤ c'.nreg 219210 ∧ c.nreg ALLOC ≤ c'.nreg 219211 ∧
      c.nreg 219204 ≤ c'.nreg 219212 ∧ c'.nreg 219212 ≤ c.nreg 219204 + 128 ∧
      ModelDescWF P (c'.nreg ALLOC) c'.nmem (c'.nreg 219210) ∧
      ∀ (H : Host) (C : Chain), HostAt c.nmem (c.nreg 219200) H → C.P = H.poly (Qof P) →
        C.s = 0 → C.m + 1 = C.P.n →
        Robust (c'.nreg ALLOC) c'.nmem
          (fun m => m (c'.nreg 219210) = 0 ∧
            ChainDescAt m (c'.nreg 219210 + 1) (Qof P) H C ∧
            m (c'.nreg 219210 + 1) = c.nreg 219200) ∧
        ∃ N, NFWithin c'.nmem (c'.nreg 219211) (c'.nreg ALLOC) N ∧
          IsCanonicalNF (chainModel C) (Qof P) N (c'.nreg 219212) regCap)
    (fun _ c => κ * (lemma41Nat (c.nreg 219202) + 1))

theorem regMeets_of {O : OracleIface} (h : RegionSpec O) : ∃ s κ, RegMeets O s κ := h

/-- The `Meets` statement of `ExtractRamSpec` for one program. -/
def ExtMeets (s : Stmt) (κ : ℕ) : Prop :=
  Meets s {bDownDrv, bSign, bLocate, bBuild, bSort}
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

theorem extMeets_of (h : ExtractRamSpec) : ∃ s κ, ExtMeets s κ := h

end

end DrvR

end Chazelle.Core
