module

public import Chazelle.Core.DownPhaseDrvXRamJ

/-!
# Down phase, extraction (D6): contracts of the remaining glue

The RAM of the extraction is verified up to the main loop (`loopS_exec`, under the facts
`XE P W v N NR ras A0 mem0` of a run, with the values `v : XV`).  Two pieces of pure glue remain:

* **`XEGlue`** (glue A): from the precondition of `DrvR.ExtractRamSpec` (for configuration `c`,
  with the room `c.nreg ALLOC + xKappa * (#chords of N_R + 1) ≤ W`), the facts `XE` of the run with
  the values `xvOf P c C N NR` and the arc list `rasOf N r`, and the memory facts and bounds of the
  set-up (`SetupFacts`).
* **`PostMath`** (glue B): for the hypotheses `XHyp` of a region and any values `v` that agree with
  the chain (`m, T, β`), the bit `li` and the host, the triple list `xL P v NR #chords` describes the
  kept chords exactly, without repetition, attached, in range, and every end lies on the closure of
  an arc of the region (`OnArcKey`).
-/

namespace Chazelle.Core

namespace DrvX

open Machine BuildNF
open DrvR (regHost keyBkt OnArcKey endPos)

@[expose] public section

/-- The cost constant of the extraction: `κ (K + 1)` steps for `K` chord records. -/
def xKappa : ℕ := 24100

/-- **The values of the run** read off the configuration `c` and the objects of the
precondition. -/
noncomputable def xvOf (P : Polygon) (c : Config) (C : Chain) (N NR : NF) : XV where
  m := C.m
  T := C.topIdx
  β := C.sideBeta
  li := decide (c.nreg 217002 = 1)
  H := regHost (decide (c.nreg 217002 = 1)) (Qof P).n N (c.nreg 217001)
  HB := c.nreg 217003
  K := NR.chords.length
  CB := c.nmem (c.nreg 217006 + 3)
  A := N.arcs.length
  AB := c.nmem (c.nreg 217000 + 4)
  nRA := (N.region (c.nreg 217001)).arcs.length
  RA := c.nmem (c.nreg 217000 + 7) +
    c.nmem (c.nmem (c.nreg 217000 + 5) + 5 * c.nreg 217001 + 1)
  LxB := c.nreg ALLOC
  BkB := c.nreg ALLOC + 3 * NR.chords.length

/-- The arc list of region `r`. -/
def rasOf (N : NF) (r : ℕ) : ℕ → ℕ := fun t => (N.region r).arcs.getD t 0

/-- **The memory facts and bounds of the set-up** (`MD = 217005`, `HB = 217003`,
`BN = 217000`, `BR = 217006`, `r = 217001`, `RB = mem (BN + 5)`). -/
def SetupFacts (P : Polygon) (W : ℕ) (c : Config) (C : Chain) (N NR : NF) : Prop :=
  c.nmem (c.nreg 217005 + 3) = C.m ∧ c.nmem (c.nreg 217005 + 4) = C.topIdx ∧
    (c.nmem (c.nreg 217005 + 5) = 1 ↔ C.sideBeta = true) ∧
    c.nmem (c.nreg 217003) = (xvOf P c C N NR).H.length ∧
    c.nmem (c.nreg 217006) = NR.chords.length ∧
    c.nmem (c.nreg 217000 + 1) = N.arcs.length ∧
    c.nmem (c.nmem (c.nreg 217000 + 5) + 5 * c.nreg 217001) =
      (N.region (c.nreg 217001)).arcs.length ∧
    P.n ≤ W ∧ c.nreg 217005 + 5 ≤ W ∧ 2 * C.m + 6 ≤ W ∧ c.nreg 217003 + 1 ≤ W ∧
    c.nreg 217006 + 3 ≤ W ∧ c.nreg 217000 + 7 ≤ W ∧
    c.nmem (c.nreg 217000 + 5) + 5 * c.nreg 217001 + 1 ≤ W ∧
    (xvOf P c C N NR).RA ≤ W ∧ 7 ≤ W

/-- **Glue A**: the facts of the run from the precondition of `DrvR.ExtractRamSpec`. -/
def XEGlue : Prop :=
  ∀ (P : Polygon) (W : ℕ) (c : Config) (L : List (ℕ × ℕ × ℕ)) (E : List ℕ) (C : Chain) (NR : NF),
    GoodEnv P → hostWords P.n ≤ W → c.nreg 217002 ≤ 1 →
    (c.nreg 217002 = 1 ↔ Mountain.LeftInside (Qof P)) → L ≠ [] →
    ChordTriplesOK (interiorModel (Qof P)) (Qof P) L → E.Perm (List.range (2 * L.length)) →
    E.Pairwise (codeLe (interiorModel (Qof P)) (Qof P) L) →
    (interiorModel (Qof P)).DegLe
      ((buildNF (interiorModel (Qof P)) (Qof P) L E).F (interiorModel (Qof P)) (Qof P)) 4 →
    NFWithin c.nmem (c.nreg 217000) (c.nreg ALLOC) (buildNF (interiorModel (Qof P)) (Qof P) L E) →
    c.nreg 217001 < (buildNF (interiorModel (Qof P)) (Qof P) L E).nRegions →
    Robust (c.nreg ALLOC) c.nmem (fun m => HostAt m (c.nreg 217003)
      (regHost (decide (c.nreg 217002 = 1)) (Qof P).n
        (buildNF (interiorModel (Qof P)) (Qof P) L E) (c.nreg 217001))) →
    c.nreg 217003 + 3 * (regHost (decide (c.nreg 217002 = 1)) (Qof P).n
        (buildNF (interiorModel (Qof P)) (Qof P) L E) (c.nreg 217001)).length + 1 ≤
      c.nreg ALLOC →
    C.P = (regHost (decide (c.nreg 217002 = 1)) (Qof P).n
      (buildNF (interiorModel (Qof P)) (Qof P) L E) (c.nreg 217001)).poly (Qof P) →
    C.s = 0 → C.m + 1 = C.P.n →
    ModelDescWF P (c.nreg ALLOC) c.nmem (c.nreg 217005) →
    Robust (c.nreg ALLOC) c.nmem (fun m => ModelDescAt m (c.nreg 217005) (Qof P) (chainModel C)) →
    Robust (c.nreg ALLOC) c.nmem (fun m => ChainDescAt m (c.nreg 217005 + 1) (Qof P)
      (regHost (decide (c.nreg 217002 = 1)) (Qof P).n
        (buildNF (interiorModel (Qof P)) (Qof P) L E) (c.nreg 217001)) C) →
    NFWithin c.nmem (c.nreg 217006) (c.nreg ALLOC) NR → IsNF (chainModel C) (Qof P) NR →
    c.nreg ALLOC + xKappa * (c.nmem (c.nreg 217006) + 1) ≤ W →
    XE P W (xvOf P c C (buildNF (interiorModel (Qof P)) (Qof P) L E) NR)
        (buildNF (interiorModel (Qof P)) (Qof P) L E) NR
        (rasOf (buildNF (interiorModel (Qof P)) (Qof P) L E) (c.nreg 217001)) (c.nreg ALLOC)
        c.nmem ∧
      SetupFacts P W c C (buildNF (interiorModel (Qof P)) (Qof P) L E) NR

/-- **Glue B**: the triples of the kept chord records describe the kept chords. -/
def PostMath : Prop :=
  ∀ (P : Polygon) (li : Bool) (L : List (ℕ × ℕ × ℕ)) (E : List ℕ) (reg : ℕ → Set Point) (r : ℕ)
    (C : Chain) (NR : NF) (v : XV), XHyp P li L E reg r C NR →
    v.m = C.m → v.T = C.topIdx → v.β = C.sideBeta → v.li = li →
    v.H = regHost li (Qof P).n (buildNF (interiorModel (Qof P)) (Qof P) L E) r →
    {x | ∃ y ∈ xL P v NR NR.chords.length, x = (recOf y).toSet (interiorModel (Qof P)) (Qof P)} =
        Extract.kept (reg r) (NR.F (chainModel C) (Qof P)) ∧
      ((xL P v NR NR.chords.length).map
        fun y => (recOf y).toSet (interiorModel (Qof P)) (Qof P)).Nodup ∧
      (∀ y ∈ xL P v NR NR.chords.length,
        (recOf y).Attached (interiorModel (Qof P)) (Qof P) ∧ y.1 < (Qof P).n) ∧
      ∀ q, q < 2 * (xL P v NR NR.chords.length).length →
        ∃ j ∈ ((buildNF (interiorModel (Qof P)) (Qof P) L E).region r).arcs,
          OnArcKey (Qof P) (buildNF (interiorModel (Qof P)) (Qof P) L E) j
            (endPos (xL P v NR NR.chords.length) q)

end

end DrvX

end Chazelle.Core
