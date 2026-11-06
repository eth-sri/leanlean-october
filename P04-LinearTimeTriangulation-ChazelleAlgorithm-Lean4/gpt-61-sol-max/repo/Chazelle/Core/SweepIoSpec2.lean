module

public import Chazelle.Core.SweepIoSpec
public import Chazelle.Core.SweepSpecH

/-!
# The sweep RAM (WP-D), answers: contracts of the query pipeline, the query loop, the assembly

The answer phase runs from a base configuration `c₀` (`ABase`: `AEnv`, the side `i` in `sSide =
sw 98`, the query list `L` at `sw 8` (`sw 9 = L.length`), the result base `sw 11 = ALLOC`, the
facts of the queries, and the auxiliary fact `Aux` of the side-0 initialisation).

* `QrySpec Aux` (`SweepIo`): the per-query procedure: from the loop registers `pJ = j`,
  `pA = sw 8 + 3 j`, `pR = sw 11 + 4 j` (the result slot `j`, allocated), it writes a record `r`
  with `SeesInWhole J (Qof P) i (L.getD j _) r` into the slot; it keeps the registers
  `sw 5000 … 5999` and the memory below the allocator outside the slot.  Cost `qCost`.
* `LoopSpec Aux`: the query loop: from `c₀`, allocate the `4 L` result words at `sw 11` and run
  the per-query procedure for `j < L.length`; the result list `R` with `SeesInWhole`.  Cost
  `loopCost` (the brute-force queries of side `1` are at most `5`: `TopCountSpec`, `L₁.length ≤ 3`).
  To be proved from `QrySpec Aux` and `TopCountSpec`.
* `AsmGoal`: `SweepSpecH` from `SweepEvSpec`, a side-0 initialisation (`InitSpec`) and the loop
  (`LoopSpec`): the program saves `sw 7` into `sSide`, sets `sw 7 := 0`, runs stage 0 (`initS`),
  stages 2/3 (`SweepEvSpec`), the initialisation of the answers (constants `K0 … K6` at
  `sw 610 … 616` (`Consts`), the table of powers at `TBR = sw 600` of length `TLR = sw 601`
  with the bounds of `AEnv`/`ABase`, `init0` for side `0`, `sw 11 := ALLOC`), then the loop.
  The fields `AEnv.hmd₁`, `AEnv.hmd₂` (the model descriptors at `sw 30`, `sw 31` hold copies of
  the chain descriptors at `sw 20`, `sw 21`) hold after stage 0 (`mdBlk_exec`), or the
  initialisation re-creates the two model descriptors (`copyDesc_exec`).

Registers of the loop: `pJ pA pR = sw 5000 … 5002`, free: `sw 5003 … 5999`.
-/

namespace Chazelle.Core

namespace SweepIo

open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed Sweep
open Chazelle.Visibility (rayPt)
open Chazelle.Merge (FreeAt)

@[expose] public section

/-- The side of the queries (saved `sw 7`; fixed in the answer phase). -/
def sSide : ℕ := sw 98

/-- The loop registers: the query index, the query address, the result address. -/
def pJ : ℕ := sw 5000
def pA : ℕ := sw 5001
def pR : ℕ := sw 5002

/-- **The base configuration of the answer phase.** -/
structure ABase (P : Polygon) (W : ℕ) (X : MemCtx) (Ok : Polygon → Model → Prop)
    (Aux : Polygon → Merge.Junction → NF → Config → Prop) (J : Merge.Junction) (H : Host)
    (N₁ N₂ : NF) (E : ℕ) (L : List (ℕ × ℕ × ℕ)) (i : ℕ) (c₀ : Config) : Prop where
  hw : WordsBounded W c₀
  hA : AEnv P W X Ok J H N₁ N₂ E c₀
  hi : i ≤ 1
  hside : c₀.nreg sSide = i
  hAux : i = 0 → Aux P J N₂ c₀
  hLn : c₀.nreg (sw 9) = L.length
  hLm : c₀.nreg (sw 8) + 3 * L.length ≤ c₀.nreg ALLOC
  hLat : ChordListAt c₀.nmem (c₀.nreg (sw 8)) L
  hq : ∀ q ∈ L, QueryOK J (Qof P) i q
  hht : ∀ q ∈ L, ((chainModel (sideChain J i)).pos (Qof P) ⟨q.1, q.2.1⟩).2 =
    ((Qof P).vtx (q.2.1 - 1)).2
  hend : i = 1 → ∃ L₁ : List (ℕ × ℕ × ℕ), L = sweepEndQ N₂.chords ++ L₁ ∧ L₁.length ≤ 3
  hres : c₀.nreg (sw 11) = c₀.nreg ALLOC
  hTLR : c₀.nreg TLR ≤ Nat.clog 2 (N₁.nChords + N₂.nChords + 1) + 6

/-- The point of the query `j`. -/
noncomputable def qPt (J : Merge.Junction) (P : Polygon) (i : ℕ) (L : List (ℕ × ℕ × ℕ)) (j : ℕ) :
    Point :=
  (chainModel (sideChain J i)).pos (Qof P) ⟨(L.getD j (0, 0, 0)).1, (L.getD j (0, 0, 0)).2.1⟩

open Classical in
/-- **The cost of the query `j`**: `κ D (F γ + TLR + 1)`, plus `κ D (A₁ + 1) (F γ + 1)` for a
brute-force query of side `1`. -/
noncomputable def qCost (κ F : ℕ → ℕ) (c₀ : Config) (J : Merge.Junction) (P : Polygon)
    (N₁ N₂ : NF) (L : List (ℕ × ℕ × ℕ)) (i j : ℕ) : ℕ :=
  κ (c₀.nreg (sw 6)) * (F (c₀.nreg (sw 5)) + c₀.nreg TLR + 1) +
    (if i = 1 ∧ BruteQ J N₂ j (qPt J P i L j) then
      κ (c₀.nreg (sw 6)) * (N₁.arcs.length + 1) * (F (c₀.nreg (sw 5)) + 1) else 0)

/-- **The per-query procedure** (`qry sh`) for the query `j`, from the loop registers. -/
def QrySpec (Aux : Polygon → Merge.Junction → NF → Config → Prop) : Prop :=
  ∃ (qry : Stmt → Stmt) (κq : ℕ → ℕ), ∀ (sh : Stmt) (Bs : Finset ℕ) (F : ℕ → ℕ) (X : MemCtx)
    (Ok : Polygon → Model → Prop), ShooterOK sh Bs F X Ok → Bs ⊆ oracleBands → X.CapLocal →
    ∀ (P : Polygon) (W : ℕ) (c₀ c : Config) (J : Merge.Junction) (H : Host) (N₁ N₂ : NF)
      (E : ℕ) (L : List (ℕ × ℕ × ℕ)) (i j : ℕ),
      ABase P W X Ok Aux J H N₁ N₂ E L i c₀ → IInv W c₀ c →
      c.nreg pJ = j → j < L.length → c.nreg pA = c₀.nreg (sw 8) + 3 * j →
      c.nreg pR = c₀.nreg (sw 11) + 4 * j → c.nreg pR + 4 ≤ c.nreg ALLOC →
      c.nreg ALLOC + qCost κq F c₀ J P N₁ N₂ L i j ≤ W →
      IRS P W c₀ (qry sh) c (qCost κq F c₀ J P N₁ N₂ L i j) (fun c' =>
        (∃ r : ℕ × ℕ × ℕ × ℕ, c'.nmem (c.nreg pR) = r.1 ∧ c'.nmem (c.nreg pR + 1) = r.2.1 ∧
          c'.nmem (c.nreg pR + 2) = r.2.2.1 ∧ c'.nmem (c.nreg pR + 3) = r.2.2.2 ∧
          SeesInWhole J (Qof P) i (L.getD j (0, 0, 0)) r) ∧
        (∀ a, a < c.nreg ALLOC → (a < c.nreg pR ∨ c.nreg pR + 4 ≤ a) → c'.nmem a = c.nmem a) ∧
        (∀ r, sw 5000 ≤ r → r < sw 6000 → c'.nreg r = c.nreg r) ∧
        c.nreg ALLOC ≤ c'.nreg ALLOC)

/-- **The cost of the loop**. -/
def loopCost (κ F : ℕ → ℕ) (c₀ : Config) (N₁ : NF) (L : List (ℕ × ℕ × ℕ)) : ℕ :=
  κ (c₀.nreg (sw 6)) * (L.length + 1) * (F (c₀.nreg (sw 5)) + c₀.nreg TLR + 1) +
    κ (c₀.nreg (sw 6)) * (N₁.arcs.length + 1) * (F (c₀.nreg (sw 5)) + 1)

/-- **The query loop** (`loopS sh`) from the base `c₀`: the result list at `sw 11`. -/
def LoopSpec (Aux : Polygon → Merge.Junction → NF → Config → Prop) : Prop :=
  ∃ (loopS : Stmt → Stmt) (κL : ℕ → ℕ), ∀ (sh : Stmt) (Bs : Finset ℕ) (F : ℕ → ℕ) (X : MemCtx)
    (Ok : Polygon → Model → Prop), ShooterOK sh Bs F X Ok → Bs ⊆ oracleBands → X.CapLocal →
    ∀ (P : Polygon) (W : ℕ) (c₀ : Config) (J : Merge.Junction) (H : Host) (N₁ N₂ : NF)
      (E : ℕ) (L : List (ℕ × ℕ × ℕ)) (i : ℕ),
      ABase P W X Ok Aux J H N₁ N₂ E L i c₀ →
      c₀.nreg ALLOC + loopCost κL F c₀ N₁ L ≤ W →
      IRS P W c₀ (loopS sh) c₀ (loopCost κL F c₀ N₁ L) (fun c' =>
        ∃ R : List (ℕ × ℕ × ℕ × ℕ), R.length = L.length ∧
          c₀.nreg (sw 11) + 4 * L.length ≤ c'.nreg ALLOC ∧
          ResultListAt c'.nmem (c₀.nreg (sw 11)) R ∧
          ∀ j, j < L.length → SeesInWhole J (Qof P) i (L.getD j (0, 0, 0)) (R.getD j (0, 0, 0, 0)))

/-- **The assembly**: `SweepSpecH` from stages 2/3, a side-0 initialisation and the loop. -/
def AsmGoal : Prop :=
  SweepEvSpec → ∀ (init0 : Stmt) (Aux : Polygon → Merge.Junction → NF → Config → Prop)
    (κ0 : ℕ → ℕ), InitSpec init0 Aux κ0 → LoopSpec Aux → SweepSpecH

end

end SweepIo

end Chazelle.Core
