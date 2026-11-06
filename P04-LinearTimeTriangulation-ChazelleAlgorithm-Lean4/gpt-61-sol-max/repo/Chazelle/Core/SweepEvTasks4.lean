module

public import Chazelle.Core.SweepEvBatch

/-!
# The sweep (WP-D), stage 3: contracts of the event loop (batch 4)

The run steps of `RunTask` are `prep ; mk2 sh ; start ; while (dF = 0) iter`, with
`iter = win ; [bF := 0, bN := 0] ; orgs (orgDo sh g) ; key`.

* `LoopInv`: the invariant at the start of an iteration (the stops of stage 2, the key, its label
  set with `EvInv`, the gap regions, the stop pointer, the log so far, the table, the layout and a
  measure).
* `StepTask` (mathematics): one iteration that does not finish keeps `LoopInv` and lowers the
  measure.
* `DoneTask` (mathematics): the iteration that finishes gives the outputs `Out`.
* `LoopStartTask` (RAM + mathematics): after `prep` and stage 2, the program `start` sets the
  start key, its label set, the gap regions, the stop pointer and the first log record.
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
open Chazelle.Chain (SideAttach sidePt)
open Chazelle.Visibility (rayPt)

@[expose] public section

/-- The capacity of the log (records). -/
def logCap (N₁ N₂ : NF) : ℕ := 16 * (N₁.nChords + N₂.nChords + 1)

section
variable (P : Polygon) (J : Merge.Junction)
include P J
/-- The offset of the current key. -/
noncomputable def keyOff (c : Config) : ℝ :=
  offK P J (c.nreg kE) (c.nreg kH)

/-- The label set of the current key. -/
noncomputable def curLab (N₂ : NF) (c : Config) :
    Set (Set Point) :=
  labSet J (Qof P) N₂ (c.nreg kN) (c.nreg kL) (c.nreg (kL + 1)) (c.nreg (kL + 2))
    (c.nreg (kL + 3))

/-- The offsets of all possible keys (`CountTask`). -/
def keyS (N₁ N₂ : NF) : Set ℝ :=
  cutOffs J (N₂.F (chainModel J.right) (Qof P)) ∪ winOffs P J N₁

/-- The offset of stop `i`. -/
noncomputable def stopOff (c : Config) (i : ℕ) : ℝ :=
  offK P J (stopE c i) (stopH c i)

/-- **The stops of stage 2** in the configuration `c` (the body of `StopOut`). -/
def StopData (N₂ : NF) (c : Config)
    (rs ax : List (ℕ × ℕ × ℕ × ℕ × ℕ)) : Prop :=
  rs.length = c.nreg sC ∧ ax.length = rs.length ∧
    StopRecsAt c.nmem (c.nreg sB) rs ∧ AuxRecsAt c.nmem (c.nreg aB) ax ∧
    StopsOK J (N₂.F (chainModel J.right) (Qof P)) (stopsOf J (Qof P) N₂ rs) ∧
    (∀ r ∈ rs, PosW P J r.1 r.2.1 ∧ r.2.2.1 ≤ 2 ∧ r.2.2.2.2 ≤ 1 ∧
      (r.2.2.1 = 1 → r.2.2.2.1 < N₂.nChords)) ∧
    (∀ i, i < rs.length → AuxOK P J N₂
      (stopSet J (Qof P) N₂ (rs.getD i (0, 0, 0, 0, 0)).2.2.1 (rs.getD i (0, 0, 0, 0, 0)).2.2.2.1
        (rs.getD i (0, 0, 0, 0, 0)).2.2.2.2) (ax.getD i (0, 0, 0, 0, 0))) ∧
    rs.length ≤ 4 * N₂.nChords + 8


end

/-- **The log so far**: `LogOK` without the condition after the last key. -/
def LogPre (J : Merge.Junction) (S₂ : Set (Set Point)) (es : List (ℕ × ℝ × Set (Set Point))) :
    Prop :=
  es ≠ [] ∧
  (∀ x ∈ es, x.1 < (chainModel J.whole).W.n ∧ 0 ≤ x.2.1 ∧ x.2.1 < 1 ∧
    (Lst J : ℝ) ≤ oW J (x.1 + x.2.1)) ∧
  (∀ x ∈ es.head?, oW J (x.1 + x.2.1) = Lst J) ∧
  es.Pairwise (fun x y => oW J (x.1 + x.2.1) < oW J (y.1 + y.2.1)) ∧
  (∀ i, i + 1 < es.length →
    NoCutIn J S₂ (oW J ((es.getD i (0, 0, ∅)).1 + (es.getD i (0, 0, ∅)).2.1))
      (oW J ((es.getD (i + 1) (0, 0, ∅)).1 + (es.getD (i + 1) (0, 0, ∅)).2.1))) ∧
  ∀ x ∈ es, LabIn J S₂ x.1 x.2.1 x.2.2

section
variable (P : Polygon) (J : Merge.Junction) (N₂ : NF)
include P J N₂
/-- The word facts of the log records (as in `Out`). -/
def LogWords
    (ls : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ)) : Prop :=
  ∀ r ∈ ls, PosW P J r.1 r.2.1 ∧ r.2.2.1 ≤ 4 ∧
    (0 < r.2.2.1 → r.2.2.2.1 < N₂.nRegions) ∧ (1 < r.2.2.1 → r.2.2.2.2.1 < N₂.nRegions) ∧
    (2 < r.2.2.1 → r.2.2.2.2.2.1 < N₂.nRegions) ∧ (3 < r.2.2.1 → r.2.2.2.2.2.2 < N₂.nRegions)

/-- **The table up to the offset `o`**: flags `≤ 1`; a flag `1` holds an accepted position
(`CandOK`); every valid query whose chord meets `C₁` first, attached on the `C₁` part beyond the
start at an offset `≤ o`, has flag `1`. -/
def TabInv (c : Config) (o : ℝ) : Prop :=
  ∀ j, j < 2 * N₂.nChords →
    c.nmem (c.nreg cTB + 3 * j) ≤ 1 ∧
    (c.nmem (c.nreg cTB + 3 * j) = 1 →
      CandOK P J (N₂.F (chainModel J.right) (Qof P)) (endOrigin J (Qof P) N₂ j) (endDir j)
        (c.nmem (c.nreg cTB + 3 * j + 1)) (c.nmem (c.nreg cTB + 3 * j + 2))) ∧
    (ValidJ J (Qof P) N₂ j →
      J.whole.hitParam (endOrigin J (Qof P) N₂ j) (endDir j) <
        J.right.hitParam (endOrigin J (Qof P) N₂ j) (endDir j) →
      ∀ (p : ℕ) (t : ℝ), SideAttach (chainModel J.whole).W
          (Merge.shoot J.whole (endOrigin J (Qof P) N₂ j) (endDir j)) p t →
        sidePt (chainModel J.whole).W p t = rayPt (endOrigin J (Qof P) N₂ j) (endDir j)
          (J.whole.hitParam (endOrigin J (Qof P) N₂ j) (endDir j)) →
        (Lst J : ℝ) < oW J (p + t) → oW J (p + t) ≤ o → c.nmem (c.nreg cTB + 3 * j) = 1)


end

/-- **The invariant of the event loop** at the start of an iteration (configuration `c`, start of
the run steps `c₀`). -/
structure LoopInv (P : Polygon) (J : Merge.Junction) (N₁ N₂ : NF) (c₀ c : Config) : Prop where
  /-- the stops of stage 2 -/
  stops : ∃ rs ax, StopData P J N₂ c rs ax
  /-- sorted, at most two stops at one offset -/
  sorted : ∀ i i', i ≤ i' → i' < c.nreg sC → stopOff P J c i ≤ stopOff P J c i'
  two : ∀ i, i + 2 < c.nreg sC → stopOff P J c i < stopOff P J c (i + 2)
  /-- the layout: table at the allocator of `c₀`, then the log, then the stop arrays -/
  tab0 : c.nreg cTB = c₀.nreg ALLOC
  lay1 : c.nreg cTB + 6 * N₂.nChords ≤ c.nreg lB
  lay2 : c.nreg lB + 7 * logCap N₁ N₂ ≤ c.nreg sB
  lay3 : c.nreg lB + 7 * logCap N₁ N₂ ≤ c.nreg aB
  lay4 : c.nreg sB + 5 * c.nreg sC ≤ c.nreg ALLOC
  lay5 : c.nreg aB + 5 * c.nreg sC ≤ c.nreg ALLOC
  /-- the key and its label set -/
  key : PosW P J (c.nreg kE) (c.nreg kH)
  keyL : (Lst J : ℝ) ≤ keyOff P J c
  labN : c.nreg kN ≤ 4
  labR : ∀ i, i < c.nreg kN → c.nreg (kL + i) < N₂.nRegions
  inv : EvInv J (N₂.F (chainModel J.right) (Qof P)) (keyOff P J c) (curLab P J N₂ c)
  /-- the gap regions -/
  gapN : c.nreg gN ≤ 2
  gapR : ∀ i, i < c.nreg gN → c.nreg (gR + i) < N₂.nRegions
  gap : ∀ V, GapLab J (N₂.F (chainModel J.right) (Qof P)) V →
    ∃ i, i < c.nreg gN ∧ regOf (chainModel J.right) (Qof P) N₂ (c.nreg (gR + i)) = V
  /-- the stop pointer: the stops at or before the key -/
  ptr : c.nreg sP ≤ c.nreg sC
  ptrL : ∀ i, i < c.nreg sC → (i < c.nreg sP ↔ stopOff P J c i ≤ keyOff P J c)
  /-- the log so far, ending with the current key -/
  log : ∃ ls : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ), ls.length = c.nreg lC ∧
    LogRecsAt c.nmem (c.nreg lB) ls ∧ LogWords P J N₂ ls ∧
    LogPre J (N₂.F (chainModel J.right) (Qof P)) (logOf J (Qof P) N₂ ls) ∧
    ls.getLast? = some (c.nreg kE, c.nreg kH, c.nreg kN, c.nreg kL, c.nreg (kL + 1),
      c.nreg (kL + 2), c.nreg (kL + 3))
  /-- the measure: the log records and the keys left -/
  meas : c.nreg lC + (keyS P J N₁ N₂ ∩ Ioi (keyOff P J c)).ncard ≤ (keyS P J N₁ N₂).ncard + 1
  /-- the table up to the key -/
  tab : TabInv P J N₂ c (keyOff P J c)
  /-- the run state -/
  done0 : c.nreg dF = 0

/-! ## One iteration -/

/-- The reset of the best candidate: `cs` is `cw` with `bF = bN = 0`. -/
def ResetRel (cw cs : Config) : Prop :=
  cs.nmem = cw.nmem ∧ cs.nreg bF = 0 ∧ cs.nreg bN = 0 ∧
    ∀ r, r ≠ bF → r ≠ bN → cs.nreg r = cw.nreg r

/-- **The facts of one iteration** from `c` (start) through `cw` (after the window), `cs` (after
the reset), `co` (after the origins) to `c'` (after the next key). -/
def IterRel (P : Polygon) (J : Merge.Junction) (N₁ N₂ : NF) (c cw cs co c' : Config) : Prop :=
  WinOut P J N₁ c cw ∧ c.nreg ALLOC ≤ cw.nreg ALLOC ∧ ResetRel cw cs ∧
    BatchInv P J N₂ cs
      (ShotList.loSet (chainModel J.left) (Qof P) cs.nmem (cs.nreg wGB) (cs.nreg wGK) [])
      (iterO N₂ cs) co ∧
    KeyOut P J co c'

/-- **Task L1 (mathematics): one iteration that does not finish** keeps the invariant and lowers
the number of keys left. -/
def StepTask : Prop :=
  ∀ (sh : Stmt) (Bs : Finset ℕ) (F : ℕ → ℕ) (X : MemCtx) (Ok : Polygon → Model → Prop)
    (P : Polygon) (W : ℕ) (c₀ : Config) (J : Merge.Junction) (N₁ N₂ : NF)
    (c cw cs co c' : Config), EvEnv sh Bs F X Ok P W c₀ J N₁ N₂ →
    LoopInv P J N₁ N₂ c₀ c → IterRel P J N₁ N₂ c cw cs co c' → c'.nreg dF = 0 →
    LoopInv P J N₁ N₂ c₀ c' ∧
      (keyS P J N₁ N₂ ∩ Ioi (keyOff P J c')).ncard < (keyS P J N₁ N₂ ∩ Ioi (keyOff P J c)).ncard

/-- **Task L2 (mathematics): the last iteration** gives the outputs (read through `fin`) and the
size of the log. -/
def DoneTask : Prop :=
  ∀ (sh : Stmt) (Bs : Finset ℕ) (F : ℕ → ℕ) (X : MemCtx) (Ok : Polygon → Model → Prop)
    (P : Polygon) (W : ℕ) (c₀ : Config) (J : Merge.Junction) (N₁ N₂ : NF)
    (c cw cs co c' : Config), EvEnv sh Bs F X Ok P W c₀ J N₁ N₂ →
    LoopInv P J N₁ N₂ c₀ c → IterRel P J N₁ N₂ c cw cs co c' → c'.nreg dF = 1 →
    Out P J N₂ (finCfg c') ∧ c'.nreg lC ≤ logCap N₁ N₂

/-! ## The start of the loop -/

/-- The registers the start may write (besides the oracle bands and the allocator). -/
def StR (r : ℕ) : Prop :=
  r = kE ∨ r = kH ∨ r = kN ∨ (kL ≤ r ∧ r < kL + 4) ∨ r = gN ∨ r = gR ∨ r = gR + 1 ∨ r = sP ∨
    r = dF ∨ r = lC ∨ (sw 2480 ≤ r ∧ r < sw 2500) ∨ (sw 700 ≤ r ∧ r < sw 2200) ∨
    (sw 2610 ≤ r ∧ r ≤ sw 2612) ∨ (sw 3000 ≤ r ∧ r < sw 6000)

/-- **Task L0: the start of the loop**, at cost `κS0 D (TLR + 1)`: after the preparation
(`PrepOut` from `c₀`) and stage 2 (`StopOut` from `c₁` to `c`), the program `start` reaches the
invariant `LoopInv` (the start key `((gW + Lst) % n, 0)`; its label set: the labels of the
anchored stops at the start key if one exists (`evInv_anchor`, through `StartMathTask`), else the
region faced before the end of the right stretch (`StartTask`); the gap regions (`face`); the stop
pointer past the stops at the start key; the first log record), writing only `StR`, the oracle
bands, the allocator and the log record. -/
def LoopStartTask : Prop :=
  ∃ (start : Stmt) (κS0 : ℕ → ℕ), ∀ (sh : Stmt) (Bs : Finset ℕ) (F : ℕ → ℕ) (X : MemCtx)
    (Ok : Polygon → Model → Prop) (P : Polygon) (W : ℕ) (c₀ c₁ c : Config) (J : Merge.Junction)
    (N₁ N₂ : NF), EvEnv sh Bs F X Ok P W c₀ J N₁ N₂ → PrepOut N₁ N₂ c₀ c₁ →
      StopOut P J N₁ N₂ c₁ c → IInv W c₀ c →
      c.nreg ALLOC + κS0 (c₀.nreg (sw 6)) * (c₀.nreg TLR + 1) ≤ W →
      IRS P W c₀ start c (κS0 (c₀.nreg (sw 6)) * (c₀.nreg TLR + 1)) (fun c' =>
        LoopInv P J N₁ N₂ c₀ c' ∧
        (∀ r, bandOf r ∉ oracleBands → ¬ StR r → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
        (∀ x, x < c.nreg ALLOC → (x < c.nreg lB ∨ c.nreg lB + 7 ≤ x) → c'.nmem x = c.nmem x))

/-! ## The arcs of a region (mathematics) -/

/-- **Task R (mathematics): the arcs of a region**: a region record of a valid normal form of a
chain model with degree cap `D` lists at most `D + 1` arcs (`arcsPerRegion`, distinct start keys
of the arcs of one region, `ArcsOK`). -/
def RegArcsTask : Prop :=
  ∀ (C : Chain) (Q : Polygon) (N : NF) (D : ℕ), C.P.Simple → IsNF (chainModel C) Q N →
    (chainModel C).DegLe (N.F (chainModel C) Q) D →
    ∀ r, r < N.nRegions → (N.region r).arcs.length ≤ D + 1

end

end SweepEv

end Chazelle.Core
