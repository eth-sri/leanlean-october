module

public import Chazelle.Core.SweepIoKb
public import Chazelle.Core.SweepEvSpec

/-!
# The sweep RAM (WP-D), answers: the environment of the answer phase and contracts of parts

**The answer phase** (after stage 0, stages 2/3 (`SweepEvSpec`) and the initialisation of the
answers) works in the run-step framework `IRS` of `SweepIoRun.lean` with base configuration `c₀`:
the registers `sw 0 … 699` are fixed (`IFix`), scratch is `sw 700 …` and the oracle bands.
`AEnv` collects the facts about `c₀` (all robust along `IInv`).

Per query the pipeline (`SweepIo`) reads the query `(qE, qH, qD)`, converts its position to the
walk of `C` (`zE`), computes the flag `zF` and the arrival position `(zP, zPh)` (`flagS`), the bits
`bL`, `bR` and the query index `qJ`, clears the accumulator, runs the **candidate step** of its
side (`Cand0Spec`, `Cand1Spec`), converts the winner of the accumulator to the walk of `C` (by its
tag and the bits, `ModB`) and computes the record (`recS`).

## Register map of the answer phase (scratch)

* `sw 1000 … sw 3199`: the local hit (`localHit`; it writes `LHW` = `sw 1000 … 2199` and
  `sw 3000 … 3199`), the accumulator `accA = sw 2000 … sw 2012`; also free for the parts;
* `sw 3200 … sw 3229`: the pipeline (`qE qH qD zE zF zP zPh … rho`, `bL bR qJ`); kept by the
  candidate steps and the parts;
* `sw 3230 … sw 3299`: scratch of the candidate steps; `sO = sw 3231 … 3233` the symbolic point
  of the query point (by convention, input of `BruteSpec` and `Lab0Spec`);
* `sw 3300 … sw 3399`: the conversion `convS` (`sw 3300 … 3302`), free for the parts;
* `sw 4000 … sw 4799`: free for the parts (`BruteSpec`, `S0CandSpec`, `Lab0Spec`);
* `sw 4800 … sw 4999`: free for the candidate steps (`Cand0Spec`, `Cand1Spec`);
* `sw 5000 … sw 5999`: the query loop.

Fixed (`IFix`): `sw 0 … 199` from stages 2/3, `sw 600, 601` the table of powers (`TBR`, `TLR`),
`sw 610 … 616` the constants `K0 … K6`, `sw 620 … 659` reserved for the initialisation of the
side-0 candidate step (`Cand0Spec`, `S0CandSpec`).

## Contracts of parts (to be proved separately)

* `Side0MathSpec`: the cases of the first hit of a side-0 query (mathematics);
* `TopCountSpec`: at most two endpoint queries of `N₂` start at the top of `C₂` (mathematics);
* `BruteSpec`: the shot in the model of `C₁` from a symbolic point at all arcs of `N₁` (RAM);
* `S0CandSpec`: the stop and table candidates of a side-0 query at its arrival position (RAM: an
  initialisation and a per-query procedure);
* `Lab0Spec`: the label candidates of a side-0 query (RAM: shots in the model of `C₂` at the arcs
  of the label regions of the log entries at the arrival position and of the gap labels);
* `Cand0Spec`, `Cand1Spec`: the candidate steps of the two sides (RAM drivers; `Cand0Spec` from
  `Side0MathSpec`, `S0CandSpec`, `Lab0Spec`; `Cand1Spec` from `BruteSpec`).
-/

namespace Chazelle.Core

namespace SweepIo

open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed Sweep
open Chazelle.Visibility (rayPt)
open Chazelle.Chain (sidePt sideLeft sideInArc)
open Chazelle.Merge (FreeAt)

@[expose] public section

/-! ## Shared definitions -/

/-- The bit `bL`: `1` iff the query point is not above the top of `C₁`. -/
def bL : ℕ := sw 3225

/-- The bit `bR`: `1` iff the query point is not above the top of `C₂`. -/
def bR : ℕ := sw 3226

/-- The index of the query in the query list. -/
def qJ : ℕ := sw 3227

/-- The symbolic point of the query point (three registers `sw 3231 … 3233`; `callSym` with
output register `sw 3230` writes it). -/
def sO : ℕ := sw 3231

/-- **The chain of an accumulator tag** under the bits `l = bL`, `r = bR`: tag `0` is `C₁` when
`l = 1`, tag `1` is `C₂` when `r = 1`, every other case is `C`.  (A candidate of `C₁` (`C₂`) is
offered only for a query point not above the top of `C₁` (`C₂`); then the winner of the
accumulator is a tour, top or box-wall position of its model, which converts to the walk of `C`.)
-/
def ModB (J : Merge.Junction) (l r t : ℕ) : Chain :=
  if t = 0 ∧ l = 1 then J.left else if t = 1 ∧ r = 1 then J.right else J.whole

/-- **The origin of a stop record** `(e, h, kind, k, b)`: the shared vertex (`kind = 0`), the end
of chord `k` of `N₂` (`kind = 1`, the left end for the direction east), or the top of `C₂`. -/
noncomputable def stopOrig (J : Merge.Junction) (Q : Polygon) (N : NF) (kind k b : ℕ) : Point :=
  if kind = 0 then J.shared
  else if kind = 1 then endOrigin J Q N (2 * k + (if dirOf b = 1 then 0 else 1))
  else J.right.top

/-- **The environment of the answer phase** at its base configuration `c₀`: the facts of the
precondition of `SweepSpecH` (without the queries), the stage-0 state of side `0`, the outputs of
stages 2 and 3 (`SweepEv.Out`, arrays below the allocator), and the initialisation of the
answers (constants `K0 … K6`, the table of powers at `TBR` of length `TLR`, large enough for the
arcs of `N₁`, `N₂` and for the stops, the log and the table). -/
structure AEnv (P : Polygon) (W : ℕ) (X : MemCtx) (Ok : Polygon → Model → Prop)
    (J : Merge.Junction) (H : Host) (N₁ N₂ : NF) (E : ℕ) (c₀ : Config) : Prop where
  hG : GoodEnv P
  hWh : hostWords P.n ≤ W
  hX : X.holds P c₀.nmem (c₀.nreg (sw 10)) (c₀.nreg ALLOC)
  hcap : c₀.nreg (sw 5) ≤ X.cap P c₀.nmem (c₀.nreg (sw 10))
  hP : J.P.Simple
  hOk₁ : Ok P (chainModel J.left)
  hOk₂ : Ok P (chainModel J.right)
  hN₁ : NFWithin c₀.nmem (c₀.nreg (sw 3)) E N₁
  hN₂ : NFWithin c₀.nmem (c₀.nreg (sw 4)) E N₂
  hNF₁ : IsNF (chainModel J.left) (Qof P) N₁
  hNF₂ : IsNF (chainModel J.right) (Qof P) N₂
  hdeg₁ : (chainModel J.left).DegLe (N₁.F (chainModel J.left) (Qof P)) (c₀.nreg (sw 6))
  hdeg₂ : (chainModel J.right).DegLe (N₂.F (chainModel J.right) (Qof P)) (c₀.nreg (sw 6))
  hsg₁ : (chainModel J.left).Semigranular (N₁.F (chainModel J.left) (Qof P)) (c₀.nreg (sw 5))
  hsg₂ : (chainModel J.right).Semigranular (N₂.F (chainModel J.right) (Qof P)) (c₀.nreg (sw 5))
  hst : SweepEv.St0S P c₀ H J
  hE : E ≤ c₀.nreg ALLOC
  hWm : 2 * J.whole.m + 7 ≤ W
  hK : Consts c₀
  htab : ∀ j, j < c₀.nreg TLR → c₀.nmem (c₀.nreg TBR + j) = 2 ^ j
  hbig₁ : N₁.arcs.length < 2 ^ c₀.nreg TLR
  hbig₂ : N₂.arcs.length < 2 ^ c₀.nreg TLR
  hbigE : rd c₀ bSweep 201 + rd c₀ bSweep 301 + 2 * N₂.nChords < 2 ^ c₀.nreg TLR
  hTB : E ≤ c₀.nreg TBR
  hTW : c₀.nreg TBR + c₀.nreg TLR ≤ c₀.nreg ALLOC
  hout : SweepEv.Out P J N₂ c₀
  hstops : rd c₀ bSweep 200 + 5 * rd c₀ bSweep 201 ≤ c₀.nreg ALLOC
  hlog : rd c₀ bSweep 300 + 7 * rd c₀ bSweep 301 ≤ c₀.nreg ALLOC
  htabw : rd c₀ bSweep 302 + 3 * (2 * N₂.nChords) ≤ c₀.nreg ALLOC
  hK₁ : c₀.nmem (c₀.nreg (sw 3)) = N₁.nChords
  hK₂ : c₀.nmem (c₀.nreg (sw 4)) = N₂.nChords
  /-- The model descriptors at `sw 30`, `sw 31` hold copies of the chain descriptors at `sw 20`,
  `sw 21` (stage 0, `mdBlk`). -/
  hmd₁ : ∀ j, j < 5 → c₀.nmem (c₀.nreg (sw 30) + 1 + j) = c₀.nmem (c₀.nreg (sw 20) + j)
  hmd₂ : ∀ j, j < 5 → c₀.nmem (c₀.nreg (sw 31) + 1 + j) = c₀.nmem (c₀.nreg (sw 21) + j)

/-- **The frame of a part** (`BruteSpec`, `S0CandSpec`, `Lab0Spec`): registers outside the oracle
bands, outside `sw 1000 … sw 3199`, `sw 3300 … sw 3399` and `sw 4000 … sw 4799`, other than the
allocator, are kept; the allocator grows; memory below it is kept. -/
def PartFr (c c' : Config) : Prop :=
  (∀ r, bandOf r ∉ oracleBands → ¬ (sw 1000 ≤ r ∧ r < sw 3200) → ¬ (sw 3300 ≤ r ∧ r < sw 3400) →
    ¬ (sw 4000 ≤ r ∧ r < sw 4800) → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
  c.nreg ALLOC ≤ c'.nreg ALLOC ∧ (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a)

/-- **The frame of a candidate step** (`Cand0Spec`, `Cand1Spec`): registers outside the oracle
bands, outside `sw 1000 … sw 3199`, `sw 3230 … sw 3399` and `sw 4000 … sw 4999`, other than the
allocator, are kept; the allocator grows; memory below it is kept. -/
def CandFr (c c' : Config) : Prop :=
  (∀ r, bandOf r ∉ oracleBands → ¬ (sw 1000 ≤ r ∧ r < sw 3200) → ¬ (sw 3230 ≤ r ∧ r < sw 3400) →
    ¬ (sw 4000 ≤ r ∧ r < sw 5000) → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
  c.nreg ALLOC ≤ c'.nreg ALLOC ∧ (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a)

/-- **The state of a query at the candidate step** (side `i`, query point `z`): the query
`(qE, qH, qD)` is a valid query of side `i` (in the model of `C₁` for `i = 0`, of `C₂` for
`i = 1`) with its height code naming its height, `(zE, qH)` is a position of `z` in the walk of
`C`, the direction is free for `C` at `z`, `(zP, zPh)` is the arrival position of `z` in the walk
of `C` (the ray in its left sector), and the bits `bL`, `bR` say whether `z` is not above the top
of `C₁`, `C₂`. -/
structure QState (P : Polygon) (J : Merge.Junction) (i : ℕ) (z : Point) (c : Config) : Prop where
  hq : QueryOK J (Qof P) i (c.nreg qE, c.nreg qH, c.nreg qD)
  hht : ((chainModel (sideChain J i)).pos (Qof P) ⟨c.nreg qE, c.nreg qH⟩).2 =
    ((Qof P).vtx (c.nreg qH - 1)).2
  hz : (chainModel (sideChain J i)).pos (Qof P) ⟨c.nreg qE, c.nreg qH⟩ = z
  hzE : c.nreg zE < (chainModel J.whole).W.n
  hzpp : ProperPos (chainModel J.whole) (Qof P) P.n ⟨c.nreg zE, c.nreg qH⟩
  hzM : (chainModel J.whole).pos (Qof P) ⟨c.nreg zE, c.nreg qH⟩ = z
  hfree : FreeAt J.whole z (dirOf (c.nreg qD))
  hzP : c.nreg zP < (chainModel J.whole).W.n
  hzPp : ProperPos (chainModel J.whole) (Qof P) P.n ⟨c.nreg zP, c.nreg zPh⟩
  harr : Arrival (chainModel J.whole).W z (-dirOf (c.nreg qD)) (c.nreg zP)
    ((chainModel J.whole).param (Qof P) ⟨c.nreg zP, c.nreg zPh⟩)
  hbL : c.nreg bL ≤ 1 ∧ (c.nreg bL = 1 ↔ z.2 ≤ J.left.top.2)
  hbR : c.nreg bR ≤ 1 ∧ (c.nreg bR = 1 ↔ z.2 ≤ J.right.top.2)

/-- **The output of a candidate step**: the accumulator (tags under the bits, `ModB`) holds
candidates of the ray from `z`, all of them hits of `C` or of the box at positive parameters,
among them the first hit of `C`. -/
def CandOut (P : Polygon) (J : Merge.Junction) (z : Point) (c c' : Config) : Prop :=
  ∃ L, AccOK P accA (ModB J (c.nreg bL) (c.nreg bR)) J.whole.radius z (dirOf (c.nreg qD)) L c' ∧
    (∀ τ ∈ L, 0 < τ ∧ OnCB J.whole (rayPt z (dirOf (c.nreg qD)) τ)) ∧
    J.whole.hitParam z (dirOf (c.nreg qD)) ∈ L

/-- The key of the log entry `i` (its offset is compared with the offset of a position). -/
noncomputable def logKey (J : Merge.Junction) (Q : Polygon) (N : NF)
    (ls : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ)) (i : ℕ) : ℝ :=
  ((logOf J Q N ls).getD i (0, 0, ∅)).1 + ((logOf J Q N ls).getD i (0, 0, ∅)).2.1

/-- The label set of the log entry `i`. -/
noncomputable def logLab (J : Merge.Junction) (Q : Polygon) (N : NF)
    (ls : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ)) (i : ℕ) : Set (Set Point) :=
  ((logOf J Q N ls).getD i (0, 0, ∅)).2.2

/-- **`i` is the log entry of the key `x`**: the last log key whose offset is not after it. -/
def LogIdx (J : Merge.Junction) (Q : Polygon) (N : NF) (ls : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ))
    (x : ℝ) (i : ℕ) : Prop :=
  i < ls.length ∧ oW J (logKey J Q N ls i) ≤ oW J x ∧
    (i + 1 < ls.length → oW J x < oW J (logKey J Q N ls (i + 1)))

/-! ## Contract 1: the cases of a side-0 query (mathematics) -/

/-- **The cases of the first hit of a side-0 query** `z` (a point of `C₁` other than the shared
vertex, not above the top of `C₂`, with a free direction `σ` for `C`), from its arrival position
`(pz, tz)` in the walk of `C` (the ray in its left sector), the event log `ls`, the stop records
`rs` and the endpoint table `T` of stages 2/3.  The position is on the `C₁` part (offset at least
`Lst`), and for the log entry `i` of the position the first hit `J.whole.hitParam z σ` is

* (C1) the first hit of `C₁` (the local hit in the model of `C₁` finds it), or
* (C2) the first hit of `C₂`, and the ray starts in a region `V` of `S₂` with a label of the log
  entry `i` or `i - 1`, or a gap label (the shot at the arcs of `V` finds it), or
* (C3) the origin of a stop record at the position, the stop chord running along the ray back to
  `z`, or
* (C4) the origin of a regular endpoint query whose table entry is the position, in the direction
  opposite to the ray. -/
def Side0MathSpec : Prop :=
  ∀ (P : Polygon) (J : Merge.Junction) (N₂ : NF) (rs : List (ℕ × ℕ × ℕ × ℕ × ℕ))
    (ls : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ)) (T : ℕ → Option (ℕ × ℝ)),
    GoodEnv P → J.P.Simple → IsNF (chainModel J.right) (Qof P) N₂ →
    LogOK J (N₂.F (chainModel J.right) (Qof P)) (logOf J (Qof P) N₂ ls) →
    StopsOK J (N₂.F (chainModel J.right) (Qof P)) (stopsOf J (Qof P) N₂ rs) →
    TabOK J (Qof P) N₂ T →
    ∀ (z : Point) (σ : ℝ), (σ = 1 ∨ σ = -1) → z ∈ J.left.set → z ≠ J.shared →
      z.2 ≤ J.right.top.2 → FreeAt J.whole z σ →
      ∀ (pz : ℕ) (tz : ℝ), Arrival (chainModel J.whole).W z (-σ) pz tz →
      (Lst J : ℝ) ≤ oW J (pz + tz) ∧
      ∀ i, LogIdx J (Qof P) N₂ ls (pz + tz) i →
        -- (C1)
        J.left.hitParam z σ = J.whole.hitParam z σ ∨
        -- (C2)
        (J.right.hitParam z σ = J.whole.hitParam z σ ∧
          ∃ V ∈ (chainModel J.right).regions (N₂.F (chainModel J.right) (Qof P)),
            (V ∈ logLab J (Qof P) N₂ ls i ∨ (0 < i ∧ V ∈ logLab J (Qof P) N₂ ls (i - 1)) ∨
              GapLab J (N₂.F (chainModel J.right) (Qof P)) V) ∧
            ∀ᶠ s in nhdsWithin (0 : ℝ) (Set.Ioi 0), rayPt z σ s ∈ V) ∨
        -- (C3)
        (∃ r ∈ rs, r.1 = pz ∧ (chainModel J.whole).param (Qof P) ⟨r.1, r.2.1⟩ = tz ∧
          dirOf r.2.2.2.2 = -σ ∧
          stopOrig J (Qof P) N₂ r.2.2.1 r.2.2.2.1 r.2.2.2.2 = rayPt z σ (J.whole.hitParam z σ)) ∨
        -- (C4)
        (∃ j, j < 2 * N₂.nChords ∧ T j = some (pz, tz) ∧ endDir j = -σ ∧
          endOrigin J (Qof P) N₂ j ∈ J.right.set ∧ endOrigin J (Qof P) N₂ j ≠ J.shared ∧
          endOrigin J (Qof P) N₂ j ≠ J.right.top ∧
          endOrigin J (Qof P) N₂ j = rayPt z σ (J.whole.hitParam z σ))

/-! ## Contract 2: endpoint queries at the top of `C₂` (mathematics) -/

/-- **At most two endpoint queries start at the top of `C₂`** (one per direction: two chords of a
normal form starting at one point in one direction are equal). -/
def TopCountSpec : Prop :=
  ∀ (P : Polygon) (J : Merge.Junction) (N₂ : NF), GoodEnv P → J.P.Simple →
    IsNF (chainModel J.right) (Qof P) N₂ →
    ((List.range (2 * N₂.nChords)).filter
      (fun j => decide (endOrigin J (Qof P) N₂ j = J.right.top))).length ≤ 2

/-! ## Contract 3: the brute-force shot in the model of `C₁` (RAM) -/

/-- **The brute-force shot** at all arcs of `N₁`, in the model of `C₁` (model descriptor `sw 30`,
normal form `sw 3`), from the point `z` of the symbolic point in `sO` (not a point of `C₁`,
strictly inside the box, not above the top of `C₁`, so `bL = 1`), in the direction of code `qD`,
offering the hit (if any) to the accumulator `accA` with tag `0`.  Every new candidate is a point
of `C₁` or of the box on the ray at a positive parameter; the first hit of `C₁` is offered.  Cost
`κB (A₁ + 1) (F γ + 1)` (`A₁` the number of arcs of `N₁`). -/
def BruteSpec : Prop :=
  ∃ (bruteS : Stmt → Stmt) (κB : ℕ), ∀ (sh : Stmt) (Bs : Finset ℕ) (F : ℕ → ℕ) (X : MemCtx)
    (Ok : Polygon → Model → Prop), ShooterOK sh Bs F X Ok → Bs ⊆ oracleBands → X.CapLocal →
    ∀ (P : Polygon) (W : ℕ) (c₀ c : Config) (J : Merge.Junction) (H : Host) (N₁ N₂ : NF)
      (E : ℕ) (L : Set ℝ) (s : SymPt) (z : Point),
      AEnv P W X Ok J H N₁ N₂ E c₀ → IInv W c₀ c →
      SymPtIn c sO s → s.Lt P.n → s.eval (Qof P) = z → z ∉ J.left.set →
      |z.1| < J.whole.radius → |z.2| < J.whole.radius → z.2 ≤ J.left.top.2 → c.nreg bL = 1 →
      AccOK P accA (ModB J (c.nreg bL) (c.nreg bR)) J.whole.radius z (dirOf (c.nreg qD)) L c →
      c.nreg ALLOC + κB * (N₁.arcs.length + 1) * (F (c₀.nreg (sw 5)) + 1) ≤ W →
      IRS P W c₀ (bruteS sh) c (κB * (N₁.arcs.length + 1) * (F (c₀.nreg (sw 5)) + 1))
        (fun c' =>
          (∃ L', AccOK P accA (ModB J (c.nreg bL) (c.nreg bR)) J.whole.radius z
              (dirOf (c.nreg qD)) L' c' ∧ L ⊆ L' ∧
            (∀ τ ∈ L', τ ∈ L ∨ (0 < τ ∧ OnCB J.left (rayPt z (dirOf (c.nreg qD)) τ))) ∧
            (FreeAt J.left z (dirOf (c.nreg qD)) →
              J.left.hitParam z (dirOf (c.nreg qD)) ∈ L')) ∧
          PartFr c c')

/-! ## Contract 4: the stop and table candidates of a side-0 query (RAM) -/

/-- **The initialisation contract** of a side-0 procedure: from a configuration satisfying `AEnv`,
`init` writes only `sw 620 … 659` among `sw 0 … 699` (besides fresh memory, scratch and the
oracle bands) and establishes `Aux`, within `κ (S + E + 2 K₂ + 1) (TLR + 1)` steps (`S` the
number of stop records, `E` of log records); `Aux` survives a write of `sw 11`. -/
def InitSpec (init : Stmt) (Aux : Polygon → Merge.Junction → NF → Config → Prop) (κ : ℕ → ℕ) :
    Prop :=
  (∀ (P : Polygon) (W : ℕ) (X : MemCtx) (Ok : Polygon → Model → Prop) (J : Merge.Junction)
    (H : Host) (N₁ N₂ : NF) (E : ℕ) (c : Config), WordsBounded W c →
    AEnv P W X Ok J H N₁ N₂ E c →
    c.nreg ALLOC + κ (c.nreg (sw 6)) * (rd c bSweep 201 + rd c bSweep 301 + 2 * N₂.nChords + 1) *
      (c.nreg TLR + 1) ≤ W →
    ∃ c' k, Exec P W init c c' k ∧
      k ≤ κ (c.nreg (sw 6)) * (rd c bSweep 201 + rd c bSweep 301 + 2 * N₂.nChords + 1) *
        (c.nreg TLR + 1) ∧
      Frame (sweepBands ∪ oracleBands) c c' k ∧
      (∀ j, j < 700 → (j < 620 ∨ 660 ≤ j) → c'.nreg (sw j) = c.nreg (sw j)) ∧
      Aux P J N₂ c') ∧
  (∀ (P : Polygon) (J : Merge.Junction) (N₂ : NF) (c : Config) (v : ℕ), Aux P J N₂ c →
    Aux P J N₂ { c with nreg := upd c.nreg (sw 11) v })

/-- **The stop and table candidates of a side-0 query.**  An initialisation `initC` (`InitSpec`)
establishes a fact `Aux`, robust along `IInv` from the base of the answer phase; then, for a query
point `z` of `C₁` (not the shared vertex, not above the top of `C₂`, so `bR = 1`) with its arrival
position `(zP, zPh)` in the walk of `C` and direction code `qD`, the procedure `candC` offers to the
accumulator the origins of the stop records at the position whose direction is opposite to the
ray, and the origins of the regular endpoint queries whose table entry is the position, in the
direction opposite to the ray.  Every new candidate is a point of `C` or of the box on the ray at
a positive parameter.  Cost of a query `κ D (TLR + 1)`. -/
def S0CandSpec : Prop :=
  ∃ (initC candC : Stmt) (Aux : Polygon → Merge.Junction → NF → Config → Prop) (κ : ℕ → ℕ),
    InitSpec initC Aux κ ∧
    (∀ (P : Polygon) (W : ℕ) (J : Merge.Junction) (N₂ : NF) (c₀ c : Config),
      Aux P J N₂ c₀ → IInv W c₀ c → Aux P J N₂ c) ∧
    ∀ (P : Polygon) (W : ℕ) (X : MemCtx) (Ok : Polygon → Model → Prop) (J : Merge.Junction)
      (H : Host) (N₁ N₂ : NF) (E : ℕ) (c₀ c : Config) (L : Set ℝ) (z : Point),
      AEnv P W X Ok J H N₁ N₂ E c₀ → Aux P J N₂ c₀ → IInv W c₀ c →
      z ∈ J.left.set → z ≠ J.shared → z.2 ≤ J.right.top.2 →
      FreeAt J.whole z (dirOf (c.nreg qD)) →
      c.nreg zP < (chainModel J.whole).W.n →
      ProperPos (chainModel J.whole) (Qof P) P.n ⟨c.nreg zP, c.nreg zPh⟩ →
      Arrival (chainModel J.whole).W z (-dirOf (c.nreg qD)) (c.nreg zP)
        ((chainModel J.whole).param (Qof P) ⟨c.nreg zP, c.nreg zPh⟩) →
      c.nreg bL = 1 → c.nreg bR = 1 →
      AccOK P accA (ModB J (c.nreg bL) (c.nreg bR)) J.whole.radius z (dirOf (c.nreg qD)) L c →
      c.nreg ALLOC + κ (c₀.nreg (sw 6)) * (c₀.nreg TLR + 1) ≤ W →
      IRS P W c₀ candC c (κ (c₀.nreg (sw 6)) * (c₀.nreg TLR + 1))
        (fun c' =>
          (∃ L', AccOK P accA (ModB J (c.nreg bL) (c.nreg bR)) J.whole.radius z
              (dirOf (c.nreg qD)) L' c' ∧ L ⊆ L' ∧
            (∀ τ ∈ L', τ ∈ L ∨ (0 < τ ∧ OnCB J.whole (rayPt z (dirOf (c.nreg qD)) τ))) ∧
            -- the stop records at the position
            (∀ (rs : List (ℕ × ℕ × ℕ × ℕ × ℕ)), rs.length = rd c₀ bSweep 201 →
              StopRecsAt c₀.nmem (rd c₀ bSweep 200) rs →
              ∀ r ∈ rs, r.1 = c.nreg zP →
                (chainModel J.whole).param (Qof P) ⟨r.1, r.2.1⟩ =
                  (chainModel J.whole).param (Qof P) ⟨c.nreg zP, c.nreg zPh⟩ →
                dirOf r.2.2.2.2 = -dirOf (c.nreg qD) →
                ∀ τ, 0 < τ → stopOrig J (Qof P) N₂ r.2.2.1 r.2.2.2.1 r.2.2.2.2 =
                  rayPt z (dirOf (c.nreg qD)) τ → τ ∈ L') ∧
            -- the table entries at the position
            (∀ j, j < 2 * N₂.nChords →
              tabOf J (Qof P) c₀.nmem (rd c₀ bSweep 302) j =
                some (c.nreg zP, (chainModel J.whole).param (Qof P) ⟨c.nreg zP, c.nreg zPh⟩) →
              endDir j = -dirOf (c.nreg qD) → endOrigin J (Qof P) N₂ j ∈ J.right.set →
              endOrigin J (Qof P) N₂ j ≠ J.shared → endOrigin J (Qof P) N₂ j ≠ J.right.top →
              ∀ τ, 0 < τ → endOrigin J (Qof P) N₂ j = rayPt z (dirOf (c.nreg qD)) τ →
                τ ∈ L')) ∧
          PartFr c c')

/-! ## Contract 5: the label candidates of a side-0 query (RAM) -/

/-- **The label candidates of a side-0 query.**  For a query point `z` of `C₁` (not the shared
vertex, not above the top of `C₂`, so `bR = 1`) with its arrival position `(zP, zPh)` in the walk
of `C`, its symbolic point in `sO` and direction code `qD`, the procedure finds the log entry `i`
of the position (binary search in the log, `LogIdx`) and shoots, in the model of `C₂`, from `z` at
the arcs of every region of `S₂` with a label of the log entries `i` and `i - 1` and of the gap
regions (`GapLab`), offering the hits to the accumulator with tag `1`.  Every new candidate is a
point of `C₂` or of the box on the ray at a positive parameter; for every such region in which
the ray starts, the first hit of `C₂` is offered.  Cost `κ D (F γ + TLR + 1)`. -/
def Lab0Spec : Prop :=
  ∃ (lab0 : Stmt → Stmt) (κ : ℕ → ℕ), ∀ (sh : Stmt) (Bs : Finset ℕ) (F : ℕ → ℕ) (X : MemCtx)
    (Ok : Polygon → Model → Prop), ShooterOK sh Bs F X Ok → Bs ⊆ oracleBands → X.CapLocal →
    ∀ (P : Polygon) (W : ℕ) (c₀ c : Config) (J : Merge.Junction) (H : Host) (N₁ N₂ : NF)
      (E : ℕ) (L : Set ℝ) (s : SymPt) (z : Point),
      AEnv P W X Ok J H N₁ N₂ E c₀ → IInv W c₀ c →
      z ∈ J.left.set → z ≠ J.shared → z.2 ≤ J.right.top.2 →
      FreeAt J.whole z (dirOf (c.nreg qD)) →
      c.nreg zP < (chainModel J.whole).W.n →
      ProperPos (chainModel J.whole) (Qof P) P.n ⟨c.nreg zP, c.nreg zPh⟩ →
      Arrival (chainModel J.whole).W z (-dirOf (c.nreg qD)) (c.nreg zP)
        ((chainModel J.whole).param (Qof P) ⟨c.nreg zP, c.nreg zPh⟩) →
      SymPtIn c sO s → s.Lt P.n → s.eval (Qof P) = z →
      c.nreg bR = 1 →
      AccOK P accA (ModB J (c.nreg bL) (c.nreg bR)) J.whole.radius z (dirOf (c.nreg qD)) L c →
      c.nreg ALLOC + κ (c₀.nreg (sw 6)) * (F (c₀.nreg (sw 5)) + c₀.nreg TLR + 1) ≤ W →
      IRS P W c₀ (lab0 sh) c (κ (c₀.nreg (sw 6)) * (F (c₀.nreg (sw 5)) + c₀.nreg TLR + 1))
        (fun c' =>
          (∃ L', AccOK P accA (ModB J (c.nreg bL) (c.nreg bR)) J.whole.radius z
              (dirOf (c.nreg qD)) L' c' ∧ L ⊆ L' ∧
            (∀ τ ∈ L', τ ∈ L ∨ (0 < τ ∧ OnCB J.right (rayPt z (dirOf (c.nreg qD)) τ))) ∧
            ∀ (ls : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ)), ls.length = rd c₀ bSweep 301 →
              LogRecsAt c₀.nmem (rd c₀ bSweep 300) ls →
              ∀ i, LogIdx J (Qof P) N₂ ls
                  (c.nreg zP + (chainModel J.whole).param (Qof P) ⟨c.nreg zP, c.nreg zPh⟩) i →
                ∀ V ∈ (chainModel J.right).regions (N₂.F (chainModel J.right) (Qof P)),
                  (V ∈ logLab J (Qof P) N₂ ls i ∨ (0 < i ∧ V ∈ logLab J (Qof P) N₂ ls (i - 1)) ∨
                    GapLab J (N₂.F (chainModel J.right) (Qof P)) V) →
                  (∀ᶠ s in nhdsWithin (0 : ℝ) (Set.Ioi 0), rayPt z (dirOf (c.nreg qD)) s ∈ V) →
                  J.right.hitParam z (dirOf (c.nreg qD)) ∈ L') ∧
          PartFr c c')

/-! ## Contracts 6, 7: the candidate steps of the two sides (RAM drivers) -/

/-- **The candidate step of side `0`** (queries in the model of `C₁`): an initialisation
`init0` (`InitSpec`, e.g. that of `S0CandSpec`) and the per-query procedure `cand0`, from a
cleared accumulator to `CandOut` (the first hit of `C` among good candidates).  Cost of a query
`κ D (F γ + TLR + 1)`.

Plan: classes of the query point `z` (with `bL = 1` always): a box wall (edges `1`, `3`): local
hits in the models of `C₁` and (if `bR = 1`) of `C₂`; the shared vertex: local hits in the model of
`C₁` and in the model of `C₂` at the arrival position of the shared vertex; a point of `C₁` above
the top of `C₂` (`bR = 0`): the local hit in the model of `C₁`; otherwise the local hit in the
model of `C₁`, `Lab0Spec` (symbolic point by `callSym` into `sO`) and `S0CandSpec`, complete by
`Side0MathSpec`. -/
def Cand0Spec : Prop :=
  ∃ (init0 : Stmt) (cand0 : Stmt → Stmt) (Aux : Polygon → Merge.Junction → NF → Config → Prop)
    (κ : ℕ → ℕ),
    InitSpec init0 Aux κ ∧
    (∀ (P : Polygon) (W : ℕ) (J : Merge.Junction) (N₂ : NF) (c₀ c : Config),
      Aux P J N₂ c₀ → IInv W c₀ c → Aux P J N₂ c) ∧
    ∀ (sh : Stmt) (Bs : Finset ℕ) (F : ℕ → ℕ) (X : MemCtx)
      (Ok : Polygon → Model → Prop), ShooterOK sh Bs F X Ok → Bs ⊆ oracleBands → X.CapLocal →
    ∀ (P : Polygon) (W : ℕ) (c₀ c : Config) (J : Merge.Junction) (H : Host) (N₁ N₂ : NF)
      (E : ℕ) (z : Point),
      AEnv P W X Ok J H N₁ N₂ E c₀ → Aux P J N₂ c₀ → IInv W c₀ c → QState P J 0 z c →
      c.nreg accA = 0 →
      c.nreg ALLOC + κ (c₀.nreg (sw 6)) * (F (c₀.nreg (sw 5)) + c₀.nreg TLR + 1) ≤ W →
      IRS P W c₀ (cand0 sh) c (κ (c₀.nreg (sw 6)) * (F (c₀.nreg (sw 5)) + c₀.nreg TLR + 1))
        (fun c' => CandOut P J z c c' ∧ CandFr c c')

/-- **A brute-force query of side `1`**: a point query (index at least `2 K₂`) or an endpoint
query from the top of `C₂`. -/
def BruteQ (J : Merge.Junction) (N₂ : NF) (j : ℕ) (z : Point) : Prop :=
  2 * N₂.nChords ≤ j ∨ z = J.right.top

open Classical in
/-- **The candidate step of side `1`** (queries in the model of `C₂`; the query of index `qJ` below
`2 K₂` is the endpoint query `qJ` of `N₂`).  Cost of a query `κ D (F γ + TLR + 1)`, plus
`κ D (A₁ + 1) (F γ + 1)` for a brute-force query (`BruteQ`).

Plan: classes of the query point `z` (with `bR = 1` always): a box wall: local hits in the models
of `C₂` and (if `bL = 1`) of `C₁`; the shared vertex: local hits in the model of `C₂` and in the
model of `C₁` at the arrival position of the shared vertex; a regular endpoint query (index below
`2 K₂`, origin not the top of `C₂`): the local hit in the model of `C₂` and the table entry of the
query (`TabOK`: the far attachment, a position of the walk of `C`, tag `2`); a brute-force query:
the local hit in the model of `C₂` and (if `bL = 1`) `BruteSpec` (symbolic point by `callSym` into
`sO`). -/
def Cand1Spec : Prop :=
  ∃ (cand1 : Stmt → Stmt) (κ : ℕ → ℕ), ∀ (sh : Stmt) (Bs : Finset ℕ) (F : ℕ → ℕ) (X : MemCtx)
    (Ok : Polygon → Model → Prop), ShooterOK sh Bs F X Ok → Bs ⊆ oracleBands → X.CapLocal →
    ∀ (P : Polygon) (W : ℕ) (c₀ c : Config) (J : Merge.Junction) (H : Host) (N₁ N₂ : NF)
      (E : ℕ) (z : Point),
      AEnv P W X Ok J H N₁ N₂ E c₀ → IInv W c₀ c → QState P J 1 z c →
      (c.nreg qJ < 2 * N₂.nChords →
        (c.nreg qE, c.nreg qH, c.nreg qD) = (sweepEndQ N₂.chords).getD (c.nreg qJ) (0, 0, 0)) →
      c.nreg accA = 0 →
      c.nreg ALLOC + (κ (c₀.nreg (sw 6)) * (F (c₀.nreg (sw 5)) + c₀.nreg TLR + 1) +
        (if BruteQ J N₂ (c.nreg qJ) z then
          κ (c₀.nreg (sw 6)) * (N₁.arcs.length + 1) * (F (c₀.nreg (sw 5)) + 1) else 0)) ≤ W →
      IRS P W c₀ (cand1 sh) c
        (κ (c₀.nreg (sw 6)) * (F (c₀.nreg (sw 5)) + c₀.nreg TLR + 1) +
          (if BruteQ J N₂ (c.nreg qJ) z then
            κ (c₀.nreg (sw 6)) * (N₁.arcs.length + 1) * (F (c₀.nreg (sw 5)) + 1) else 0))
        (fun c' => CandOut P J z c c' ∧ CandFr c c')

end

end SweepIo

end Chazelle.Core
