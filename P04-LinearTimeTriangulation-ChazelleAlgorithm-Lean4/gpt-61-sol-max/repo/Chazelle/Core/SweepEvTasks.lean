module

public import Chazelle.Core.SweepEvCand5
public import Chazelle.Core.SweepEvStep
public import Chazelle.Core.SweepMachine3

/-!
# The sweep (WP-D), stages 2–3: contracts of the pieces

All pieces run as run steps (`IRS`, `SweepIoRun`) after the initialisation of `sweepEvSpec`'s
program: `c₀` is the start configuration of the run steps, with the environment `EvEnv`
(`SweepEvEnv.lean`).  The fixed registers `sw 0 … 699` never change (`IInv`); the registers
`sw 2200 … 2599` belong to stage 3 and must not be written by the pieces.

* `GenTask` (genuineness check of a candidate by a reverse local hit): a program `mkG sh` with
  the contract `GenOK` (`SweepEvCand2.lean`).
* `StopTask` (stage 2: the stop records, sorted and without duplicates, with auxiliary data):
  a program `mk2 sh` with the post `StopOut`.
* `FaceTask` (the region of `N₂` faced just before / just after a vertex position of the walk of
  `C₂`): a program `face` with the post `FaceOut`.
* `StartTask` (mathematics): the invariant of the event loop at the start when every chord at the
  start key is a bracket.
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
open Chazelle.Chain (SideAttach sidePt)

@[expose] public section

/-! ## A: the genuineness check -/

/-- **Task A.**  The genuineness check for every shooter (cost `κG D · (F γ + TLR + 1)`,
`γ = c₀.nreg (sw 5)`, `D = c₀.nreg (sw 6)`, `TLR = c₀.nreg TLR` the length of the power table of
`locJ`). -/
def GenTask : Prop :=
  ∃ (mkG : Stmt → Stmt) (κG : ℕ → ℕ), ∀ (sh : Stmt) (Bs : Finset ℕ) (F : ℕ → ℕ) (X : MemCtx)
    (Ok : Polygon → Model → Prop) (P : Polygon) (W : ℕ) (c₀ : Config) (J : Merge.Junction)
    (N₁ N₂ : NF), EvEnv sh Bs F X Ok P W c₀ J N₁ N₂ →
      GenOK P W c₀ J (mkG sh)
        (κG (c₀.nreg (sw 6)) * (F (c₀.nreg (sw 5)) + c₀.nreg TLR + 1))

/-! ## B: stage 2 (the stops) -/

/-- The output registers of stage 2: the stop records (`sB`, count `sC`) and the auxiliary
records (`aB`). -/
def sB : ℕ := sw 2600
def sC : ℕ := sw 2601
def aB : ℕ := sw 2602

/-- The registers stage 2 may write (besides the oracle bands and the allocator). -/
def S2R (r : ℕ) : Prop :=
  (sw 700 ≤ r ∧ r < sw 2200) ∨ (sw 2600 ≤ r ∧ r ≤ sw 2602) ∨ (sw 3000 ≤ r ∧ r < sw 6000)

/-- `E` auxiliary records of five words `(anc, nl, l₀, l₁, par)` at `A`. -/
def AuxRecsAt (m : ℕ → ℕ) (A : ℕ) (ax : List (ℕ × ℕ × ℕ × ℕ × ℕ)) : Prop :=
  ∀ i, i < ax.length →
    m (A + 5 * i) = (ax.getD i (0, 0, 0, 0, 0)).1 ∧
    m (A + 5 * i + 1) = (ax.getD i (0, 0, 0, 0, 0)).2.1 ∧
    m (A + 5 * i + 2) = (ax.getD i (0, 0, 0, 0, 0)).2.2.1 ∧
    m (A + 5 * i + 3) = (ax.getD i (0, 0, 0, 0, 0)).2.2.2.1 ∧
    m (A + 5 * i + 4) = (ax.getD i (0, 0, 0, 0, 0)).2.2.2.2

section
variable (P : Polygon) (J : Merge.Junction)
include P J
/-- **The auxiliary data of a stop chord `e`**: `anc = 1` iff `e` is not a bracket (it has an
attachment with offset `< Lst`); then, unless `e` is a pocket (attached at offset `0`), the
`nl ≤ 2` labels `l₀, l₁` (region indices of `N₂`) are side labels of `e` (`EvSideLab`); `par` is
`k + 1` for the chord `k` of `N₂` containing `e`, if any (`0` if none). -/
def AuxOK (N₂ : NF) (e : Set Point)
    (x : ℕ × ℕ × ℕ × ℕ × ℕ) : Prop :=
  x.1 ≤ 1 ∧ (x.1 = 1 ↔ ¬ EvBrk J e) ∧ x.2.1 ≤ 2 ∧
    (0 < x.2.1 → x.2.2.1 < N₂.nRegions) ∧ (1 < x.2.1 → x.2.2.2.1 < N₂.nRegions) ∧
    (x.1 = 1 → (∀ (q : ℕ) (s : ℝ), SideAttach (chainModel J.whole).W e q s → oW J (q + s) ≠ 0) →
      EvSideLab J (N₂.F (chainModel J.right) (Qof P))
        (labSet J (Qof P) N₂ x.2.1 x.2.2.1 x.2.2.2.1 0 0) e) ∧
    x.2.2.2.2 ≤ N₂.nChords ∧
    (∀ c ∈ N₂.F (chainModel J.right) (Qof P), e ⊆ c →
      0 < x.2.2.2.2 ∧ (N₂.chord (x.2.2.2.2 - 1)).toSet (chainModel J.right) (Qof P) = c) ∧
    (0 < x.2.2.2.2 → e ⊆ (N₂.chord (x.2.2.2.2 - 1)).toSet (chainModel J.right) (Qof P))

/-- **The post of stage 2** (from `c` to `c'`, normal forms `N₁`, `N₂`): the stop records `rs`
(`StopRecsAt` at `sB`, count `sC`) satisfy `StopsOK` (all attachments on the `C₁` part of the stop
chords, sorted by offset, without duplicates) and the word facts of `Out`; the auxiliary records
(`aB`, one per stop) satisfy `AuxOK`; at most `4 K₂ + 8` stops (each of the `≤ 2 K₂ + 4`
stop chords has at most two attachments); both arrays are fresh
(between the allocators of `c` and `c'`); the memory below the allocator of `c` and the registers
outside `S2R` (and the oracle bands, the allocator) are unchanged. -/
def StopOut (_N₁ N₂ : NF) (c c' : Config) : Prop :=
  ∃ (rs : List (ℕ × ℕ × ℕ × ℕ × ℕ)) (ax : List (ℕ × ℕ × ℕ × ℕ × ℕ)),
    rs.length = c'.nreg sC ∧ ax.length = rs.length ∧
    StopRecsAt c'.nmem (c'.nreg sB) rs ∧ AuxRecsAt c'.nmem (c'.nreg aB) ax ∧
    StopsOK J (N₂.F (chainModel J.right) (Qof P)) (stopsOf J (Qof P) N₂ rs) ∧
    (∀ r ∈ rs, PosW P J r.1 r.2.1 ∧ r.2.2.1 ≤ 2 ∧ r.2.2.2.2 ≤ 1 ∧
      (r.2.2.1 = 1 → r.2.2.2.1 < N₂.nChords)) ∧
    (∀ i, i < rs.length → AuxOK P J N₂
      (stopSet J (Qof P) N₂ (rs.getD i (0, 0, 0, 0, 0)).2.2.1 (rs.getD i (0, 0, 0, 0, 0)).2.2.2.1
        (rs.getD i (0, 0, 0, 0, 0)).2.2.2.2) (ax.getD i (0, 0, 0, 0, 0))) ∧
    rs.length ≤ 4 * N₂.nChords + 8 ∧
    c.nreg ALLOC ≤ c'.nreg sB ∧ c'.nreg sB + 5 * rs.length ≤ c'.nreg ALLOC ∧
    c.nreg ALLOC ≤ c'.nreg aB ∧ c'.nreg aB + 5 * rs.length ≤ c'.nreg ALLOC ∧
    (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) ∧
    (∀ r, bandOf r ∉ oracleBands → ¬ S2R r → r ≠ ALLOC → c'.nreg r = c.nreg r)


end

/-- **Task B: stage 2**, for every shooter, at cost
`κS D · (K₁ + K₂ + 1) · (F γ + ⌈log₂ (K₁ + K₂ + 1)⌉ + 1)`. -/
def StopTask : Prop :=
  ∃ (mk2 : Stmt → Stmt) (κS : ℕ → ℕ), ∀ (sh : Stmt) (Bs : Finset ℕ) (F : ℕ → ℕ) (X : MemCtx)
    (Ok : Polygon → Model → Prop) (P : Polygon) (W : ℕ) (c₀ c : Config) (J : Merge.Junction)
    (N₁ N₂ : NF), EvEnv sh Bs F X Ok P W c₀ J N₁ N₂ → IInv W c₀ c →
      c.nreg ALLOC + κS (c₀.nreg (sw 6)) * (N₁.nChords + N₂.nChords + 1) *
          (F (c₀.nreg (sw 5)) + Nat.clog 2 (N₁.nChords + N₂.nChords + 1) + 1) ≤ W →
      IRS P W c₀ (mk2 sh) c (κS (c₀.nreg (sw 6)) * (N₁.nChords + N₂.nChords + 1) *
          (F (c₀.nreg (sw 5)) + Nat.clog 2 (N₁.nChords + N₂.nChords + 1) + 1))
        (StopOut P J N₁ N₂ c)

/-! ## D: faced regions of `N₂` and the start -/

/-- The input registers of `face`: a walk edge `fE` of `C₂` (vertex position `(fE, 0)`), the side
`fA` (`0` before, `1` after); the output `fR`. -/
def fE : ℕ := sw 2610
def fA : ℕ := sw 2611
def fR : ℕ := sw 2612

/-- The registers `face` may write (besides the oracle bands and the allocator). -/
def FR (r : ℕ) : Prop := (sw 700 ≤ r ∧ r < sw 2200) ∨ r = fR ∨ (sw 3000 ≤ r ∧ r < sw 6000)

/-- **The post of `face`**: `fR` is the index of a region of `N₂` faced just before (`fA = 0`) or
just after (`fA = 1`) the vertex position `(fE, 0)` of the walk of `C₂`. -/
def FaceOut (P : Polygon) (J : Merge.Junction) (N₂ : NF) (c c' : Config) : Prop :=
  c'.nreg fR < N₂.nRegions ∧
    (c.nreg fA = 0 → BeforeFaces (chainModel J.right) (c.nreg fE) 0
      (regOf (chainModel J.right) (Qof P) N₂ (c'.nreg fR))) ∧
    (c.nreg fA = 1 → AfterFaces (chainModel J.right) (c.nreg fE) 0
      (regOf (chainModel J.right) (Qof P) N₂ (c'.nreg fR))) ∧
    (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) ∧ c.nreg ALLOC ≤ c'.nreg ALLOC ∧
    (∀ r, bandOf r ∉ oracleBands → ¬ FR r → r ≠ ALLOC → c'.nreg r = c.nreg r)

/-- **Task D2** (mathematics): **the invariant at the start** when every chord of `F₂⁺` attached
at the start key (offset `Lst`, the copy of the shared vertex on the `C₁` side) is a bracket: the
label set `{V}` of the region of `S₂` faced just before the end of the right stretch in the walk
of `C₂` (`valid_start`). -/
def StartTask : Prop :=
  ∀ (J : Merge.Junction) (Q : Polygon) (S₂ : Set (Set Point)), J.P.Simple →
    (chainModel J.right).ChordFamily Q S₂ → (chainModel J.whole).ChordFamily Q (F₂plus J S₂) →
    (∀ e ∈ F₂plus J S₂, SideAttach (chainModel J.whole).W e
      ((gW J + Lst J) % (chainModel J.whole).W.n) 0 → EvBrk J e) →
    ∀ V ∈ (chainModel J.right).regions S₂,
      BeforeFaces (chainModel J.right)
        ((6 + tpos J.right 0 + (dq (rL1 J) (rδ J) (rL1 J + rL2 J - 1) + 1)) %
          (chainModel J.right).W.n) 0 V →
      EvInv J S₂ (Lst J) {V}

/-! ## C: the window of the event loop -/

/-- The window registers (outputs): the part-end flag `wX`, the window end `(wE, wH)` (a position
of the walk of `C`), the gathered arcs `(wGB, wGK)` (`SweepEvShot.lean`). -/
def wE : ℕ := sw 2423
def wH : ℕ := sw 2424
def wX : ℕ := sw 2425

/-- The registers the window computation may write (besides the oracle bands and the allocator). -/
def WR (r : ℕ) : Prop :=
  (sw 700 ≤ r ∧ r < sw 2200) ∨ (sw 2420 ≤ r ∧ r ≤ sw 2425) ∨ (sw 3000 ≤ r ∧ r < sw 6000)

/-- **The post of the window computation** from the current key `(kE, kH)` (offset `oL`): the
arcs of at most two regions `rs` of `N₁` are gathered (`regArcs`, normalised `nArc`, fresh
array); the window ends at the part end (`wX = 1`) or at the position `(wE, wH)` beyond the key
(`wX = 0`), which is the gap start (offset `Lst + lL1`) or the image of a cut key of `N₁`; every
valid offset of the walk of `C₁` whose image lies in `(oL, end]` has its point on the gathered
arcs (`loSet`, no holes). -/
def WinOut (P : Polygon) (J : Merge.Junction) (N₁ : NF) (c c' : Config) : Prop :=
  ∃ rs : List ℕ, rs.length ≤ 2 ∧ (∀ r ∈ rs, r < N₁.nRegions) ∧
    c'.nreg wGK = (regArcs N₁ rs).length ∧ c.nreg ALLOC ≤ c'.nreg wGB ∧
    c'.nreg wGB + 4 * (regArcs N₁ rs).length ≤ c'.nreg ALLOC ∧
    (∀ k, k < (regArcs N₁ rs).length → ShotList.arcAt c'.nmem (c'.nreg wGB) k =
      nArc (chainModel J.left) (Qof P) N₁ ((regArcs N₁ rs).getD k 0)) ∧
    c'.nreg wX ≤ 1 ∧
    (c'.nreg wX = 0 → PosW P J (c'.nreg wE) (c'.nreg wH) ∧
      offK P J (c.nreg kE) (c.nreg kH) < offK P J (c'.nreg wE) (c'.nreg wH) ∧
      (offK P J (c'.nreg wE) (c'.nreg wH) = (Lst J : ℝ) + lL1 J ∨
        ∃ (d : ℕ) (t : ℝ), MValid J d t ∧ 0 ≤ t ∧ t ≤ 1 ∧
          offK P J (c'.nreg wE) (c'.nreg wH) = (Lst J : ℝ) + ψ J d + t ∧
          (chainModel J.left).IsCut (N₁.F (chainModel J.left) (Qof P))
            (((b₁ J + d) % (chainModel J.left).W.n : ℕ) + t))) ∧
    (∀ (d : ℕ) (t : ℝ), MValid J d t → 0 ≤ t → t < 1 →
      offK P J (c.nreg kE) (c.nreg kH) < (Lst J : ℝ) + ψ J d + t →
      (c'.nreg wX = 0 → (Lst J : ℝ) + ψ J d + t ≤ offK P J (c'.nreg wE) (c'.nreg wH)) →
      sidePt (chainModel J.left).W ((b₁ J + d) % (chainModel J.left).W.n) t ∈
        ShotList.loSet (chainModel J.left) (Qof P) c'.nmem (c'.nreg wGB)
          (regArcs N₁ rs).length []) ∧
    (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) ∧
    (∀ r, bandOf r ∉ oracleBands → ¬ WR r → r ≠ ALLOC → c'.nreg r = c.nreg r)

/-- **Task C1: the window**, for a key `(kE, kH)` of the `C₁` part (`Lst ≤ oL < n`), at cost
`κW D · (TLR + 1)` (`TLR = c₀.nreg TLR`, the length of the power table of `locJ`). -/
def WinTask : Prop :=
  ∃ (win : Stmt) (κW : ℕ → ℕ), ∀ (sh : Stmt) (Bs : Finset ℕ) (F : ℕ → ℕ) (X : MemCtx)
    (Ok : Polygon → Model → Prop) (P : Polygon) (W : ℕ) (c₀ c : Config) (J : Merge.Junction)
    (N₁ N₂ : NF), EvEnv sh Bs F X Ok P W c₀ J N₁ N₂ → IInv W c₀ c →
      PosW P J (c.nreg kE) (c.nreg kH) → (Lst J : ℝ) ≤ offK P J (c.nreg kE) (c.nreg kH) →
      c.nreg ALLOC + κW (c₀.nreg (sw 6)) * (c₀.nreg TLR + 1) ≤ W →
      IRS P W c₀ win c (κW (c₀.nreg (sw 6)) * (c₀.nreg TLR + 1)) (WinOut P J N₁ c)

/-- **Task C2 (mathematics): the number of arcs** of a normal form of a chain model:
`arcs ≤ 3 K + 1` (`K + 1` regions, `arcsPerRegion`, each chord on two regions). -/
def ArcsTask : Prop :=
  ∀ (C : Chain) (Q : Polygon) (N : NF), C.P.Simple → IsNF (chainModel C) Q N →
    N.arcs.length ≤ 3 * N.nChords + 1

end

end SweepEv

end Chazelle.Core
