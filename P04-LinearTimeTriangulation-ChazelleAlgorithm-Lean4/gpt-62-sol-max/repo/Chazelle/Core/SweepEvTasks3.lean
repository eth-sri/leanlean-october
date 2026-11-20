module

public import Chazelle.Core.SweepEvTasks2

/-!
# The sweep (WP-D), stage 3: contracts of the pieces of the event loop (batch 3)

* `OrgsTask` (RAM, generic): the enumeration of the endpoint queries tried in one iteration — the
  chords of the regions of the current label list (`kN`, `kL`), of the gap regions (`gN`, `gR`) and
  the parents of the stops `sP`, `sP + 1` — running an abstract per-origin statement `od` with an
  abstract invariant `Inv` (a set of processed queries and a configuration).
* `KeyTask` (RAM): the next key of the event loop (the best candidate, the next stop, the window
  end), its label list, the log record, the stop pointer.
* `PrepTask` (RAM): the endpoint table cleared and the log array allocated.
* `StartMathTask` (mathematics): the start key is a word-level position, and every chord attached
  at it is a stop chord.
* `CountTask` (mathematics): the offsets of the cut keys of `F₂⁺` and of the window ends are at
  most `4 K₂ + 2 K₁ + 9`.
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
open Chazelle.Chain (SideAttach sidePt)
open Chazelle.Visibility (rayPt)

@[expose] public section

/-! ## Registers of the event loop -/

/-- The label list of the current key: count `kN`, labels `kL … kL + 3`. -/
def kN : ℕ := sw 2402
def kL : ℕ := sw 2403
/-- The gap regions: count `gN ≤ 2`, regions `gR`, `gR + 1`. -/
def gN : ℕ := sw 2440
def gR : ℕ := sw 2441
/-- The stop pointer (the first stop beyond the current key) and the done flag. -/
def sP : ℕ := sw 2450
def dF : ℕ := sw 2451

/-! ## E: the origins of one iteration -/

/-- The registers the enumeration writes besides those of `od`: `oK`, `oS` and the loop
registers `sw 2460 … 2479`. -/
def LR (r : ℕ) : Prop := r = oK ∨ r = oS ∨ (sw 2460 ≤ r ∧ r < sw 2480)

/-- The registers the enumeration reads (kept by `od`). -/
def ER (r : ℕ) : Prop :=
  r = kN ∨ (kL ≤ r ∧ r < kL + 4) ∨ r = gN ∨ r = gR ∨ r = gR + 1 ∨ r = sP ∨ r = sC ∨ r = aB

/-- The endpoint queries of the chords of region `r` of `N` (both ends). -/
def regO (N : NF) (r : ℕ) : Set ℕ :=
  {j | ∃ k ∈ (N.region r).chords, ∃ s, s ≤ 1 ∧ j = 2 * k + s}

/-- The parent field of the auxiliary record `i` (`k + 1` for the chord `k` of `N₂`, or `0`). -/
def parOf (c : Config) (i : ℕ) : ℕ := c.nmem (c.nreg aB + 5 * i + 4)

/-- The endpoint queries of the parents of the stops `sP` and `sP + 1` (both ends). -/
def parO (c : Config) : Set ℕ :=
  {j | ∃ i, (i = c.nreg sP ∨ i = c.nreg sP + 1) ∧ i < c.nreg sC ∧ 0 < parOf c i ∧
    ∃ s, s ≤ 1 ∧ j = 2 * (parOf c i - 1) + s}

/-- **The endpoint queries tried in one iteration**: the chords of the regions of the label list,
of the gap regions, and the parents of the next two stops. -/
def iterO (N : NF) (c : Config) : Set ℕ :=
  {j | ∃ i, i < min (c.nreg kN) 4 ∧ j ∈ regO N (c.nreg (kL + i))} ∪
    {j | ∃ i, i < min (c.nreg gN) 2 ∧ j ∈ regO N (c.nreg (gR + i))} ∪ parO c

/-- **Task E: the origin enumeration**, generic in the per-origin statement `od` (cost `Kod`, run
with `oK = k`, `oS = s`, `k < K₂`, `s ≤ 1`) and the invariant `Inv O c` (`O` the processed
queries; stable under changes of the loop registers `LR`).  Cost
`(12 D + 8) (Kod + κO) + κO` (`D = c₀.nreg (sw 6)` bounds the chords of a region,
`GranSize`). -/
def OrgsTask : Prop :=
  ∃ (orgs : Stmt → Stmt) (κO : ℕ), ∀ (sh : Stmt) (Bs : Finset ℕ) (F : ℕ → ℕ) (X : MemCtx)
    (Ok : Polygon → Model → Prop) (P : Polygon) (W : ℕ) (c₀ : Config) (J : Merge.Junction)
    (N₁ N₂ : NF), EvEnv sh Bs F X Ok P W c₀ J N₁ N₂ →
    ∀ (od : Stmt) (Kod : ℕ) (Inv : Set ℕ → Config → Prop),
    (∀ (O : Set ℕ) (c : Config), IInv W c₀ c → Inv O c → c.nreg oK < N₂.nChords →
      c.nreg oS ≤ 1 → c.nreg ALLOC + Kod ≤ W →
      IRS P W c₀ od c Kod (fun c' => Inv (insert (2 * c.nreg oK + c.nreg oS) O) c' ∧
        (∀ r, (LR r ∧ r ≠ oK ∧ r ≠ oS) ∨ ER r → c'.nreg r = c.nreg r) ∧
        (∀ x, c.nreg aB ≤ x → x < c.nreg aB + 5 * c.nreg sC → c'.nmem x = c.nmem x))) →
    (∀ (O : Set ℕ) (c c' : Config), Inv O c → (∀ r, ¬ LR r → c'.nreg r = c.nreg r) →
      c'.nmem = c.nmem → c'.rmem = c.rmem → c'.rreg = c.rreg → c'.output = c.output →
      Inv O c') →
    ∀ (O : Set ℕ) (c : Config), IInv W c₀ c → Inv O c →
      (∀ i, i < min (c.nreg kN) 4 → c.nreg (kL + i) < N₂.nRegions) →
      (∀ i, i < min (c.nreg gN) 2 → c.nreg (gR + i) < N₂.nRegions) →
      (∀ i, i < c.nreg sC → parOf c i ≤ N₂.nChords) →
      c.nreg aB + 5 * c.nreg sC ≤ c.nreg ALLOC →
      c.nreg ALLOC + ((12 * c₀.nreg (sw 6) + 8) * (Kod + κO) + κO) ≤ W →
      IRS P W c₀ (orgs od) c ((12 * c₀.nreg (sw 6) + 8) * (Kod + κO) + κO)
        (Inv (O ∪ iterO N₂ c))

/-! ## K: the next key -/

/-- The position of stop `i` (the stop records at `sB`, five words each). -/
def stopE (c : Config) (i : ℕ) : ℕ := c.nmem (c.nreg sB + 5 * i)
def stopH (c : Config) (i : ℕ) : ℕ := c.nmem (c.nreg sB + 5 * i + 1)

/-- The labels of the auxiliary record `i` at `A` if it is anchored: `l₀, l₁` up to the count
`nl` (at most two). -/
def stopLabs (m : ℕ → ℕ) (A i : ℕ) : List ℕ :=
  if m (A + 5 * i) = 1 then (List.range (min (m (A + 5 * i + 1)) 2)).map fun t => m (A + 5 * i + 2 + t)
  else []

/-- Appending a list of labels (`addL` each). -/
def addLs (l vs : List ℕ) : List ℕ := vs.foldl addL l

/-- The registers the next-key step may write (besides the oracle bands and the allocator). -/
def KR (r : ℕ) : Prop :=
  r = kE ∨ r = kH ∨ r = kN ∨ (kL ≤ r ∧ r < kL + 4) ∨ r = sP ∨ r = dF ∨ r = lC ∨
    (sw 2480 ≤ r ∧ r < sw 2500) ∨ (sw 700 ≤ r ∧ r < sw 2200) ∨ (sw 3000 ≤ r ∧ r < sw 6000)

/-- **The post of the next-key step** from `c` to `c'`.  The candidates are the best candidate
`(bE, bH)` (if `bF = 1`), the stop `sP` (if `sP < sC`) and the window end `(wE, wH)` (if
`wX = 0`).  If there is none, `dF = 1` and only the scratch changes.  Otherwise `dF = 0`; the new
key `(kE, kH)` is a candidate of least offset `o'`; the stop pointer skips exactly the stops at
offset `o'`; the label list is the best candidate's (if at offset `o'`) followed by the labels of
the skipped anchored stops when one of these exists (`An`), and the old one otherwise; the log
record `(kE, kH, kN, kL … kL + 3)` is written at `lB + 7 lC` and `lC` is incremented. -/
def KeyOut (P : Polygon) (J : Merge.Junction) (c c' : Config) : Prop :=
  (∀ r, bandOf r ∉ oracleBands → ¬ KR r → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
  c.nreg ALLOC ≤ c'.nreg ALLOC ∧
  ((c.nreg bF ≠ 1 ∧ ¬ c.nreg sP < c.nreg sC ∧ c.nreg wX ≠ 0) →
    c'.nreg dF = 1 ∧ c'.nreg lC = c.nreg lC ∧ (∀ x, x < c.nreg ALLOC → c'.nmem x = c.nmem x)) ∧
  ((c.nreg bF = 1 ∨ c.nreg sP < c.nreg sC ∨ c.nreg wX = 0) →
    c'.nreg dF = 0 ∧
    ((c.nreg bF = 1 ∧ c'.nreg kE = c.nreg bE ∧ c'.nreg kH = c.nreg bH) ∨
      (c.nreg sP < c.nreg sC ∧ c'.nreg kE = stopE c (c.nreg sP) ∧
        c'.nreg kH = stopH c (c.nreg sP)) ∨
      (c.nreg wX = 0 ∧ c'.nreg kE = c.nreg wE ∧ c'.nreg kH = c.nreg wH)) ∧
    (c.nreg bF = 1 →
      offK P J (c'.nreg kE) (c'.nreg kH) ≤ offK P J (c.nreg bE) (c.nreg bH)) ∧
    (c.nreg sP < c.nreg sC → offK P J (c'.nreg kE) (c'.nreg kH) ≤
      offK P J (stopE c (c.nreg sP)) (stopH c (c.nreg sP))) ∧
    (c.nreg wX = 0 →
      offK P J (c'.nreg kE) (c'.nreg kH) ≤ offK P J (c.nreg wE) (c.nreg wH)) ∧
    c.nreg sP ≤ c'.nreg sP ∧ c'.nreg sP ≤ c.nreg sC ∧
    (∀ i, c.nreg sP ≤ i → i < c'.nreg sP →
      offK P J (stopE c i) (stopH c i) = offK P J (c'.nreg kE) (c'.nreg kH)) ∧
    (c'.nreg sP < c.nreg sC →
      offK P J (stopE c (c'.nreg sP)) (stopH c (c'.nreg sP)) ≠
        offK P J (c'.nreg kE) (c'.nreg kH)) ∧
    c'.nreg kN ≤ 4 ∧
    (((c.nreg bF = 1 ∧ offK P J (c.nreg bE) (c.nreg bH) = offK P J (c'.nreg kE) (c'.nreg kH)) ∨
        ∃ i, c.nreg sP ≤ i ∧ i < c'.nreg sP ∧ c.nmem (c.nreg aB + 5 * i) = 1) →
      lblOf c' kN kL = addLs
        (if c.nreg bF = 1 ∧ offK P J (c.nreg bE) (c.nreg bH) = offK P J (c'.nreg kE) (c'.nreg kH)
          then lblOf c bN bL else [])
        ((List.range' (c.nreg sP) (c'.nreg sP - c.nreg sP)).flatMap
          (stopLabs c.nmem (c.nreg aB)))) ∧
    (¬ ((c.nreg bF = 1 ∧ offK P J (c.nreg bE) (c.nreg bH) = offK P J (c'.nreg kE) (c'.nreg kH)) ∨
        ∃ i, c.nreg sP ≤ i ∧ i < c'.nreg sP ∧ c.nmem (c.nreg aB + 5 * i) = 1) →
      lblOf c' kN kL = lblOf c kN kL ∧ c'.nreg kN = c.nreg kN) ∧
    c'.nreg lC = c.nreg lC + 1 ∧
    c'.nmem (c.nreg lB + 7 * c.nreg lC) = c'.nreg kE ∧
    c'.nmem (c.nreg lB + 7 * c.nreg lC + 1) = c'.nreg kH ∧
    c'.nmem (c.nreg lB + 7 * c.nreg lC + 2) = c'.nreg kN ∧
    (∀ i, i < 4 → c'.nmem (c.nreg lB + 7 * c.nreg lC + 3 + i) = c'.nreg (kL + i)) ∧
    (∀ x, x < c.nreg ALLOC → (x < c.nreg lB + 7 * c.nreg lC ∨ c.nreg lB + 7 * c.nreg lC + 7 ≤ x) →
      c'.nmem x = c.nmem x))

/-- **Task K: the next key**, at a constant cost `κK`.  Hypotheses: the positions involved are
word-level (`PosW`), the stop records are sorted by offset with at most two at one offset, the
label lists have at most four labels, the stop and auxiliary arrays lie below the allocator, and
the log array has room for one more record (at or above the allocator of `c₀`). -/
def KeyTask : Prop :=
  ∃ (key : Stmt) (κK : ℕ), ∀ (sh : Stmt) (Bs : Finset ℕ) (F : ℕ → ℕ) (X : MemCtx)
    (Ok : Polygon → Model → Prop) (P : Polygon) (W : ℕ) (c₀ c : Config) (J : Merge.Junction)
    (N₁ N₂ : NF), EvEnv sh Bs F X Ok P W c₀ J N₁ N₂ → IInv W c₀ c →
      PosW P J (c.nreg kE) (c.nreg kH) →
      (c.nreg bF = 1 → PosW P J (c.nreg bE) (c.nreg bH)) →
      (c.nreg wX = 0 → PosW P J (c.nreg wE) (c.nreg wH)) →
      (∀ i, i < c.nreg sC → PosW P J (stopE c i) (stopH c i)) →
      (∀ i i', i ≤ i' → i' < c.nreg sC →
        offK P J (stopE c i) (stopH c i) ≤ offK P J (stopE c i') (stopH c i')) →
      (∀ i, i + 2 < c.nreg sC →
        offK P J (stopE c i) (stopH c i) < offK P J (stopE c (i + 2)) (stopH c (i + 2))) →
      c.nreg sP ≤ c.nreg sC → c.nreg kN ≤ 4 → c.nreg bN ≤ 4 →
      c.nreg sB + 5 * c.nreg sC ≤ c.nreg ALLOC → c.nreg aB + 5 * c.nreg sC ≤ c.nreg ALLOC →
      c₀.nreg ALLOC ≤ c.nreg lB → c.nreg lB + 7 * (c.nreg lC + 1) ≤ c.nreg ALLOC →
      c.nreg ALLOC + κK ≤ W →
      IRS P W c₀ key c κK (KeyOut P J c)

/-! ## P: the table and the log array -/

/-- The registers the preparation may write (besides the oracle bands and the allocator). -/
def PR (r : ℕ) : Prop := r = lB ∨ r = lC ∨ (sw 2480 ≤ r ∧ r < sw 2500)

/-- **The post of the preparation**: the flags of the `2 K₂` table records at `cTB` are `0`, the
log array of `16 (K₁ + K₂ + 1)` records (count `lC = 0`) lies after the table, below the
allocator. -/
def PrepOut (N₁ N₂ : NF) (c c' : Config) : Prop :=
  (∀ j, j < 2 * N₂.nChords → c'.nmem (c.nreg cTB + 3 * j) = 0) ∧
  c.nreg cTB + 6 * N₂.nChords ≤ c'.nreg lB ∧ c'.nreg lC = 0 ∧
  c'.nreg lB + 7 * (16 * (N₁.nChords + N₂.nChords + 1)) ≤ c'.nreg ALLOC ∧
  (∀ x, x < c.nreg ALLOC → c'.nmem x = c.nmem x) ∧
  (∀ r, bandOf r ∉ oracleBands → ¬ PR r → r ≠ ALLOC → c'.nreg r = c.nreg r)

/-- **Task P: the preparation**, from a configuration whose allocator is the table base, at cost
`κP (K₁ + K₂ + 1)`. -/
def PrepTask : Prop :=
  ∃ (prep : Stmt) (κP : ℕ), ∀ (sh : Stmt) (Bs : Finset ℕ) (F : ℕ → ℕ) (X : MemCtx)
    (Ok : Polygon → Model → Prop) (P : Polygon) (W : ℕ) (c₀ c : Config) (J : Merge.Junction)
    (N₁ N₂ : NF), EvEnv sh Bs F X Ok P W c₀ J N₁ N₂ → IInv W c₀ c →
      c.nreg ALLOC = c.nreg cTB →
      c.nreg ALLOC + κP * (N₁.nChords + N₂.nChords + 1) ≤ W →
      IRS P W c₀ prep c (κP * (N₁.nChords + N₂.nChords + 1)) (PrepOut N₁ N₂ c)

/-! ## S: the start key (mathematics) -/

/-- **Task S (mathematics)**: the start key `((gW + Lst) % n, 0)` (offset `Lst`, the copy of the
shared vertex on the `C₁` side) is a word-level position, and every chord of `F₂⁺` attached at it
is a stop chord (a chord from a valid origin ending at the shared vertex is the shared chord seen
from the shared vertex). -/
def StartMathTask : Prop :=
  ∀ (P : Polygon) (J : Merge.Junction) (N : NF), J.P.Simple → IsNF (chainModel J.right) (Qof P) N →
    PosW P J ((gW J + Lst J) % (chainModel J.whole).W.n) 0 ∧
    oW J (((gW J + Lst J) % (chainModel J.whole).W.n : ℕ) + 0) = Lst J ∧
    ∀ e ∈ F₂plus J (N.F (chainModel J.right) (Qof P)),
      SideAttach (chainModel J.whole).W e ((gW J + Lst J) % (chainModel J.whole).W.n) 0 →
      StopChord2 J (N.F (chainModel J.right) (Qof P)) e

/-! ## C: the number of keys (mathematics) -/

/-- The offsets of the cut keys of `F₂⁺` (in the walk of `C`). -/
def cutOffs (J : Merge.Junction) (S₂ : Set (Set Point)) : Set ℝ :=
  {o | ∃ x : ℝ, (chainModel J.whole).IsCut (F₂plus J S₂) x ∧ 0 ≤ x ∧
    x < (chainModel J.whole).W.n ∧ o = oW J x}

/-- The offsets of the possible window ends: the gap start and the images of the cut keys of
`N₁` (`WinOut`). -/
def winOffs (P : Polygon) (J : Merge.Junction) (N₁ : NF) : Set ℝ :=
  {(Lst J : ℝ) + lL1 J} ∪
    {o | ∃ (d : ℕ) (t : ℝ), MValid J d t ∧ 0 ≤ t ∧ t ≤ 1 ∧
      (chainModel J.left).IsCut (N₁.F (chainModel J.left) (Qof P))
        (((b₁ J + d) % (chainModel J.left).W.n : ℕ) + t) ∧ o = (Lst J : ℝ) + ψ J d + t}

/-- **Task C (mathematics): the number of keys**: the offsets of the cut keys of `F₂⁺` and of the
window ends form a finite set of at most `4 K₂ + 2 K₁ + 9` offsets. -/
def CountTask : Prop :=
  ∀ (P : Polygon) (J : Merge.Junction) (N₁ N₂ : NF), J.P.Simple →
    IsNF (chainModel J.left) (Qof P) N₁ → IsNF (chainModel J.right) (Qof P) N₂ →
    (cutOffs J (N₂.F (chainModel J.right) (Qof P)) ∪ winOffs P J N₁).Finite ∧
    (cutOffs J (N₂.F (chainModel J.right) (Qof P)) ∪ winOffs P J N₁).ncard ≤
      4 * N₂.nChords + 2 * N₁.nChords + 9

end

end SweepEv

end Chazelle.Core
