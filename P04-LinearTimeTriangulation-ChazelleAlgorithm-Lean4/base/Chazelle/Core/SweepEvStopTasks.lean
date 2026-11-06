module

public import Chazelle.Core.SweepEvStopR

/-!
# The sweep (WP-D), stage 2: contracts of the pieces of `StopTask`

Stage 2 computes, per stop origin, the raw stop records
`(e, h, dc, kind, k, b, anc, nl, l₀, l₁, par)` (11 words at `gRB + 11 i`, count `gRC`):
the position `(e, h)` of an attachment of the stop chord on the `C₁` part, the leaving direction
code `dc` (`1`: the position is the left end of the chord), the record codes, the auxiliary data.
The pieces:

* `SortTask` (RAM): sort the raw records by the key `(offset, dc)`, drop equal neighbours, and
  write the stop records and the auxiliary records (`StopOut` layout);
* `LabTask` (mathematics): the side labels of an anchored stop chord (`EvSideLab`) from its parent
  chord in `S₂` (`{up, dn}`) or, without a parent, from the regions of `S₂` faced just after and
  just before the counterpart in the walk of `C₂` of its attachment on the open right stretch;
* `FaceRTask` (RAM): those faced regions (indices of `N₂`) at a position of the walk of `C₂`;
* `BruteTask` (RAM): the first hit of `C₁` from a symbolic point off `C₁` (the top of `C₂`), by
  a shot at all arcs of `N₁`.
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep SweepStop
open Chazelle.Visibility (rayPt)
open Chazelle.Chain (SideAttach sidePt sideLeft)
open Chazelle.Merge (FreeAt)

@[expose] public section

/-! ## The raw records -/

/-- The record `(e, h, kind, k, b)` of the raw record `i` at `RB`. -/
def rawRec (m : ℕ → ℕ) (RB i : ℕ) : ℕ × ℕ × ℕ × ℕ × ℕ :=
  (m (RB + 11 * i), m (RB + 11 * i + 1), m (RB + 11 * i + 3), m (RB + 11 * i + 4),
    m (RB + 11 * i + 5))

/-- The leaving direction code of the raw record `i`. -/
def rawDc (m : ℕ → ℕ) (RB i : ℕ) : ℕ := m (RB + 11 * i + 2)

/-- The auxiliary record `(anc, nl, l₀, l₁, par)` of the raw record `i`. -/
def rawAux (m : ℕ → ℕ) (RB i : ℕ) : ℕ × ℕ × ℕ × ℕ × ℕ :=
  (m (RB + 11 * i + 6), m (RB + 11 * i + 7), m (RB + 11 * i + 8), m (RB + 11 * i + 9),
    m (RB + 11 * i + 10))

/-! ## Sort and dedupe (RAM) -/

/-- The registers the sort may write (besides the oracle bands and the allocator). -/
def SoR (r : ℕ) : Prop :=
  (sw 700 ≤ r ∧ r < sw 2200) ∨ (sw 2600 ≤ r ∧ r ≤ sw 2602) ∨ (sw 3000 ≤ r ∧ r < sw 4000) ∨
    (sw 5000 ≤ r ∧ r < sw 6000)

/-- **The post of the sort**: a list `O` of raw record indices with strictly increasing keys
`(offK, dc)` covering the keys of all raw records; the stop records (`sB`, count `sC`) and the
auxiliary records (`aB`) are those of `O`, in fresh arrays. -/
def SortOut (P : Polygon) (J : Merge.Junction) (c c' : Config) : Prop :=
  ∃ O : List ℕ, (∀ i ∈ O, i < c.nreg gRC) ∧
    O.Pairwise (fun i j => KLt (rKey P J (rawRec c.nmem (c.nreg gRB) i) (rawDc c.nmem (c.nreg gRB) i))
      (rKey P J (rawRec c.nmem (c.nreg gRB) j) (rawDc c.nmem (c.nreg gRB) j))) ∧
    (∀ i, i < c.nreg gRC → ∃ j ∈ O,
      rKey P J (rawRec c.nmem (c.nreg gRB) j) (rawDc c.nmem (c.nreg gRB) j) =
        rKey P J (rawRec c.nmem (c.nreg gRB) i) (rawDc c.nmem (c.nreg gRB) i)) ∧
    c'.nreg sC = O.length ∧
    StopRecsAt c'.nmem (c'.nreg sB) (O.map (rawRec c.nmem (c.nreg gRB))) ∧
    AuxRecsAt c'.nmem (c'.nreg aB) (O.map (rawAux c.nmem (c.nreg gRB))) ∧
    c.nreg ALLOC ≤ c'.nreg sB ∧ c'.nreg sB + 5 * O.length ≤ c'.nreg ALLOC ∧
    c.nreg ALLOC ≤ c'.nreg aB ∧ c'.nreg aB + 5 * O.length ≤ c'.nreg ALLOC ∧
    (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) ∧
    (∀ r, bandOf r ∉ oracleBands → ¬ SoR r → r ≠ ALLOC → c'.nreg r = c.nreg r)

/-- **Task S: sort and dedupe** the `S = gRC` raw records at `gRB` (positions `PosW`, codes
`dc ≤ 1`, below the allocator), at cost `κ (S + 1) (⌈log₂ (S + 1)⌉ + 1)`. -/
def SortTask : Prop :=
  ∃ (srt : Stmt) (κ : ℕ), ∀ (sh : Stmt) (Bs : Finset ℕ) (F : ℕ → ℕ) (X : MemCtx)
    (Ok : Polygon → Model → Prop) (P : Polygon) (W : ℕ) (c₀ c : Config) (J : Merge.Junction)
    (N₁ N₂ : NF), EvEnv sh Bs F X Ok P W c₀ J N₁ N₂ → IInv W c₀ c →
      (∀ i, i < c.nreg gRC → PosW P J (c.nmem (c.nreg gRB + 11 * i))
        (c.nmem (c.nreg gRB + 11 * i + 1)) ∧ rawDc c.nmem (c.nreg gRB) i ≤ 1) →
      c.nreg gRB + 11 * c.nreg gRC ≤ c.nreg ALLOC →
      c.nreg ALLOC + κ * (c.nreg gRC + 1) * (Nat.clog 2 (c.nreg gRC + 1) + 1) ≤ W →
      IRS P W c₀ srt c (κ * (c.nreg gRC + 1) * (Nat.clog 2 (c.nreg gRC + 1) + 1))
        (SortOut P J c)

/-! ## The labels (mathematics) -/

/-- The position of the walk of `C₂` corresponding to the offset `d` of the right stretch, just
after the position (`dq d`). -/
noncomputable def cpA (J : Merge.Junction) (d : ℕ) : ℕ :=
  (6 + tpos J.right 0 + dq (rL1 J) (rδ J) d) % (chainModel J.right).W.n

/-- The position of the walk of `C₂` just before the vertex at offset `d` of the right stretch
(`dq (d - 1) + 1`: the end of the previous edge; it differs from `cpA d` only at the split
vertex). -/
noncomputable def cpB (J : Merge.Junction) (d : ℕ) : ℕ :=
  (6 + tpos J.right 0 + (dq (rL1 J) (rδ J) (d - 1) + 1)) % (chainModel J.right).W.n

/-- **Task L (mathematics): the side labels of an anchored stop chord** `e` (not a pocket),
attached on the `C₁` part, with an attachment at the position `(gW + d, t)` of the open right
stretch:
* if `e` lies in a chord `c ∈ S₂`, the regions of `S₂` above and below `c` are side labels;
* otherwise the regions of `S₂` faced just after (`cpA d`, parameter `t`) and just before
  (`cpA d` for `t > 0`, `cpB d` at a vertex) the counterpart position are side labels. -/
def LabTask : Prop :=
  ∀ (J : Merge.Junction) (Q : Polygon) (S₂ : Set (Set Point)) (e : Set Point), J.P.Simple →
    (chainModel J.right).ChordFamily Q S₂ → (chainModel J.whole).ChordFamily Q (F₂plus J S₂) →
    e ∈ F₂plus J S₂ → StopChord2 J S₂ e →
    (∀ (q : ℕ) (s : ℝ), SideAttach (chainModel J.whole).W e q s → oW J (q + s) ≠ 0) →
    (∃ (q : ℕ) (s : ℝ), SideAttach (chainModel J.whole).W e q s ∧ (Lst J : ℝ) ≤ oW J (q + s)) →
    ∀ (d : ℕ) (t : ℝ), d < Lst J → 0 ≤ t → t < 1 → (t = 0 → d ≠ 0) →
    SideAttach (chainModel J.whole).W e ((gW J + d) % (chainModel J.whole).W.n) t →
    (∀ c ∈ S₂, e ⊆ c → ∀ Vu ∈ (chainModel J.right).regions S₂,
      ∀ Vd ∈ (chainModel J.right).regions S₂, SideOf (chainModel J.right) 1 c Vu →
      SideOf (chainModel J.right) (-1) c Vd → EvSideLab J S₂ {Vu, Vd} e) ∧
    ((∀ c ∈ S₂, ¬ e ⊆ c) → ∀ Va ∈ (chainModel J.right).regions S₂,
      ∀ Vb ∈ (chainModel J.right).regions S₂, AfterFaces (chainModel J.right) (cpA J d) t Va →
      (0 < t → BeforeFaces (chainModel J.right) (cpA J d) t Vb) →
      (t = 0 → BeforeFaces (chainModel J.right) (cpB J d) 0 Vb) →
      EvSideLab J S₂ {Va, Vb} e)

/-! ## The faced regions (RAM) -/

def fpE : ℕ := sw 4110
def fpH : ℕ := sw 4111
def fqE : ℕ := sw 4112
def fqH : ℕ := sw 4113
def frA : ℕ := sw 4114
def frB : ℕ := sw 4115

/-- The registers the faced-region procedure may write. -/
def FRR (r : ℕ) : Prop :=
  (sw 700 ≤ r ∧ r < sw 2200) ∨ r = frA ∨ r = frB ∨ (sw 3000 ≤ r ∧ r < sw 4000) ∨
    (sw 5000 ≤ r ∧ r < sw 6000)

/-- **The post of the faced regions**: `frA` is a region of `N₂` faced just after the position
`(fpE, fpH)` of the walk of `C₂`, `frB` one faced just before `(fqE, fqH)`. -/
def FaceROut (P : Polygon) (J : Merge.Junction) (N₂ : NF) (c c' : Config) : Prop :=
  c'.nreg frA < N₂.nRegions ∧ c'.nreg frB < N₂.nRegions ∧
    AfterFaces (chainModel J.right) (c.nreg fpE)
      ((chainModel J.right).param (Qof P) ⟨c.nreg fpE, c.nreg fpH⟩)
      (regOf (chainModel J.right) (Qof P) N₂ (c'.nreg frA)) ∧
    BeforeFaces (chainModel J.right) (c.nreg fqE)
      ((chainModel J.right).param (Qof P) ⟨c.nreg fqE, c.nreg fqH⟩)
      (regOf (chainModel J.right) (Qof P) N₂ (c'.nreg frB)) ∧
    (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) ∧ c.nreg ALLOC ≤ c'.nreg ALLOC ∧
    (∀ r, bandOf r ∉ oracleBands → ¬ FRR r → r ≠ ALLOC → c'.nreg r = c.nreg r)

/-- **Task F: the faced regions** at two proper positions of the walk of `C₂` (the position is a
vertex or not a cut of `S₂`), cost `κ D (TLR + 1)`. -/
def FaceRTask : Prop :=
  ∃ (fr : Stmt) (κ : ℕ → ℕ), ∀ (sh : Stmt) (Bs : Finset ℕ) (F : ℕ → ℕ) (X : MemCtx)
    (Ok : Polygon → Model → Prop) (P : Polygon) (W : ℕ) (c₀ c : Config) (J : Merge.Junction)
    (N₁ N₂ : NF), EvEnv sh Bs F X Ok P W c₀ J N₁ N₂ → IInv W c₀ c →
      c.nreg fpE < (chainModel J.right).W.n →
      ProperPos (chainModel J.right) (Qof P) P.n ⟨c.nreg fpE, c.nreg fpH⟩ →
      ((chainModel J.right).param (Qof P) ⟨c.nreg fpE, c.nreg fpH⟩ = 0 ∨
        ¬ (chainModel J.right).IsCut (N₂.F (chainModel J.right) (Qof P))
          ((chainModel J.right).key (Qof P) ⟨c.nreg fpE, c.nreg fpH⟩)) →
      c.nreg fqE < (chainModel J.right).W.n →
      ProperPos (chainModel J.right) (Qof P) P.n ⟨c.nreg fqE, c.nreg fqH⟩ →
      ((chainModel J.right).param (Qof P) ⟨c.nreg fqE, c.nreg fqH⟩ = 0 ∨
        ¬ (chainModel J.right).IsCut (N₂.F (chainModel J.right) (Qof P))
          ((chainModel J.right).key (Qof P) ⟨c.nreg fqE, c.nreg fqH⟩)) →
      c.nreg ALLOC + κ (c₀.nreg (sw 6)) * (c₀.nreg TLR + 1) ≤ W →
      IRS P W c₀ fr c (κ (c₀.nreg (sw 6)) * (c₀.nreg TLR + 1)) (FaceROut P J N₂ c)

/-! ## The brute-force shot at `N₁` (RAM) -/

def brOS : ℕ := sw 4080
def brOD : ℕ := sw 4083
def brF : ℕ := sw 4084

/-- The registers the brute-force shot may write. -/
def BrR (r : ℕ) : Prop :=
  (sw 700 ≤ r ∧ r < sw 2200) ∨ (sw 4084 ≤ r ∧ r ≤ sw 4090) ∨ (sw 3000 ≤ r ∧ r < sw 4000) ∨
    (sw 5000 ≤ r ∧ r < sw 6000)

/-- **The post of the brute-force shot** from the point `z` in the direction `σ`: the flag `brF`;
if set, a proper walk position `(brF + 1, brF + 2)` of the model of `C₁` of a point of `C₁` or of
the box on the ray at a positive parameter, with its abscissa record at `brF + 3 … brF + 6`; if the
direction is free for `C₁`, the flag is set and the parameter is the first hit of `C₁`. -/
def BruteOut (P : Polygon) (J : Merge.Junction) (z : Point) (σ : ℝ) (c c' : Config) : Prop :=
  c'.nreg brF ≤ 1 ∧
    (c'.nreg brF = 1 → ∃ τ, 0 < τ ∧ OnCB J.left (rayPt z σ τ) ∧
      c'.nreg (brF + 1) < (chainModel J.left).W.n ∧
      ProperPos (chainModel J.left) (Qof P) P.n ⟨c'.nreg (brF + 1), c'.nreg (brF + 2)⟩ ∧
      (chainModel J.left).pos (Qof P) ⟨c'.nreg (brF + 1), c'.nreg (brF + 2)⟩ = rayPt z σ τ ∧
      AbsRec P c' (brF + 3) (rayPt z σ τ).1 J.left.radius ∧
      (FreeAt J.left z σ → τ = J.left.hitParam z σ)) ∧
    (FreeAt J.left z σ → c'.nreg brF = 1) ∧
    (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) ∧ c.nreg ALLOC ≤ c'.nreg ALLOC ∧
    (∀ r, bandOf r ∉ oracleBands → ¬ BrR r → r ≠ ALLOC → c'.nreg r = c.nreg r)

/-- **Task B: the brute-force shot** in the model of `C₁` at all arcs of `N₁` from the
symbolic point `s` in `brOS … brOS + 2` (off `C₁`, strictly inside the box, not above the top of
`C₁`) in the direction of code `brOD ≤ 1`, cost `κ (K₁ + 1) (F γ + 1)`. -/
def BruteTask : Prop :=
  ∃ (br : Stmt → Stmt) (κ : ℕ), ∀ (sh : Stmt) (Bs : Finset ℕ) (F : ℕ → ℕ) (X : MemCtx)
    (Ok : Polygon → Model → Prop) (P : Polygon) (W : ℕ) (c₀ c : Config) (J : Merge.Junction)
    (N₁ N₂ : NF), EvEnv sh Bs F X Ok P W c₀ J N₁ N₂ → IInv W c₀ c →
      ∀ s : SymPt, SymPtIn c brOS s → s.Lt P.n → s.eval (Qof P) ∉ J.left.set →
      |(s.eval (Qof P)).1| < J.whole.radius → |(s.eval (Qof P)).2| < J.whole.radius →
      (s.eval (Qof P)).2 ≤ J.left.top.2 → c.nreg brOD ≤ 1 →
      c.nreg ALLOC + κ * (N₁.nChords + 1) * (F (c₀.nreg (sw 5)) + 1) ≤ W →
      IRS P W c₀ (br sh) c (κ * (N₁.nChords + 1) * (F (c₀.nreg (sw 5)) + 1))
        (BruteOut P J (s.eval (Qof P)) (dirOf (c.nreg brOD)) c)

end

end SweepEv

end Chazelle.Core
