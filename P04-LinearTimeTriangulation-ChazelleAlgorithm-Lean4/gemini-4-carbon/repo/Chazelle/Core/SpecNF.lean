module

public import Chazelle.Core.SpecBase

/-!
# Core specification, part 2: normal forms and host curves

The **normal form** of a submap (Chazelle §2.4, p. 498), as a finite record structure over
naturals, with its abstraction to the Euclidean chord family of a disk model and the validity
predicate `IsNF`.  Design decision D3 (`docs/design-chazelle-core.md` §3).

* Chord records `CRec` (the edges of the tree of the submap, p. 498 (i)–(ii)): the height vertex
  `h` and the walk edges carrying the left and right endpoints, and the regions above and below
  (with distinct heights the two sides of a horizontal chord are "above" and "below").
* Arc records `ARec` (the arc-structures, p. 497): the region faced and the two ends as walk
  positions.  The walk is the double boundary (chain model) or the boundary of the closed
  polygon (interior model); walk edges map to input edges by index arithmetic, so an arc record
  *is* the paper's pair of pointers into the input table with side flags.
* Region records `RRec` (the nodes of the tree): arcs, exit chords, weight.
* `seq`: the arc-sequence table (p. 498 (iii)), arcs sorted by the key of their start.
* `dec`, `root`: the tree decomposition (p. 498 (iv), §2.3), optional.

Everything stored is an index, so it stays below the table sizes (word bound, design doc §6).

## Host curves

The chains of the down phase live in *virtual* host polygons (the boundary `R*` of a region,
paper p. 519): runs of consecutive input vertices and symbolic points of input edges at vertex
heights.  `Host` describes such a polygon and `Host.poly Q` is its Euclidean realisation.
-/

namespace Chazelle.Core

@[expose] public section

open Set
open Chazelle.Chain (TouchesIn)

/-! ## Records -/

/-- A chord record. -/
structure CRec where
  /-- The height vertex: the chord lies at the height of vertex `h` of `Q`. -/
  h : ℕ
  /-- The walk edge carrying the left endpoint. -/
  lp : ℕ
  /-- The walk edge carrying the right endpoint. -/
  rp : ℕ
  /-- The region above the chord. -/
  up : ℕ
  /-- The region below the chord. -/
  dn : ℕ
  deriving DecidableEq

/-- An arc record. -/
structure ARec where
  /-- The region faced by the arc. -/
  reg : ℕ
  /-- Its start (a cut; for the arc of the empty submap, any position). -/
  s : WPos
  /-- Its end (a cut; equal to `s` for the arc of the empty submap). -/
  e : WPos
  deriving DecidableEq

/-- A region record (a node of the tree of the submap). -/
structure RRec where
  /-- Its arcs (indices into the arc list). -/
  arcs : List ℕ
  /-- Its exit chords (indices into the chord list). -/
  chords : List ℕ
  /-- Its weight. -/
  wt : ℕ
  deriving DecidableEq

/-- A node of the tree decomposition: an exit chord and its two children.  Children are coded as
`2 k` (the node of chord `k`) or `2 r + 1` (the leaf of region `r`); `par` is the code of the
parent, the root being its own parent. -/
structure DNode where
  /-- The parent code. -/
  par : ℕ
  /-- The child on the lower side of the chord. -/
  lo : ℕ
  /-- The child on the upper side of the chord. -/
  hi : ℕ
  deriving DecidableEq

/-- A submap in normal form.  `dec` is indexed like `chords` (node `k` belongs to chord `k`); it
is empty when no decomposition is stored. -/
structure NF where
  /-- The chords. -/
  chords : List CRec
  /-- The arcs. -/
  arcs : List ARec
  /-- The regions. -/
  regions : List RRec
  /-- The arc-sequence table: arc indices sorted by the key of their start. -/
  seq : List ℕ
  /-- The tree decomposition (empty if absent). -/
  dec : List DNode
  /-- The code of the root of the tree decomposition. -/
  root : ℕ
  /-- The parent code of the leaf of each region (empty if no decomposition). -/
  lpar : List ℕ

namespace CRec

/-- The walk position of the left endpoint. -/
def lpos (c : CRec) : WPos := ⟨c.lp, c.h + 1⟩

/-- The walk position of the right endpoint. -/
def rpos (c : CRec) : WPos := ⟨c.rp, c.h + 1⟩

/-- **The Euclidean chord** of a record in the model `M` with heights from `Q`. -/
noncomputable def toSet (M : Model) (Q : Polygon) (c : CRec) : Set Point :=
  Visibility.hseg (Q.vtx c.h).2 (M.pos Q c.lpos).1 (M.pos Q c.rpos).1

/-- The record names the walk positions at which its chord is attached (side-aware,
`Chazelle.Chain.SideAttach`): the walk edges `lp`, `rp` are the ones whose left sector the chord
enters, not the other side of the same point. -/
def Attached (M : Model) (Q : Polygon) (c : CRec) : Prop :=
  Chazelle.Chain.SideAttach M.W (c.toSet M Q) c.lp (M.param Q c.lpos) ∧
    Chazelle.Chain.SideAttach M.W (c.toSet M Q) c.rp (M.param Q c.rpos)

end CRec

namespace NF

variable (N : NF)

/-- **The abstraction function**: the chord family of a normal form. -/
def F (M : Model) (Q : Polygon) : Set (Set Point) := {c | ∃ r ∈ N.chords, c = r.toSet M Q}

/-- Number of chords. -/
def nChords : ℕ := N.chords.length

/-- Number of regions. -/
def nRegions : ℕ := N.regions.length

/-- The chord record `i` (a default record out of range). -/
def chord (i : ℕ) : CRec := N.chords.getD i ⟨0, 0, 0, 0, 0⟩

/-- The arc record `j`. -/
def arc (j : ℕ) : ARec := N.arcs.getD j ⟨0, ⟨0, 0⟩, ⟨0, 0⟩⟩

/-- The region record `r`. -/
def region (r : ℕ) : RRec := N.regions.getD r ⟨[], [], 0⟩

/-- The decomposition node of chord `k`. -/
def dnode (k : ℕ) : DNode := N.dec.getD k ⟨0, 0, 0⟩

/-- Two region indices are adjacent in the record tree through a chord other than `k`. -/
def AdjAvoid (k r r' : ℕ) : Prop :=
  ∃ i, i < N.nChords ∧ i ≠ k ∧
    ((N.chord i).up = r ∧ (N.chord i).dn = r' ∨ (N.chord i).up = r' ∧ (N.chord i).dn = r)

/-- The regions on the lower side of chord `k` (reachable from its lower region without using
`k`). -/
def lowSide (k : ℕ) : Set ℕ := {r | Relation.ReflTransGen (N.AdjAvoid k) (N.chord k).dn r}

/-- The regions on the upper side of chord `k`. -/
def highSide (k : ℕ) : Set ℕ := {r | Relation.ReflTransGen (N.AdjAvoid k) (N.chord k).up r}

/-- The parent of a code in the decomposition (the root is its own parent). -/
def parentCode (x : ℕ) : ℕ :=
  if x % 2 = 0 then (N.dnode (x / 2)).par else N.lpar.getD (x / 2) N.root

/-- Region `r` is a leaf below the code `x` of the decomposition. -/
def Below (x r : ℕ) : Prop := ∃ j, N.parentCode^[j] (2 * r + 1) = x

end NF

/-! ## Validity -/

/-- **The region correspondence**: `reg` maps region indices bijectively onto the regions of the
chord family. -/
def RegionCorr (M : Model) (Q : Polygon) (N : NF) (reg : ℕ → Set Point) : Prop :=
  (∀ r, r < N.nRegions → reg r ∈ M.regions (N.F M Q)) ∧
    (∀ r r', r < N.nRegions → r' < N.nRegions → reg r = reg r' → r = r') ∧
    (∀ U ∈ M.regions (N.F M Q), ∃ r, r < N.nRegions ∧ reg r = U)

/-- The chord records describe their regions: the region above (below) the chord `i` contains the
points just above (below) every point of its open part in the domain. -/
def ChordSidesOK (M : Model) (Q : Polygon) (N : NF) (reg : ℕ → Set Point) : Prop :=
  ∀ i, i < N.nChords →
    (N.chord i).up < N.nRegions ∧ (N.chord i).dn < N.nRegions ∧
    ∀ z ∈ (N.chord i).toSet M Q, z ∈ M.D →
      ∃ ε₀ > (0 : ℝ), ∀ ε, 0 < ε → ε < ε₀ →
        (z.1, z.2 + ε) ∈ reg (N.chord i).up ∧ (z.1, z.2 - ε) ∈ reg (N.chord i).dn

/-- The arc records are exactly the arcs of the regions, each listed once, and the region records
list them. -/
def ArcsOK (M : Model) (Q : Polygon) (N : NF) (reg : ℕ → Set Point) : Prop :=
  (∀ j, j < N.arcs.length → (N.arc j).reg < N.nRegions ∧
    M.IsArc (N.F M Q) (reg (N.arc j).reg) (M.key Q (N.arc j).s) (M.key Q (N.arc j).e)) ∧
  (∀ j j', j < N.arcs.length → j' < N.arcs.length →
    (N.arc j).reg = (N.arc j').reg → M.key Q (N.arc j).s = M.key Q (N.arc j').s → j = j') ∧
  (∀ r, r < N.nRegions → ∀ a b : ℝ, M.IsArc (N.F M Q) (reg r) a b →
    ∃ j, j < N.arcs.length ∧ (N.arc j).reg = r ∧ M.key Q (N.arc j).s = a ∧
      M.key Q (N.arc j).e = b) ∧
  (∀ r, r < N.nRegions → ∀ j, (j ∈ (N.region r).arcs ↔ j < N.arcs.length ∧ (N.arc j).reg = r))

/-- The region records list their exit chords and weights. -/
def RegionsOK (M : Model) (Q : Polygon) (N : NF) (reg : ℕ → Set Point) : Prop :=
  ∀ r, r < N.nRegions →
    (∀ i, (i ∈ (N.region r).chords ↔
      i < N.nChords ∧ TouchesIn M.D ((N.chord i).toSet M Q) (reg r))) ∧
    (N.region r).chords.Nodup ∧ (N.region r).arcs.Nodup ∧
    (N.region r).wt = M.weight (N.F M Q) (reg r)

/-- The arc-sequence table lists every arc once, by nondecreasing start key. -/
def SeqOK (M : Model) (Q : Polygon) (N : NF) : Prop :=
  N.seq.Perm (List.range N.arcs.length) ∧
    N.seq.Pairwise (fun j j' => M.key Q (N.arc j).s ≤ M.key Q (N.arc j').s)

/-- **A position of the walk proper** whose height code is in range: parameter in `[0, 1)`, code
`≤ n` (review finding C6; formerly `WalkKey.ProperPos`).  Keys of such positions are compared by
at most one sign-kernel height test (`WalkKey.keyDec_iff`). -/
def ProperPos (M : Model) (Q : Polygon) (n : ℕ) (x : WPos) : Prop :=
  0 ≤ M.param Q x ∧ M.param Q x < 1 ∧ x.hgt ≤ n

/-- **Validity of a normal form** (without the decomposition): the chord records describe an
admissible chord family (distinct records, distinct chords) and the region, chord, arc and
sequence records describe its regions, tree, arcs, weights and canonical order; every chord
record names its height vertex by an index `< n` (review finding N1: otherwise a record could use
an out-of-range index whose default vertex `(0, 0)` has the same height, and the index of the
chord's vertex would not be recoverable); both ends of every arc record are stored as positions
of the walk proper (`ProperPos`, review finding C6: otherwise an arc start could be stored with a
parameter outside `[0, 1)` on the previous walk edge, and comparing its key would need a ratio
test outside the sign kernel; the ends are passed to the oracles as subarc ends). -/
def IsNF (M : Model) (Q : Polygon) (N : NF) : Prop :=
  M.ChordFamily Q (N.F M Q) ∧
    (∀ i i', i < N.nChords → i' < N.nChords →
      (N.chord i).toSet M Q = (N.chord i').toSet M Q → i = i') ∧
    (∀ i, i < N.nChords → (N.chord i).Attached M Q) ∧
    ∃ reg : ℕ → Set Point, RegionCorr M Q N reg ∧ ChordSidesOK M Q N reg ∧
      ArcsOK M Q N reg ∧ RegionsOK M Q N reg ∧ SeqOK M Q N ∧
      (∀ i, i < N.nChords → (N.chord i).h < Q.n) ∧
      ∀ j, j < N.arcs.length → ProperPos M Q Q.n (N.arc j).s ∧ ProperPos M Q Q.n (N.arc j).e

/-- **A valid tree decomposition** (§2.3) of depth at most `d`: every chord has a node; the
children of the node of chord `k` split the leaves below it along the two sides of `k`; every
region is a leaf; the iterated parents of every code reach the root within `d` steps.  (Finding
R-D1: the tree is proper — only its own region is below a leaf, the children of a chord node are
valid codes other than the root, and the root is a valid code — so that a descent from the root
stops at the leaf of its target region within `d` steps.) -/
def IsDecomp (N : NF) (d : ℕ) : Prop :=
  N.dec.length = N.nChords ∧ N.lpar.length = N.nRegions ∧
    (∀ k, k < N.nChords →
      N.parentCode (N.dnode k).lo = 2 * k ∧ N.parentCode (N.dnode k).hi = 2 * k) ∧
    (∀ k, k < N.nChords → ∀ r, N.Below (2 * k) r → (N.Below (N.dnode k).lo r ↔ r ∈ N.lowSide k)) ∧
    (∀ k, k < N.nChords → ∀ r, N.Below (2 * k) r → (N.Below (N.dnode k).hi r ↔ r ∈ N.highSide k)) ∧
    (∀ r, r < N.nRegions → N.Below N.root r) ∧
    (∀ x, (x % 2 = 0 → x / 2 < N.nChords) → ∃ j, j ≤ d ∧ N.parentCode^[j] x = N.root) ∧
    (∀ r r', r < N.nRegions → r' < N.nRegions → N.Below (2 * r + 1) r' → r' = r) ∧
    (∀ k, k < N.nChords → ∀ x, (x = (N.dnode k).lo ∨ x = (N.dnode k).hi) →
      x ≠ N.root ∧ ((x % 2 = 0 ∧ x / 2 < N.nChords) ∨ (x % 2 = 1 ∧ x / 2 < N.nRegions))) ∧
    ((N.root % 2 = 0 ∧ N.root / 2 < N.nChords) ∨ (N.root % 2 = 1 ∧ N.root / 2 < N.nRegions))

/-- The depth allowed for the decomposition of a submap with `k` chords whose regions have at
most `D` exit chords (a centroid edge leaves at most a fraction `1 - 1/D` of the edges on each
side, p. 495): `D ⌈log₂ (k + 1)⌉ + 1`. -/
def decDepth (D k : ℕ) : ℕ := D * Nat.clog 2 (k + 1) + 1

/-- **A γ-canonical normal form with degree cap `D`** (the paper's canonical submaps have
`D = 4`; host curves of the down phase use a larger constant cap, design doc §2.6). -/
def IsCanonicalNF (M : Model) (Q : Polygon) (N : NF) (γ D : ℕ) : Prop :=
  IsNF M Q N ∧ M.DegLe (N.F M Q) D ∧ M.Granular (N.F M Q) γ ∧ IsDecomp N (decDepth D N.nChords)

/-! ## Host curves -/

/-- An item of a host description. -/
inductive HostItem where
  /-- The input vertices `a, a + 1, …, a + ℓ` (indices modulo `n`). -/
  | run (a ℓ : ℕ)
  /-- One symbolic point. -/
  | pt (x : SymPt)
  deriving DecidableEq

/-- A host polygon, as a list of items. -/
abbrev Host : Type := List HostItem

/-- The symbolic points of a host item. -/
def HostItem.pts (n : ℕ) : HostItem → List SymPt
  | .run a ℓ => (List.range (ℓ + 1)).map fun k => SymPt.vtx ((a + k) % n)
  | .pt x => [x]

/-- The symbolic vertex list of a host. -/
def Host.pts (n : ℕ) (H : Host) : List SymPt := H.flatMap (HostItem.pts n)

/-- **The Euclidean host polygon.** -/
noncomputable def Host.poly (Q : Polygon) (H : Host) : Polygon :=
  ⟨(H.pts Q.n).map (SymPt.eval Q)⟩

/-- **Well-formed host** (review finding C8; formerly `NFLoc.HostWF`): runs start and extend
within `n`, points are in range (so every host point is a symbolic point the sign kernel
accepts). -/
def HostWF (n : ℕ) (H : Host) : Prop :=
  ∀ it ∈ H, match it with
    | .run a ℓ => a < n ∧ ℓ < n
    | .pt x => x.Lt n

/-- Two consecutive host points span a piece of an edge of `Q` or a horizontal chord edge (both
ends at the height of one vertex): consecutive input vertices, a vertex and a point of an
incident edge, two points of one edge, or two points at the height of one vertex. -/
def HostEdgeOK (n : ℕ) : SymPt → SymPt → Prop
  | .vtx i, .vtx j => j = (i + 1) % n ∨ i = (j + 1) % n
  | .vtx i, .onEdge e _ => i = e ∨ i = (e + 1) % n
  | .onEdge e _, .vtx j => j = e ∨ j = (e + 1) % n
  | .onEdge e h, .onEdge e' h' => h = h' ∨ e = e'

/-- **A regular host** (review finding S1): every edge of the host polygon is a piece of an edge
of `Q` or a horizontal chord edge, so every non-box walk position of a chain of the host at a
vertex height is a symbolic point of `Q` (the shooters accept it as an origin).  The up-phase host
and the region boundaries `R*` of the down phase are regular. -/
def HostRegular (n : ℕ) (H : Host) : Prop :=
  ∀ i, i < (H.pts n).length →
    HostEdgeOK n ((H.pts n).getD i (.vtx 0)) ((H.pts n).getD ((i + 1) % (H.pts n).length) (.vtx 0))

/-- A well-formed host has at most `n` points per item. -/
theorem Host.pts_length_le {n : ℕ} {H : Host} (h : HostWF n H) :
    (H.pts n).length ≤ H.length * n := by
  induction H with
  | nil => simp [Host.pts]
  | cons it H ih =>
    have hit := h it (by simp)
    have ih' := ih fun it' hit' => h it' (List.mem_cons_of_mem _ hit')
    have e : (Host.pts n (it :: H)).length = (it.pts n).length + (Host.pts n H).length := by
      simp [Host.pts]
    have hi : (it.pts n).length ≤ n := by
      cases it with
      | run a l =>
        simp only [HostItem.pts, List.length_map, List.length_range]
        exact hit.2
      | pt x =>
        simp only [HostItem.pts, List.length_singleton]
        cases x with
        | vtx i => simp only [SymPt.Lt] at hit; omega
        | onEdge e' h' => simp only [SymPt.Lt] at hit; omega
    rw [e, List.length_cons, Nat.succ_mul]
    omega

/-- The host of the up phase: the geometry polygon itself. -/
def Host.whole (n : ℕ) : Host := [.run 0 (n - 1)]

/-- The whole host has one symbolic vertex per input vertex. -/
theorem Host.whole_pts_length (n : ℕ) (hn : 1 ≤ n) : ((Host.whole n).pts n).length = n := by
  simp [Host.whole, Host.pts, HostItem.pts]
  omega

end

end Chazelle.Core
