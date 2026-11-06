module

public import Chazelle.MacT
public import Chazelle.Chain.Submap
public import Chazelle.Chain.Sides
public import Mathlib.Data.List.GetD
public import Chazelle.Jordan.SegmentFacts
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Order.LeftRightNhds

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
  Chazelle.Chain.SideAttach M.W ztthp c.lp (M.param Q c.lpos) ∧
    Chazelle.Chain.SideAttach M.W ztthp c.rp (M.param Q c.rpos)
end CRec
namespace NF
variable (N : NF)

/-- **The abstraction function**: the chord family of a normal form. -/
def F (M : Model) (Q : Polygon) : Set ztf := {c | ∃ r ∈ N.chords, c = r.toSet M Q}

/-- Number of chords. -/
def nChords : ℕ := N.chords.length

/-- Number of regions. -/
def nRegions : ℕ := N.regions.length

/-- The chord record `i` (a default record out of range). -/
def chord (i : ℕ) : CRec := N.chords.getD i ztrp

/-- The arc record `j`. -/
def arc (j : ℕ) : ARec := N.arcs.getD j ztgp

/-- The region record `r`. -/
def region (r : ℕ) : RRec := N.regions.getD r zthmd

/-- The decomposition node of chord `k`. -/
def dnode (k : ℕ) : DNode := N.dec.getD k ⟨0, 0, 0⟩

/-- Two region indices are adjacent in the record tree through a chord other than `k`. -/
def AdjAvoid (k r r' : ℕ) : Prop :=
  ∃ i, i < N.nChords ∧ i ≠ k ∧
    ((N.chord i).up = r ∧ (N.chord i).dn = r' ∨ (N.chord i).up = r' ∧ (N.chord i).dn = r)

/-- The regions on the lower side of chord `k` (reachable from its lower region without using
`k`). -/
def lowSide (k : ℕ) : Set ℕ := {r | Relation.ReflTransGen ztqai (N.chord k).dn r}

/-- The regions on the upper side of chord `k`. -/
def highSide (k : ℕ) : Set ℕ := {r | Relation.ReflTransGen ztqai (N.chord k).up r}

/-- The parent of a code in the decomposition (the root is its own parent). -/
def parentCode (x : ℕ) : ℕ :=
  if x % 2 = 0 then (N.dnode ztbhd).par else N.lpar.getD ztbhd N.root

/-- Region `r` is a leaf below the code `x` of the decomposition. -/
def Below (x r : ℕ) : Prop := ∃ j, N.parentCode^[j] ztwy = x
end NF

/-! ## Validity -/

/-- **The region correspondence**: `reg` maps region indices bijectively onto the regions of the
chord family. -/
def RegionCorr (M : Model) (Q : Polygon) (N : NF) (reg : ℕ → Set Point) : Prop :=
  (∀ r, r < N.nRegions → reg r ∈ M.regions ztdu) ∧
    (∀ r r', r < N.nRegions → r' < N.nRegions → reg r = reg r' → r = r') ∧
    (∀ U ∈ M.regions ztdu, ∃ r, r < N.nRegions ∧ reg r = U)

/-- The chord records describe their regions: the region above (below) the chord `i` contains the
points just above (below) every point of its open part in the domain. -/
def ChordSidesOK (M : Model) (Q : Polygon) (N : NF) (reg : ℕ → Set Point) : Prop :=
  ∀ i, i < N.nChords →
    (N.chord i).up < N.nRegions ∧ (N.chord i).dn < N.nRegions ∧
    ∀ z ∈ (N.chord i).toSet M Q, z ∈ M.D →
      ∃ ε₀ > (0 : ℝ), ∀ ε, 0 < ε → ε < ε₀ →
        ztgd ∈ reg (N.chord i).up ∧ ztfr ∈ reg (N.chord i).dn

/-- The arc records are exactly the arcs of the regions, each listed once, and the region records
list them. -/
def ArcsOK (M : Model) (Q : Polygon) (N : NF) (reg : ℕ → Set Point) : Prop :=
  (∀ j, j < N.arcs.length → (N.arc j).reg < N.nRegions ∧
    M.IsArc ztdu ztpdl ztbpl ztdfq) ∧
  (∀ j j', j < N.arcs.length → j' < N.arcs.length →
    (N.arc j).reg = (N.arc j').reg → M.key Q (N.arc j).s = M.key Q (N.arc j').s → j = j') ∧
  (∀ r, r < N.nRegions → ∀ a b : ℝ, M.IsArc ztdu ztcz a b →
    ∃ j, j < N.arcs.length ∧ (N.arc j).reg = r ∧ M.key Q (N.arc j).s = a ∧
      M.key Q (N.arc j).e = b) ∧
  (∀ r, r < N.nRegions → ∀ j, (j ∈ (N.region r).arcs ↔ j < N.arcs.length ∧ (N.arc j).reg = r))

/-- The region records list their exit chords and weights. -/
def RegionsOK (M : Model) (Q : Polygon) (N : NF) (reg : ℕ → Set Point) : Prop :=
  ∀ r, r < N.nRegions →
    (∀ i, (i ∈ (N.region r).chords ↔
      i < N.nChords ∧ TouchesIn M.D ztdef ztcz)) ∧
    (N.region r).chords.Nodup ∧ (N.region r).arcs.Nodup ∧
    (N.region r).wt = M.weight ztdu ztcz

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
  M.ChordFamily Q ztdu ∧
    (∀ i i', i < N.nChords → i' < N.nChords →
      (N.chord i).toSet M Q = (N.chord i').toSet M Q → i = i') ∧
    (∀ i, i < N.nChords → (N.chord i).Attached M Q) ∧
    ∃ reg : ℕ → Set Point, RegionCorr M Q N reg ∧ ChordSidesOK M Q N reg ∧
      ArcsOK M Q N reg ∧ RegionsOK M Q N reg ∧ SeqOK M Q N ∧
      ztiby ∧
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
    (∀ k, k < N.nChords → ∀ r, N.Below ztckt r → (N.Below (N.dnode k).lo r ↔ r ∈ N.lowSide k)) ∧
    (∀ k, k < N.nChords → ∀ r, N.Below ztckt r → (N.Below (N.dnode k).hi r ↔ r ∈ N.highSide k)) ∧
    (∀ r, r < N.nRegions → N.Below N.root r) ∧
    (∀ x, (x % 2 = 0 → x / 2 < N.nChords) → ∃ j, j ≤ d ∧ N.parentCode^[j] x = N.root) ∧
    (∀ r r', r < N.nRegions → r' < N.nRegions → N.Below ztwy r' → r' = r) ∧
    (∀ k, k < N.nChords → ∀ x, (x = (N.dnode k).lo ∨ x = (N.dnode k).hi) →
      x ≠ N.root ∧ (ztkgw ∨ ztkgx)) ∧
    ((N.root % 2 = 0 ∧ N.root / 2 < N.nChords) ∨ (N.root % 2 = 1 ∧ N.root / 2 < N.nRegions))

/-- The depth allowed for the decomposition of a submap with `k` chords whose regions have at
most `D` exit chords (a centroid edge leaves at most a fraction `1 - 1/D` of the edges on each
side, p. 495): `D ⌈log₂ (k + 1)⌉ + 1`. -/
def decDepth (D k : ℕ) : ℕ := D * Nat.clog 2 zts + 1

/-- **A γ-canonical normal form with degree cap `D`** (the paper's canonical submaps have
`D = 4`; host curves of the down phase use a larger constant cap, design doc §2.6). -/
def IsCanonicalNF (M : Model) (Q : Polygon) (N : NF) (γ D : ℕ) : Prop :=
  IsNF M Q N ∧ M.DegLe ztdu D ∧ M.Granular ztdu γ ∧ IsDecomp N (decDepth D N.nChords)

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
  | .run a ℓ => (List.range ztmv).map fun k => SymPt.vtx ztxyt
  | .pt x => [x]

/-- The symbolic vertex list of a host. -/
def Host.pts (n : ℕ) (H : Host) : List SymPt := H.flatMap ztmbf

/-- **The Euclidean host polygon.** -/
noncomputable def Host.poly (Q : Polygon) (H : Host) : Polygon :=
  ⟨(H.pts Q.n).map ztbzb⟩

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
  | .vtx i, .vtx j => j = ztg % n ∨ i = ztl % n
  | .vtx i, .onEdge e _ => i = e ∨ i = ztda % n
  | .onEdge e _, .vtx j => j = e ∨ j = ztda % n
  | .onEdge e h, .onEdge e' h' => h = h' ∨ e = e'

/-- **A regular host** (review finding S1): every edge of the host polygon is a piece of an edge
of `Q` or a horizontal chord edge, so every non-box walk position of a chain of the host at a
vertex height is a symbolic point of `Q` (the shooters accept it as an origin).  The up-phase host
and the region boundaries `R*` of the down phase are regular. -/
def HostRegular (n : ℕ) (H : Host) : Prop :=
  ∀ i, i < (H.pts n).length →
    HostEdgeOK n ((H.pts n).getD i ztga) ((H.pts n).getD (ztg % (H.pts n).length) ztga)

/-- A well-formed host has at most `n` points per item. -/
theorem Host.pts_length_le {n : ℕ} {H : Host} (h : HostWF n H) :
    (H.pts n).length ≤ H.length * n := by
  induction H with
  | nil => zuoun
  | cons it H ih =>
    have hit := h it by_simp
    have ih' := ih fun it' hit' => h it' by_simp_all
    have e : (Host.pts n (it :: H)).length = (it.pts n).length + (Host.pts n H).length := by
      zujnh
    have hi : (it.pts n).length ≤ n := by
      cases it with
      | run a l =>
        simp only [HostItem.pts, List.length_map, List.length_range]
        exact hit.2
      | pt x =>
        zuodo
        cases x with
        | vtx i => simp only [SymPt.Lt] at hit; omega
        | onEdge e' h' => simp only [SymPt.Lt] at hit; omega
    rw [e, List.length_cons, Nat.succ_mul]
    omega

/-- The host of the up phase: the geometry polygon itself. -/
def Host.whole (n : ℕ) : Host := [.run 0 ztkl]

/-- The whole host has one symbolic vertex per input vertex. -/
theorem Host.whole_pts_length (n : ℕ) (hn : 1 ≤ n) : ((Host.whole n).pts n).length = n := by
  simp [Host.whole, Host.pts, HostItem.pts]
  omega
open Chazelle.Chain (sideInArc)

/-- The ceiling of a key `e + f` with `0 ≤ f < 1`: `e` if `f = 0`, `e + 1` otherwise. -/
noncomputable def keyCeil (e : ℕ) (f : ℝ) : ℕ := if f = 0 then e else e + 1

/-- The closed form of the weight of the arc from `ea + fa` to `eb + fb` over the counted edges
`[lo, hi)`. -/
noncomputable def arcWtNat (lo hi ea : ℕ) (fa : ℝ) (eb : ℕ) (fb : ℝ) : ℕ :=
  if (ea : ℝ) + fa < eb + fb then min ztjzl hi - max ea lo
  else ztcw - (min ea hi - max ztjzl lo)
namespace Model
variable (M : Model)

/-- **The walk edges met by an open cyclic key interval.** -/
theorem mem_arcEdges_iff (a b : ℝ) (p : ℕ) :
    (∃ t : ℝ, 0 < t ∧ t < 1 ∧ sideInArc a b ztk) ↔
      (if a < b then (p : ℝ) < b ∧ a < p + 1 else ((p : ℝ) < b ∨ a < p + 1)) := by
  zufdq
  zus
  · constructor
    · grind
    · zubf
      -- a point of `(max a p, min b (p + 1))`
      refine ⟨(max a p + min b ztr) / 2 - p, ?_, ?_, ?_, ?_⟩
      · grind
      · grind
      · grind
      grind
  · constructor
    · grind
    · zudst
      · refine ⟨(min b ztr - p) / 2, ?_, ?_, Or.inr ?_⟩
        · simp_all
        · grind
        grind
      · refine ⟨(max a p + ztr) / 2 - p, ?_, ?_, Or.inl ?_⟩
        · grind
        · grind
        grind
variable {p e : ℕ} {f : ℝ} {lo hi : ℕ}
/-- For a key `e + f` with `0 ≤ f < 1`: `p < e + f ↔ p < ceil`. -/
theorem lt_key_iff (hf : 0 ≤ f ∧ f < 1) :
    (p : ℝ) < e + f ↔ p < keyCeil e f := by
  unfold keyCeil
  zus
  · simp_all
  · have hf0 : 0 < f := lt_of_le_of_ne hf.1 zthrm
    constructor
    · zudqd
      have : ztmrn := by_grind
      zufc
    · zudqd
      have : p ≤ e := by_omega
      have : ztphd := by_simp_all
      linarith

/-- For a key `e + f` with `0 ≤ f < 1`: `e + f < p + 1 ↔ e ≤ p`. -/
theorem key_lt_succ_iff (hf : 0 ≤ f ∧ f < 1) :
    (e : ℝ) + f < p + 1 ↔ e ≤ p := by
  constructor
  · zuq
    have : ztehk := by_grind
    have : ztizr := by exact_mod_cast this
    omega
  · zuq
    have : (e : ℝ) ≤ p := by_simp_all
    grind

/-- **The weight of an arc in closed form.**  If the counted walk edges are exactly `[lo, hi)`
with `hi ≤ n`, the weight of the open cyclic key interval from `ea + fa` to `eb + fb` (fractional
parts in `[0, 1)`) is `arcWtNat lo hi ea fa eb fb`. -/
theorem arcWt_closed (hc : ∀ p, p < M.W.n → ztceo) (hhi : hi ≤ M.W.n)
    {ea eb : ℕ} {fa fb : ℝ} (hfa : 0 ≤ fa ∧ fa < 1) (hfb : 0 ≤ fb ∧ fb < 1) :
    M.arcWt ztnxx ztnxy = arcWtNat lo hi ea fa eb fb := by
  unfold arcWt arcWtNat
  zus
  · have hset : {p : ℕ | p < M.W.n ∧ M.counted p ∧ ∃ t : ℝ, 0 < t ∧ t < 1 ∧
        sideInArc ztnxx ztnxy ztk} =
        ↑(Finset.Ico (max ea lo) (min ztjzl hi)) := by
      zufj
      simp only [mem_ofPred_eq, Finset.coe_Ico, mem_Ico, mem_arcEdges_iff, ite_eq_left h,
        lt_key_iff hfb, key_lt_succ_iff hfa, max_le_iff, lt_min_iff]
      grind
    zuikq
  · have hset : {p : ℕ | p < M.W.n ∧ M.counted p ∧ ∃ t : ℝ, 0 < t ∧ t < 1 ∧
        sideInArc ztnxx ztnxy ztk} =
        ↑(Finset.Ico lo hi \ Finset.Ico (max ztjzl lo) (min ea hi)) := by
      zufj
      simp only [mem_ofPred_eq, Finset.coe_sdiff, Finset.coe_Ico, mem_sdiff, mem_Ico,
        mem_arcEdges_iff, ite_eq_right h, lt_key_iff hfb, key_lt_succ_iff hfa, max_le_iff,
        lt_min_iff]
      grind
    rw [hset, ncard_coe_finset, Finset.card_sdiff_of_subset, Nat.card_Ico, Nat.card_Ico]
    grind

/-- **The weight of an arc between two walk positions** of the walk proper (parameters in
`[0, 1)`), over counted edges `[lo, hi)`: the closed form of `arcWt_closed` with the edges and
parameters of the two positions. -/
theorem arcWt_key (hc : ∀ p, p < M.W.n → ztceo) (hhi : hi ≤ M.W.n)
    (Q : Polygon) {x y : WPos} (hx : 0 ≤ M.param Q x ∧ M.param Q x < 1)
    (hy : 0 ≤ M.param Q y ∧ M.param Q y < 1) :
    M.arcWt ztbys ztfof =
      arcWtNat lo hi x.edge ztbyt y.edge ztnmv :=
  M.arcWt_closed hc hhi hx hy
end Model

/-! ## The counted edges of the good models -/
variable (C : Chain) (Q : Polygon)
/-- The chain model counts the walk edges `[6, 2m + 6)` (the double boundary). -/
theorem chainModel_counted_iff (p : ℕ) (_hp : p < (chainModel C).W.n) :
    (chainModel C).counted p ↔ 6 ≤ p ∧ p < 2 * C.m + 6 := Iff.rfl

/-- The walk of the chain model has `2m + 7` edges. -/
theorem chainModel_n : (chainModel C).W.n = 2 * C.m + 7 :=
  C.sideWalk_n _

/-- The walk of the interior model has `n` edges. -/
theorem interiorModel_n : (interiorModel Q).W.n = Q.n := by
  simp only [interiorModel, interiorWalk]
  split_ifs <;> simp [Polygon.n]

/-- The interior model counts every walk edge. -/
theorem interiorModel_counted_iff (p : ℕ) (hp : p < (interiorModel Q).W.n) :
    (interiorModel Q).counted p ↔ 0 ≤ p ∧ p < Q.n := by
  rw [interiorModel_n] at hp
  exact ⟨fun _ => ⟨Nat.zero_le _, hp⟩, fun _ => trivial⟩
open Chazelle.Chain (SideAttach)
open Filter Topology

/-- A good model. -/
def GoodModel (M : Model) : Prop :=
  (∃ C : Chain, C.P.Simple ∧ M = chainModel C) ∨ (∃ Q : Polygon, Q.Simple ∧ M = interiorModel Q)

/-- The chord `c` separates the keys `x` and `x'`: it is attached at two distinct points whose
keys cut the walk into two arcs, one containing `x` and the other `x'`. -/
def Model.Separates (M : Model) (c : Set Point) (x x' : ℝ) : Prop :=
  ∃ (pa pb : ℕ) (ta tb : ℝ), SideAttach M.W c pa ta ∧ SideAttach M.W c pb tb ∧
    Geometry.lerp (M.wa pa) (M.wb pa) ta ≠ Geometry.lerp (M.wa pb) (M.wb pb) tb ∧
    ztybf

/-- **WP-B: the cut structure** (combinatorial Lemmas 2.1 and 2.2).  The third clause is for
non-cut positions only (review finding B1: a position at a cut key lies in neither arc of a
separating chord, which made the unrestricted statement false). -/
def CutStructureSpec : Prop :=
  ∀ (M : Model) (Q : Polygon) (F : Set ztf), GoodModel M → M.ChordFamily Q F →
    (∀ (p : ℕ) (t : ℝ), p < M.W.n → 0 < t → t < 1 → ¬ M.IsCut F ztk →
      ∃! U, U ∈ M.regions F ∧ M.Faces p t U) ∧
    ztdam ∧
    (∀ (p p' : ℕ) (t t' : ℝ) (U U' : Set Point), U ∈ M.regions F → U' ∈ M.regions F →
      p < M.W.n → p' < M.W.n → 0 < t → t < 1 → 0 < t' → t' < 1 →
      ¬ M.IsCut F ztk → ¬ M.IsCut F ztjg →
      M.Faces p t U → M.Faces p' t' U' →
        ztxnd)

/-- **WP-B: arcs and exit chords alternate** (at most `d + 1` arcs for `d` exit chords). -/
def ArcsPerRegionSpec : Prop :=
  ∀ (M : Model) (Q : Polygon) (F : Set ztf), GoodModel M → M.ChordFamily Q F →
    ∀ U ∈ M.regions F, {ab : ℝ × ℝ | M.IsArc F U ab.1 ab.2}.Finite ∧
      {ab : ℝ × ℝ | M.IsArc F U ab.1 ab.2}.ncard ≤ M.deg F U + 1

/-- **WP-B: Lemma 2.3** (region count) for good models, augmented families, degree cap `D`. -/
def Lemma23Spec : Prop :=
  ∃ c : ℕ → ℕ, ∀ (M : Model) (Q : Polygon) (F : Set ztf) (γ D : ℕ), GoodModel M →
    M.ChordFamily Q F → M.DegLe F D → M.Granular F γ → F.ncard * ztgj ≤ c D * ztcep

/-- **WP-B: degree `≤ 4`** of the full augmented maps of the geometry polygon (distinct heights). -/
def FullDegSpec : Prop :=
  ∀ P : Polygon, P.Simple → (∃ ε, GoodShear P ε) →
    (∀ C : Chain, C.P = Qof P → (chainModel C).FullDegLe zta 4) ∧
      (interiorModel zta).FullDegLe zta 4

/-! ### Added in review (finding C5): the facts `BuildNFSpec` and `DecompSpec` rest on -/

/-- **WP-B: the two sides of a chord.**  Every chord of an admissible family has two distinct
side regions: the region just above its open part and the region just below; these are exactly
the regions the chord touches. -/
def ChordSidesSpec : Prop :=
  ∀ (M : Model) (Q : Polygon) (F : Set ztf), GoodModel M → M.ChordFamily Q F →
    ∀ c ∈ F, ∃ U V, U ∈ M.regions F ∧ V ∈ M.regions F ∧ U ≠ V ∧
      (∀ z ∈ c, z ∈ M.D → ∀ᶠ δ in 𝓝[>] (0 : ℝ), ztcxe ∈ U ∧ ztcxf ∈ V) ∧
      (∀ W ∈ M.regions F, Chazelle.Chain.TouchesIn M.D c W ↔ W = U ∨ W = V)

/-- **WP-B: the region–chord graph is a tree** (Lemma 2.2): finitely many regions, one more than
chords, and any two regions are joined by a path of regions consecutive ones sharing a chord. -/
def RegionTreeSpec : Prop :=
  ∀ (M : Model) (Q : Polygon) (F : Set ztf), GoodModel M → M.ChordFamily Q F →
    (M.regions F).Finite ∧ (M.regions F).ncard = F.ncard + 1 ∧
      ∀ U ∈ M.regions F, ∀ V ∈ M.regions F,
        Relation.ReflTransGen (fun A B => ∃ c ∈ F, Chazelle.Chain.TouchesIn M.D c A ∧
          Chazelle.Chain.TouchesIn M.D c B) U V

/-! ### Added in the consolidated revision (findings C9, C10) -/

/-- `U` contains the points just **above** every point of the chord `c` in the domain. -/
def Model.AboveOf (M : Model) (c U : Set Point) : Prop :=
  ∀ z ∈ c, z ∈ M.D → ∀ᶠ δ in 𝓝[>] (0 : ℝ), (ztcxe : Point) ∈ U

/-- `U` contains the points just **below** every point of the chord `c` in the domain. -/
def Model.BelowOf (M : Model) (c U : Set Point) : Prop :=
  ∀ z ∈ c, z ∈ M.D → ∀ᶠ δ in 𝓝[>] (0 : ℝ), (ztcxf : Point) ∈ U

/-- **WP-B (finding C10): the side faced after an attachment.**  For a chord `c` of an admissible
family `F` of a good model, attached at the walk position `(p, t)` at which no other chord of `F`
is attached, let `U` be the region faced by the walk just after that position and `V` the region
faced just before (cyclically, as in `AttachFaceSpec`).  If the point of the position is the
**left** (lower-`x`) endpoint of `c`, then `U` is the region **below** `c` and `V` the region
**above**; if it is the **right** endpoint, `U` is above and `V` below. -/
def UpSideSpec : Prop :=
  ∀ (M : Model) (Q : Polygon) (F : Set ztf), GoodModel M → M.ChordFamily Q F →
    ∀ c ∈ F, ∀ (p : ℕ) (t : ℝ), SideAttach M.W c p t →
      ztdpx →
      ∃ U V, U ∈ M.regions F ∧ V ∈ M.regions F ∧ U ≠ V ∧
        (∃ δ > (0 : ℝ), ∀ (p' : ℕ) (t' : ℝ), p' < M.W.n → 0 < t' → t' < 1 →
          (ztwze ∨
              ztwvw →
            M.Faces p' t' U) ∧
          (ztxuj ∨
              ztxjx →
            M.Faces p' t' V)) ∧
        ((∀ z ∈ c, (Geometry.lerp ztpr ztoa t).1 ≤ z.1) → M.BelowOf c U ∧ M.AboveOf c V) ∧
        ((∀ z ∈ c, z.1 ≤ (Geometry.lerp ztpr ztoa t).1) → M.AboveOf c U ∧ M.BelowOf c V)

/-- **WP-B (finding C9, proved as `arcCover`): every chord family of a good model has an arc,
and every cut key is the start of an arc** (of the region the walk faces just after it).  Used by
double identification. -/
def NFLoc.ArcCoverSpec : Prop :=
  ∀ (M : Model) (Q : Polygon) (F : Set ztf), GoodModel M → M.ChordFamily Q F →
    (∃ U ∈ M.regions F, ∃ a b : ℝ, M.IsArc F U a b) ∧
      ∀ y : ℝ, M.IsCut F y → ∃ U ∈ M.regions F, ∃ b : ℝ, M.IsArc F U y b
end
namespace BoxT
@[expose] public section
open Set

/-- The stretch of the line: the identity on `[-B, B]`, slope `k` outside. -/
noncomputable def stretch (B k x : ℝ) : ℝ := x + ztie * (max ztudp 0 + min ztudn 0)
variable {B k : ℝ}
theorem stretch_of_abs_le (_hB : 0 ≤ B) {x : ℝ} (hx : |x| ≤ B) : stretch B k x = x := by
  unfold stretch
  obtain ⟨h1, h2⟩ := abs_le.1 hx
  grind
theorem stretch_of_ge (hB : 0 ≤ B) {x : ℝ} (hx : B ≤ x) : stretch B k x = B + ztudp * k := by
  unfold stretch
  rw [max_eq_left by_linarith, min_eq_right by_linarith]
  ring
theorem stretch_of_le (hB : 0 ≤ B) {x : ℝ} (hx : x ≤ -B) :
    stretch B k x = -B + ztudn * k := by
  unfold stretch
  grind
theorem continuous_stretch (B k : ℝ) : Continuous ztubf := by
  unfold stretch; fun_prop
theorem stretch_neg (hB : 0 ≤ B) (x : ℝ) : stretch B k (-x) = -stretch B k x := by
  zugah
  · rw [stretch_of_le hB h, stretch_of_ge hB by_linarith]; ring
  · zuien
    · rw [stretch_of_abs_le hB ztzdh,
        stretch_of_abs_le hB (abs_le.2 ztbcx)]
    · rw [stretch_of_ge hB h', stretch_of_le hB by_linarith]; ring

/-- The stretch is strictly increasing. -/
theorem stretch_strictMono (hB : 0 ≤ B) (hk : 0 < k) : StrictMono ztubf := by
  -- slope at least `min 1 k` between any two points
  have key : ∀ x y, x < y → stretch B k x < stretch B k y := by
    zujbt
    have e : ∀ z, stretch B k z = if z ≤ -B then -B + (z + B) * k else if z ≤ B then z
        else B + (z - B) * k := by
      intro z
      zupi
      · exact stretch_of_le hB h1
      · exact stretch_of_abs_le hB (abs_le.2 ztuga)
      · exact stretch_of_ge hB by_linarith
    rw [e x, e y]
    split_ifs <;> nlinarith
  tauto
theorem stretch_inv (hB : 0 ≤ B) (hk : 0 < k) (x : ℝ) : stretch B k⁻¹ (stretch B k x) = x := by
  zugah
  · have h1 : stretch B k x ≤ -B := by
      rw [stretch_of_le hB h]; nlinarith
    rw [stretch_of_le hB h1, stretch_of_le hB h]; grind
  · zuien
    · rw [stretch_of_abs_le hB ztzdh, stretch_of_abs_le hB ztzdh]
    · have h1 : B ≤ stretch B k x := by
        rw [stretch_of_ge hB h']; nlinarith
      rw [stretch_of_ge hB h1, stretch_of_ge hB h']; grind

/-- The stretch as a homeomorphism of the line. -/
noncomputable def stretchHomeoLine (hB : 0 ≤ B) (hk : 0 < k) : ℝ ≃ₜ ℝ where
  toFun := stretch B k
  invFun := stretch B k⁻¹
  left_inv := stretch_inv hB hk
  right_inv x := by
    have := stretch_inv hB (inv_pos.2 hk) x
    simp_all
  continuous_toFun := continuous_stretch B k
  continuous_invFun := continuous_stretch B k⁻¹

/-- **The box stretch** of the plane. -/
noncomputable def stretchPt (B k : ℝ) (p : Point) : Point := (stretch B k p.1, stretch B k p.2)

/-- The box stretch as a homeomorphism of the plane. -/
noncomputable def stretchHomeo (hB : 0 ≤ B) (hk : 0 < k) : Point ≃ₜ Point :=
  (stretchHomeoLine hB hk).prodCongr (stretchHomeoLine hB hk)
theorem stretchPt_of_le (hB : 0 ≤ B) {p : Point} (h1 : |p.1| ≤ B) (h2 : |p.2| ≤ B) :
    stretchPt B k p = p := by
  unfold stretchPt; rw [stretch_of_abs_le hB h1, stretch_of_abs_le hB h2]

/-- The slope that maps the radius `R` to `R'`. -/
noncomputable def slope (B R R' : ℝ) : ℝ := (R' - B) / (R - B)
theorem slope_pos {R R' : ℝ} (hR : B < R) (hR' : B < R') : 0 < slope B R R' :=
  div_pos by_linarith by_linarith
theorem stretch_radius (hB : 0 ≤ B) {R R' : ℝ} (hR : B < R) :
    stretch B ztegd R = R' := by
  have h : R - B ≠ 0 := by_linarith
  rw [stretch_of_ge hB hR.le]; unfold slope; grind

/-- The stretch maps the open interval `(-R, R)` onto `(-R', R')`. -/
theorem abs_stretch_lt_iff (hB : 0 ≤ B) {R R' : ℝ} (hR : B < R) (hR' : B < R') (x : ℝ) :
    |stretch B (slope B R R') x| < R' ↔ |x| < R := by
  have hk := slope_pos hR hR'
  have hm := stretch_strictMono hB hk
  have h1 : stretch B ztegd R = R' := stretch_radius hB hR
  have h2 : stretch B ztegd (-R) = -R' := by rw [stretch_neg hB, h1]
  have e1 : ∀ x, stretch B ztegd x < R' ↔ x < R := fun x => by
    have := hm.lt_iff_lt (a := x) (b := R); simp_all
  have e2 : ∀ x, -R' < stretch B ztegd x ↔ -R < x := fun x => by
    have := hm.lt_iff_lt (a := -R) (b := x); simp_all
  grind

/-- **The box image.** -/
theorem stretchPt_mem_box_iff (hB : 0 ≤ B) {R R' : ℝ} (hR : B < R) (hR' : B < R') (p : Point) :
    stretchPt B ztegd p ∈ Chazelle.Chain.box R' ↔ p ∈ Chazelle.Chain.box R := by
  simp only [Chazelle.Chain.mem_box_iff, stretchPt, abs_stretch_lt_iff hB hR hR']
open Chazelle.Chain
structure Twin (C C' : Chain) : Prop where
  m_eq : C.m = C'.m
  vtx_eq : ∀ k, k ≤ C.m → C.vertex k = C'.vertex k

/-- The fixed band `[-B, B]` of the stretch. -/
noncomputable def bnd (C C' : Chain) : ℝ := min C.radius C'.radius - 1 / 2

/-- The slope of the stretch. -/
noncomputable def kk (C C' : Chain) : ℝ := slope ztes C.radius C'.radius

/-- **The box stretch of twin chains.** -/
noncomputable def phi (C C' : Chain) : Point → Point := stretchPt ztes zteq
variable {C C' : Chain}
theorem one_le_radius (C : Chain) : 1 ≤ C.radius := by
  unfold Chain.radius; linarith [C.coordBound_nonneg]
theorem bnd_nonneg : 0 ≤ bnd C C' := by
  unfold bnd; have := one_le_radius C; have := one_le_radius C'
  grind
theorem bnd_lt : bnd C C' < C.radius := by
  zumrw
theorem bnd_lt' : bnd C C' < C'.radius := by
  zumrw
theorem kk_pos : 0 < kk C C' := slope_pos bnd_lt bnd_lt'
namespace Twin
variable (h : Twin C C')
include h
theorem set_eq : C.set = C'.set := by
  zugmq
  zufj
  simp only [Chain.set, mem_ofPred_eq]
  constructor
  · zucje
    zuhjc

    rwa [← h.vtx_eq k by_omega, ← h.vtx_eq zts by_omega]
  · zucje
    zuhjc

    rwa [h.vtx_eq k by_omega, h.vtx_eq zts by_omega]
variable {p : Point} (i : ℕ)
/-- Points of the chain are well inside the fixed band. -/
theorem abs_le_of_mem (hp : p ∈ C.set) :
    |p.1| ≤ bnd C C' - 1 / 2 ∧ |p.2| ≤ bnd C C' - 1 / 2 := by
  have h1 := C.abs_le_coordBound_of_mem_set hp
  have h2 := C'.abs_le_coordBound_of_mem_set (h.set_eq ▸ hp)
  unfold bnd Chain.radius
  grind
theorem topIdx_eq : C.topIdx = C'.topIdx := by
  zugmq
  zudmc
  · refine C.topIdx_min zttnz fun i hi => ?_
    rw [h.vtx_eq i hi, h.vtx_eq _ zttnz]
    exact C'.topIdx_spec.2 i ztoav
  · refine C'.topIdx_min (hm ▸ C.topIdx_le) fun i hi => ?_
    rw [← h.vtx_eq i ztoav, ← h.vtx_eq _ C.topIdx_le]
    exact C.topIdx_spec.2 i ztoav
theorem top_eq : C.top = C'.top := by
  unfold Chain.top; rw [← h.topIdx_eq]; exact h.vtx_eq _ C.topIdx_le
theorem phi_fix (hp : p ∈ C.set) : phi C C' p = p := by
  have := h.abs_le_of_mem hp
  exact stretchPt_of_le bnd_nonneg by_grind by_grind
omit h in
theorem stretch_fix (_h : Twin C C') {x : ℝ} (hx : |x| ≤ bnd C C') : stretch ztes
    zteq x = x :=
  stretch_of_abs_le bnd_nonneg hx
theorem top_abs : |C.top.1| ≤ bnd C C' - 1 / 2 ∧ |C.top.2| ≤ bnd C C' - 1 / 2 :=
  h.abs_le_of_mem C.top_mem_set
omit h in
theorem stretch_radius_eq (_h : Twin C C') : stretch ztes zteq C.radius = C'.radius :=
  stretch_radius bnd_nonneg bnd_lt
theorem stretch_neg_radius_eq : stretch ztes zteq (-C.radius) = -C'.radius := by
  rw [stretch_neg bnd_nonneg, h.stretch_radius_eq]
theorem phi_slitTop : phi C C' C.slitTop = C'.slitTop := by
  unfold phi stretchPt Chain.slitTop
  rw [h.stretch_fix ztqen, h.stretch_radius_eq, h.top_eq]
omit h in
theorem stretch_inj (_h : Twin C C') {x y : ℝ} (hxy : stretch ztes
    zteq x = stretch ztes zteq y) :
    x = y := (stretch_strictMono bnd_nonneg kk_pos).injective hxy
omit h in
theorem stretch_le_iff (_h : Twin C C') {x y : ℝ} :
    stretch ztes zteq x ≤ stretch ztes zteq y ↔ x ≤ y :=
  (stretch_strictMono bnd_nonneg kk_pos).le_iff_le

/-- A point whose stretch lies on the chain is fixed. -/
theorem eq_of_phi_mem (hp : phi C C' p ∈ C.set) : phi C C' p = p := by
  have hb := h.abs_le_of_mem hp
  simp only [phi, stretchPt] at hb
  have e1 := stretch_inv (B := bnd C C') (k := kk C C') (bnd_nonneg (C := C) (C' := C'))
    (kk_pos (C := C) (C' := C')) p.1
  have e2 := stretch_inv (B := bnd C C') (k := kk C C') (bnd_nonneg (C := C) (C' := C'))
    (kk_pos (C := C) (C' := C')) p.2
  rw [stretch_of_abs_le bnd_nonneg by_grind] at e1
  rw [stretch_of_abs_le bnd_nonneg by_grind] at e2
  exact Prod.ext e1 e2
theorem phi_mem_set_iff (p : Point) : phi C C' p ∈ C'.set ↔ p ∈ C.set := by
  constructor
  · zulmw
    rw [← h.set_eq] at hp
    rwa [h.eq_of_phi_mem hp] at hp
  · intro hp; rw [h.phi_fix hp, ← h.set_eq]; exact hp
theorem phi_mem_slit_iff (p : Point) : phi C C' p ∈ C'.slit ↔ p ∈ C.slit := by
  rw [Chain.mem_slit_iff, Chain.mem_slit_iff, ← h.top_eq]
  have ht1 := h.stretch_fix (x := C.top.1) ztqen
  have ht2 := h.stretch_fix (x := C.top.2) (by linarith [h.top_abs.2])
  zujos
  constructor
  · zuifp
    refine ⟨h.stretch_inj (e1.trans ht1.symm), ?_, ?_⟩
    · rw [← ht2] at e2; exact h.stretch_le_iff.1 e2
    · rw [← h.stretch_radius_eq] at e3; exact h.stretch_le_iff.1 e3
  · zuifp
    zujft
    · rw [← ht2]; exact h.stretch_le_iff.2 e2
    · rw [← h.stretch_radius_eq]; exact h.stretch_le_iff.2 e3
omit h in
theorem phi_mem_box_iff (_h : Twin C C')
    (p : Point) : phi C C' p ∈ box C'.radius ↔ p ∈ box C.radius :=
  stretchPt_mem_box_iff bnd_nonneg bnd_lt bnd_lt' p

/-- **The stretch maps the domain of `C` onto the domain of `C'`.** -/
theorem phi_mem_dom_iff (p : Point) : phi C C' p ∈ C'.dom ↔ p ∈ C.dom := by
  simp only [Chain.dom, Chain.obstacle, mem_sdiff, mem_union, h.phi_mem_box_iff,
    h.phi_mem_set_iff, h.phi_mem_slit_iff]

/-! ## The walks -/
theorem sideIdx_eq : C.sideIdx C.sideBeta i = C'.sideIdx C'.sideBeta i := by
  zugmq
  have hT := h.topIdx_eq
  have hTle := C.topIdx_le
  unfold Chain.sideIdx Chain.sideS
  rw [← hm, ← hT]
  -- the tour does not depend on the turn when the top is an end of the chain
  by_cases hend : C.topIdx = 0 ∨ C.topIdx = C.m
  · have hm0 : ztmsi := by have := C.one_le; omega
    rcases hend with h0 | h0
    · zudty
      cases C.sideBeta <;> cases C'.sideBeta <;> simp [Nat.add_mod_left]
    grind
  · push Not at hend
    have hbeta : C.sideBeta = C'.sideBeta := by
      unfold Chain.sideBeta
      rw [← h.top_eq, ← hT, ← h.vtx_eq _ by_omega, ← h.vtx_eq _ by_omega]
      zucr
      apply propext
      -- the slit direction is `(0, R - top.2)` resp. `(0, R' - top.2)`: same direction
      zueqq
      have hR' := C'.top_snd_lt_radius
      rw [h.top_eq] at hR ⊢
      unfold Chain.slitTop
      zuord
      set A := C.vertex ztbap - C.top
      set Bv := C.vertex ztbao - C.top
      have e1 : (ztnka : Point) - C.top = ztpsj := by
        zuity
      have e2 : ((C.top.1, C'.radius) : Point) - C.top = (0, C'.radius - C.top.2) := by
        zuity
      zuea
      have hc1 : ztixs := by zuotr
      have hc2 : 0 < C'.radius - C.top.2 := by rw [h.top_eq]; linarith
      zumun
      zubi
      constructor <;> intro hh <;>
        rcases hh with ⟨a, b, c⟩ | ⟨a, b⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩
      all_goals first
        | (left; refine ⟨a, ?_, ?_⟩ <;> nlinarith)
        | (right; left; refine ⟨a, ?_⟩; rcases b with b | b
           · simp_all
           · right; nlinarith)
        | (right; right; left; refine ⟨a, b, ?_⟩; nlinarith)
        | (right; right; right; refine ⟨a, b, ?_⟩; rcases c with c | c
           · grind
           · right; nlinarith)
    simp_all
omit h in
theorem sideIdx_le (_h : Twin C C') (i : ℕ) : C.sideIdx C.sideBeta i ≤ C.m := by
  unfold Chain.sideIdx
  exact sideE_le (Nat.mod_lt _ (by have := C.one_le; omega)).le
theorem walk_n : (C'.sideWalk C'.sideBeta).n = (C.sideWalk C.sideBeta).n := by
  rw [Chain.sideWalk_n, Chain.sideWalk_n, h.m_eq]

/-- **The walk vertices correspond under the stretch.** -/
theorem phi_walk_vtx :
    (C'.sideWalk C'.sideBeta).vtx i = phi C C' ((C.sideWalk C.sideBeta).vtx i) := by
  zugmq
  have hR := h.stretch_radius_eq
  have hRn := h.stretch_neg_radius_eq
  rcases Nat.lt_or_ge i 6 with hi | hi
  · interval_cases i
    · rw [Chain.sideWalk_vtx_zero, Chain.sideWalk_vtx_zero, h.phi_slitTop]
    · rw [Chain.sideWalk_vtx_one, Chain.sideWalk_vtx_one]
      zughu
    · rw [Chain.sideWalk_vtx_two, Chain.sideWalk_vtx_two]
      simp only [phi, stretchPt, hRn]
    · rw [Chain.sideWalk_vtx_three, Chain.sideWalk_vtx_three]
      zughu
    · rw [Chain.sideWalk_vtx_four, Chain.sideWalk_vtx_four]
      simp only [phi, stretchPt, hR]
    · rw [Chain.sideWalk_vtx_five, Chain.sideWalk_vtx_five, h.phi_slitTop]
  · rcases Nat.lt_or_ge ztjyn ztyw with hi' | hi'
    · have e : i = ztjyn + 6 := by_omega
      rw [e, C.sideWalk_vtx_tour _ by_omega, C'.sideWalk_vtx_tour _ by_omega]
      zueev
      rw [← h.sideIdx_eq, ← h.vtx_eq _ ztvrz,
        h.phi_fix (C.vertex_mem_set ztvrz)]
    · -- beyond the walk: the default vertex `(0, 0)`, fixed by the stretch
      have hn : (C.sideWalk C.sideBeta).n ≤ i := by rw [Chain.sideWalk_n]; omega
      have hn' : (C'.sideWalk C'.sideBeta).n ≤ i := by rw [Chain.sideWalk_n]; omega
      unfold Polygon.vtx
      rw [List.getD_eq_default _ _ hn, List.getD_eq_default _ _ hn']
      exact (stretchPt_of_le bnd_nonneg ztqfj ztqfj).symm
end Twin
noncomputable def ratio (a b y : ℝ) : ℝ := ztkhj / zthu
variable {a b y : ℝ}
theorem ratio_mem_iff (hab : a ≠ b) :
    (0 ≤ ratio a b y ∧ ratio a b y < 1) ↔ (if a < b then a ≤ y ∧ y < b else b < y ∧ y ≤ a) := by
  zuhqz

  · rw [ite_eq_left h, le_div_iff₀ by_linarith, div_lt_one by_linarith]
    simp
  · rw [ite_eq_right ztwal, div_nonneg_iff, div_lt_one_of_neg by_linarith]
    grind
theorem ratio_eq_zero_iff (hab : a ≠ b) : ratio a b y = 0 ↔ y = a := by
  unfold ratio
  grind
theorem ratio_lt_iff {a b y y' : ℝ} (hab : a ≠ b) :
    ratio a b y < ratio a b y' ↔ (if a < b then y < y' else y' < y) := by
  zuhqz

  · rw [ite_eq_left h, div_lt_div_iff_of_pos_right by_linarith]
    simp
  · rw [ite_eq_right ztwal, div_lt_div_right_of_neg by_linarith]
    simp
variable {C C' : Chain}
theorem sig_strictMono : StrictMono (stretch ztes zteq) := stretch_strictMono bnd_nonneg kk_pos
theorem sig_lt_iff {x y : ℝ} : stretch ztes zteq x < stretch ztes zteq y ↔ x < y := sig_strictMono.lt_iff_lt
theorem sig_le_iff {x y : ℝ} : stretch ztes zteq x ≤ stretch ztes zteq y ↔ x ≤ y := sig_strictMono.le_iff_le
theorem sig_inj {x y : ℝ} : stretch ztes zteq x = stretch ztes zteq y ↔ x = y := sig_strictMono.injective.eq_iff
theorem ratio_mem_sig_iff (hab : a ≠ b) :
    (0 ≤ ratio ztwvd ztwve ztxot ∧
      ratio ztwvd ztwve ztxot < 1) ↔ (0 ≤ ratio a b y ∧ ratio a b y < 1) := by
  rw [ratio_mem_iff zthfd, ratio_mem_iff hab]
  simp only [sig_lt_iff, sig_le_iff]
theorem ratio_eq_zero_sig_iff (hab : a ≠ b) :
    ratio ztwvd ztwve ztxot = 0 ↔ ratio a b y = 0 := by
  rw [ratio_eq_zero_iff zthfd, ratio_eq_zero_iff hab, sig_inj]
theorem ratio_lt_sig_iff {a b y y' : ℝ} (hab : a ≠ b) :
    ratio ztwvd ztwve ztxot < ratio ztwvd ztwve (stretch ztes zteq y') ↔
      ratio a b y < ratio a b y' := by
  rw [ratio_lt_iff zthfd, ratio_lt_iff hab]
  simp only [sig_lt_iff]

/-! ## Positions -/

/-- A walk position whose height code is `0` or the height of a vertex of `Q` inside the fixed
band of the stretch. -/
def BandPos (C C' : Chain) (Q : Polygon) (x : WPos) : Prop :=
  x.hgt = 0 ∨ ∃ h, x.hgt = h + 1 ∧ |(Q.vtx h).2| < bnd C C'

/-- The parameter of a height code in the chain model, as a ratio. -/
theorem param_eq (M : Model) (Q : Polygon) (x : WPos) (k : ℕ) (hk : x.hgt = k + 1) :
    M.param Q x = if (M.wa x.edge).2 = (M.wb x.edge).2 then 0
      else ratio (M.wa x.edge).2 (M.wb x.edge).2 (Q.vtx k).2 := by
  unfold Model.param ratio; rw [hk]

/-- Keys of positions with parameters in `[0, 1)` compare lexicographically. -/
theorem key_lt_iff_lex (M : Model) (Q : Polygon) {x x' : WPos}
    (hm : 0 ≤ M.param Q x ∧ M.param Q x < 1) (hm' : 0 ≤ M.param Q x' ∧ M.param Q x' < 1) :
    M.key Q x < M.key Q x' ↔ x.edge < x'.edge ∨ (x.edge = x'.edge ∧ M.param Q x < M.param Q x') := by
  zuhqn
  constructor
  · zufia
    rcases lt_trichotomy x.edge x'.edge with h1 | h1 | h1
    · omega
    · simp_all
    · exfalso
      have : (x'.edge : ℝ) + 1 ≤ x.edge := by exact_mod_cast h1
      grind
  · zuczc
    · have : (x.edge : ℝ) + 1 ≤ x'.edge := by exact_mod_cast h1
      grind
    simp_all
namespace Twin
variable (h : Twin C C')
include h
variable (p : ℕ) {Q : Polygon} {x : WPos}
theorem wa_eq : (chainModel C').wa p = phi C C' ztbkd :=
  h.phi_walk_vtx p
theorem wb_eq : (chainModel C').wb p = phi C C' ztbke := by
  show (C'.sideWalk C'.sideBeta).vtx (ztr % (C'.sideWalk C'.sideBeta).n) = _
  rw [h.walk_n]; exact h.phi_walk_vtx _
omit h in
theorem sig_band {y : ℝ} (hy : |y| < bnd C C') : stretch ztes zteq y = y :=
  stretch_of_abs_le bnd_nonneg hy.le

/-- **The parameters in the two models.**  For a band position the parameter in `M'` is the
ratio of the stretched heights. -/
theorem param'_eq {k : ℕ} (hk : x.hgt = k + 1)
    (hy : |(Q.vtx k).2| < bnd C C') :
    (chainModel C').param Q x = if ((chainModel C).wa x.edge).2 = ((chainModel C).wb x.edge).2
      then 0 else ratio (stretch ztes zteq ((chainModel C).wa x.edge).2)
        (stretch ztes zteq ((chainModel C).wb x.edge).2) ztyka := by
  rw [param_eq _ Q x k hk, h.wa_eq, h.wb_eq, sig_band hy]
  zujos
  zucfn
  · simp_all
  · have hh' : ¬ stretch ztes zteq ((chainModel C).wa x.edge).2 =
        stretch ztes zteq ((chainModel C).wb x.edge).2 := fun e => hh (sig_inj.1 e)
    simp_all
theorem param_mem_iff (hx : BandPos C C' Q x) :
    (0 ≤ (chainModel C').param Q x ∧ (chainModel C').param Q x < 1) ↔
      (0 ≤ (chainModel C).param Q x ∧ (chainModel C).param Q x < 1) := by
  zuceg
  · zulae
  · zubyp
    split_ifs with hh
    · simp
    · exact ratio_mem_sig_iff hh
theorem param_eq_zero_iff (hx : BandPos C C' Q x) :
    (chainModel C').param Q x = 0 ↔ (chainModel C).param Q x = 0 := by
  zuceg
  · zulae
  · zubyp
    split_ifs with hh
    · simp
    · exact ratio_eq_zero_sig_iff hh

/-- On one walk edge the parameters of band positions are ordered alike. -/
theorem param_lt_iff {x x' : WPos} (hx : BandPos C C' Q x) (hx' : BandPos C C' Q x')
    (he : x.edge = x'.edge) (hm : 0 ≤ (chainModel C).param Q x ∧ (chainModel C).param Q x < 1)
    (hm' : 0 ≤ (chainModel C).param Q x' ∧ (chainModel C).param Q x' < 1) :
    (chainModel C').param Q x < (chainModel C').param Q x' ↔
      (chainModel C).param Q x < (chainModel C).param Q x' := by
  have z1 := h.param_eq_zero_iff hx
  have z2 := h.param_eq_zero_iff hx'
  zuddm

  -- when one parameter is zero the comparison is with zero
  have hzero : ∀ (u v u' v' : ℝ), 0 ≤ u → 0 ≤ v → 0 ≤ u' → 0 ≤ v' → (u' = 0 ↔ u = 0) →
      (v' = 0 ↔ v = 0) → (u = 0 ∨ v = 0) → (u' < v' ↔ u < v) := by
    grind
  by_cases h0 : (chainModel C).param Q x = 0 ∨ (chainModel C).param Q x' = 0
  · exact hzero _ _ _ _ hm.1 hm'.1 r1.1 r2.1 z1 z2 h0
  zugre
  rcases hx with hx0 | ⟨k, hk, hy⟩
  · exact absurd ztnuq h0.1
  rcases hx' with hx0 | ⟨k', hk', hy'⟩
  · exact absurd ztnuq h0.2
  have hne0 := h0.1
  rw [param_eq _ Q x k hk] at hne0
  rw [h.param'_eq hk hy, h.param'_eq hk' hy', param_eq _ Q x k hk, param_eq _ Q x' k' hk', ← he]
  zucfn
  · simp_all
  · simp only [hh, ↓reduceIte]; exact ratio_lt_sig_iff hh

/-- **Keys are ordered alike in the two models.** -/
theorem key_lt_iff {x x' : WPos} (hx : BandPos C C' Q x) (hx' : BandPos C C' Q x')
    (hm : 0 ≤ (chainModel C).param Q x ∧ (chainModel C).param Q x < 1)
    (hm' : 0 ≤ (chainModel C).param Q x' ∧ (chainModel C).param Q x' < 1) :
    (chainModel C').key Q x < (chainModel C').key Q x' ↔
      (chainModel C).key Q x < (chainModel C).key Q x' := by
  rw [key_lt_iff_lex _ Q ((h.param_mem_iff hx).2 hm) ((h.param_mem_iff hx').2 hm'),
    key_lt_iff_lex _ Q hm hm']
  constructor
  · zuczc
    · omega
    · exact Or.inr ⟨h1, (h.param_lt_iff hx hx' h1 hm hm').1 h2⟩
  · zuczc
    · omega
    · exact Or.inr ⟨h1, (h.param_lt_iff hx hx' h1 hm hm').2 h2⟩

/-- **Arc weights between band positions agree.** -/
theorem arcWt_eq {x x' : WPos} (hx : BandPos C C' Q x) (hx' : BandPos C C' Q x')
    (hm : 0 ≤ (chainModel C).param Q x ∧ (chainModel C).param Q x < 1)
    (hm' : 0 ≤ (chainModel C).param Q x' ∧ (chainModel C).param Q x' < 1) :
    (chainModel C').arcWt ((chainModel C').key Q x) ((chainModel C').key Q x') =
      (chainModel C).arcWt ztlb ((chainModel C).key Q x') := by
  have hn : (chainModel C).W.n = 2 * C.m + 6 + 1 := by rw [chainModel_n]
  have hn' : (chainModel C').W.n = 2 * C.m + 6 + 1 := by rw [chainModel_n, ← h.m_eq]
  have hc : ∀ p, p < (chainModel C).W.n →
      ztfxr := fun p _ => Iff.rfl
  have hc' : ∀ p, p < (chainModel C').W.n →
      ((chainModel C').counted p ↔ 6 ≤ p ∧ p < 2 * C.m + 6) := by
    intro p _; show (6 ≤ p ∧ p < 2 * C'.m + 6) ↔ _; rw [h.m_eq]
  zuddm

  rw [Model.arcWt_key _ hc by_omega Q hm hm', Model.arcWt_key _ hc' by_omega Q r1 r2]
  zuluc
  have hlt := h.key_lt_iff hx hx' hm hm'
  unfold Model.key at hlt
  simp only [hlt, h.param_eq_zero_iff hx']
end Twin
open Chazelle.Visibility
theorem tour_mem (C : Chain) {j : ℕ} (hj6 : 6 ≤ j) (hj : j ≤ 2 * C.m + 6) :
    (C.sideWalk C.sideBeta).vtx j ∈ C.set := by
  have e : j = (j - 6) + 6 := by_omega
  rw [e, C.sideWalk_vtx_tour _ by_omega]
  exact C.vertex_mem_set ztbdw
theorem walk_last (C : Chain) : (C.sideWalk C.sideBeta).vtx ztcc = C.top := by
  have := C.sideWalk_vtx_tour C.sideBeta (i := 2 * C.m) le_rfl
  rwa [C.sideTour_two_m] at this

/-- **The kinds of walk edges**: horizontal, vertical, or between two chain vertices. -/
theorem edge_kind (C : Chain) {p : ℕ} (hp : p < (C.sideWalk C.sideBeta).n) :
    ((C.sideWalk C.sideBeta).vtx p).2 =
        ((C.sideWalk C.sideBeta).vtx ztwqw).2 ∨
      ((C.sideWalk C.sideBeta).vtx p).1 =
        ((C.sideWalk C.sideBeta).vtx ztwqw).1 ∨
      ((C.sideWalk C.sideBeta).vtx p ∈ C.set ∧
        (C.sideWalk C.sideBeta).vtx ztwqw ∈ C.set) := by
  zuern
  zugei
  zuidp
  · have hmod : ztycy := by
      zucjs
    zugvd
    interval_cases p
    · tauto
    · tauto
    · tauto
    · tauto
    · tauto
    · right; left; rw [C.sideWalk_vtx_five, C.sideWalk_vtx_six]; rfl
  · zuidq
    · zulw
      have hmod : ztycy := by
        zucjs
      zugvd
      exact ⟨tour_mem C h6 by_omega, tour_mem C by_omega by_omega⟩
    · zuhl
      zudzk

      rw [C.sideWalk_vtx_wrap, walk_last]; rfl

/-! ## Points of band positions -/

/-- Points of a segment between two points of the fixed band stay in it. -/
theorem abs_lerp_le {u v : Point} {c : ℝ} (hu : |u.1| ≤ c ∧ |u.2| ≤ c) (hv : |v.1| ≤ c ∧ |v.2| ≤ c)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    |(Geometry.lerp u v t).1| ≤ c ∧ |(Geometry.lerp u v t).2| ≤ c := by
  simp only [Geometry.lerp]
  have key : ∀ a b : ℝ, |a| ≤ c → |b| ≤ c → |a + t * zthu| ≤ c := by
    intro a b ha hb
    rw [abs_le] at *
    constructor <;> nlinarith [ha.1, ha.2, hb.1, hb.2]
  simp_all
namespace Twin
variable (h : Twin C C')
include h
variable {Q : Polygon} {y a b : ℝ}
/-- **Band positions correspond under the stretch.** -/
theorem pos_eq {x : WPos} (hxn : x.edge < (chainModel C).W.n)
    (hx : BandPos C C' Q x) (hm : 0 ≤ (chainModel C).param Q x ∧ (chainModel C).param Q x < 1) :
    (chainModel C').pos Q x = phi C C' ztte := by
  zueew
  zukro
  set u := (chainModel C).wa x.edge with hu
  set v := (chainModel C).wb x.edge with hv
  zuceg
  · simp [Model.param, h0, Geometry.lerp_zero]
  zubyp
  rw [param_eq _ Q x k hk] at hm
  by_cases hh : u.2 = v.2
  · simp_all
  simp only [← hu, ← hv, hh, ↓reduceIte] at hm ⊢
  zubkp
  rcases edge_kind C hxn with hk2 | hk1 | ⟨hua, hvb⟩
  · tauto
  · -- a vertical edge
    have hk1' : u.1 = v.1 := hk1
    have hne : ztsmu := sub_ne_zero.2 ztqaz
    have hne' : (phi C C' v).2 - (phi C C' u).2 ≠ 0 := by
      simp only [phi, stretchPt]; exact sub_ne_zero.2 (fun e => hh (sig_inj.1 e).symm)
    zujrv
    · simp only [Geometry.lerp, phi, stretchPt, ← hk1', sub_self, mul_zero, add_zero]
    · have hne2 : stretch ztes zteq v.2 - stretch ztes zteq u.2 ≠ 0 :=
        hne'
      have e1 : u.2 + ratio u.2 v.2 (Q.vtx k).2 * ztgv = (Q.vtx k).2 := by
        zumub
      have e2 : stretch ztes zteq u.2 + ratio (stretch ztes zteq u.2)
          (stretch ztes zteq v.2) ztyka *
          (stretch ztes zteq v.2 - stretch ztes zteq u.2) =
          stretch ztes zteq (Q.vtx k).2 := by
        zumub
      simp only [Geometry.lerp, phi, stretchPt]
      simp_all
  · -- an edge between two chain vertices: nothing moves
    have hu' : phi C C' u = u := h.phi_fix hua
    have hv' : phi C C' v = v := h.phi_fix hvb
    rw [hu', hv']
    have hsu : stretch ztes zteq u.2 = u.2 := by
      have := congrArg Prod.snd hu'; tauto
    have hsv : stretch ztes zteq v.2 = v.2 := by
      have := congrArg Prod.snd hv'; tauto
    rw [hsu, hsv, hy']
    have hb := abs_lerp_le (u := u) (v := v) (h.abs_le_of_mem hua) (h.abs_le_of_mem hvb) hm.1
      hm.2.le
    exact (stretchPt_of_le bnd_nonneg by_grind by_grind).symm

/-! ## Chords -/
omit h in
/-- The stretch of a horizontal segment at a band height. -/
theorem image_hseg (hy : |y| < bnd C C') :
    phi C C' '' hseg y a b = hseg y ztwvd
      ztwve := by
  zubkp
  zumai
  constructor
  · rintro ⟨w, ⟨hw1, hw2, hw3⟩, rfl⟩
    refine ⟨?_, sig_le_iff.2 hw2, sig_le_iff.2 hw3⟩
    simp only [phi, stretchPt]; simp_all
  · rintro ⟨hz1, hz2, hz3⟩
    set w : Point := (stretch ztes zteq⁻¹ z.1, y)
    have hinv : stretch ztes zteq (stretch ztes zteq⁻¹ z.1) = z.1 := by
      have := stretch_inv (B := bnd C C') (k := zteq⁻¹) bnd_nonneg
        ztvxi z.1
      simp_all
    refine ⟨w, ztkw, ?_⟩
    · zudks
    · zudks
    · zujrv
      · tauto
      · simp only [phi, stretchPt, w]; simp_all

/-- **The chord of a band record in the model of `C'` is the stretched chord.** -/
theorem toSet_eq {r : CRec} (hy : |(Q.vtx r.h).2| < bnd C C')
    (hl : r.lp < (chainModel C).W.n) (hr : r.rp < (chainModel C).W.n)
    (hml : 0 ≤ (chainModel C).param Q r.lpos ∧ (chainModel C).param Q r.lpos < 1)
    (hmr : 0 ≤ (chainModel C).param Q r.rpos ∧ (chainModel C).param Q r.rpos < 1) :
    r.toSet ztbmo Q = phi C C' '' r.toSet ztc Q := by
  have hbl : BandPos C C' Q r.lpos := Or.inr ztrea
  have hbr : BandPos C C' Q r.rpos := Or.inr ztrea
  unfold CRec.toSet
  rw [image_hseg hy, h.pos_eq hl hbl hml, h.pos_eq hr hbr hmr]
  rfl

/-- **Admissibility transfers**: the stretch of an augmented chord of `C` at a band height is an
augmented chord of `C'`. -/
theorem augChords_transfer (hy : |y| < bnd C C')
    (hc : hseg y a b ∈ Merge.augChords C) :
    hseg y ztwvd ztwve ∈
      Merge.augChords C' := by
  obtain ⟨y', a', b', hh, hy'', he⟩ := hc
  -- the representation is unique: `hseg y a b = hseg y' a' b'` with `a' < b'`
  have hne : (hseg y' a' b').Nonempty := ⟨ztdtr, rfl, le_rfl, hh.lt.le⟩
  zvndl at hne
  zucik
  have hz' : z ∈ hseg y' a' b' := he ▸ hz
  have hyy : ztsne := hz.1.symm.trans hz'.1
  zulau
  have hab : a = a' ∧ b = b' := by
    have hl : ztygi := by zvmxm; exact ⟨rfl, le_rfl, hh.lt.le⟩
    have hr : ztygj := by zvmxm; exact ⟨rfl, hh.lt.le, le_rfl⟩
    have ha : (ztdv : Point) ∈ hseg y a' b' := by
      zvndl; exact ⟨rfl, le_rfl, le_trans hl.2.1 hl.2.2⟩
    have hb : (ztdy : Point) ∈ hseg y a' b' := by
      zvndl; exact ⟨rfl, le_trans hl.2.1 hl.2.2, le_rfl⟩
    exact ⟨le_antisymm hl.2.1 ha.2.1, le_antisymm hb.2.2 hr.2.2⟩
  zuidd
  zubkp
  refine ⟨y, _, _, ⟨sig_lt_iff.2 hh.lt, ?_, ?_, ?_⟩, ?_, rfl⟩
  · zujbb
    have : phi C C' ztdv ∈ C'.dom := by zunuy; exact hm
    exact hh.left_not ztoss
  · zujbb
    have : phi C C' ztdy ∈ C'.dom := by zunuy; exact hm
    exact hh.right_not ztoss
  · zuetl
    set w := stretch ztes zteq⁻¹ x
    have hinv : stretch ztes zteq w = x := by
      have := stretch_inv (B := bnd C C') (k := zteq⁻¹) bnd_nonneg ztvxi x
      grind
    have hw := hh.open_mem w (by zunex; omega)
      (by zunex; omega)
    have := (h.phi_mem_dom_iff (w, y)).2 hw
    simpa only [phi, stretchPt, hinv, hy'] using this
  · zuord; omega
end Twin
theorem pos_mul_iff {p c : ℝ} (hp : 0 < p) :
    (0 < p * c ↔ 0 < c) ∧ (p * c < 0 ↔ c < 0) ∧ (p * c = 0 ↔ c = 0) := by
  refine ⟨⟨fun h => ?_, fun h => mul_pos hp h⟩,
    ⟨fun h => ?_, fun h => mul_neg_of_pos_of_neg hp h⟩, ⟨fun h => ?_, fun h => by_simp_all⟩⟩
  · simp_all
  · by_contra h'; nlinarith
  grind
variable (a b : ℝ) (u v : Point) (W : Polygon) (p : ℕ) (t : ℝ)
theorem sideCross_smul :
    sideCross ztteq zttfm = zthdh * sideCross u v := by
  zubsv
theorem sideDot_smul :
    sideDot ztteq zttfm = zthdh * sideDot u v := by
  zuenx

/-- **The sector test is invariant under positive scalings.** -/
theorem sideCcw_smul {l k m : ℝ} (hl : 0 < l) (hk : 0 < k) (hm : 0 < m) (B X A : Point) :
    sideCcw (l • B) (k • X) (m • A) ↔ sideCcw B X A := by
  zufqe
  rw [sideCross_smul, sideCross_smul, sideCross_smul, sideDot_smul, sideDot_smul]
  obtain ⟨a1, a2, a3⟩ := pos_mul_iff (c := sideCross B A) zttts
  obtain ⟨b1, -, b3⟩ := pos_mul_iff (c := sideCross B X) ztttr
  obtain ⟨c1, -, -⟩ := pos_mul_iff (c := sideCross X A) (mul_pos hk hm)
  obtain ⟨d1, d2, -⟩ := pos_mul_iff (c := sideDot B A) zttts
  obtain ⟨-, e2, -⟩ := pos_mul_iff (c := sideDot B X) ztttr
  grind

/-- The left sector test at a walk position, in terms of the corner vectors. -/
theorem sideLeft_eq (x : Point) :
    sideLeft W p t x ↔ sideCcw ztmoi (x - sidePt W p t)
      (sidePrev W p t - sidePt W p t) := Iff.rfl
theorem next_sub_pt :
    sideNext W p - sidePt W p t = ztca • ztbalz := by
  unfold sideNext sidePt
  apply Prod.ext <;> zuoul <;> ring
theorem prev_sub_pt {t : ℝ} (ht : t ≠ 0) :
    sidePrev W p t - sidePt W p t = (-t) • ztbalz := by
  unfold sidePrev sidePt
  zulqk
  apply Prod.ext <;> zuoul
theorem prev_sub_pt_zero :
    sidePrev W p 0 - sidePt W p 0 =
      (-1 : ℝ) • (W.vtx p - W.vtx ztbvk) := by
  unfold sidePrev sidePt
  simp
theorem prev_succ {n p : ℕ} (hp : p < n) : ztxhn % n = p := by
  zuevd
  · zubvi
    zufsw
    rw [e, Nat.sub_add_cancel (by omega : 1 ≤ n), Nat.mod_self]
  · have e : ztxfl := by
      zuxw
    rw [e, Nat.sub_add_cancel h0, Nat.mod_eq_of_lt hp]

/-! ## Twin chains -/
variable {C C' : Chain}

/-- The stretch has positive slopes. -/
theorem sig_slope :
    ∃ l : ℝ, 0 < l ∧ stretch ztes zteq b - stretch ztes zteq a = l * zthu := by
  rcases lt_trichotomy a b with hab | rfl | hab
  · have h1 : stretch ztes zteq a < stretch ztes zteq b := sig_lt_iff.2 hab
    refine ⟨ztyft / zthu,
      div_pos by_linarith by_linarith, ?_⟩
    grind
  · exact ⟨1, one_pos, by_ring⟩
  · have h1 : stretch ztes zteq b < stretch ztes zteq a := sig_lt_iff.2 hab
    refine ⟨ztyft / zthu,
      div_pos_of_neg_of_neg by_linarith by_linarith, ?_⟩
    grind
namespace Twin
variable (h : Twin C C')
include h

/-- **The stretch scales horizontal, vertical and chain segments positively.** -/
theorem scale_pt {u v : Point} (hk : u.2 = v.2 ∨ u.1 = v.1 ∨ (u ∈ C.set ∧ v ∈ C.set)) :
    ∃ l : ℝ, 0 < l ∧ phi C C' v - phi C C' u = l • ztbnr := by
  rcases hk with hk | hk | ⟨hu, hv⟩
  · obtain ⟨l, hl, e⟩ := sig_slope (C := C) (C' := C') u.1 v.1
    refine ztoox
    · tauto
    · zuios
  · obtain ⟨l, hl, e⟩ := sig_slope (C := C) (C' := C') u.2 v.2
    refine ztoox
    · zuios
    tauto
  · exact ⟨1, one_pos, by rw [h.phi_fix hu, h.phi_fix hv, one_smul]⟩

/-- **Walk edges scale positively.** -/
theorem edge_scale {q : ℕ} (hq : q < (C.sideWalk C.sideBeta).n) :
    ∃ l : ℝ, 0 < l ∧ (C'.sideWalk C'.sideBeta).vtx ztwtw -
        (C'.sideWalk C'.sideBeta).vtx q =
      l • ((C.sideWalk C.sideBeta).vtx ztwtw -
        (C.sideWalk C.sideBeta).vtx q) := by
  rw [h.phi_walk_vtx, h.phi_walk_vtx]
  exact h.scale_pt (edge_kind C hq)

/-- **The corner vectors of corresponding walk positions scale positively.** -/
theorem sector_scale {p : ℕ} {t t' : ℝ} (hp : p < (C.sideWalk C.sideBeta).n)
    (ht : 0 ≤ t ∧ t < 1) (ht' : 0 ≤ t' ∧ t' < 1) (h0 : t = 0 ↔ t' = 0) :
    ∃ α : ℝ, 0 < α ∧ ∃ β : ℝ, 0 < β ∧
      sideNext ztffh p - sidePt ztffh p t' =
          α • (sideNext ztcs p - sidePt ztcs p t) ∧
        sidePrev ztffh p t' - sidePt ztffh p t' =
          β • (sidePrev ztcs p t - sidePt ztcs p t) := by
  set W := C.sideWalk C.sideBeta
  set W' := C'.sideWalk C'.sideBeta
  have hn : W'.n = W.n := h.walk_n
  obtain ⟨l, hl, e⟩ := h.edge_scale hp
  have hα : 0 < ztndn * l / ztca := div_pos (mul_pos by_linarith hl) by_linarith
  have eN : sideNext W' p - sidePt W' p t' =
      (ztndn * l / ztca) • ztmoi := by
    rw [next_sub_pt, next_sub_pt, hn, e, smul_smul, smul_smul]
    zucr
    field_simp [show 1 - t ≠ 0 by linarith]
  refine ⟨_, hα, ?_⟩
  by_cases ht0 : t = 0
  · have ht0' : ztmwy := h0.1 ht0
    zultf
    set q := (p + W.n - 1) % W.n
    have hnpos : ztmsm := by_omega
    have hq : q < W.n := Nat.mod_lt _ hnpos
    obtain ⟨l', hl', e'⟩ := h.edge_scale hq
    have hqp : ztfo % W.n = p := prev_succ hp
    rw [hqp] at e'
    refine ⟨l', hl', eN, ?_⟩
    rw [prev_sub_pt_zero, prev_sub_pt_zero, hn, e', smul_smul, smul_smul, mul_comm]
  · have ht0' : t' ≠ 0 := fun e0 => ht0 (h0.2 e0)
    have htp : ztfkp := lt_of_le_of_ne ht.1 ztqbb
    have htp' : ztrzn := lt_of_le_of_ne ht'.1 (Ne.symm ht0')
    refine ⟨t' * l / t, div_pos (mul_pos htp' hl) htp, eN, ?_⟩
    rw [prev_sub_pt _ _ ht0, prev_sub_pt _ _ ht0', hn, e, smul_smul, smul_smul]
    grind

/-- **Attachment transfers.**  A set on a horizontal line attached to the walk of `C` at `(p, t)`
has its stretch attached to the walk of `C'` at the corresponding position `(p, t')`. -/
theorem attach_transfer {d : Set Point} {y : ℝ} (hdy : ∀ z ∈ d, z.2 = y) {p : ℕ} {t t' : ℝ}
    (hpt : sidePt ztffh p t' = phi C C' ztyfq)
    (ht' : 0 ≤ t' ∧ t' < 1) (h0 : t = 0 ↔ t' = 0)
    (hA : SideAttach ztcs d p t) :
    SideAttach ztffh (phi C C' '' d) p t' := by
  obtain ⟨hp, ht0, ht1, hmem, r, hr, hnear⟩ := hA
  refine ⟨h.walk_n ▸ hp, ht'.1, ht'.2, hpt ▸ mem_image_of_mem _ hmem, ?_⟩
  obtain ⟨α, hα, β, hβ, eN, eP⟩ := h.sector_scale hp ztcoy ht' h0
  set ψ := (stretchHomeo (bnd_nonneg (C := C) (C' := C')) (kk_pos (C := C) (C' := C'))).symm
  have hψ : ∀ z, ψ (phi C C' z) = z := fun z =>
    (stretchHomeo (bnd_nonneg (C := C) (C' := C')) (kk_pos (C := C) (C' := C'))).symm_apply_apply z
  obtain ⟨r', hr', hball⟩ := Metric.continuous_iff.1 ψ.continuous
    (sidePt ztffh p t') r hr
  refine ⟨r', hr', ?_⟩
  rintro x' ⟨z, hz, rfl⟩ hne hdist
  set s := sidePt ztcs p t
  have hzd : dist z s < r := by
    grind
  have hzne : z ≠ s := fun e => hne by_grind
  have hL := hnear z hz hzne hzd
  have hz2 : s.2 = z.2 := (hdy s hmem).trans (hdy z hz).symm
  obtain ⟨κ, hκ, eX⟩ := h.scale_pt (Or.inl hz2)
  rw [sideLeft_eq, eN, eP, hpt, eX, sideCcw_smul hα hκ hβ]
  exact hL
end Twin
end
end BoxT
namespace DownMath
@[expose] public section
open Set
open Chazelle.Chain (sideE)

/-- The coordinate bound is invariant under rotation. -/
theorem coordBound_rotate (P : Polygon) (s : ℕ) :
    Chazelle.Jordan.coordBound ztqbh = Chazelle.Jordan.coordBound P := by
  unfold Chazelle.Jordan.coordBound
  zunrt
  rw [← Existence.sum_range_rot (fun i => |(P.vtx i).1| + |(P.vtx i).2|) s P.n]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Existence.vtx_rotate _ _ (Finset.mem_range.1 hi)]
section
variable {C C' : Chain} (hm : C.m = C'.m) (hv : ∀ k, C.vertex k = C'.vertex k)
  (hr : Chazelle.Jordan.coordBound C.P = Chazelle.Jordan.coordBound C'.P)
include hm hv hr
omit hr in
theorem set_congr : C.set = C'.set := by
  zufj
  simp only [Chain.set, Set.mem_ofPred_eq, Chain.chainEdge_eq, hv, hm]
omit hr in
theorem topIdx_congr : C.topIdx = C'.topIdx := by
  zudmc
  · apply C.topIdx_min (by zvmwi; exact C'.topIdx_le)
    zug
    rw [hv, hv]; exact C'.topIdx_spec.2 i by_omega
  · apply C'.topIdx_min (by rw [← hm]; exact C.topIdx_le)
    zug
    rw [← hv, ← hv]; exact C.topIdx_spec.2 i by_omega
omit hr in
theorem top_congr : C.top = C'.top := by
  unfold Chain.top; rw [hv, topIdx_congr hm hv]
omit hm hv in
theorem radius_congr : C.radius = C'.radius := by
  unfold Chain.radius; zvnel
theorem slitTop_congr : C.slitTop = C'.slitTop := by
  unfold Chain.slitTop; rw [top_congr hm hv, radius_congr hr]
theorem dom_congr : C.dom = C'.dom := by
  unfold Chain.dom Chain.obstacle Chain.slit
  rw [set_congr hm hv, slitTop_congr hm hv hr, top_congr hm hv, radius_congr hr]
theorem sideBeta_congr : C.sideBeta = C'.sideBeta := by
  rw [Bool.eq_iff_iff, Chain.sideBeta_eq_true_iff, Chain.sideBeta_eq_true_iff]
  simp only [hv, top_congr hm hv, slitTop_congr hm hv hr, topIdx_congr hm hv]
theorem sideWalk_congr (β : Bool) : C.sideWalk β = C'.sideWalk β := by
  unfold Chain.sideWalk Chain.boxList Chain.sideTour Chain.sideIdx Chain.sideS
  simp only [hv, hm, slitTop_congr hm hv hr, radius_congr hr, topIdx_congr hm hv]
theorem augChords_congr : Merge.augChords C = Merge.augChords C' := by
  unfold Merge.augChords
  rw [dom_congr hm hv hr, top_congr hm hv]
theorem chords_congr : C.chords = C'.chords := by
  unfold Chain.chords Chain.DirFree Chain.chordSet Chain.chordEnd Chain.chordParam
    Chain.hitParam Chain.hitSet
  simp only [hv, hm, dom_congr hm hv hr]

/-- **The chain model depends only on the vertices, the length and the box radius.** -/
theorem chainModel_congr : chainModel C = chainModel C' := by
  unfold chainModel
  rw [dom_congr hm hv hr, sideBeta_congr hm hv hr, sideWalk_congr hm hv hr,
    augChords_congr hm hv hr, chords_congr hm hv hr, hm]
end
end
end DownMath
namespace Mir
@[expose] public section
open Set Filter Topology
open Chazelle.Chain (freeIn regionsIn TouchesIn SideAttach sideInArc IsHChordIn)
open Chazelle.Visibility (hseg rayPt)

/-! ## Points, rays, horizontal segments -/
theorem mir_pt (x y : ℝ) : mir (ztjw : Point) = (-x, y) := rfl
theorem mir_rayPt (p : Point) (σ t : ℝ) : mir (rayPt p σ t) = rayPt ztqtn (-σ) t := by
  apply Prod.ext <;> simp [mir, rayPt]; ring
theorem hseg_mir (y a b : ℝ) : mir '' hseg y a b = hseg y (-b) (-a) := by
  zumx
  zudal
  simp only [hseg, mem_ofPred_eq, mir_fst, mir_snd]
  grind

/-- **Horizontal chords of the mirrored domain.** -/
theorem isHChordIn_mir {D : Set Point} {y a b : ℝ} :
    IsHChordIn zthiq y (-b) (-a) ↔ IsHChordIn D y a b := by
  constructor
  · zuq
    refine ⟨by zuowv, fun hm => h.right_not ?_, fun hm => h.left_not ?_,
      fun x h1 h2 => ?_⟩
    · zugfb
    · zugfb
    · have := h.open_mem (-x) by_linarith by_linarith
      rwa [mem_image_mir, mir_pt, neg_neg] at this
  · zuq
    refine ⟨by zuowv, fun hm => h.right_not ?_, fun hm => h.left_not ?_,
      fun x h1 h2 => ?_⟩
    · zugya
    · zugya
    · rw [mem_image_mir, mir_pt]; exact h.open_mem _ by_linarith by_linarith
theorem closure_mir (U : Set Point) : closure ztdht = mir '' closure U :=
  (mirHomeo.image_closure U).symm

/-! ## Mirrored families -/

/-- The mirror image of a family of sets. -/
def mirF (F : Set ztf) : Set ztf := (fun c => mir '' c) '' F
variable {F : Set (Set Point)} (D : Set Point)
theorem mem_mirF {c : Set Point} : c ∈ mirF F ↔ mir '' c ∈ F := by
  constructor
  · rintro ⟨e, he, rfl⟩; rwa [image_mir_image_mir]
  · intro h; exact ⟨mir '' c, h, image_mir_image_mir c⟩
theorem image_mem_mirF {e : Set Point} : mir '' e ∈ mirF F ↔ e ∈ F := by
  rw [mem_mirF, image_mir_image_mir]
theorem mirF_mirF (F : Set ztf) : mirF ztciv = F := by
  ext c; rw [mem_mirF, mem_mirF, image_mir_image_mir]
theorem mirF_injective : Function.Injective (fun c : Set Point => mir '' c) := fun a b hab => by
  have := congrArg (fun c : Set Point => mir '' c) hab
  simpa only [image_mir_image_mir] using this
theorem mirF_finite : (mirF F).Finite ↔ F.Finite :=
  ⟨fun h => by rw [← mirF_mirF F]; exact h.image _, fun h => h.image _⟩
@[simp] theorem mirF_empty : mirF ∅ = ∅ := image_empty _
theorem mirF_nonempty : (mirF F).Nonempty ↔ F.Nonempty := image_nonempty
theorem mirF_subset {F G : Set ztf} : mirF F ⊆ mirF G ↔ F ⊆ G :=
  image_subset_image_iff mirF_injective
theorem mirF_union (F G : Set ztf) : mirF (F ∪ G) = mirF F ∪ mirF G := image_union _ _ _
theorem sUnion_mirF (F : Set ztf) : ⋃₀ mirF F = mir '' ⋃₀ F := by
  zumx
  rw [mem_image_mir, mem_sUnion, mem_sUnion]
  constructor
  · rintro ⟨c, hc, hx⟩
    exact ⟨mir '' c, mem_mirF.1 hc, by_grind⟩
  · rintro ⟨e, he, hx⟩
    exact ⟨mir '' e, image_mem_mirF.2 he, mem_image_mir.2 hx⟩
theorem freeIn_mir (F : Set ztf) :
    freeIn zthiq ztciv = mir '' freeIn D F := by
  unfold freeIn; rw [sUnion_mirF, image_sdiff mir_injective]

/-- **The regions of the mirrored family are the mirrored regions.** -/
theorem regionsIn_mir (F : Set ztf) :
    regionsIn zthiq ztciv = mirF (regionsIn D F) := by
  zulge
  zudux
  unfold regionsIn
  rw [freeIn_mir]
  constructor
  · zuecs
    refine ⟨mir z, mem_image_mir.1 hz, ?_⟩
    rw [image_connectedComponentIn_mir, image_mir_image_mir]
  · rintro ⟨z, hz, hU⟩
    refine ⟨mir z, by_grind, ?_⟩
    rw [← image_mir_image_mir U, hU, image_connectedComponentIn_mir]
theorem touchesIn_mir {D c U : Set Point} :
    TouchesIn zthiq ztodo ztdht ↔ TouchesIn D c U := by
  unfold TouchesIn
  rw [← image_inter mir_injective, closure_mir]
  constructor
  · zuifx
    exact ⟨mir z, mem_image_mir.1 hz, mem_image_mir.1 hzU⟩
  · zuifx
    exact ⟨mir z, by_grind, by_grind⟩

/-! ## Mirrored models -/

/-- **`M'` is the mirror image of the model `M`**, its walk traversed backwards (shift `c`). -/
structure ModelMir (M M' : Model) (c : ℕ) : Prop where
  D : M'.D = mir '' M.D
  walk : WalkMir M.W M'.W c
  counted : ∀ p, p < M.W.n → (M'.counted p ↔ M.counted (ztlkb % M.W.n))
  Adm : M'.Adm = mirF M.Adm
  Full : M'.Full = mirF M.Full

/-- Cut keys lie in `[0, n)`. -/
theorem isCut_bounds {M : Model} {F : Set ztf} {x : ℝ} (hx : M.IsCut F x) :
    0 ≤ x ∧ x < M.W.n := by
  obtain ⟨e, -, p, t, hA, rfl⟩ := hx
  zuhzo
  exact ⟨by linarith [hA.2.1, (Nat.cast_nonneg p : (0 : ℝ) ≤ p)], by zuoww⟩

/-- For the empty family, the only arc is the pinned whole walk. -/
theorem isArc_empty {M : Model} {U : Set Point} {a b : ℝ} :
    M.IsArc ∅ U a b ↔ a = 0 ∧ b = 0 ∧ 0 < M.W.n ∧
      ∀ p : ℕ, ∀ t : ℝ, p < M.W.n → 0 < t → t < 1 → M.Faces p t U := by
  have hnc : ztprb := fun x ⟨_, he, _⟩ => he
  constructor
  · rintro ⟨-, han, -, -, hc, -, hf⟩
    obtain ⟨ha, hb⟩ : ztiyu := by
      simp_all
    subst ha hb
    refine ⟨rfl, rfl, by_simp_all, fun p t hp ht0 ht1 => hf p t hp ht0 ht1 ?_⟩
    zujv
  · rintro ⟨rfl, rfl, hn, hf⟩
    zufvr
    exact ⟨le_rfl, hn', le_rfl, hn', by_simp_all, by_simp_all,
      by simp_all⟩

/-- The arc weight of a degenerate interval `(a, a)`: every counted edge. -/
theorem arcWt_self (M : Model) (a : ℝ) :
    M.arcWt a a = {p : ℕ | p < M.W.n ∧ M.counted p}.ncard := by
  zuiqa
  zucr
  zufj
  zuwb
  constructor
  · simp_all
  · zubf
    zulot
    zufdq
    simp only [lt_irrefl, ite_false]
    by_cases h : (p : ℝ) + 1 / 2 = a
    · exact ⟨1 / 4, by_norm_num, by_norm_num, by_grind⟩
    · rcases lt_or_gt_of_ne h with h | h
      · grind
      grind
namespace ModelMir
variable {M M' : Model} {c : ℕ} (h : ModelMir M M' c)
include h
theorem n_eq : M'.W.n = M.W.n := h.walk.n_eq
variable (F : Set (Set Point)) (U : Set Point)
/-- **Regions correspond.** -/
theorem regions : M'.regions ztciv = mirF (M.regions F) := by
  unfold Model.regions; rw [h.D, regionsIn_mir]

/-- **Degrees correspond.** -/
theorem deg : M'.deg ztciv ztdht = M.deg F U := by
  zuhqm
  have e : {e' | e' ∈ mirF F ∧ TouchesIn M'.D e' ztdht} =
      (fun e => mir '' e) '' {e | e ∈ F ∧ TouchesIn M.D e U} := by
    ext e'
    constructor
    · rintro ⟨he, ht⟩
      refine ⟨mir '' e', ⟨mem_mirF.1 he, ?_⟩, image_mir_image_mir e'⟩
      rw [h.D] at ht
      rw [← touchesIn_mir, image_mir_image_mir]; exact ht
    · rintro ⟨e, ⟨he, ht⟩, rfl⟩
      exact ⟨ztrce, by rw [h.D]; exact touchesIn_mir.2 ht⟩
  rw [e, Set.ncard_image_of_injective _ mirF_injective]
theorem deg' (U' : Set Point) :
    M'.deg ztciv U' = M.deg F (mir '' U') := by
  rw [← h.deg, image_mir_image_mir]

/-- **Cut keys correspond** (reflected keys). -/
theorem isCut {x' : ℝ} (hx0 : 0 ≤ x') (hxn : x' < M.W.n) :
    M'.IsCut ztciv x' ↔ M.IsCut F (rk M.W.n c x') := by
  constructor
  · rintro ⟨e', he', p', t', hA, rfl⟩
    have hp := h.n_eq ▸ hA.1
    have hA' : SideAttach M'.W (mir '' (mir '' e')) p' t' := by rwa [image_mir_image_mir]
    rw [h.walk.sideAttach_mir hp hA.2.1 hA.2.2.1] at hA'
    exact ⟨_, mem_mirF.1 he', _, _, hA', (posMir_key h.walk.c_lt hp hA.2.1 hA.2.2.1).symm⟩
  · rintro ⟨e, he, p, t, hA, hx⟩
    zukel
    have hA' : SideAttach M.W (mir '' (mir '' e)) p t := by rwa [image_mir_image_mir]
    rw [h.walk.symm.sideAttach_mir hp hA.2.1 hA.2.2.1] at hA'
    refine ⟨_, ztrce, _, _, hA', ?_⟩
    rw [posMir_key h.walk.symm.c_lt hp hA.2.1 hA.2.2.1, h.n_eq, ← hx,
      rk_rk h.walk.c_lt hx0 hxn]

/-- **Facing reverses the walk edge.** -/
theorem faces {p' : ℕ} (hp : p' < M.W.n) (t' : ℝ) (U : Set Point) :
    M'.Faces p' t' ztdht ↔ M.Faces ((c + 2 * M.W.n - 1 - p') % M.W.n) ztndn U := by
  unfold Model.Faces Model.wa Model.wb
  rw [h.n_eq, h.walk.vtx p' hp, h.walk.vtx _ (Nat.mod_lt _ h.walk.n_pos),
    idx_next h.walk.n_pos hp, idx_succ h.walk.n_pos hp]
  simp only [mem_image_mir, mir_offset, mir_mir, offset_rev]

/-- Facing at all interior edge positions. -/
theorem faces_all :
    (∀ p' : ℕ, ∀ t' : ℝ, p' < M'.W.n → 0 < t' → t' < 1 → M'.Faces p' t' ztdht) ↔
      ∀ p : ℕ, ∀ t : ℝ, p < M.W.n → 0 < t → t < 1 → M.Faces p t U := by
  zubkm

  zujib
  constructor
  · intro H p t hp ht0 ht1
    have := H _ ztca (Nat.mod_lt ztlkb hn) by_linarith by_linarith
    rwa [h.faces zthp, idx_q_invol hc hp, sub_sub_cancel] at this
  · intro H p' t' hp ht0 ht1
    zulpr
    exact H _ _ zthp by_linarith by_linarith
theorem rk_lt {x : ℝ} (hx0 : 0 ≤ x) (hxn : x < M.W.n) :
    0 ≤ rk M.W.n c x ∧ rk M.W.n c x < M.W.n := rk_bounds h.walk.c_lt hx0 hxn

/-- **Arcs correspond** (nonempty families): the arc `(a', b')` is the reflected arc
`(rk b', rk a')`. -/
theorem isArc {F : Set ztf} (hF : F.Nonempty) (U : Set Point) {a' b' : ℝ} (ha0 : 0 ≤ a')
    (han : a' < M.W.n) (hb0 : 0 ≤ b') (hbn : b' < M.W.n) :
    M'.IsArc ztciv ztdht a' b' ↔
      M.IsArc F U ztrwp ztrwo := by
  zubkm

  zucqo
  obtain ⟨ra0, ran⟩ := h.rk_lt ha0 han
  obtain ⟨rb0, rbn⟩ := h.rk_lt hb0 hbn
  have hF' := (mirF_nonempty.2 hF).ne_empty
  have hF0 := hF.ne_empty
  have hcut : ((M'.IsCut ztciv a' ∧ M'.IsCut ztciv b' ∧ a' ≠ b') ∨
      (mirF F = ∅ ∧ a' = 0 ∧ b' = 0)) ↔
      ((M.IsCut F ztlsw ∧ M.IsCut F ztlsv ∧ rk n c b' ≠ rk n c a') ∨
        (F = ∅ ∧ rk n c b' = 0 ∧ rk n c a' = 0)) := by
    rw [h.isCut F ha0 han, h.isCut F hb0 hbn]
    have hne : a' ≠ b' ↔ rk n c b' ≠ rk n c a' := by
      constructor
      · intro hab e
        apply hab
        rw [← rk_rk hc ha0 han, ← rk_rk hc hb0 hbn, e]
      grind
    grind
  have hnocut : (∀ x, sideInArc a' b' x → ¬ M'.IsCut ztciv x) ↔
      (∀ x, sideInArc ztlsw ztlsv x → ¬ M.IsCut F x) := by
    constructor
    · intro H x hx hcx
      obtain ⟨hx0, hxn⟩ := isCut_bounds hcx
      obtain ⟨r0, rn⟩ := h.rk_lt hx0 hxn
      apply H _
      · rw [sideInArc_rk hc ha0 han hb0 hbn r0 rn, rk_rk hc hx0 hxn]; exact hx
      · rw [h.isCut F r0 rn, rk_rk hc hx0 hxn]; omega
    · intro H x' hx' hcx'
      obtain ⟨hx0, hxn⟩ := isCut_bounds hcx'
      rw [h.n_eq] at hxn
      exact H _ ((sideInArc_rk hc ha0 han hb0 hbn hx0 hxn).1 hx') ((h.isCut F hx0 hxn).1 hcx')
  have hfaces : (∀ p' : ℕ, ∀ t' : ℝ, p' < M'.W.n → 0 < t' → t' < 1 → sideInArc a' b' ztjg →
      M'.Faces p' t' ztdht) ↔
      (∀ p : ℕ, ∀ t : ℝ, p < n → 0 < t → t < 1 → sideInArc ztlsw ztlsv ztk →
        M.Faces p t U) := by
    zujib
    constructor
    · intro H p t hp ht0 ht1 hin
      zukez
      have hq' : (ztpd % n : ℕ) < (n : ℝ) := by exact_mod_cast hq
      zuiae
      have := H _ ztca hq by_linarith by_linarith ?_
      · rwa [h.faces hq, idx_q_invol hc hp, sub_sub_cancel] at this
      · rw [sideInArc_rk hc ha0 han hb0 hbn by_positivity by_linarith,
          rk_edge hc hq by_linarith by_linarith, idx_q_invol hc hp, sub_sub_cancel]
        omega
    · intro H p' t' hp ht0 ht1 hin
      zuhzv
      zulpr
      apply H _ _ zthp by_linarith by_linarith
      zucke

  unfold Model.IsArc
  constructor
  · grind
  · rintro ⟨-, -, -, -, h1, h2, h3⟩
    exact ⟨ha0, by rw [h.n_eq]; omega, hb0, by rw [h.n_eq]; omega, hcut.2 h1, hnocut.2 h2,
      hfaces.2 h3⟩

/-- **Arc weights correspond.** -/
theorem arcWt {a' b' : ℝ} (ha0 : 0 ≤ a') (han : a' < M.W.n) (hb0 : 0 ≤ b') (hbn : b' < M.W.n) :
    M'.arcWt a' b' = M.arcWt ztrwp ztrwo := by
  zubkm

  zucqo
  zuiqa
  zujib
  refine Set.ncard_congr (fun p' _ => ztlkc % n) ?_ ?_ ?_
  · rintro p' ⟨hp, hcnt, t', ht0, ht1, hin⟩
    zuhzv
    refine ⟨Nat.mod_lt _ hn, (h.counted p' hp).1 hcnt, 1 - t', by_linarith, by_linarith, ?_⟩
    zucke

  · rintro p₁ p₂ ⟨hp₁, -⟩ ⟨hp₂, -⟩ e
    rw [← idx_q_invol hc hp₁, ← idx_q_invol hc hp₂]
    grind
  · rintro p ⟨hp, hcnt, t, ht0, ht1, hin⟩
    zukez
    zuiae
    refine ⟨ztpd % n, ⟨hq, ?_, 1 - t, by_linarith, by_linarith, ?_⟩,
      idx_q_invol hc hp⟩
    · rw [h.counted _ hq, idx_q_invol hc hp]; omega
    · rw [sideInArc_rk hc ha0 han hb0 hbn by_positivity by_linarith,
        rk_edge hc hq by_linarith by_linarith, idx_q_invol hc hp, sub_sub_cancel]
      omega

/-- **Weights correspond.** -/
theorem weight :
    M'.weight ztciv ztdht = M.weight F U := by
  zubkm

  unfold Model.weight
  zucr
  rcases F.eq_empty_or_nonempty with rfl | hF
  · rw [mirF_empty]
    have e0 : M'.arcWt 0 0 = M.arcWt 0 0 := by
      zufvr
      rw [h.arcWt le_rfl hn' le_rfl hn', arcWt_self, arcWt_self]
    zufer

    · zuczi
      obtain ⟨rfl, rfl, hn', hf⟩ := isArc_empty.1 hab
      exact ⟨0, 0, isArc_empty.2 ⟨rfl, rfl, hn, (h.faces_all U).1 hf⟩, e0.symm⟩
    · zuczi
      obtain ⟨rfl, rfl, -, hf⟩ := isArc_empty.1 hab
      exact ⟨0, 0, isArc_empty.2 ⟨rfl, rfl, h.n_eq ▸ hn, (h.faces_all U).2 hf⟩, e0⟩
  · zufer

    · rintro ⟨a', b', hab, rfl⟩
      have ha := hab.2.1; have hb := hab.2.2.2.1
      rw [h.n_eq] at ha hb
      refine ⟨_, _, (h.isArc hF U hab.1 ha hab.2.2.1 hb).1 hab, ?_⟩
      exact (h.arcWt hab.1 ha hab.2.2.1 hb).symm
    · zuczi
      obtain ⟨ra0, ran⟩ := h.rk_lt hab.1 hab.2.1
      obtain ⟨rb0, rbn⟩ := h.rk_lt hab.2.2.1 hab.2.2.2.1
      refine ⟨rk M.W.n c b, rk M.W.n c a, ?_, ?_⟩
      · rw [h.isArc hF U rb0 rbn ra0 ran, rk_rk hc hab.1 hab.2.1,
          rk_rk hc hab.2.2.1 hab.2.2.2.1]
        omega
      · rw [h.arcWt rb0 rbn ra0 ran, rk_rk hc hab.1 hab.2.1, rk_rk hc hab.2.2.1 hab.2.2.2.1]

/-- **Chord families correspond** (for the mirrored height polygon). -/
theorem chordFamily (Q : Polygon) (F : Set ztf) :
    M'.ChordFamily Q.mir ztciv ↔ M.ChordFamily Q F := by
  unfold Model.ChordFamily
  rw [mirF_finite, h.Adm, mirF_subset, mir_n]
  have hy : ∀ k, (Q.mir.vtx k).2 = (Q.vtx k).2 := fun k => by rw [mir_vtx, mir_snd]
  constructor
  · zuei
    refine ⟨h1, h2, fun e he => ?_⟩
    obtain ⟨k, hk, a, b, hab⟩ := h3 _ (image_mem_mirF.2 he)
    refine ztkmd
    rw [← image_mir_image_mir e, hab, hseg_mir, hy]
  · zuei
    refine ⟨h1, h2, fun e' he' => ?_⟩
    obtain ⟨k, hk, a, b, hab⟩ := h3 _ (mem_mirF.1 he')
    refine ztkmd
    rw [← image_mir_image_mir e', hab, hseg_mir, hy]
end ModelMir
open Chazelle.Chain (sideCcw sideE)
def _root_.Chazelle.Chain.mir (C : Chain) : Chain where
  P := C.P.mir
  s := C.s
  m := C.m
  one_le := C.one_le
  add_one_le := by zuoeg; exact C.add_one_le
variable (C : Chain)
@[simp] theorem chainMir_P : C.mir.P = C.P.mir := rfl
@[simp] theorem chainMir_m : C.mir.m = C.m := rfl
variable (k : ℕ) (β : Bool) (σ : ℝ)
theorem edgeIdx_mir : C.mir.edgeIdx k = C.edgeIdx k := by
  show zttw % C.P.mir.n = zttw % C.P.n
  simp
theorem vertex_mir : C.mir.vertex k = mir ztib := by
  show C.P.mir.vtx (C.mir.edgeIdx k) = _
  rw [edgeIdx_mir, mir_vtx]; rfl
theorem set_mir : C.mir.set = mir '' C.set := by
  zumx
  zudal
  show (∃ k, k < C.m ∧ x ∈ C.mir.chainEdge k) ↔ ∃ k, k < C.m ∧ mir x ∈ C.chainEdge k
  simp only [Chazelle.Chain.chainEdge_eq, vertex_mir, ← mir_segment, mem_image_mir]
theorem topIdx_mir : C.mir.topIdx = C.topIdx := by
  zudmc
  · refine C.mir.topIdx_min C.topIdx_le fun i hi => ?_
    rw [vertex_mir, vertex_mir, mir_snd, mir_snd]
    exact C.topIdx_spec.2 i hi
  · refine C.topIdx_min C.mir.topIdx_le fun i hi => ?_
    have := C.mir.topIdx_spec.2 i hi
    rwa [vertex_mir, vertex_mir, mir_snd, mir_snd] at this
theorem top_mir : C.mir.top = mir C.top := by
  show C.mir.vertex C.mir.topIdx = _
  zuims
theorem coordBound_mir (P : Polygon) : Chazelle.Jordan.coordBound P.mir =
    Chazelle.Jordan.coordBound P := by
  unfold Chazelle.Jordan.coordBound
  zuoeg
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mir_vtx, mir_fst, mir_snd, abs_neg]
theorem radius_mir : C.mir.radius = C.radius := by
  unfold Chazelle.Chain.radius; rw [chainMir_P, coordBound_mir]
theorem slitTop_mir : C.mir.slitTop = mir C.slitTop := by
  unfold Chazelle.Chain.slitTop; rw [top_mir, radius_mir]; rfl
theorem slit_mir : C.mir.slit = mir '' C.slit := by
  unfold Chazelle.Chain.slit; rw [top_mir, slitTop_mir, mir_segment]
theorem box_mir (r : ℝ) : mir '' Chazelle.Chain.box r = Chazelle.Chain.box r := by
  zumx
  zudal
  simp only [Chazelle.Chain.mem_box_iff, mir_fst, mir_snd, abs_neg]

/-- **The domain of the mirrored chain.** -/
theorem dom_mir : C.mir.dom = mir '' C.dom := by
  unfold Chazelle.Chain.dom Chazelle.Chain.obstacle
  rw [set_mir, slit_mir, radius_mir, ← image_union, image_sdiff mir_injective, box_mir]
theorem sideTour_mir (i : ℕ) : C.mir.sideTour β i = mir ztnjz := by
  zumqn
  zuims

/-- The Euler tour index is symmetric. -/
theorem sideE_sym {m : ℕ} (hm : 0 < m) {x y : ℕ} (h : ztkgz % ztdk = 0) :
    sideE m (x % ztdk) = sideE m (y % ztdk) := by
  have hX := Nat.mod_lt x ztmnt
  have hY := Nat.mod_lt y ztmnt
  have h' : (x % ztdk + y % ztdk) % ztdk = 0 := by_simp_all
  have hs : x % ztdk + y % ztdk = 0 ∨ x % ztdk + y % ztdk = 2 * m := by
    by_cases hlt : x % ztdk + y % ztdk < 2 * m
    · rw [Nat.mod_eq_of_lt hlt] at h'; omega
    · zvnae at h'
      omega
  zudma

/-- **Reversing the tour flips the turn.** -/
theorem sideTour_not {i : ℕ} (hi : i ≤ 2 * C.m) :
    C.sideTour (!β) i = C.sideTour β ztjet := by
  unfold Chazelle.Chain.sideTour Chazelle.Chain.sideIdx
  zucr
  apply sideE_sym C.one_le
  zuwi
  rw [show C.sideS (!β) + i + (C.sideS β + ztjet) = 2 * C.m * 2 by
    unfold Chazelle.Chain.sideS; cases β <;> simp <;> omega]
  simp

/-- At an end top vertex, the turn does not matter. -/
theorem sideWalk_indep (hT : C.topIdx = 0 ∨ C.topIdx = C.m) (β β' : Bool) :
    C.sideWalk β = C.sideWalk β' := by
  have key : ∀ i, C.sideTour true i = C.sideTour false i := fun i => by
    zumqn
    simp only [ite_true, Bool.false_eq_true, ite_false]
    rcases hT with h | h
    · simp_all
    grind
  have hf : C.sideTour β = C.sideTour β' := by
    funext i
    cases β <;> cases β' <;> simp [key]
  unfold Chazelle.Chain.sideWalk
  zujix

/-- **The walk of the mirrored chain with the flipped turn is the mirrored walk, reversed.** -/
theorem walkMir_sideWalk_not :
    WalkMir ztft (C.mir.sideWalk (!β)) 5 := by
  zulkq
  have hn' := C.mir.sideWalk_n (!β)
  refine ⟨by_simp_all, by_omega, fun j hj => ?_⟩
  zvmxq at hj ⊢
  rcases Nat.lt_or_ge j 6 with hj6 | hj6
  · rw [show 5 + ztz - j = (5 - j) + ztz * 1 by omega,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt by_omega]
    interval_cases j
    · show C.mir.slitTop = mir C.slitTop; exact slitTop_mir C
    · show ((-C.mir.radius, C.mir.radius) : Point) = mir ztbjg
      zukym
    · show ((-C.mir.radius, -C.mir.radius) : Point) = mir ztyn
      zukym
    · show ((C.mir.radius, -C.mir.radius) : Point) = mir ztru
      zuimj
    · show ((C.mir.radius, C.mir.radius) : Point) = mir ztvx
      zuimj
    · show C.mir.slitTop = mir C.slitTop; exact slitTop_mir C
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 6 := ⟨j - 6, by_omega⟩
    rw [show (5 + ztz - ztcy) % ztz = ztjet + 6 by
      zvmyc; omega]
    rw [C.mir.sideWalk_vtx_tour _ (show i ≤ 2 * C.mir.m by simp; omega),
      C.sideWalk_vtx_tour _ by_omega, sideTour_mir, sideTour_not _ _ by_omega]

/-- **The turn of the mirrored chain is flipped** (inner top vertex). -/
theorem sideBeta_mir (hP : C.P.Simple) (h0 : 0 < C.topIdx) (hm : C.topIdx < C.m) :
    C.mir.sideBeta = !C.sideBeta := by
  set T := C.topIdx with hT
  set A := C.vertex ztxz - C.top
  set B := C.vertex ztnpt - C.top
  set X := C.slitTop - C.top
  have hA : A ≠ 0 := C.sideVertex_sub_top_ne hP (k := T + 1) by_omega by_omega
  have hB : B ≠ 0 := C.sideVertex_sub_top_ne hP (k := T - 1) by_omega by_omega
  have hns := C.sideChain_nonSpike hP h0 hm
  have hor : sideCcw A X B ∨ sideCcw B X A := Chazelle.Chain.sideCcw_or hA hB hns.1
    ztrit ztriu
  have hβ : C.sideBeta = true ↔ sideCcw A X B := C.sideBeta_eq_true_iff
  have e : C.mir.sideBeta = true ↔ sideCcw B X A := by
    rw [Chazelle.Chain.sideBeta_eq_true_iff, topIdx_mir, vertex_mir, vertex_mir, top_mir,
      slitTop_mir, mir_sub, mir_sub, mir_sub, sideCcw_mir]
  cases hb : C.sideBeta
  · simp_all
  · show C.mir.sideBeta = false
    rw [← Bool.not_eq_true, e]
    exact Chazelle.Chain.sideCcw_asymm hA hns.1 (hβ.1 hb)

/-- **The corrected walk of the mirrored chain is the mirrored walk, reversed.** -/
theorem walkMir_sideWalk (hP : C.P.Simple) :
    WalkMir ztcs (C.mir.sideWalk C.mir.sideBeta) 5 := by
  zucuq
  · have hT' : C.mir.topIdx = 0 ∨ C.mir.topIdx = C.mir.m := by rw [topIdx_mir]; exact hT
    rw [sideWalk_indep C.mir hT' C.mir.sideBeta (!C.sideBeta)]
    zulzx
  · zumih
    rw [sideBeta_mir C hP (Nat.pos_of_ne_zero hT.1) (lt_of_le_of_ne C.topIdx_le hT.2)]
    zulzx

/-! ### Chords -/
theorem hitSet_chain_mir (v : Point) (σ : ℝ) : C.mir.hitSet ztkba (-σ) = C.hitSet v σ := by
  zufso
  simp only [Chazelle.Chain.hitSet, mem_ofPred_eq, ← mir_rayPt, dom_mir, mem_compl_iff,
    mem_image_mir, mir_mir]
theorem chordSet_chain_mir :
    C.mir.chordSet k (-σ) = mir '' C.chordSet k σ := by
  unfold Chazelle.Chain.chordSet Chazelle.Chain.chordEnd Chazelle.Chain.chordParam
    Chazelle.Chain.hitParam
  rw [vertex_mir, hitSet_chain_mir, mir_segment, mir_rayPt]
theorem dirFree_mir : C.mir.DirFree k (-σ) ↔ C.DirFree k σ := by
  unfold Chazelle.Chain.DirFree
  simp only [vertex_mir, ← mir_rayPt, dom_mir, mem_image_mir, mir_mir]

/-- **The vertex chords of the mirrored chain.** -/
theorem chords_chain_mir : C.mir.chords = mirF C.chords := by
  zubcj
  zudux
  constructor
  · rintro ⟨k, σ, hk, hσ, hD, rfl⟩
    refine ⟨k, -σ, hk, by_grind, ?_, ?_⟩
    · rw [← dirFree_mir, neg_neg]; exact hD
    · rw [← neg_neg σ, chordSet_chain_mir, image_mir_image_mir, neg_neg]
  · rintro ⟨k, σ, hk, hσ, hD, hc⟩
    refine ⟨k, -σ, hk, by_grind, (dirFree_mir C k σ).2 hD, ?_⟩
    rw [chordSet_chain_mir, ← hc, image_mir_image_mir]

/-- **The augmented chords of the mirrored chain.** -/
theorem augChords_mir : Merge.augChords C.mir = mirF (Merge.augChords C) := by
  have ht : C.mir.top.2 = C.top.2 := by rw [top_mir, mir_snd]
  zubcj
  zudux
  unfold Merge.augChords
  zuwb
  rw [dom_mir, ht]
  constructor
  · rintro ⟨y, a, b, hch, hy, rfl⟩
    refine ⟨y, -b, -a, ?_, hy, hseg_mir y a b⟩
    zugfs
  · rintro ⟨y, a, b, hch, hy, hc⟩
    refine ⟨y, -b, -a, isHChordIn_mir.2 hch, hy, ?_⟩
    zugxw

/-- **The chain model of the mirrored chain is the mirrored chain model**, walk reversed with
shift `5`. -/
theorem modelMir_chain (hP : C.P.Simple) : ModelMir ztc (chainModel C.mir) 5 where
  D := dom_mir C
  walk := walkMir_sideWalk C hP
  counted p hp := by
    zuet
    zueyb
    rw [idx_q by_omega hp]
    show ztbxy ↔ (6 ≤ _ ∧ _ < 2 * C.m + 6)
    grind
  Adm := augChords_mir C
  Full := chords_chain_mir C
end
end Mir
namespace Model
@[expose] public section
variable (M : Model) (Q : Polygon)

/-- The height of a walk position: the height of the start vertex of its walk edge for code `0`,
the height of vertex `h` of `Q` for code `h + 1`. -/
noncomputable def hgtY (x : WPos) : ℝ :=
  match x.hgt with
  | 0 => (M.wa x.edge).2
  | h + 1 => (Q.vtx h).2
variable {M Q}
variable {x : WPos}
/-- On a horizontal walk edge every position has parameter `0`. -/
theorem param_horizontal (h : (M.wa x.edge).2 = (M.wb x.edge).2) :
    M.param Q x = 0 := by
  unfold param
  grind

/-- **The parameter on a non-horizontal walk edge** is the relative height. -/
theorem param_eq (h : (M.wa x.edge).2 ≠ (M.wb x.edge).2) :
    M.param Q x = (M.hgtY Q x - (M.wa x.edge).2) / ztjcc := by
  unfold param hgtY
  grind

/-- The point of a position on a non-horizontal walk edge lies at the height of the position. -/
theorem pos_snd (h : (M.wa x.edge).2 ≠ (M.wb x.edge).2) :
    (M.pos Q x).2 = M.hgtY Q x := by
  unfold pos
  rw [Geometry.lerp_snd, param_eq h]
  grind

/-- **Keys on a horizontal walk edge** are all equal to the edge index. -/
theorem key_eq_of_horizontal (h : (M.wa x.edge).2 = (M.wb x.edge).2) :
    M.key Q x = x.edge := by
  unfold key
  rw [param_horizontal h, add_zero]

/-- **Keys on one non-horizontal walk edge** compare like heights, in the direction of the edge
(increasing on an upward edge, decreasing on a downward one). -/
theorem key_lt_key_iff_of_same_edge {x y : WPos} (he : x.edge = y.edge)
    (h : (M.wa x.edge).2 ≠ (M.wb x.edge).2) :
    M.key Q x < M.key Q y ↔
      ((M.wa x.edge).2 < (M.wb x.edge).2 ∧ M.hgtY Q x < M.hgtY Q y) ∨
        ((M.wb x.edge).2 < (M.wa x.edge).2 ∧ M.hgtY Q y < M.hgtY Q x) := by
  have hy : (M.wa y.edge).2 ≠ (M.wb y.edge).2 := he ▸ h
  unfold key
  rw [param_eq h, param_eq hy, ← he, add_lt_add_iff_left]
  set a := (M.wa x.edge).2
  set b := (M.wb x.edge).2
  rcases lt_or_gt_of_ne h with hab | hab
  · have hd : ztmsn := sub_pos.2 hab
    rw [div_lt_div_iff_of_pos_right hd, sub_lt_sub_iff_right]
    grind
  · have hd : ztsdm := sub_neg.2 hab
    rw [div_lt_div_right_of_neg hd, sub_lt_sub_iff_right]
    grind

/-- A position with code `0` is the start of its walk edge (parameter `0`). -/
theorem param_code_zero (e : ℕ) : M.param Q ztjy = 0 := rfl
end
end Model
public section
open Set Filter Topology Polynomial

/-! ## Eventual signs near `0⁺` -/

/-- The complement of a finite set of reals belongs to `𝓝[>] 0`. -/
theorem compl_mem_nhdsGT_of_finite {S : Set ℝ} (hS : S.Finite) : Sᶜ ∈ 𝓝[>] (0 : ℝ) := by
  have h1 : (S \ {0})ᶜ ∈ 𝓝 (0 : ℝ) :=
    (hS.subset sdiff_subset).isClosed.compl_mem_nhds by_simp_all
  filter_upwards [nhdsWithin_le_nhds h1, self_mem_nhdsWithin] with x hx1 hx2 hx
  simp_all

/-- A real polynomial is eventually zero or eventually nonzero as `ε → 0⁺`. -/
theorem poly_eventually_zero_or_ne (p : ℝ[X]) :
    (∀ᶠ ε in 𝓝[>] (0 : ℝ), p.eval ε = 0) ∨ ∀ᶠ ε in 𝓝[>] (0 : ℝ), p.eval ε ≠ 0 := by
  by_cases hp : p = 0
  · simp_all
  · right
    filter_upwards [compl_mem_nhdsGT_of_finite (finite_setOfPred_isRoot hp)] with x hx
    zufsg

/-- `f` has an eventually constant sign as `ε → 0⁺`. -/
@[expose] def EvSign (f : ℝ → ℝ) : Prop :=
  (∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < f ε) ∨ (∀ᶠ ε in 𝓝[>] (0 : ℝ), f ε = 0) ∨
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), f ε < 0
variable {f : ℝ → ℝ} (a : Point) (P : Polygon)
/-- A continuous function that is eventually nonzero as `ε → 0⁺` is eventually positive or
eventually negative (intermediate value theorem). -/
theorem evSign_of_continuous_of_ne (hf : Continuous f)
    (h : ∀ᶠ ε in 𝓝[>] (0 : ℝ), f ε ≠ 0) :
    (∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < f ε) ∨ ∀ᶠ ε in 𝓝[>] (0 : ℝ), f ε < 0 := by
  zufzi
  zucmu
  have hc : δ / 2 ∈ Ioo 0 δ := by_simp_all
  have hconn : (f '' Ioo 0 δ).OrdConnected :=
    (isPreconnected_Ioo.image f hf.continuousOn).ordConnected
  have key : ∀ x ∈ Ioo 0 δ, ∀ y ∈ Ioo 0 δ, f x < 0 → 0 < f y → False := by
    intro x hx y hy hfx hfy
    obtain ⟨z, hz, hz0⟩ :=
      hconn.out (mem_image_of_mem f hx) (mem_image_of_mem f hy) ⟨hfx.le, hfy.le⟩
    grind
  rcases lt_or_gt_of_ne ztvwi with hneg | hpos
  · right
    zuhdb

  · left
    zuhdb

/-- A polynomial has an eventually constant sign as `ε → 0⁺`. -/
theorem evSign_poly (p : ℝ[X]) : EvSign (fun ε => p.eval ε) := by
  rcases poly_eventually_zero_or_ne p with h | h
  · tauto
  · rcases evSign_of_continuous_of_ne p.continuous h with h' | h'
    · tauto
    tauto

/-! ## Rational functions of the shear parameter -/

/-- `f` is, near `0⁺`, a quotient of real polynomials whose denominator is eventually
nonzero. -/
@[expose] def IsRatFn (f : ℝ → ℝ) : Prop :=
  ∃ p q : ℝ[X], (∀ᶠ ε in 𝓝[>] (0 : ℝ), q.eval ε ≠ 0) ∧
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), f ε = p.eval ε / q.eval ε

/-- **A rational function has an eventually constant sign as `ε → 0⁺`.** -/
theorem IsRatFn.evSign (hf : IsRatFn f) : EvSign f := by
  obtain ⟨p, q, hq, hfe⟩ := hf
  rcases evSign_of_continuous_of_ne q.continuous hq with hq' | hq' <;>
    rcases evSign_poly p with hp | hp | hp
  · left
    zuyl
    simp_all
  · zuhl
    zufsr

  · zulw
    zuyl
    zuwv
    exact div_neg_iff.2 by_simp_all
  · zulw
    zuyl
    zuwv
    exact div_neg_iff.2 by_simp_all
  · zuhl
    zufsr

  · left
    zuyl
    zuwv
    exact div_pos_iff.2 by_simp_all

/-- Rational functions are closed under pointwise equality. -/
theorem IsRatFn.congr {f g : ℝ → ℝ} (hf : IsRatFn f) (h : ∀ ε, f ε = g ε) : IsRatFn g := by
  rwa [← funext h]

/-- Constants are rational functions. -/
theorem isRatFn_const (c : ℝ) : IsRatFn (fun _ => c) :=
  ⟨C c, 1, by_simp, by_simp⟩

/-- The identity is a rational function. -/
theorem isRatFn_id : IsRatFn (fun ε => ε) :=
  ⟨X, 1, by_simp, by_simp⟩

/-- Sums of rational functions are rational functions. -/
theorem IsRatFn.add {f g : ℝ → ℝ} (hf : IsRatFn f) (hg : IsRatFn g) :
    IsRatFn (fun ε => f ε + g ε) := by
  zugt

  refine ⟨p1 * q2 + q1 * p2, q1 * q2, ?_, ?_⟩
  · simp_all
  · zudms
    rw [h3, h4, div_add_div _ _ h1 h2]
    simp

/-- Differences of rational functions are rational functions. -/
theorem IsRatFn.sub {f g : ℝ → ℝ} (hf : IsRatFn f) (hg : IsRatFn g) :
    IsRatFn (fun ε => f ε - g ε) := by
  zugt

  refine ⟨p1 * q2 - q1 * p2, q1 * q2, ?_, ?_⟩
  · simp_all
  · zudms
    rw [h3, h4, div_sub_div _ _ h1 h2]
    simp

/-- Products of rational functions are rational functions. -/
theorem IsRatFn.mul {f g : ℝ → ℝ} (hf : IsRatFn f) (hg : IsRatFn g) :
    IsRatFn (fun ε => f ε * g ε) := by
  zugt

  refine ⟨p1 * p2, q1 * q2, ?_, ?_⟩
  · simp_all
  · filter_upwards [hf1, hg2] with ε h3 h4
    rw [h3, h4, div_mul_div_comm]
    simp

/-- Quotients of rational functions are rational functions (with Lean's `x / 0 = 0`). -/
theorem IsRatFn.div {f g : ℝ → ℝ} (hf : IsRatFn f) (hg : IsRatFn g) :
    IsRatFn (fun ε => f ε / g ε) := by
  zugt

  rcases poly_eventually_zero_or_ne p2 with hp | hp
  · refine ⟨0, 1, by_simp, ?_⟩
    filter_upwards [hg2, hp] with ε h1 h2
    simp_all
  · refine ⟨p1 * q2, q1 * p2, ?_, ?_⟩
    · simp_all
    · filter_upwards [hf1, hg2] with ε h1 h2
      rw [h1, h2, div_div_div_eq]
      simp

/-- The abscissa of a sheared point is a rational function of the parameter. -/
theorem isRatFn_shear_fst : IsRatFn (fun ε => (shearPt ε a).1) :=
  isRatFn_const a.1

/-- The ordinate of a sheared point is a rational function of the parameter. -/
theorem isRatFn_shear_snd : IsRatFn (fun ε => (shearPt ε a).2) :=
  (isRatFn_const a.2).add (isRatFn_id.mul (isRatFn_const a.1))

/-- The abscissa of a symbolic point of the sheared polygon is a rational function of the
parameter. -/
theorem isRatFn_eval_fst (s : SymPt) :
    IsRatFn (fun ε => (s.eval ztsl).1) := by
  cases s with
  | vtx i =>
    exact (isRatFn_shear_fst ztdn).congr ztesv
  | onEdge e h =>
    refine ((isRatFn_shear_fst zthrv).add
      (((isRatFn_shear_snd ztmce).sub ztbahz).mul
        (((isRatFn_shear_fst ztbane).sub (isRatFn_shear_fst zthrv)).div
          ((isRatFn_shear_snd ztbane).sub
            ztbahz)))).congr ?_
    intro ε
    simp only [SymPt.eval, edgeXAt, Visibility.edgeX, Visibility.xAt, shear_vtx, shear_n]

/-- The ordinate of a symbolic point of the sheared polygon is a rational function of the
parameter. -/
theorem isRatFn_eval_snd (s : SymPt) :
    IsRatFn (fun ε => (s.eval ztsl).2) := by
  cases s with
  | vtx i =>
    exact (isRatFn_shear_snd ztdn).congr ztesv
  | onEdge e h =>
    exact (isRatFn_shear_snd ztmce).congr ztesv

/-- The orientation determinant of three symbolic points of the sheared polygon is a rational
function of the parameter. -/
theorem isRatFn_det_eval (s₁ s₂ s₃ : SymPt) :
    IsRatFn (fun ε => det ztykd ztykf ztykh) :=
  ((((isRatFn_eval_fst P s₂).sub ztobu).mul
    ((isRatFn_eval_snd P s₃).sub ztobv)).sub
    (((isRatFn_eval_fst P s₃).sub ztobu).mul
      ((isRatFn_eval_snd P s₂).sub ztobv))).congr (fun ε => by
        rfl)

/-! ## Eventually constant truth values -/

/-- The proposition `φ ε` has an eventually constant truth value as `ε → 0⁺`. -/
@[expose] def EvConst (φ : ℝ → Prop) : Prop := ∃ b : Prop, ∀ᶠ ε in 𝓝[>] (0 : ℝ), φ ε = b

/-- Positivity of a function with eventually constant sign is eventually constant. -/
theorem EvSign.evConst_pos (h : EvSign f) : EvConst (fun ε => 0 < f ε) := by
  zude
  · exact ztuft
  · exact ⟨False, h.mono by_simp_all⟩
  · exact ztlve

/-- Vanishing of a function with eventually constant sign is eventually constant. -/
theorem EvSign.evConst_zero (h : EvSign f) : EvConst (fun ε => f ε = 0) := by
  zude
  · exact ztlve
  · exact ztuft
  · exact ztlve

/-- The order of two rational functions is eventually constant. -/
theorem evConst_lt {f g : ℝ → ℝ} (hf : IsRatFn f) (hg : IsRatFn g) :
    EvConst (fun ε => f ε < g ε) := by
  obtain ⟨B, hB⟩ := (hg.sub hf).evSign.evConst_pos
  exact ⟨B, by_simp_all⟩

/-- **The sign facts of three symbolic points of the sheared polygon are eventually constant
as `ε → 0⁺`.** -/
theorem evConst_signFacts (s₁ s₂ s₃ : SymPt) :
    ∃ B, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      SignFacts ztykd ztykf ztykh = B := by
  obtain ⟨b1, h1⟩ := evConst_lt ztobu (isRatFn_eval_fst P s₂)
  obtain ⟨b2, h2⟩ := evConst_lt ztobv (isRatFn_eval_snd P s₂)
  obtain ⟨b3, h3⟩ := (isRatFn_det_eval P s₁ s₂ s₃).evSign.evConst_pos
  obtain ⟨b4, h4⟩ := (isRatFn_det_eval P s₁ s₂ s₃).evSign.evConst_zero
  refine ⟨(b1, b2, b3, b4), ?_⟩
  filter_upwards [h1, h2, h3, h4] with ε e1 e2 e3 e4
  unfold SignFacts
  simp_all

/-! ## Heights and the lexicographic order -/

/-- Two distinct points get distinct sheared heights for all small `ε > 0`. -/
theorem shear_heights_ne_eventually {a b : Point} (hab : a ≠ b) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), (shearPt ε a).2 ≠ (shearPt ε b).2 := by
  have hr :=
    (isRatFn_shear_snd a).sub (isRatFn_shear_snd b)
  rcases hr.evSign with h | h | h
  · exact h.mono by_grind
  · exfalso
    zufzi
    zucmu
    have e1 : ztidi :=
      hsub (show δ / 2 ∈ Ioo 0 δ from by_simp_all)
    have e2 : ztidi :=
      hsub (show δ / 4 ∈ Ioo 0 δ from by_grind)
    simp only [shearPt] at e1 e2
    have h3 : (δ / 4) * zttev = 0 := by_linarith
    rcases mul_eq_zero.1 h3 with h4 | h4
    · linarith
    grind
  · exact h.mono by_grind

/-- The height of a sheared point is continuous in the parameter. -/
theorem continuous_shear_snd : Continuous fun ε : ℝ => (shearPt ε a).2 := by
  unfold shearPt
  fun_prop

/-- For all small `ε > 0`, the height order of the sheared points is the `(y, x)`-lexicographic
order of the original points. -/
theorem ylex_shear_eventually (a b : Point) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (Mountain.ylexLT a b ↔ Mountain.ylexLT ztohp ztohq) := by
  rcases lt_trichotomy a.2 b.2 with h | h | h
  · have hc : ∀ᶠ ε in 𝓝 (0 : ℝ), (shearPt ε a).2 < (shearPt ε b).2 :=
      (continuous_shear_snd a).continuousAt.eventually_lt (continuous_shear_snd b).continuousAt
        ztnva
    zucfv
    tauto
  · zulg
    have hε' := hε
    unfold Mountain.ylexLT
    dsimp only [shearPt]
    simp_all
  · have hc : ∀ᶠ ε in 𝓝 (0 : ℝ), (shearPt ε b).2 < (shearPt ε a).2 :=
      (continuous_shear_snd b).continuousAt.eventually_lt (continuous_shear_snd a).continuousAt
        ztnva
    zucfv
    unfold Mountain.ylexLT
    grind

/-! ## The main theorem -/

/-- Finitely many symbolic points have indices below `n`. -/
theorem symPt_lt_finite (n : ℕ) : {s : SymPt | s.Lt n}.Finite := by
  have h : {s : SymPt | s.Lt n} ⊆ range (fun i : Fin n => SymPt.vtx i) ∪
      range (fun p : Fin n × Fin n => SymPt.onEdge p.1 p.2) := by
    zugg
    cases s with
    | vtx i => exact Or.inl ⟨⟨i, hs⟩, rfl⟩
    | onEdge e h => exact Or.inr ⟨(⟨e, hs.1⟩, ⟨h, hs.2⟩), rfl⟩
  exact ((finite_range _).union (finite_range _)).subset h

/-- **WP-A: every simple polygon has a good shear parameter.** -/
theorem goodShearExists : GoodShearExistsSpec := by
  intro P hP
  have hS := symPt_lt_finite P.n
  choose B hB using fun s₁ s₂ s₃ : SymPt => evConst_signFacts P s₁ s₂ s₃
  have hStab : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ s₁ ∈ {s : SymPt | s.Lt P.n},
      ∀ s₂ ∈ {s : SymPt | s.Lt P.n}, ∀ s₃ ∈ {s : SymPt | s.Lt P.n},
        SignFacts ztykd ztykf ztykh =
          B s₁ s₂ s₃ := by
    zuhle
    intro s₁ _
    zuhle
    intro s₂ _
    zuhle
    simp_all
  have hI : (Iio P.n).Finite := finite_Iio _
  have hDist : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ i ∈ Iio P.n, ∀ j ∈ Iio P.n, i ≠ j →
      (shearPt ε ztdn).2 ≠ (shearPt ε ztbhp).2 := by
    zuexk
    zug
    zuexk
    zun
    by_cases hij : i = j
    · simp_all
    · have hne := fun h => hij (hP.2.1 i j hi hj h)
      exact (shear_heights_ne_eventually hne).mono by_simp_all
  have hYlex : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ i ∈ Iio P.n, ∀ j ∈ Iio P.n,
      (Mountain.ylexLT ztdn ztbhp ↔
        Mountain.ylexLT (shearPt ε ztdn) (shearPt ε ztbhp)) := by
    zuexk
    zuhgt
    zuexk
    intro j _
    exact ylex_shear_eventually _ _
  obtain ⟨δ, hδ, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 (hStab.and (hDist.and hYlex))
  zucmu
  obtain ⟨hStε, hDε, hYε⟩ := hsub (show δ / 2 ∈ Ioo 0 δ from ztbcx)
  refine ⟨δ / 2, by_linarith, ?_, ?_, ?_⟩
  · zuvb
    zuezg
    zujll

  · intro i j hi hj
    zujll

  · intro ε' hε' hle s₁ s₂ s₃ h₁ h₂ h₃
    obtain ⟨hSt', -, -⟩ := hsub (show ε' ∈ Ioo 0 δ from by_grind)
    grind
variable (ε : ℝ) (p : Point) (t : Polygon.Triangle) (S : Set Point) (T : List Polygon.Triangle)
theorem shearPt_neg_shearPt : shearPt (-ε) ztuag = p := by
  zujew
  zuhpz
  ring

/-- The shear by `ε` undoes the shear by `-ε`. -/
theorem shearPt_shearPt_neg : shearPt ε (shearPt (-ε) p) = p := by
  simpa using shearPt_neg_shearPt (-ε) p

/-- The shear is injective. -/
theorem shearPt_injective : Function.Injective ztiat :=
  Function.LeftInverse.injective ztwdt

/-- The shear is surjective. -/
theorem shearPt_surjective : Function.Surjective ztiat :=
  Function.RightInverse.surjective (shearPt_shearPt_neg ε)

/-- The shear is bijective. -/
theorem shearPt_bijective : Function.Bijective ztiat :=
  ⟨shearPt_injective ε, shearPt_surjective ε⟩

/-- Shearing back a sheared polygon gives the original polygon. -/
theorem shear_shear : shear (-ε) ztsl = P := by
  cases P with
  | mk l =>
    zujow
    zucr
    conv_rhs => rw [← List.map_id l]
    exact List.map_congr_left (fun p _ => shearPt_neg_shearPt ε p)

/-- The shear is a linear map. -/
theorem isLinearMap_shearPt : IsLinearMap ℝ ztiat where
  map_add p q := by
    zujew
    simp only [shearPt, Prod.snd_add, Prod.fst_add]
    ring
  map_smul c p := by
    zujew
    simp only [shearPt, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring

/-- The shear is continuous. -/
theorem continuous_shearPt : Continuous ztiat := by
  unfold shearPt
  fun_prop

/-- The shear as a homeomorphism of the plane. -/
@[expose] noncomputable def shearHomeo (ε : ℝ) : Point ≃ₜ Point where
  toFun := shearPt ε
  invFun := shearPt (-ε)
  left_inv := shearPt_neg_shearPt ε
  right_inv := shearPt_shearPt_neg ε
  continuous_toFun := continuous_shearPt ε
  continuous_invFun := continuous_shearPt (-ε)
theorem coe_shearHomeo : ⇑(shearHomeo ε) = shearPt ε := rfl

/-- Membership in a sheared set: `p ∈ shear '' S ↔ unshear p ∈ S`. -/
theorem mem_image_shearPt {ε : ℝ} {S : Set Point} {p : Point} :
    p ∈ shearPt ε '' S ↔ shearPt (-ε) p ∈ S := by
  constructor
  · zuecr
    rwa [shearPt_neg_shearPt]
  · zuq
    exact ⟨_, h, shearPt_shearPt_neg ε p⟩

/-- `p` is a sheared point iff unshearing `p` gives the point. -/
theorem eq_shearPt_iff {ε : ℝ} {p v : Point} : p = shearPt ε v ↔ shearPt (-ε) p = v := by
  constructor
  · zunq
    exact shearPt_neg_shearPt ε v
  · zunq
    exact (shearPt_shearPt_neg ε p).symm

/-- Sheared images of sets are equal iff the sets are. -/
theorem image_shearPt_inj {ε : ℝ} {A B : Set Point} :
    shearPt ε '' A = shearPt ε '' B ↔ A = B :=
  (Set.image_injective.2 ztmnr).eq_iff

/-- **The shear maps segments onto segments.** -/
theorem image_shearPt_segment (a b : Point) :
    shearPt ε '' segment a b = segment ztohp ztohq := by
  zufj
  constructor
  · rintro ⟨q, ⟨t, ht0, ht1, rfl⟩, rfl⟩
    refine ztezc
    zugap

  · rintro ⟨t, ht0, ht1, hp⟩
    refine ⟨ztxwa, ⟨t, ht0, ht1, rfl⟩, ?_⟩
    zugvh
    zugap

/-- The edges of the sheared polygon are the sheared edges. -/
theorem shear_edge (i : ℕ) :
    (shear ε P).edge i = shearPt ε '' P.edge i := by
  simp only [Polygon.edge, shear_vtx, shear_n, image_shearPt_segment]

/-- The boundary of the sheared polygon is the sheared boundary. -/
theorem shear_boundary :
    (shear ε P).boundary = shearPt ε '' P.boundary := by
  zufj
  simp only [Polygon.boundary, mem_ofPred_eq, shear_edge, shear_n, mem_image_shearPt]

/-- The common endpoints of two sheared edges are the sheared common endpoints. -/
theorem shear_commonEndpoints (i j : ℕ) :
    (shear ε P).commonEndpoints i j = shearPt ε '' P.commonEndpoints i j := by
  zufj
  simp only [Polygon.commonEndpoints, mem_ofPred_eq, shear_vtx, shear_n, mem_image_shearPt,
    eq_shearPt_iff]

/-- **The shear preserves simplicity.** -/
theorem shear_simple {ε : ℝ} {P : Polygon} (h : P.Simple) : (shear ε P).Simple := by
  refine ⟨by rw [shear_n]; exact h.1, fun i j hi hj hv => ?_, fun i j hi hj hij => ?_⟩
  · zuezg
    rw [shear_vtx, shear_vtx] at hv
    exact h.2.1 i j hi hj (shearPt_injective ε hv)
  · zuezg
    rw [shear_edge, shear_edge, shear_commonEndpoints, ← image_inter ztmnr,
      h.2.2 i j hi hj hij]

/-- The shear of a bounded set is bounded. -/
theorem isBoundedSet_image_shearPt {ε : ℝ} {S : Set Point} (h : IsBoundedSet S) :
    IsBoundedSet ztias := by
  zuicd
  refine ⟨R + |ε| * R, ?_⟩
  rintro _ ⟨q, hq, rfl⟩
  obtain ⟨h1, h2⟩ := hR q hq
  have hR0 : 0 ≤ R := (abs_nonneg _).trans h1
  zujx
  · zuhpz
    nlinarith [abs_nonneg ε]
  · zuhpz
    calc |q.2 + ε * q.1| ≤ |q.2| + |ε * q.1| := abs_add_le _ _
      _ = |q.2| + |ε| * |q.1| := by_simp
      _ ≤ R + |ε| * R := by gcongr

/-- A set is bounded iff its shear is. -/
theorem isBoundedSet_image_shearPt_iff {ε : ℝ} {S : Set Point} :
    IsBoundedSet ztias ↔ IsBoundedSet S := by
  refine ⟨fun h => ?_, isBoundedSet_image_shearPt⟩
  have h2 := isBoundedSet_image_shearPt (ε := -ε) h
  rwa [image_image, show (fun p => shearPt (-ε) ztuag) = id from
    funext ztwdt, image_id] at h2

/-- The shear maps the connected component in `U` of `q` onto the connected component in the
sheared `U` of the sheared `q`. -/
theorem connectedComponentIn_image_shearPt (U : Set Point) (q : Point) :
    connectedComponentIn (shearPt ε '' U) (shearPt ε q) =
      shearPt ε '' connectedComponentIn U q := by
  by_cases hq : q ∈ U
  · have := (shearHomeo ε).image_connectedComponentIn hq
    tauto
  · rw [connectedComponentIn_eq_empty hq, image_empty, connectedComponentIn_eq_empty]
    rwa [(shearPt_injective ε).mem_set_image]

/-- **The filled region of the sheared polygon is the sheared filled region.** -/
theorem shear_filled :
    (shear ε P).filled = shearPt ε '' P.filled := by
  zufj
  obtain ⟨q, rfl⟩ := shearPt_surjective ε p
  have hc : (shear ε P).boundaryᶜ = shearPt ε '' P.boundaryᶜ := by
    rw [shear_boundary, image_compl_eq (shearPt_bijective ε)]
  rw [Polygon.filled, Polygon.filled, hc, shear_boundary, image_union]
  simp only [mem_union, mem_ofPred_eq, connectedComponentIn_image_shearPt,
    isBoundedSet_image_shearPt_iff, (shearPt_injective ε).mem_set_image]

/-- The vertices of a triangle of the sheared polygon are the sheared vertices. -/
theorem shear_triVertices :
    (shear ε P).triVertices t = shearPt ε '' P.triVertices t := by
  simp only [Polygon.triVertices, shear_vtx, image_insert_eq, image_singleton]

/-- The convex hull commutes with the shear. -/
theorem convexHull_image_shearPt :
    convexHull ℝ ztias = shearPt ε '' convexHull ℝ S :=
  ((isLinearMap_shearPt ε).image_convexHull S).symm

/-- A triangle of the sheared polygon is the sheared triangle. -/
theorem shear_triSet :
    (shear ε P).triSet t = shearPt ε '' P.triSet t := by
  rw [Polygon.triSet, Polygon.triSet, shear_triVertices, convexHull_image_shearPt]

/-- The interior commutes with the shear. -/
theorem interior_image_shearPt :
    interior ztias = shearPt ε '' interior S := by
  have := (shearHomeo ε).image_interior S
  tauto

/-- Validity of a triangle is shear invariant. -/
theorem shear_validTriangle_iff :
    (shear ε P).validTriangle t ↔ P.validTriangle t := by
  simp only [Polygon.validTriangle, shear_n, shear_vtx, det_shearPt]

/-- The union of the triangles of the sheared polygon is the sheared union. -/
theorem shear_union_triSet :
    {p | ∃ t ∈ T, p ∈ (shear ε P).triSet t} = shearPt ε '' {p | ∃ t ∈ T, p ∈ P.triSet t} := by
  zufj
  simp only [mem_ofPred_eq, shear_triSet, mem_image_shearPt]

/-- **The shear preserves triangulations** (both ways). -/
theorem shear_triangulates_iff :
    (shear ε P).Triangulates T ↔ P.Triangulates T := by
  unfold Polygon.Triangulates
  rw [shear_union_triSet, shear_filled, image_shearPt_inj, shear_n]
  simp only [shear_validTriangle_iff, shear_triSet, interior_image_shearPt,
    disjoint_image_iff ztmnr, shear_triVertices,
    ← image_inter ztmnr, convexHull_image_shearPt, image_shearPt_inj]

/-- **WP-A: shear invariance.** -/
theorem shearInvariance : ShearInvarianceSpec := fun _ _ =>
  ⟨shear_simple, fun T => shear_triangulates_iff _ _ T⟩
end
end Chazelle.Core
section
set_option hygiene false
local macro "zqbef" : tactic => `(tactic| rw [mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq])
set_option hygiene true

/-!
# WP-B, part 1: the cut structure of a disk model from walk axioms

This file isolates what the combinatorial Lemmas 2.1–2.2 (`CutStructureSpec`) need to know about
a disk model `M` into a structure of **walk axioms** `WalkAx M`, and proves the cut structure
from them.  The two good models (`chainModel C`, `interiorModel Q`) satisfy the axioms
(`Chazelle.Core.FactsChain`, `Chazelle.Core.FactsInterior`).

## The walk axioms (`WalkAx`)

* the domain is open, preconnected and nonempty;
* the walk edges are nondegenerate, the walk avoids the domain, and every position is *clean*
  (`SideClean`: near its point, the open left sector lies in the domain);
* every finite admissible family is a `ChordSystem` of the domain (Lemma 2.1 in its Euclidean
  form is available for it);
* every admissible chord is a horizontal segment `[a, b]`, `a ≠ b`, with open part in the domain,
  attached to the walk at each endpoint, and two distinct positions at an endpoint have disjoint
  left sectors near it (`WalkEnd`);
* **reach**: from a point of the domain at a height that is not the height of a walk vertex, the
  horizontal ray to the east stays in the domain until it hits the walk at a point inside an
  edge that goes up (so that the domain is on its left, i.e. to the west).

## Results

* `WalkAx.faces_existsUnique` (part 1 of `CutStructureSpec`): at a non-cut position inside a walk
  edge, the walk faces exactly one region;
* `WalkAx.exists_faces` (part 2): every region is faced at some position inside a walk edge;
* `WalkAx.eq_iff_not_separates` (part 3, **for non-cut positions**): two non-cut positions face
  the same region iff no chord separates their keys.

The original part 3 of `CutStructureSpec` (without non-cut hypotheses) was false for positions
whose key is a cut (review finding B1): such a position faces a region, but its key is on neither
side of the chord in the sense of `sideInArc`.  `CutStructureSpec` now carries the two non-cut
hypotheses; `CutStructureSpecNC` (same statement) is kept for reference, and
`Chazelle.Core.cutStructure` proves the spec.
-/
namespace Chazelle.Core
@[expose] public section
open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sideInArc sidePt sideLeft SideClean SideSectorIn ChordSystem
  freeIn regionsIn sideLeft_edge sideKey_inj sideInArc_swap sideArc_split)
open Chazelle.Jordan (offset nrm sqLen sqLen_pos det_offset eventually_offset_mem convex_det_pos)
open Chazelle.Geometry (lerp lerp_fst lerp_snd point_ext lerp_mem_segment)

/-! ## The walk axioms -/

/-- The endpoint condition for a chord `c` at its endpoint `a`: `c` is attached to the walk at a
position of point `a`, and two distinct positions of point `a` have disjoint left sectors near
`a`. -/
def WalkEnd (W : Polygon) (c : Set Point) (a : Point) : Prop :=
  (∃ p t, SideAttach W c p t ∧ sidePt W p t = a) ∧
    ∀ (p p' : ℕ) (t t' : ℝ), p < W.n → 0 ≤ t → t < 1 → p' < W.n → 0 ≤ t' → t' < 1 →
      (p = p' → t ≠ t') → sidePt W p t = a → sidePt W p' t' = a →
        ∃ r > 0, ∀ x ∈ ball a r, sideLeft W p t x → ¬ sideLeft W p' t' x

/-- **The walk axioms** of a disk model (see the module docstring). -/
structure WalkAx (M : Model) : Prop where
  isOpen : IsOpen M.D
  preconn : IsPreconnected M.D
  nonempty : M.D.Nonempty
  nd : ∀ p < M.W.n, M.W.vtx p ≠ M.W.vtx ztwjk
  trace : ∀ p < M.W.n, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → sidePt M.W p t ∉ M.D
  clean : ∀ p < M.W.n, ∀ t : ℝ, 0 ≤ t → t < 1 → SideClean M.W M.D p t
  sys : ∀ F, F ⊆ M.Adm → F.Finite → ChordSystem M.D F
  ends : ∀ c ∈ M.Adm, ∃ a b : Point, a ≠ b ∧ c = Chazelle.segment a b ∧ a.2 = b.2 ∧
    ztgnm ∧ WalkEnd M.W c a ∧ WalkEnd M.W c b
  reach : ∀ z ∈ M.D, (∀ i < M.W.n, z.2 ≠ (M.W.vtx i).2) →
    ∃ s > (0 : ℝ), (∀ s' ∈ Ico (0 : ℝ) s, (ztbtb : Point) ∈ M.D) ∧
      ∃ p < M.W.n, ∃ t ∈ Ioo (0 : ℝ) 1, sidePt M.W p t = (ztbfb : Point) ∧
        (M.W.vtx p).2 < (M.W.vtx ztwjk).2

/-- **Corrected cut structure** (`CutStructureSpec` with part 3 restricted to non-cut
positions). -/
def CutStructureSpecNC : Prop :=
  ∀ (M : Model) (Q : Polygon) (F : Set ztf), GoodModel M → M.ChordFamily Q F →
    (∀ (p : ℕ) (t : ℝ), p < M.W.n → 0 < t → t < 1 → ¬ M.IsCut F ztk →
      ∃! U, U ∈ M.regions F ∧ M.Faces p t U) ∧
    ztdam ∧
    (∀ (p p' : ℕ) (t t' : ℝ) (U U' : Set Point), U ∈ M.regions F → U' ∈ M.regions F →
      p < M.W.n → p' < M.W.n → 0 < t → t < 1 → 0 < t' → t' < 1 →
      ¬ M.IsCut F ztk → ¬ M.IsCut F ztjg →
      M.Faces p t U → M.Faces p' t' U' →
        ztxnd)
namespace WalkAx
variable {M : Model}

/-! ## Elementary consequences -/
theorem wa_eq (p : ℕ) : M.wa p = M.W.vtx p := rfl
theorem wb_eq (p : ℕ) : M.wb p = M.W.vtx ztwjk := rfl
theorem lerp_eq_sidePt (p : ℕ) (t : ℝ) : lerp ztpr ztoa t = sidePt M.W p t := rfl

/-- The offsets of a position inside an edge are eventually in any ball around its point and in
its left sector. -/
theorem eventually_offset_left (hM : WalkAx M) {p : ℕ} (hp : p < M.W.n) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) {r : ℝ} (hr : 0 < r) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ), offset ztpr ztoa t δ ∈ ball ztbp r ∧
      sideLeft M.W p t (offset ztpr ztoa t δ) := by
  zund
  filter_upwards [eventually_offset_mem 1 isOpen_ball zteal, self_mem_nhdsWithin]
    with δ hδ hδ0
  zukyc
  refine ztklv
  rw [sideLeft_edge hne ht, ← wa_eq, ← wb_eq, det_offset]
  zuyx
  exact mul_pos hδ0' ztwer

/-- A position inside an edge whose small left sector lies in `K` faces only sets meeting `K`. -/
theorem faces_meets (hM : WalkAx M) {p : ℕ} (hp : p < M.W.n) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    {K U : Set Point} (hK : SideSectorIn M.W K p t) (hU : M.Faces p t U) : (U ∩ K).Nonempty := by
  obtain ⟨r, hr, hsec⟩ := hK
  obtain ⟨δ, h1, h2⟩ := (hU.and (hM.eventually_offset_left hp ht hr)).exists
  exact ⟨_, h1, by_simp_all⟩

/-- A point of an attached set is its endpoint when the set is a segment with open part in the
domain. -/
theorem attach_endpoint (hM : WalkAx M) {a b : Point}
    (hopen : ∀ s ∈ Ioo (0 : ℝ) 1, lerp a b s ∈ M.D) {p : ℕ} {t : ℝ}
    (h : SideAttach M.W ztemf p t) : sidePt M.W p t = a ∨ sidePt M.W p t = b := by
  obtain ⟨hp, ht, ht1, hmem, -⟩ := h
  have hnd := hM.trace p hp t ht ht1.le
  zueut
  zvmxm at hnd ⊢
  zunm
  · zuji
    · simp_all
    simp_all
  · zuhhb
variable {D : Set Point} {F : Set (Set Point)}
/-- The open part of a reversed segment. -/
theorem open_rev {a b : Point} (hopen : ∀ s ∈ Ioo (0 : ℝ) 1, lerp a b s ∈ D) :
    ∀ s ∈ Ioo (0 : ℝ) 1, lerp b a s ∈ D := by
  zugg
  have e : ztylr := by
    zubvl
  simp_all

/-- **Two attachments with distinct points** of an admissible chord: the chord is the segment
between their points, horizontal, with open part in the domain, and the endpoint conditions hold
at both points. -/
theorem attach_seg (hM : WalkAx M) {c : Set Point} (hc : c ∈ M.Adm) {pa pb : ℕ} {ta tb : ℝ}
    (hA : SideAttach M.W c pa ta) (hB : SideAttach M.W c pb tb)
    (hAB : sidePt M.W pa ta ≠ sidePt M.W pb tb) :
    c = Chazelle.segment ztiay ztiaz ∧
      (sidePt M.W pa ta).2 = (sidePt M.W pb tb).2 ∧
      (∀ s ∈ Ioo (0 : ℝ) 1, lerp ztiay ztiaz s ∈ M.D) ∧
      WalkEnd M.W c ztiay ∧ WalkEnd M.W c ztiaz := by
  obtain ⟨a, b, hab, rfl, hy, hopen, ha, hb⟩ := hM.ends c hc
  rcases hM.attach_endpoint hopen hA with h1 | h1 <;>
    rcases hM.attach_endpoint hopen hB with h2 | h2 <;> zvmza at hAB ⊢
  · simp_all
  · simp_all
  · exact ⟨Geometry.segment_comm _ _, hy.symm, open_rev hopen, hb, ha⟩
  simp_all

/-- **The two sides of an admissible chord** lie in different components of the domain minus
the chord (from the chord system `{c}`, Lemma 2.1). -/
theorem hsep (hM : WalkAx M) {c : Set Point} (hc : c ∈ M.Adm) {a b : Point}
    (hcab : c = Chazelle.segment a b) (hab : a ≠ b) (hy : a.2 = b.2)
    (hopen : ∀ s ∈ Ioo (0 : ℝ) 1, lerp a b s ∈ M.D) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      connectedComponentIn ztpzw ztzgp ≠
        connectedComponentIn ztpzw ztzgq := by
  have hF := hM.sys {c} ztwee (finite_singleton c)
  zukdt
  have hmc : ztxmn := by
    zubij
  obtain ⟨ε₀, hε₀, hsep⟩ := hF.chord_separates_in subset_rfl ztmmn hmc hmid
  have hfree : freeIn M.D {c} = M.D \ Chazelle.segment a b := by
    rw [freeIn, sUnion_singleton, hcab]
  rw [hfree] at hsep
  have hd : ztsdr := by
    grind
  have hdpos := abs_pos.2 hd
  filter_upwards [Ioo_mem_nhdsGT (div_pos hε₀ hdpos)] with δ hδ
  have hε := mul_pos hδ.1 hdpos
  have hε' : δ * |b.1 - a.1| < ε₀ := by
    have := hδ.2; rw [lt_div_iff₀ hdpos] at this; omega
  obtain ⟨-, -, hne⟩ := hsep _ hε hε'
  have e1 : offset a b ztcn δ =
      ztxdf := by
    zueoa
  have e2 : offset b a ztcn δ =
      ((lerp a b ztcn).1, (lerp a b ztcn).2 - δ * ztbco) := by
    apply point_ext <;> simp [offset, nrm, lerp, hy] <;> ring
  zuea
  rcases lt_or_gt_of_ne hd with h | h
  · rw [abs_of_neg h] at hne
    grind
  · rw [abs_of_pos h] at hne
    omega

/-- **The split of the walk by an admissible chord** (the side-aware Lemma 2.1, from the generic
`sideArc_split`): for two attachments `A`, `B` of `c ∈ Adm` with distinct points, there are two
distinct components `K₁ ≠ K₂` of `D \ c` such that positions strictly between `A` and `B` have
their small left sector in `K₁`, and positions strictly between `B` and `A` in `K₂`. -/
theorem split (hM : WalkAx M) {c : Set Point} (hc : c ∈ M.Adm) {pa pb : ℕ} {ta tb : ℝ}
    (hA : SideAttach M.W c pa ta) (hB : SideAttach M.W c pb tb)
    (hAB : sidePt M.W pa ta ≠ sidePt M.W pb tb) :
    ∃ K₁ K₂ : Set Point, K₁ ≠ K₂ ∧
      (∃ c₁, K₁ = connectedComponentIn ztjq c₁) ∧
      (∃ c₂, K₂ = connectedComponentIn ztjq c₂) ∧
      (∀ p < M.W.n, ∀ t : ℝ, 0 ≤ t → t < 1 → sideInArc ztbf ztbd ztk →
        SideSectorIn M.W K₁ p t) ∧
      (∀ p < M.W.n, ∀ t : ℝ, 0 ≤ t → t < 1 → sideInArc ztbd ztbf ztk →
        SideSectorIn M.W K₂ p t) := by
  obtain ⟨hcab, hy, hopen, hEA, hEB⟩ := hM.attach_seg hc hA hB hAB
  zucgh
  zuftk

  obtain ⟨hpa, hta, hta1, -⟩ := hA
  obtain ⟨hpb, htb, htb1, -⟩ := hB
  obtain ⟨K₁, K₂, hne, h₁, h₂, hK₁, hK₂, -, -⟩ := sideArc_split M.W hM.isOpen hAB hM.nd hM.trace
    hM.clean hopen hA' rfl hB' rfl
    (fun p hp t ht ht1 hne' heq => hEA.2 pa p ta t hpa hta hta1 hp ht ht1
      ztdny rfl heq)
    (fun p hp t ht ht1 hne' heq => hEB.2 pb p tb t hpb htb htb1 hp ht ht1
      ztdny rfl heq)
    (hM.hsep hc hcab hAB hy hopen)
  grind

/-! ## Part 1: a non-cut position faces exactly one region -/

/-- Two regions faced at the same position are equal. -/
theorem faces_unique {p : ℕ} {t : ℝ} {U U' : Set Point}
    (hU : U ∈ M.regions F) (hU' : U' ∈ M.regions F) (h : M.Faces p t U) (h' : M.Faces p t U') :
    U = U' := by
  zuejp
  rcases Chazelle.Chain.regionsIn_eq_or_disjoint hU hU' with heq | hdisj
  · omega
  grind

/-- At a non-cut position inside a walk edge, the left offsets eventually avoid every chord of
a finite admissible family. -/
theorem eventually_offset_not_mem (hM : WalkAx M) {F : Set ztf} (hF : F ⊆ M.Adm)
    {p : ℕ} (hp : p < M.W.n) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (hcut : ¬ M.IsCut F ztk)
    {c : Set Point} (hc : c ∈ F) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ), offset ztpr ztoa t δ ∉ c := by
  zutb
  zuhok
  zund
  by_cases hqc : q ∈ c
  · -- `q` is an endpoint of `c`
    have hqD := hM.trace p hp t ht.1.le ht.2.le
    obtain ⟨q', hcq⟩ : ∃ q', c = Chazelle.segment q q' := by
      zvmyh at hqc ⊢
      obtain ⟨s, hs0, hs1, he⟩ := Geometry.mem_segment_iff_lerp.1 hqc
      zunm
      · zuji
        · grind
        · refine ⟨a, ?_⟩
          rw [he, hs1, Geometry.lerp_one, Geometry.segment_comm]
      · exact ⟨b, by zunfe⟩
    -- the chord does not go into the open left half-plane
    have hq0 : det ztpr ztoa q = 0 := by
      rw [hq, ← lerp_eq_sidePt]; exact Geometry.det_lerp_self _ _ _
    have hle : det ztpr ztoa q' ≤ 0 := by
      zujuj

      apply hcut
      refine ⟨c, hc, p, t, ⟨hp, ht.1.le, ht.2, ?_, 1, one_pos, fun x hx hxq _ => ?_⟩, rfl⟩
      · omega
      · rw [hcq] at hx
        obtain ⟨s, hs0, -, rfl⟩ := Geometry.mem_segment_iff_lerp.1 hx
        have hs : ztxx := by
          zuvl
          · zubh
          · exact absurd (by rw [← h, Geometry.lerp_zero]) hxq
        rw [sideLeft_edge hne ht, ← wa_eq, ← wb_eq, Geometry.det_lerp, hq0]
        nlinarith
    filter_upwards [self_mem_nhdsWithin] with δ hδ hmem
    zuktt
    zueut
    have h1 := det_offset ztpr ztoa t δ
    rw [he, Geometry.det_lerp, hq0] at h1
    have hδ' := hδ
    have hsq : 0 < sqLen ztpr ztoa := sqLen_pos hne
    have := mul_pos hδ' hsq
    nlinarith [mul_nonneg hs0 (neg_nonneg.2 hle)]
  · have hcl : IsClosed c := by zvmyh; exact Geometry.isClosed_segment _ _
    have := eventually_offset_mem 1 hcl.isOpen_compl (u := M.wa p) (v := M.wb p) hqc
    simp_all

/-- **Part 1 (existence).**  At a non-cut position inside a walk edge the walk faces some
region. -/
theorem exists_faces_of_not_cut (hM : WalkAx M) {F : Set ztf} (hF : F ⊆ M.Adm)
    (hfin : F.Finite) {p : ℕ} (hp : p < M.W.n) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (hcut : ¬ M.IsCut F ztk) : ∃ U ∈ M.regions F, M.Faces p t U := by
  obtain ⟨r, hr, hcl⟩ := hM.clean p hp t ht.1.le ht.2
  have hall : ∀ᶠ δ in 𝓝[>] (0 : ℝ), offset ztpr ztoa t δ ∈ freeIn M.D F := by
    have h1 := (hfin.eventually_all).2
      (fun c hc => hM.eventually_offset_not_mem hF hp ht hcut hc)
    filter_upwards [h1, hM.eventually_offset_left hp ht hr] with δ hδ1 hδ2
    zujfw
    grind
  obtain ⟨δ₀, hδ₀, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hall
  rw [mem_Ioi] at hδ₀
  set L := (offset ztpr ztoa t) '' Ioo 0 δ₀ with hL
  have hLc : ztulg :=
    isPreconnected_Ioo.image _ (Chazelle.Jordan.continuous_offset _ _ _).continuousOn
  have hLF : ztgua := by
    grind
  set z := offset ztpr ztoa t (δ₀ / 2) with hz
  have hzL : ztpqp := by_grind
  refine ⟨connectedComponentIn _ z, ⟨z, hLF hzL, rfl⟩, ?_⟩
  zuhup
  exact hLc.subset_connectedComponentIn hzL hLF by_grind

/-- **Part 1.**  At a non-cut position inside a walk edge the walk faces exactly one region. -/
theorem faces_existsUnique (hM : WalkAx M) {F : Set ztf} (hF : F ⊆ M.Adm)
    (hfin : F.Finite) {p : ℕ} (hp : p < M.W.n) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (hcut : ¬ M.IsCut F ztk) : ∃! U, U ∈ M.regions F ∧ M.Faces p t U := by
  obtain ⟨U, hU, hf⟩ := hM.exists_faces_of_not_cut hF hfin hp ht hcut
  exact ⟨U, by_simp_all, fun U' ⟨hU', hf'⟩ => faces_unique hU' hU hf' hf⟩

/-! ## Part 2: every region is faced -/

/-- The heights of the points of a finite chord family form a finite set. -/
theorem finite_chord_heights (hF : ChordSystem M.D F) :
    {y : ℝ | ∃ c ∈ F, ∃ x ∈ c, x.2 = y}.Finite := by
  have : {y : ℝ | ∃ c ∈ F, ∃ x ∈ c, x.2 = y} ⊆ ⋃ c ∈ F, Prod.snd '' c := by
    rintro y ⟨c, hc, x, hx, rfl⟩
    zughs

  refine Set.Finite.subset (hF.finite.biUnion fun c hc => ?_) this
  obtain ⟨y, a, b, -, rfl⟩ := hF.hchord c hc
  refine (finite_singleton y).subset ?_
  rintro _ ⟨x, hx, rfl⟩
  exact hx.1

/-- **Part 2.**  Every region of a finite admissible family is faced at some position inside a
walk edge. -/
theorem exists_faces (hM : WalkAx M) {F : Set ztf} (hF : F ⊆ M.Adm) (hfin : F.Finite)
    {U : Set Point} (hU : U ∈ M.regions F) :
    ∃ (p : ℕ) (t : ℝ), p < M.W.n ∧ 0 < t ∧ t < 1 ∧ M.Faces p t U := by
  zudr
  zufue
  zutj

  -- a point of `U` at a generic height
  set B : Set ℝ := {y | ∃ i < M.W.n, (M.W.vtx i).2 = y} ∪ {y | ∃ c ∈ F, ∃ x ∈ c, x.2 = y}
    with hB
  have hBfin : B.Finite := by
    zumja
    have : ztwpy := by
      rfl
    zuces
  zunj

  have hzU : ztmxh := by
    apply hball
    zqbef
    zubet

  zubdr
  zuehk

  have hzc : ztebl := by
    grind
  zucs

  -- the segment from `z` to `q` (half-open) is in `U`

  have hLc : ztulg :=
    isPreconnected_Ico.image _ (by fun_prop : Continuous fun s' : ℝ => (ztbtb : Point)).continuousOn
  have hLF : ztgua := by
    zuvn
    tauto
  zukhl
  have hLU : ztpkn := by
    zuczk

  -- a half-disk on the left of the edge at `q` is free
  zukfc
  zuba

  have hHF : ztmtg := by
    zunr

    · zudkb
    · zuedy
  -- a point of the segment lies in the half-disk
  have hq0 : zthot := by
    zucqj
  zucx

  have hw : ztxsx := by
    zujx
    · zqbef
      zujt

    · zufbr
      have e : ztwoj := by
        zubzu
      zuexh

  zukgq
  have hHU : ztsbq := by
    zuczl

  refine ⟨p, t, hp, ht.1, ht.2, ?_⟩
  zukg

/-! ## Part 3: the parenthesis structure -/

/-- **Separation by a single chord** (generic): in a chord system of a preconnected domain, two
free points of a submap `S` that no chord of `S` separates (they lie in the same component of
`D \ c` for every `c ∈ S`) lie in the same region of `S`. -/
theorem sameComp_of_forall (hF : ChordSystem D F)
    (hD : IsPreconnected D) {S : Set ztf} (hS : S ⊆ F) :
    ∀ {u u' : Point}, u ∈ freeIn D S → u' ∈ freeIn D S →
      (∀ c ∈ S, connectedComponentIn ztjhu u = connectedComponentIn ztjhu u') →
        connectedComponentIn ztbzw u = connectedComponentIn ztbzw u' := by
  zubwj
  induction S, hfin using Set.Finite.induction_on with
  | empty =>
    intro u u' hu hu' _
    rw [Chazelle.Chain.freeIn_empty] at hu hu' ⊢
    rw [hD.connectedComponentIn hu, hD.connectedComponentIn hu']
  | @insert c S hcS hSfin ih =>
    intro u u' hu hu' h
    zuccx

    have hins : ztmvz := by_omega
    set A := freeIn D S with hA
    set A' := freeIn D _ with hA'
    have hA'eq : ztmsu := Chazelle.Chain.freeIn_insert D c S
    have huA : u ∈ A := by_grind
    have hu'A : u' ∈ A := by_grind
    have hIH : connectedComponentIn A u = connectedComponentIn A u' :=
      by grind
    obtain ⟨R, hR, hcR, R₁, R₂, hne, hunion, hR₁, hR₂, heq⟩ := hF.regionsIn_insert hS' hc hcS
    -- the region of `u` in `insert c S`
    set V := connectedComponentIn A' u with hV
    have hVmem : ztscw := ⟨u, hu, rfl⟩
    have huV : u ∈ V := mem_connectedComponentIn hu
    have hfin_eq : ∀ {x : Point} {X : Set Point}, X ∈ regionsIn D _ → x ∈ X →
        X = connectedComponentIn A' x := fun hX hx => Chazelle.Chain.regionsIn_eq_component hX hx
    zvnbk at hVmem
    rcases hVmem with ⟨hVS, hVR⟩ | hVR₁₂
    · -- `V` is an old region
      have hV' := Chazelle.Chain.regionsIn_eq_component hVS huV
      have hu'V : u' ∈ V := by rw [hV', hIH]; exact mem_connectedComponentIn hu'A
      grind
    · -- `V` is one of the two new regions
      have hR₁R : R₁ ⊆ R \ c := by_grind
      have hR₂R : R₂ ⊆ R \ c := by_grind
      have hVR : V ⊆ R \ c := by
        rcases hVR₁₂ with h1 | h1
        · grind
        grind
      have hRu : R = connectedComponentIn A u := Chazelle.Chain.regionsIn_eq_component hR by_grind
      have hu'R : u' ∈ R := by rw [hRu, hIH]; exact mem_connectedComponentIn hu'A
      have hu'c : u' ∉ c := by_grind
      -- the two sides of `c` at a point `w`
      obtain ⟨w, hwc, hwD⟩ := (hF.chord_inter_nonempty_isPreconnected hc).1
      have hRo := hF.regionsIn_open hS' hR
      obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hRo w (hcR ztuim)
      obtain ⟨ε₁, hε₁, hs₁⟩ := hF.chord_separates_in hins zthip hwc hwD
      obtain ⟨ε₂, hε₂, hs₂⟩ := hF.chord_separates_in ztwee
        ztmmn hwc hwD
      set ε := min ztttl r / 2 with hε
      zucmw
      have hεm : ε < min ztttl r := by_grind
      have hε₁' := hεm.trans_le ztwth
      have hε₂' := hεm.trans_le ztwti
      have hεr := hεm.trans_le ztgh
      obtain ⟨hp₁, hm₁, hne₁⟩ := hs₁ ε hε0 hε₁'
      obtain ⟨-, -, hne₂⟩ := hs₂ ε hε0 hε₂'
      have hfc : freeIn D {c} = D \ c := by rw [Chazelle.Chain.freeIn, sUnion_singleton]
      rw [hfc] at hne₂
      set wp : Point := (w.1, w.2 + ε) with hwp
      set wm : Point := (w.1, w.2 - ε) with hwm
      have hwpR : wp ∈ R := hball (by
        zqbef
        simp only [hwp, sub_self, abs_zero, add_sub_cancel_left, abs_of_pos hε0]
        exact max_lt hr hεr)
      have hwmR : wm ∈ R := hball (by
        zqbef
        simp only [hwm, sub_self, abs_zero, sub_sub_cancel_left, abs_neg, abs_of_pos hε0]
        exact max_lt hr hεr)
      -- the region of every point of `R \ c` is `R₁` or `R₂`
      have hin12 : ∀ x ∈ R \ c, connectedComponentIn A' x = R₁ ∨ connectedComponentIn A' x = R₂ := by
        zuh
        rw [← hunion] at hx
        zuky
        · exact Or.inl (hfin_eq hR₁ hx).symm
        · exact Or.inr (hfin_eq hR₂ hx).symm
      have hwpc : wp ∉ c := by
        have : wp ∈ A' := hp₁
        zuhlj
      have hwmc : wm ∉ c := by
        have : wm ∈ A' := hm₁
        zuhlj
      -- the component of a free point of `insert c S` in `D \ c`
      have hcomp : ∀ x w0 : Point, w0 ∈ A' → x ∈ connectedComponentIn A' w0 →
          connectedComponentIn ztjhu x = connectedComponentIn ztjhu w0 := by
        intro x w0 hw0 hx
        have hsub : connectedComponentIn A' w0 ⊆ D \ c := by
          rw [← hfc]
          exact (connectedComponentIn_subset _ _).trans
            (Chazelle.Chain.freeIn_anti D (singleton_subset_iff.2 zthip))
        have := isPreconnected_connectedComponentIn.subset_connectedComponentIn hx hsub
        exact connectedComponentIn_eq (this (mem_connectedComponentIn hw0))
      by_contra hfalse
      have hVne := hfalse
      rcases hin12 wp ⟨hwpR, hwpc⟩ with hp | hp <;> rcases hin12 wm ⟨hwmR, hwmc⟩ with hm | hm <;>
        rcases hin12 u ⟨(hVR huV).1, (hVR huV).2⟩ with hU | hU <;>
        rcases hin12 u' ⟨hu'R, hu'c⟩ with hU' | hU'
      all_goals first
        | exact hne₁ (hp.trans hm.symm)
        | exact hVne (hU.trans hU'.symm)
        | skip
      all_goals refine absurd (h c zthip) ?_
      all_goals first
        | (rw [hcomp u wp hp₁ (by rw [hp, ← hU]; omega),
            hcomp u' wm hm₁ (by rw [hm, ← hU']; exact mem_connectedComponentIn hu')]
           exact hne₂)
        | (rw [hcomp u wm hm₁ (by rw [hm, ← hU]; omega),
            hcomp u' wp hp₁ (by rw [hp, ← hU']; exact mem_connectedComponentIn hu')]
           exact fun h' => hne₂ h'.symm)

/-- A region faced at a position whose small left sector lies in a component `K` of `D \ c`
(`c ∈ F`) is contained in `K`. -/
theorem region_subset_of_sector (hM : WalkAx M) {F : Set ztf} {c : Set Point}
    (hc : c ∈ F) {U : Set Point} (hU : U ∈ M.regions F) {p : ℕ} (hp : p < M.W.n) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) (hf : M.Faces p t U) {k : Point}
    (hK : SideSectorIn M.W ztyqh p t) :
    U ⊆ connectedComponentIn ztjq k := by
  obtain ⟨x, hxU, hxK⟩ := hM.faces_meets hp ht hK hf
  have hsub : ztscu := fun y hy =>
    ⟨(Chazelle.Chain.regionsIn_subset hU hy).1,
      fun hyc => (Chazelle.Chain.regionsIn_subset hU hy).2 by_grind⟩
  zuorw
  exact (Chazelle.Chain.regionsIn_isPreconnected hU).subset_connectedComponentIn hxU hsub

/-- The key of a non-cut position differs from the key of every attachment of a chord of `F`. -/
theorem key_ne_of_not_cut {c : Set Point} (hc : c ∈ F) {p pa : ℕ}
    {t ta : ℝ} (hcut : ¬ M.IsCut F ztk) (hA : SideAttach M.W c pa ta) :
    (p : ℝ) + t ≠ pa + ta := fun h => hcut ztexy

/-- Two attachments with distinct points have distinct keys. -/
theorem key_ne_of_pt_ne {pa pb : ℕ} {ta tb : ℝ} {c d : Set Point} (hA : SideAttach M.W c pa ta)
    (hB : SideAttach M.W d pb tb) (hAB : sidePt M.W pa ta ≠ sidePt M.W pb tb) :
    (pa : ℝ) + ta ≠ pb + tb := by
  zuq
  obtain ⟨rfl, rfl⟩ := sideKey_inj hA.2.1 hA.2.2.1 hB.2.1 hB.2.2.1 h
  simp_all

/-- **Part 3 (for non-cut positions).**  Two non-cut positions inside walk edges face the same
region iff no chord of `F` separates their keys. -/
theorem eq_iff_not_separates (hM : WalkAx M) {F : Set ztf} (hF : F ⊆ M.Adm)
    (hfin : F.Finite) {p p' : ℕ} {t t' : ℝ} {U U' : Set Point} (hU : U ∈ M.regions F)
    (hU' : U' ∈ M.regions F) (hp : p < M.W.n) (hp' : p' < M.W.n) (ht : t ∈ Ioo (0 : ℝ) 1)
    (ht' : t' ∈ Ioo (0 : ℝ) 1) (hcut : ¬ M.IsCut F ztk) (hcut' : ¬ M.IsCut F ztjg)
    (hf : M.Faces p t U) (hf' : M.Faces p' t' U') :
    U = U' ↔ ∀ c ∈ F, ¬ M.Separates c ztk ztjg := by
  -- the two arcs of a chord
  have harcs : ∀ c ∈ F, ∀ {pa pb : ℕ} {ta tb : ℝ}, SideAttach M.W c pa ta →
      SideAttach M.W c pb tb → sidePt M.W pa ta ≠ sidePt M.W pb tb →
      ∃ k₁ k₂ : Point, connectedComponentIn ztjq k₁ ≠ connectedComponentIn ztjq k₂ ∧
        (sideInArc ztbf ztbd ztk → U ⊆ connectedComponentIn ztjq k₁) ∧
        (¬ sideInArc ztbf ztbd ztk → U ⊆ connectedComponentIn ztjq k₂) ∧
        (sideInArc ztbf ztbd ztjg → U' ⊆ connectedComponentIn ztjq k₁) ∧
        (¬ sideInArc ztbf ztbd ztjg →
          U' ⊆ connectedComponentIn ztjq k₂) := by
    intro c hc pa pb ta tb hA hB hAB
    obtain ⟨K₁, K₂, hne, ⟨k₁, rfl⟩, ⟨k₂, rfl⟩, h₁, h₂⟩ := hM.split ztlz hA hB hAB
    have hkAB := key_ne_of_pt_ne hA hB hAB
    refine ⟨k₁, k₂, hne, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
    · zuhue
    · have h' := (sideInArc_swap hkAB (key_ne_of_not_cut hc hcut hA)
        (key_ne_of_not_cut hc hcut hB)).2
      have h'' : sideInArc ztbd ztbf ztk := by
        simp_all
      zuhue
    · zuhuf
    · have h' := (sideInArc_swap hkAB (key_ne_of_not_cut hc hcut' hA)
        (key_ne_of_not_cut hc hcut' hB)).2
      have h'' : sideInArc ztbd ztbf ztjg := by
        simp_all
      zuhuf
  zuvh
  obtain ⟨u', hu'⟩ := Chazelle.Chain.regionsIn_nonempty hU'
  constructor
  · rintro rfl c hc ⟨pa, pb, ta, tb, hA, hB, hAB, hiff⟩
    obtain ⟨k₁, k₂, hne, h1, h2, h1', h2'⟩ := harcs c hc hA hB hAB
    by_cases hx : sideInArc ztbf ztbd ztk
    · have hx' := hiff.1 hx
      have e1 := h1 hx hu
      have e2 := h2' hx' hu
      exact hne ((connectedComponentIn_eq e1).trans (connectedComponentIn_eq e2).symm)
    · have hx' : sideInArc ztbf ztbd ztjg := by
        grind
      have e1 := h2 hx hu
      have e2 := h1' hx' hu
      exact hne ((connectedComponentIn_eq e2).trans (connectedComponentIn_eq e1).symm)
  · intro hno
    by_contra hUU
    zudr
    have hcomp : connectedComponentIn zttke u ≠ connectedComponentIn zttke u' := by
      rw [← Chazelle.Chain.regionsIn_eq_component hU hu,
        ← Chazelle.Chain.regionsIn_eq_component hU' hu']
      omega
    have hex : ∃ c ∈ F, connectedComponentIn ztjq u ≠ connectedComponentIn ztjq u' := by
      by_contra hall
      zugrg
      exact hcomp (sameComp_of_forall hsys hM.preconn subset_rfl
        (Chazelle.Chain.regionsIn_subset hU hu) (Chazelle.Chain.regionsIn_subset hU' hu') hall)
    obtain ⟨c, hc, hcne⟩ := hex
    zuds
    have hAB : ztmwu := by_grind
    obtain ⟨k₁, k₂, -, h1, h2, h1', h2'⟩ := harcs c hc hA hB hAB
    apply hno c hc
    refine ztdjg
    by_cases hx : sideInArc ztbf ztbd ztk <;>
      by_cases hx' : sideInArc ztbf ztbd ztjg
    · exact absurd ((connectedComponentIn_eq by_grind).symm.trans
        (connectedComponentIn_eq (h1' hx' hu'))) hcne
    · grind
    · grind
    · exact absurd ((connectedComponentIn_eq by_grind).symm.trans
        (connectedComponentIn_eq (h2' hx' hu'))) hcne
end WalkAx
end
end Chazelle.Core
end
namespace Chazelle.Core
@[expose] public section
open Set Filter Topology Metric
open Chazelle.Chain
open Chazelle.Geometry (lerp lerp_fst lerp_snd point_ext lerp_mem_segment)
open Chazelle.Visibility (hseg segment_horizontal_eq_hseg)

/-- **First exit of a horizontal ray** from an open set lying left of the line `x = R`: the ray
to the east from `z ∈ D` stays in `D` on `[0, s)` and leaves it at `s > 0`. -/
theorem exists_first_exit {D : Set Point} (hD : IsOpen D) {z : Point} (hz : z ∈ D) {R : ℝ}
    (hR : ∀ x ∈ D, x.1 < R) :
    ∃ s > (0 : ℝ), (∀ s' ∈ Ico (0 : ℝ) s, (ztbtb : Point) ∈ D) ∧
      (ztbfb : Point) ∉ D := by
  set T := {s : ℝ | 0 ≤ s ∧ (ztbfb : Point) ∉ D} with hT
  have hcont : Continuous fun s : ℝ => (ztbfb : Point) := by fun_prop
  have hTc : IsClosed T :=
    (isClosed_le continuous_const continuous_id).inter (hD.isClosed_compl.preimage hcont)
  have hz1 := hR z hz
  have hTne : T.Nonempty := ⟨R - z.1 + 1, by_linarith, fun h => by
    grind⟩
  have hbdd : BddBelow T := ztoli
  have hmem := hTc.csInf_mem hTne hbdd
  refine ⟨sInf T, ?_, fun s' hs' => ?_, hmem.2⟩
  · rcases hmem.1.lt_or_eq with h | h
    · zubh
    · exfalso; grind
  · by_contra hs
    exact absurd (csInf_le hbdd ⟨hs'.1, hs⟩) (not_le.2 hs'.2)
namespace FactsChain
variable (C : Chain)
variable {y a b : ℝ} {k : ℕ}
/-- A horizontal segment as a segment. -/
theorem hseg_eq_segment (hab : a ≤ b) :
    hseg y a b = Chazelle.segment (ztdv : Point) ztdy := by
  zuceo
  simp_all

/-- An endpoint of an augmented chord is on the chain or on an open vertical side of the box. -/
theorem end_cases (h : IsHChordIn C.dom y a b) (hy : y ≤ C.top.2) {e : Point}
    (he : C.Anchorable e) (he2 : e.2 = y) :
    e ∈ C.set ∨ (|e.1| = C.radius ∧ |e.2| < C.radius) := by
  have hmid := h.open_mem ztwwr ztbsh ztbsh
  have hyR : ztsnv := (C.dom_subset_box hmid).2
  rcases he with h1 | h1 | h1 | h1
  · simp_all
  · left
    obtain ⟨e1, e2, -⟩ := C.mem_slit_iff.1 h1
    have : e = C.top := point_ext e1 (le_antisymm (he2 ▸ hy) e2)
    zudaq
  · simp_all
  simp_all

/-- The walk-end condition at an endpoint of an augmented chord. -/
theorem walkEnd (hP : C.P.Simple) {e e' : Point} (hee : e ≠ e') (hy : e.2 = e'.2)
    (hopen : ∀ s ∈ Ioo (0 : ℝ) 1, lerp e e' s ∈ C.dom)
    (he : e ∈ C.set ∨ (|e.1| = C.radius ∧ |e.2| < C.radius)) :
    WalkEnd ztcs ztnkg e := by
  zujx
  · obtain ⟨p, t, hp, ht, ht1, hpt, hl⟩ := C.sideSees_chordEnd hP C.sideBeta hee hy hopen he
    exact ⟨p, t, sideAttach_of_left hp ht ht1 hpt hl, hpt⟩
  · intro p p' t t' hp ht ht1 hp' ht' ht1' hne h1 h2
    refine ⟨1, one_pos, fun x _ hx hx' => ?_⟩
    exact C.sideWalk_disj hP ztuxh hp ht ht1 hp' ht' ht1'
      (fun h => fun h' => hne h.symm h'.symm) (h2.trans h1.symm) (h1 ▸ he) x ⟨hx, hx'⟩

/-- Every chain vertex is a vertex of the corrected walk. -/
theorem vertex_mem_walk (hk : k ≤ C.m) :
    ∃ i < (C.sideWalk C.sideBeta).n, (C.sideWalk C.sideBeta).vtx i = C.vertex k := by
  zubt
  obtain ⟨i, hi, hidx, -⟩ := C.sideIdx_visit C.sideBeta (j := k) by_omega
  refine ⟨i + 6, by rw [sideWalk_n]; omega, ?_⟩
  rw [C.sideWalk_vtx_tour _ hi.le, sideTour, hidx]
  congr 1; unfold sideE; simp_all

/-- The two traversals of a chain edge by the tour of the double boundary. -/
theorem tour_edges (hk : k < C.m) :
    (∃ i < 2 * C.m, C.sideIdx C.sideBeta i = k ∧ C.sideIdx C.sideBeta ztg = k + 1) ∧
      (∃ i < 2 * C.m, C.sideIdx C.sideBeta i = k + 1 ∧ C.sideIdx C.sideBeta ztg = k) := by
  zujx
  · obtain ⟨i, hi, h1, h2, -⟩ := C.sideIdx_visit C.sideBeta (j := k) by_omega
    zumkr
    · zuhlh
    · zvmxx; unfold sideE; simp_all
  · obtain ⟨i, hi, h1, h2, -⟩ := C.sideIdx_visit C.sideBeta (j := 2 * C.m - 1 - k) by_omega
    zumkr
    · zuhlh
    · zvmxx; unfold sideE; grind

/-- **Reach for the chain model.** -/
theorem reach {z : Point} (hz : z ∈ C.dom)
    (hzv : ∀ i < (C.sideWalk C.sideBeta).n, z.2 ≠ ((C.sideWalk C.sideBeta).vtx i).2) :
    ∃ s > (0 : ℝ), (∀ s' ∈ Ico (0 : ℝ) s, (ztbtb : Point) ∈ C.dom) ∧
      ∃ p < (C.sideWalk C.sideBeta).n, ∃ t ∈ Ioo (0 : ℝ) 1,
        sidePt ztcs p t = (ztbfb : Point) ∧
        ((C.sideWalk C.sideBeta).vtx p).2 <
          ((C.sideWalk C.sideBeta).vtx ztwqw).2 := by
  zujmu
  zubt
  have hn : ztiyt := C.sideWalk_n _
  zubo
  have hbox : ∀ x ∈ C.dom, |x.1| < C.radius ∧ |x.2| < C.radius := fun x hx => C.dom_subset_box hx
  obtain ⟨s, hs, hseg, hq⟩ := exists_first_exit C.isOpen_dom hz (R := C.radius)
    (fun x hx => (abs_lt.1 (hbox x hx).1).2)
  refine ztopl
  have hz1 := abs_lt.1 (hbox z hz).1
  have hz2 := abs_lt.1 (hbox z hz).2
  -- `z.2` is not the height of the top of the box, nor of a chain vertex
  have hzR : z.2 ≠ C.radius := fun h => hzv 0 by_omega by_simp_all
  have hzv' : ∀ k ≤ C.m, z.2 ≠ (C.vertex k).2 := by
    zujbh
    obtain ⟨i, hi, hvi⟩ := vertex_mem_walk C hk
    grind
  -- the exit point is at abscissa at most `R`
  have hqR : z.1 + s ≤ C.radius := by
    zuum

    have hs' : s - (z.1 + s - C.radius) / 2 ∈ Ico (0 : ℝ) s := ztbcx
    grind
  rw [C.mem_dom_iff] at hq
  by_cases hqbox : (ztbfb : Point) ∈ box C.radius
  · by_cases hqset : (ztbfb : Point) ∈ C.set
    · -- inside a chain edge
      obtain ⟨k, hk, hmem⟩ := hqset
      zukoo
      obtain ⟨s₀, hs₀0, hs₀1, he⟩ := Geometry.mem_segment_iff_lerp.1 hmem
      have he2 := congrArg Prod.snd he
      simp only [lerp_snd] at he2
      have hs₀0' : ztphv := by
        grind
      have hs₀1' : s₀ < 1 := by
        grind
      have hne : (C.vertex k).2 ≠ (C.vertex zts).2 := by
        grind
      obtain ⟨⟨i, hi, hi1, hi2⟩, ⟨i', hi', hi1', hi2'⟩⟩ := tour_edges C hk
      have hvi : W.vtx ztcy = C.vertex k := by
        rw [hW, C.sideWalk_vtx_tour _ hi.le, sideTour, hi1]
      have hvi1 : W.vtx (ztcim % W.n) = C.vertex zts := by
        rw [hW, C.sideWalk_next_tour _ hi, C.sideWalk_vtx_tour _ by_omega, sideTour, hi2]
      have hvi' : W.vtx ztetl = C.vertex zts := by
        rw [hW, C.sideWalk_vtx_tour _ hi'.le, sideTour, hi1']
      have hvi1' : W.vtx ((i' + 6 + 1) % W.n) = C.vertex k := by
        rw [hW, C.sideWalk_next_tour _ hi', C.sideWalk_vtx_tour _ by_omega, sideTour, hi2']
      rcases lt_or_gt_of_ne hne with hup | hdn
      · refine ⟨i + 6, by_omega, s₀, ⟨hs₀0', hs₀1'⟩, ?_, by_grind⟩
        zuhbc
      · refine ⟨i' + 6, by_omega, 1 - s₀, ztbcx, ?_,
          by grind⟩
        unfold sidePt; rw [hvi', hvi1', he]
        zucco
    · -- on the slit, above the top vertex
      have hslit : (ztbfb : Point) ∈ C.slit := by
        simp_all
      obtain ⟨e1, e2, e3⟩ := C.mem_slit_iff.1 hslit
      simp only at e1 e2 e3
      have htop : C.top.2 < z.2 := by
        rcases e2.lt_or_eq with h | h
        · zubh
        · exact absurd h.symm (hzv' C.topIdx C.topIdx_le)
      have hzR' : z.2 < C.radius := lt_of_le_of_ne e3 hzR
      have hv0 : W.vtx ztcc = C.top := by
        rw [hW, C.sideWalk_vtx_tour _ le_rfl, C.sideTour_two_m]
      have hv1 : W.vtx (ztbjc % W.n) = C.slitTop := by
        rw [hW, C.sideWalk_next_last]; rfl
      have hpos : ztixs := by_linarith
      refine ⟨2 * C.m + 6, by_omega, (z.2 - C.top.2) / ztox,
        ⟨div_pos by_linarith hpos, (div_lt_one hpos).2 by_linarith⟩, ?_, ?_⟩
      · rw [(C.sidePt_box _ _).2.2.2.2.2.2]
        zubjw
        · grind
        · zulao
      · rw [hv0, hv1]; exact C.top_snd_lt_radius
  · -- on the right side of the box
    have hq1 : z.1 + s = C.radius := by
      zuct
      apply hqbox
      refine ⟨abs_lt.2 ⟨by_linarith, lt_of_le_of_ne hqR hne⟩, abs_lt.2 hz2⟩
    have hv3 : W.vtx 3 = ztyn := C.sideWalk_vtx_three _
    have hv4 : W.vtx (ztjfq % W.n) = ztbjg := by
      rfl
    refine ⟨3, by_omega, (z.2 + C.radius) / ztekt,
      ⟨div_pos by_linarith by_linarith, (div_lt_one by_linarith).2 by_linarith⟩, ?_, ?_⟩
    · rw [(C.sidePt_box _ _).2.2.2.1]
      zubjw
      · simp_all
      · zulao
    simp_all

/-- **The chain model satisfies the walk axioms.** -/
theorem walkAx (hP : C.P.Simple) : WalkAx ztc where
  isOpen := C.isOpen_dom
  preconn := C.dom_connected hP
  nonempty := C.dom_nonempty
  nd := C.sideWalk_nd hP _
  trace := C.sideWalk_trace _
  clean := C.sideWalk_clean hP ztuxh
  sys := fun _ hF hfin => Merge.augChordSystem C hF hfin
  ends := by
    zung
    zudrs
    have hopen : ∀ s ∈ Ioo (0 : ℝ) 1, lerp (ztdv : Point) ztdy s ∈ C.dom := by
      zugg
      have e : ztxbu := by
        zuenz
      zui
      zulfe
    have hab : ztxfd := fun e => h.lt.ne (congrArg Prod.fst e)
    have hseg := hseg_eq_segment (y := y) h.lt.le
    have ha := end_cases C h hy (Merge.anchorable_left C h) rfl
    have hb := end_cases C h hy (Merge.anchorable_right C h) rfl
    refine ztxmj
    · rw [hseg]; exact walkEnd C hP hab rfl hopen ha
    · zukwd
      exact walkEnd C hP hab.symm rfl ztjnr hb
  reach := fun z hz hzv => reach C hz hzv
