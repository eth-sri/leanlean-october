module

public import Chazelle.Core.SpecRam
public import Chazelle.Core.SpecFacts
public import Chazelle.Separator.Graph
public import Chazelle.Cost.Oracle

/-!
# Core specification, part 4a: kernels, the normal-form toolkit, and the oracle interfaces

RAM-level interfaces shared by several work packages (design doc §4, §8):

* bands of the procedures (`bSign`, `bBuild`, …);
* WP-A: `SignKernelSpec`, the only statement that reads coordinates (every geometric test of the
  stage is one of its four sign tests on symbolic points of `Q = Qof P`);
* WP-C: `BuildNFSpec` (normal form from a chord list: sorting along the walk, parenthesis
  structure, regions, arcs, weights), `LocateSpec` (double identification), `DecompSpec` (tree
  decomposition);
* the **oracle interfaces** used by the merge procedures, stated for an arbitrary statement:
  `ShooterOK` (the ray-shooter of p. 501 (i), cost `F γ`) and `CutterOK` (the arc-cutter of
  p. 501 (ii), at most `G γ` pieces, granularity `H γ`); WP-G builds them from the up-phase data;
* WP-H's per-chain structure of Lemma 3.6 as an interface `OracleIface` with validity;
* WP-I: `ClusterSpec`, the cluster decomposition of a planar map stored in memory.

A procedure's inputs are the first registers of its band (`rd c b i = c.nreg (bandReg b i)`),
its outputs follow them; handles are addresses.

**Consolidated revision** (design doc §10): the band `bSweep = 24` of the fusion's sweep; every
procedure that reads a model or chain descriptor requires it well formed and below the allocator
(`ModelDescWF`, `ChainWF`, findings C7/C8), reads its normal-form inputs below the allocator
(`NFWithin`), and assumes the word bound `hostWords n = 128 n + 3`; `LocateSpec` is the
specification proved by `locate`; the oracles' subarc ends are proper positions (C6).
-/

namespace Chazelle.Core

@[expose] public section

open Chazelle.Machine (Stmt)
open Chazelle.Chain (sideInArc)

/-! ## Bands -/

/-- Band of the sign kernel (WP-A). -/
def bSign : ℕ := 1
/-- Band of sorting (WP-C). -/
def bSort : ℕ := 3
/-- Band of normal-form construction (WP-C). -/
def bBuild : ℕ := 4
/-- Band of double identification (WP-C). -/
def bLocate : ℕ := 5
/-- Band of the tree decomposition (WP-C). -/
def bDecomp : ℕ := 6
/-- Band of the fusion (WP-D). -/
def bFuse : ℕ := 7
/-- Band of conformality restoration (WP-E). -/
def bRestore : ℕ := 8
/-- Band of granularity enforcement (WP-F). -/
def bGran : ℕ := 9
/-- Band of the merge driver (WP-F). -/
def bMerge : ℕ := 10
/-- Band of oracle preprocessing (WP-H). -/
def bOPrep : ℕ := 11
/-- Band of oracle queries (WP-H). -/
def bOQuery : ℕ := 12
/-- Band of the cluster algorithm (WP-I). -/
def bCluster : ℕ := 13
/-- Band of the ray-shooter for merges (WP-G). -/
def bShoot : ℕ := 14
/-- Band of the arc-cutter (WP-G). -/
def bCut : ℕ := 15
/-- Band of Lemma 4.1 (WP-J). -/
def bL41 : ℕ := 16
/-- Band of the up-phase driver (WP-J). -/
def bUp : ℕ := 17
/-- Band of brute-force maps (WP-K). -/
def bBrute : ℕ := 18
/-- Band of the transition to the interior model (WP-M). -/
def bTrans : ℕ := 19
/-- Band of the down step (WP-M). -/
def bDown : ℕ := 20
/-- Band of the down-phase driver (WP-M). -/
def bDownDrv : ℕ := 21
/-- Band of the core driver (WP-L). -/
def bCore : ℕ := 23
/-- Band of the sweep of the fusion (WP-D; added in the consolidated revision, design doc §10). -/
def bSweep : ℕ := 24

/-- The leaf toolkit (sign kernel, sorting, normal-form construction, double identification,
tree decomposition): scratch bands that any call may clobber; no caller keeps state in them.
(Review finding F6: every package now writes a fixed band set, so callers know what survives.) -/
def kernelBands : Finset ℕ := {bSign, bSort, bBuild, bLocate, bDecomp}

/-- The bands an oracle (ray-shooter, arc-cutter, Lemma 3.6 query) may write. -/
def oracleBands : Finset ℕ := kernelBands ∪ {bOQuery, bShoot, bCut, bCluster}

/-- The bands of granularity enforcement. -/
def granBands : Finset ℕ := kernelBands ∪ {bGran}

/-- The bands of the sweep itself (without its oracle). -/
def sweepBands : Finset ℕ := kernelBands ∪ {bSweep}

/-- The bands of the fusion itself (the fusion driver and its sweeps, without their oracle). -/
def fuseBands : Finset ℕ := kernelBands ∪ {bFuse, bSweep}

/-- The bands of conformality restoration itself (without its oracles). -/
def restoreBands : Finset ℕ := kernelBands ∪ {bRestore}

/-- The bands of a merge itself (without its oracles). -/
def mergeBands : Finset ℕ := kernelBands ∪ {bFuse, bRestore, bGran, bMerge, bSweep}

/-- Register `i` of band `b` in the configuration `c`. -/
def rd (c : Config) (b i : ℕ) : ℕ := c.nreg (bandReg b i)

/-- The geometric environment of every procedure: a simple input with a good shear, so that
`Qof P` is the (simple, distinct-heights) geometry polygon. -/
def GoodEnv (P : Polygon) : Prop := P.Simple ∧ ∃ ε, GoodShear P ε

/-! ## WP-A: the sign kernel -/

/-- A symbolic point held in three registers from `r` on: kind (`0` vertex, `1` edge point) and
its indices. -/
def SymPtIn (c : Config) (r : ℕ) : SymPt → Prop
  | .vtx i => c.nreg r = 0 ∧ c.nreg (r + 1) = i
  | .onEdge e h => c.nreg r = 1 ∧ c.nreg (r + 1) = e ∧ c.nreg (r + 2) = h

/-- The four sign tests: `0` abscissa order, `1` ordinate order, `2` positive orientation,
`3` collinearity. -/
def SignTest (op : ℕ) (a b d : Point) : Prop :=
  match op with
  | 0 => a.1 < b.1
  | 1 => a.2 < b.2
  | 2 => 0 < det a b d
  | _ => det a b d = 0

/-! ## WP-C: the normal-form toolkit -/

/-- A list of chord triples `(h, lp, rp)` at `A`, three words each. -/
def ChordListAt (m : ℕ → ℕ) (A : ℕ) (L : List (ℕ × ℕ × ℕ)) : Prop :=
  ∀ i, i < L.length →
    m (A + 3 * i) = (L.getD i (0, 0, 0)).1 ∧ m (A + 3 * i + 1) = (L.getD i (0, 0, 0)).2.1 ∧
      m (A + 3 * i + 2) = (L.getD i (0, 0, 0)).2.2

/-- The chord record of a triple (regions unknown). -/
def recOf (x : ℕ × ℕ × ℕ) : CRec := ⟨x.1, x.2.1, x.2.2, 0, 0⟩

/-- The triples describe distinct, admissible, correctly attached chords of `M`. -/
def ChordTriplesOK (M : Model) (Q : Polygon) (L : List (ℕ × ℕ × ℕ)) : Prop :=
  M.ChordFamily Q {c | ∃ x ∈ L, c = (recOf x).toSet M Q} ∧
    (L.map fun x => (recOf x).toSet M Q).Nodup ∧ (∀ x ∈ L, (recOf x).Attached M Q) ∧
    ∀ x ∈ L, x.1 < Q.n

/-- **WP-C: normal form from a chord list.**  Inputs: model descriptor (register `0`), chord
list base (`1`) and length (`2`).  Output (`3`): a fresh normal-form handle whose chords are the
given ones in the given order (no decomposition).  Cost `κ (K (⌈log₂ K⌉ + 1) + 1)`.
(Consolidated revision: the descriptor is well formed and the descriptor and the chord list lie
below the allocator, findings C7/C8; the output's arc records are proper positions, part of
`IsNF`, finding C6; the side regions of each chord are fixed by `UpSideSpec`, finding C10.) -/
def BuildNFSpec : Prop :=
  ∃ (s : Stmt) (κ : ℕ), Meets s {bBuild, bSort, bSign}
    (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧
      ModelDescWF P (c.nreg ALLOC) c.nmem (rd c bBuild 0) ∧
      ∃ M L, ModelDescAt c.nmem (rd c bBuild 0) (Qof P) M ∧
      GoodModel M ∧ rd c bBuild 2 = L.length ∧ rd c bBuild 1 + 3 * L.length ≤ c.nreg ALLOC ∧
      ChordListAt c.nmem (rd c bBuild 1) L ∧ ChordTriplesOK M (Qof P) L)
    (fun P c c' => ∀ M L, ModelDescAt c.nmem (rd c bBuild 0) (Qof P) M →
      rd c bBuild 2 = L.length → ChordListAt c.nmem (rd c bBuild 1) L →
        ∃ N, c.nreg ALLOC ≤ rd c' bBuild 3 ∧ NFWithin c'.nmem (rd c' bBuild 3) (c'.nreg ALLOC) N ∧
          IsNF M (Qof P) N ∧ N.chords.map (fun r => (r.h, r.lp, r.rp)) = L ∧ N.dec = [])
    (fun _ c => κ * (rd c bBuild 2 * (Nat.clog 2 (rd c bBuild 2) + 1) + 1))

/-- **WP-C: tree decomposition** (§2.3).  Inputs: model descriptor (`0`), normal form (`1`),
degree cap `D` (`2`).  Output (`3`): a fresh copy with a decomposition of depth
`decDepth D K`.  Cost `κ (D + 1) (K (⌈log₂ K⌉ + 1) + 1)`.  (Consolidated revision: well-formed
descriptor and input below the allocator, findings C7/C8.) -/
def DecompSpec : Prop :=
  ∃ (s : Stmt) (κ : ℕ), Meets s {bDecomp}
    (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧
      ModelDescWF P (c.nreg ALLOC) c.nmem (rd c bDecomp 0) ∧
      ∃ M N, ModelDescAt c.nmem (rd c bDecomp 0) (Qof P) M ∧
      GoodModel M ∧ NFWithin c.nmem (rd c bDecomp 1) (c.nreg ALLOC) N ∧ IsNF M (Qof P) N ∧
      M.DegLe (N.F M (Qof P)) (rd c bDecomp 2))
    (fun P c c' => ∀ M N, ModelDescAt c.nmem (rd c bDecomp 0) (Qof P) M →
      NFAt c.nmem (rd c bDecomp 1) N → IsNF M (Qof P) N →
        ∃ N', c.nreg ALLOC ≤ rd c' bDecomp 3 ∧
          NFWithin c'.nmem (rd c' bDecomp 3) (c'.nreg ALLOC) N' ∧
          N'.chords = N.chords ∧ N'.arcs = N.arcs ∧ N'.regions = N.regions ∧ N'.seq = N.seq ∧
          IsDecomp N' (decDepth (rd c bDecomp 2) N.nChords))
    (fun _ c => κ * (rd c bDecomp 2 + 1) *
      (c.nmem (rd c bDecomp 1) * (Nat.clog 2 (c.nmem (rd c bDecomp 1)) + 1) + 1))

/-! ## Oracle interfaces for the merges -/

/-- A **memory context**: a property of the memory below a bound, found through a handle (the
up-phase data: canonical submaps and oracle structures of all processed chains, reached through
the grade table), insensitive to the memory above the bound, together with the largest weight
bound `cap` it supports. -/
structure MemCtx where
  /-- `holds P m g A`: the memory `m` holds the context at handle `g`, below address `A`. -/
  holds : Polygon → (ℕ → ℕ) → ℕ → ℕ → Prop
  /-- The largest arc weight the oracles built on the context support. -/
  cap : Polygon → (ℕ → ℕ) → ℕ → ℕ
  /-- Locality. -/
  local_ : ∀ P m m' g A, (∀ a, a < A → m a = m' a) → holds P m g A → holds P m' g A
  /-- Monotonicity in the bound. -/
  mono : ∀ P m g A A', A ≤ A' → holds P m g A → holds P m g A'

/-- **Capacity locality** (review finding E4): the capacity read at a handle does not change when
the memory changes at or above a bound below which the context holds.  Procedures that allocate
before calling an oracle (restore, fusion, sweep, merge) need it to re-establish the oracles'
precondition `γ ≤ cap`; the contexts of the project (`gradeCtx`) have it (`gradeCtx_capLocal`). -/
def MemCtx.CapLocal (X : MemCtx) : Prop :=
  ∀ P m m' g A, (∀ a, a < A → m' a = m a) → X.holds P m g A → X.cap P m' g = X.cap P m g

/-- **A halving table** (review finding R-D3): the context stores `⌊x / 2⌋` for `x ≤ n` at the
address read at `g + 3`.  The RAM has no division, and the search of Lemma 3.2 halves the codes of
a tree decomposition at every node of its descent; with the table this costs `O(1)`.  The
contexts of the project (`gradeCtx`) have it (`gradeCtx_halves`). -/
def MemCtx.Halves (X : MemCtx) : Prop :=
  ∀ P m g A, X.holds P m g A → g + 3 < A ∧
    ∀ x, x ≤ P.n → m (g + 3) + x < A ∧ m (m (g + 3) + x) = x / 2

/-- The points of the walk with keys in the closed cyclic interval `[a, b]`. -/
def Model.arcSet (M : Model) (a b : ℝ) : Set Point :=
  {x | ∃ p : ℕ, ∃ t : ℝ, p < M.W.n ∧ 0 ≤ t ∧ t ≤ 1 ∧
    (sideInArc a b (p + t) ∨ (p : ℝ) + t = a ∨ (p : ℝ) + t = b) ∧
      x = Geometry.lerp (M.wa p) (M.wb p) t}

section
variable (A : Set Point) (p : Point)
include A p
/-- The first hit of the horizontal ray from `p` in direction `σ` on the set `A` is at
parameter `t`. -/
def FirstHit (σ t : ℝ) : Prop :=
  0 < t ∧ Visibility.rayPt p σ t ∈ A ∧ ∀ t', 0 < t' → t' < t → Visibility.rayPt p σ t' ∉ A

/-- The horizontal ray from `p` in direction `σ` misses `A`. -/
def NoHit (σ : ℝ) : Prop :=
  ∀ t, 0 < t → Visibility.rayPt p σ t ∉ A


end

/-- The direction coded by a register value (`1` right, otherwise left). -/
def dirOf (v : ℕ) : ℝ := if v = 1 then 1 else -1

/-- **A ray origin** of a merge (review finding F5): the fusion shoots from chord endpoints, which
are symbolic points of `Q` or points of the model's walk (box and slit edges included). -/
inductive Origin where
  /-- A symbolic point of `Q`. -/
  | sym (p : SymPt)
  /-- A walk position of the model. -/
  | walk (x : WPos)
  deriving DecidableEq

/-- An origin held in three registers from `r` on: kinds `0, 1` as `SymPtIn`, kind `2` a walk
position (edge, height code). -/
def OriginIn (c : Config) (r : ℕ) : Origin → Prop
  | .sym p => SymPtIn c r p
  | .walk x => c.nreg r = 2 ∧ c.nreg (r + 1) = x.edge ∧ c.nreg (r + 2) = x.hgt

/-- The indices of an origin are in range. -/
def Origin.Lt (n : ℕ) (M : Model) : Origin → Prop
  | .sym p => p.Lt n
  | .walk x => x.edge < M.W.n ∧ x.hgt ≤ n

/-- The Euclidean point of an origin. -/
noncomputable def Origin.eval (M : Model) (Q : Polygon) : Origin → Point
  | .sym p => p.eval Q
  | .walk x => M.pos Q x

/-- **An inner point** of a model (review finding G2): strictly between the heights of two walk
vertices and between the abscissae of two walk vertices (for a chain model: inside the box
height band).  Shots from other points, or at subarcs ending at other non-vertex points, may
depend on the box radius, a sum over all host vertices, which the shooter cannot afford to read. -/
def Model.InnerPt (M : Model) (z : Point) : Prop :=
  (∃ p q, p < M.W.n ∧ q < M.W.n ∧ (M.W.vtx p).2 < z.2 ∧ z.2 < (M.W.vtx q).2) ∧
    (∃ p q, p < M.W.n ∧ q < M.W.n ∧ (M.W.vtx p).1 ≤ z.1 ∧ z.1 ≤ (M.W.vtx q).1)

/-- **The ray-shooter interface** (p. 501 (i)).  `sh` answers, for a model `M` accepted by `Ok`
(registers `0`: model descriptor; `1, 2` and `3, 4`: the ends of a subarc; `5 … 7`: the query
point (an `Origin`); `8`: the direction; `9`: a bound `γ ≤ cap` on the counted edges of the subarc; `13`: the
context handle), the first point of the subarc hit by the ray (register `10`: hit flag; `11, 12`:
its walk position), in at most `F γ` steps, provided the context `X` (the up-phase data) is in
memory below the allocator.  (Consolidated revision: the model descriptor is well formed and
below the allocator, the subarc ends are proper positions, findings C6–C8; the origin is a walk
vertex or an inner point, and non-vertex subarc ends are inner points, finding G2.) -/
def ShooterOK (sh : Stmt) (B : Finset ℕ) (F : ℕ → ℕ) (X : MemCtx)
    (Ok : Polygon → Model → Prop) : Prop :=
  Meets sh B
    (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧
      X.holds P c.nmem (rd c bShoot 13) (c.nreg ALLOC) ∧
      rd c bShoot 9 ≤ X.cap P c.nmem (rd c bShoot 13) ∧
      ModelDescWF P (c.nreg ALLOC) c.nmem (rd c bShoot 0) ∧
      (c.nmem (rd c bShoot 0) = 0 → ∀ H C, ChainDescAt c.nmem (rd c bShoot 0 + 1) (Qof P) H C →
        HostRegular (Qof P).n H) ∧
      ∃ M, ModelDescAt c.nmem (rd c bShoot 0) (Qof P) M ∧ Ok P M ∧
        ProperPos M (Qof P) P.n ⟨rd c bShoot 1, rd c bShoot 2⟩ ∧
        ProperPos M (Qof P) P.n ⟨rd c bShoot 3, rd c bShoot 4⟩ ∧
        rd c bShoot 1 < M.W.n ∧ rd c bShoot 3 < M.W.n ∧
        (rd c bShoot 2 = 0 ∨ M.InnerPt (M.pos (Qof P) ⟨rd c bShoot 1, rd c bShoot 2⟩)) ∧
        (rd c bShoot 4 = 0 ∨ M.InnerPt (M.pos (Qof P) ⟨rd c bShoot 3, rd c bShoot 4⟩)) ∧
        M.arcWt (M.key (Qof P) ⟨rd c bShoot 1, rd c bShoot 2⟩)
          (M.key (Qof P) ⟨rd c bShoot 3, rd c bShoot 4⟩) ≤ rd c bShoot 9 ∧
        ∃ o : Origin, o.Lt P.n M ∧ OriginIn c (bandReg bShoot 5) o ∧
          ((∃ p, o = .walk ⟨p, 0⟩) ∨ (M.InnerPt (o.eval M (Qof P)) ∧
            ∀ x, o = .walk x → ProperPos M (Qof P) P.n x)) ∧
          o.eval M (Qof P) ∉ M.arcSet (M.key (Qof P) ⟨rd c bShoot 1, rd c bShoot 2⟩)
            (M.key (Qof P) ⟨rd c bShoot 3, rd c bShoot 4⟩))
    (fun P c c' => ∀ M (o : Origin), ModelDescAt c.nmem (rd c bShoot 0) (Qof P) M →
      OriginIn c (bandReg bShoot 5) o →
        let A := M.arcSet (M.key (Qof P) ⟨rd c bShoot 1, rd c bShoot 2⟩)
          (M.key (Qof P) ⟨rd c bShoot 3, rd c bShoot 4⟩)
        (rd c' bShoot 10 = 1 → ∃ t, FirstHit A (o.eval M (Qof P)) (dirOf (rd c bShoot 8)) t ∧
          ProperPos M (Qof P) P.n ⟨rd c' bShoot 11, rd c' bShoot 12⟩ ∧ rd c' bShoot 11 < M.W.n ∧
          M.pos (Qof P) ⟨rd c' bShoot 11, rd c' bShoot 12⟩ =
            Visibility.rayPt (o.eval M (Qof P)) (dirOf (rd c bShoot 8)) t) ∧
        (rd c' bShoot 10 ≠ 1 → NoHit A (o.eval M (Qof P)) (dirOf (rd c bShoot 8))))
    (fun _ c => F (rd c bShoot 9))

/-- The walks `W` and `W'` **agree** on the stretch of length `L` starting at their vertices `g`
and `g'` (indices modulo the lengths); the same as `WalkEmbed.Agree`, stated here to keep the
specification files free of implementation imports. -/
def WalkAgree (W W' : Polygon) (g g' L : ℕ) : Prop :=
  ∀ d, d ≤ L → W.vtx ((g + d) % W.n) = W'.vtx ((g' + d) % W'.n)

/-- **The walk of a kind-1 piece** (review finding E5).  The piece of the walk of `M` from the
walk vertex `s` to the walk vertex `e` traverses the chain `Cα` on one side, as `Cα.m`
consecutive walk edges.  It agrees with the walk of `chainModel Cα` either along one stretch, or
along two stretches that meet at the top of `Cα`, where the walk of `chainModel Cα` leaves up
the slit (walk vertex `2 m + 6`) and comes back down (walk vertex `6`). -/
def PieceWalk (M : Model) (Cα : Chain) (s e : WPos) : Prop :=
  s.hgt = 0 ∧ e.hgt = 0 ∧ s.edge < M.W.n ∧ e.edge = (s.edge + Cα.m) % M.W.n ∧
    ∃ g' : ℕ, g' < (chainModel Cα).W.n ∧
      (WalkAgree M.W (chainModel Cα).W s.edge g' Cα.m ∨
        ∃ L₁, 0 < L₁ ∧ L₁ < Cα.m ∧ g' + L₁ = 2 * Cα.m + 6 ∧
          WalkAgree M.W (chainModel Cα).W s.edge g' L₁ ∧
          WalkAgree M.W (chainModel Cα).W ((s.edge + L₁) % M.W.n) 6 (Cα.m - L₁))

/-- **The arc-cutter interface** (p. 501 (ii)).  Inputs as for the shooter (registers `0 … 4`,
bound `γ ≤ cap` in `9`, context handle in `13`).  Output (`10`): a fresh piece list — its length `q ≤ G γ`, then seven words
per piece: the two ends (walk positions), a kind (`0` a single-edge end piece, `1` a
vertex-to-vertex piece), a chain descriptor and a normal-form handle.  The pieces tile the subarc
in order; a piece of kind `1` covers the point set of its chain once (no double-backing) and
carries a `γ'`-canonical normal form of it (degree cap `4`) for some `γ' ≤ H γ` (review finding
F2: the paper, p. 517, bounds the granularity of the pieces, it does not fix it); its chain is a
chain of `Qof P` and its walk visits the vertices of the chain upward or downward (finding R-D2:
the search descends the normal form in the chain's own model, which must satisfy the walk axioms,
and converts positions between the two walks).  The piece list
lies below the new allocator (finding F8), and so do the pieces' descriptors (well formed) and
normal forms (consolidated revision, findings C7/C8).  A kind-`1` piece's walk agrees with its
chain's model walk (`PieceWalk`, finding E5). -/
def CutterOK (cu : Stmt) (B : Finset ℕ) (G H : ℕ → ℕ) (X : MemCtx)
    (Ok : Polygon → Model → Prop) : Prop :=
  Meets cu B
    (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧ X.holds P c.nmem (rd c bCut 13) (c.nreg ALLOC) ∧
      rd c bCut 9 ≤ X.cap P c.nmem (rd c bCut 13) ∧
      ModelDescWF P (c.nreg ALLOC) c.nmem (rd c bCut 0) ∧
      ∃ M, ModelDescAt c.nmem (rd c bCut 0) (Qof P) M ∧ Ok P M ∧
        ProperPos M (Qof P) P.n ⟨rd c bCut 1, rd c bCut 2⟩ ∧
        ProperPos M (Qof P) P.n ⟨rd c bCut 3, rd c bCut 4⟩ ∧
        rd c bCut 1 < M.W.n ∧ rd c bCut 3 < M.W.n ∧
        (rd c bCut 2 = 0 ∨ M.InnerPt (M.pos (Qof P) ⟨rd c bCut 1, rd c bCut 2⟩)) ∧
        (rd c bCut 4 = 0 ∨ M.InnerPt (M.pos (Qof P) ⟨rd c bCut 3, rd c bCut 4⟩)) ∧
        M.arcWt (M.key (Qof P) ⟨rd c bCut 1, rd c bCut 2⟩)
          (M.key (Qof P) ⟨rd c bCut 3, rd c bCut 4⟩) ≤ rd c bCut 9)
    (fun P c c' => ∀ M, ModelDescAt c.nmem (rd c bCut 0) (Qof P) M →
      let L := rd c' bCut 10
      let q := c'.nmem L
      let pc := fun (i j : ℕ) => c'.nmem (L + 1 + 7 * i + j)
      let key := fun (e h : ℕ) => M.key (Qof P) ⟨e, h⟩
      c.nreg ALLOC ≤ L ∧ L + 1 + 7 * q ≤ c'.nreg ALLOC ∧ q ≤ G (rd c bCut 9) ∧ 1 ≤ q ∧
      key (pc 0 0) (pc 0 1) = key (rd c bCut 1) (rd c bCut 2) ∧
      key (pc (q - 1) 2) (pc (q - 1) 3) = key (rd c bCut 3) (rd c bCut 4) ∧
      (∀ i, i + 1 < q → key (pc i 2) (pc i 3) = key (pc (i + 1) 0) (pc (i + 1) 1)) ∧
      (∀ i, i + 1 < q → sideInArc (key (pc i 0) (pc i 1)) (key (rd c bCut 3) (rd c bCut 4))
        (key (pc i 2) (pc i 3))) ∧
      (∀ i, i < q → pc i 4 = 0 → M.arcWt (key (pc i 0) (pc i 1)) (key (pc i 2) (pc i 3)) ≤ 1) ∧
      (∀ i, i < q → pc i 4 = 1 → ChainWF P (c'.nreg ALLOC) c'.nmem (pc i 5) ∧
        ∃ Hs Cα N, ChainDescAt c'.nmem (pc i 5) (Qof P) Hs Cα ∧
        NFWithin c'.nmem (pc i 6) (c'.nreg ALLOC) N ∧
        (∃ γ', γ' ≤ H (rd c bCut 9) ∧ IsCanonicalNF (chainModel Cα) (Qof P) N γ' 4) ∧
        M.arcSet (key (pc i 0) (pc i 1)) (key (pc i 2) (pc i 3)) = Cα.set ∧
        M.arcWt (key (pc i 0) (pc i 1)) (key (pc i 2) (pc i 3)) = Cα.m ∧
        PieceWalk M Cα ⟨pc i 0, pc i 1⟩ ⟨pc i 2, pc i 3⟩ ∧ Cα.P = Qof P ∧
        ((∀ d, d ≤ Cα.m → M.W.vtx ((pc i 0 + d) % M.W.n) = Cα.vertex d) ∨
          (∀ d, d ≤ Cα.m → M.W.vtx ((pc i 0 + d) % M.W.n) = Cα.vertex (Cα.m - d)))) ∧
      (∀ i, i < q → ProperPos M (Qof P) P.n ⟨pc i 0, pc i 1⟩ ∧
        ProperPos M (Qof P) P.n ⟨pc i 2, pc i 3⟩ ∧ pc i 0 < M.W.n ∧ pc i 2 < M.W.n) ∧
      (∀ i, i < q → pc i 4 ≤ 1))
    (fun _ c => G (rd c bCut 9))

/-! ## WP-H: the oracle of Lemma 3.6 -/

/-- **An oracle implementation** (Lemma 3.6): a predicate `At P m O` ("the memory holds at `O` a
structure for the chain and normal form recorded at `O`, `O + 1`, with granularity at `O + 2`"),
a preprocessing and a query statement. -/
structure OracleIface where
  /-- The structure predicate. -/
  At : Polygon → (ℕ → ℕ) → ℕ → Prop
  /-- Preprocessing. -/
  prep : Stmt
  /-- Query. -/
  query : Stmt
  /-- The bands written. -/
  bands : Finset ℕ
  /-- The cost constant. -/
  κ : ℕ

/-- **A query origin** of the Lemma 3.6 structure: a symbolic point of `Q`, or the point of the
box of the structure's chain at the height of vertex `h` on the side the ray comes from (rays
from box, slit or far points reduce to this: review finding F5). -/
inductive QOrigin where
  /-- A symbolic point of `Q`. -/
  | sym (p : SymPt)
  /-- The box point at the height of vertex `h`, on the side opposite to the ray direction. -/
  | box (h : ℕ)
  deriving DecidableEq

/-- A query origin in registers from `r` on: kinds `0, 1` as `SymPtIn`, kind `2` a box point. -/
def QOriginIn (c : Config) (r : ℕ) : QOrigin → Prop
  | .sym p => SymPtIn c r p
  | .box h => c.nreg r = 2 ∧ c.nreg (r + 1) = h

/-- The indices of a query origin are in range. -/
def QOrigin.Lt (n : ℕ) : QOrigin → Prop
  | .sym p => p.Lt n
  | .box h => h < n

/-- The point of a query origin for the chain `C` and the ray direction `σ`. -/
noncomputable def QOrigin.eval (Q : Polygon) (C : Chain) (σ : ℝ) : QOrigin → Point
  | .sym p => p.eval Q
  | .box h => (-σ * C.radius, (Q.vtx h).2)

/-- **Validity of an oracle implementation.**
* Preprocessing (band `bOPrep`): from a well-formed chain descriptor (`0`) of a chain of the
  geometry polygon and a `γ`-canonical normal form (`1`) of it, both below the allocator (`γ` in `2`, degree cap `4`), builds a fresh
  structure (`3`) in at most `κ (K (⌈log₂ m⌉ + 1) + 1)` steps (`K` chords, `m` edges); the
  structure lies below the new allocator.
* Bands: at most `oracleBands ∪ {bOPrep}` for the preprocessing (review finding F6), and
  `kernelBands ∪ {bOQuery}` for the query (findings G3, G5: the shooter calls queries inside its
  own frame and keeps its state in the bands `bShoot`, `bCut` across them).
* Query (band `bOQuery`): from a structure (`0`), a query origin (`1 … 3`) and a direction
  (`4`), reports the first hit of the ray on the chain (`5`: flag; `6`: the hit edge of `Q`) in
  at most `κ (γ^{1/3} (m + 1)^{2/3} + 1)` steps. -/
def OracleIface.Valid (O : OracleIface) : Prop :=
  O.bands ⊆ oracleBands ∪ {bOPrep} ∧
  Meets O.prep O.bands
    (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧ ChainWF P (c.nreg ALLOC) c.nmem (rd c bOPrep 0) ∧
      ∃ H C N, ChainDescAt c.nmem (rd c bOPrep 0) (Qof P) H C ∧
      C.P = Qof P ∧ NFWithin c.nmem (rd c bOPrep 1) (c.nreg ALLOC) N ∧
      IsCanonicalNF (chainModel C) (Qof P) N (rd c bOPrep 2) 4)
    (fun P c c' => c.nreg ALLOC ≤ rd c' bOPrep 3 ∧ rd c' bOPrep 3 + 3 ≤ c'.nreg ALLOC ∧
      c'.nmem (rd c' bOPrep 3) = rd c bOPrep 0 ∧ c'.nmem (rd c' bOPrep 3 + 1) = rd c bOPrep 1 ∧
      c'.nmem (rd c' bOPrep 3 + 2) = rd c bOPrep 2 ∧
      ∀ m', (∀ a, a < c'.nreg ALLOC → m' a = c'.nmem a) → O.At P m' (rd c' bOPrep 3))
    (fun _ c => O.κ * (c.nmem (rd c bOPrep 1) *
      (Nat.clog 2 (c.nmem (rd c bOPrep 0 + 2)) + 1) + 1)) ∧
  Meets O.query (kernelBands ∪ {bOQuery})
    (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧ O.At P c.nmem (rd c bOQuery 0) ∧
      ∃ o : QOrigin, o.Lt P.n ∧ QOriginIn c (bandReg bOQuery 1) o)
    (fun P c c' => ∀ H C (o : QOrigin),
      ChainDescAt c.nmem (c.nmem (rd c bOQuery 0)) (Qof P) H C →
      QOriginIn c (bandReg bOQuery 1) o →
        let z := o.eval (Qof P) C (dirOf (rd c bOQuery 4))
        (rd c' bOQuery 5 = 1 → ∃ t, FirstHit C.set z (dirOf (rd c bOQuery 4)) t ∧
          rd c' bOQuery 6 < P.n ∧
          Visibility.rayPt z (dirOf (rd c bOQuery 4)) t ∈ (Qof P).edge (rd c' bOQuery 6)) ∧
        (rd c' bOQuery 5 ≠ 1 → NoHit C.set z (dirOf (rd c bOQuery 4))))
    (fun _ c => ⌈(O.κ : ℝ) * ((c.nmem (rd c bOQuery 0 + 2) : ℝ) ^ ((1 : ℝ) / 3) *
      ((c.nmem (c.nmem (rd c bOQuery 0) + 2) : ℝ) + 1) ^ ((2 : ℝ) / 3) + 1)⌉₊)

/-! ## WP-I: clusters of a planar map in memory -/

section
variable (m : ℕ → ℕ)
include m
/-- A combinatorial map with `μ` vertices and `2 E` darts stored at `B`: the bases of the
`opp`, `rot`, `vert` arrays at `B`, `B + 1`, `B + 2`; it is planar. -/
def PlanarMapAt (B μ E : ℕ) : Prop :=
  ∃ (F : Type) (_ : Fintype F) (_ : DecidableEq F)
    (M : Separator.CombMap (Fin μ) F (Fin (2 * E))), M.Planar ∧
      ∀ d : Fin (2 * E), m (m B + d) = M.opp d ∧ m (m (B + 1) + d) = M.rot d ∧
        m (m (B + 2) + d) = M.vert d

/-- A dart of the map stored at `B` goes from `u` to `v`. -/
def MemDart (B E u v : ℕ) : Prop :=
  ∃ d, d < 2 * E ∧ m (m (B + 2) + d) = u ∧ m (m (B + 2) + m (m B + d)) = v

/-- The (simple) graph of the map stored at `B`, on the vertices `Fin μ`. -/
def memGraph (B μ E : ℕ) : SimpleGraph (Fin μ) where
  Adj u v := u ≠ v ∧ (MemDart m B E u v ∨ MemDart m B E v u)
  symm := ⟨by
    grind⟩
  loopless := ⟨fun u h => h.1 rfl⟩


end

end

end Chazelle.Core
