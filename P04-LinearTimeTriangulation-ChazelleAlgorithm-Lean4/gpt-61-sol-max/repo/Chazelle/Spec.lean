module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Specification: simple polygons, triangulations, and an exact real RAM

This file is the **single authoritative statement**: the geometric definitions, the machine
semantics and the target proposition `LinearTimeTriangulation`.  It imports only Mathlib and
nothing from the proof development, and the proof (`Chazelle.Core.linearTimeTriangulation`,
re-exported by `Solution.lean`) is a theorem about exactly these declarations.

`Challenge.lean` is a generated, self-contained display copy (Palomar requires the Challenge to
import only Lean core and Mathlib) that adds the sorried target theorem; that sorry template is
imported by nothing.  The copy is produced by `scripts/gen_challenge.py`, but the generator is
not trusted for which theorem is proved: `lake comparator` checks that every constant in the
closure of the Challenge statement has the same kernel declaration (type and value) as in the
solution's environment, and `Checks/SpecIdentity.lean` checks independently that `Challenge`
and `Chazelle.Spec` declare equal constants with equal docstrings.

The target is the triangulation conclusion of Theorem 4.3 of

  B. Chazelle, *Triangulating a simple polygon in linear time*,
  Discrete & Computational Geometry 6 (1991), 485–524:

a single deterministic program for an exact real RAM triangulates every
simple polygon with `n` vertices in at most `C·(n+1)` steps, with the natural
numbers it manipulates bounded by `K·(n+1)`.  Any program meeting this
specification proves the target; that the submitted program is Chazelle's
algorithm is documented outside the statement (`docs/hardening/contract.md` §5,
`docs/paper-lemma-map.md` §7).

## Input/output contract (explained in `docs/hardening/contract.md`)

* **Input:** one list of vertices in boundary order; edge `i` joins vertex `i` to vertex
  `(i+1) mod n`, so the first vertex is not repeated at the end.  Either orientation is
  accepted.  Coordinates are arbitrary exact reals.  Vertices with a straight angle count
  towards `n` and must be retained (corners of output triangles).
* **Promise:** the statement only speaks about simple polygons.  On other inputs the
  behaviour is unspecified; `P.Simple` is a promise about the input, not information the
  machine can access (it sees only `n` and the coordinates, through `inputSize`, `readX`,
  `readY`).
* **Output:** the triangles emitted by the run, as index triples into the input list.
* **Uniformity:** the program and the constants `C`, `K` are chosen before the polygon
  (`∃ prog C K, ∀ P`), the initial memory is fixed (`initConfig`, all zero), and the only
  constants a program contains are literals in its instructions (naturals and integer
  reals); nothing depends on `P`, its coordinates or `n`.

## Conventions

* A point is a pair of real numbers; the plane `ℝ × ℝ` carries its ordinary
  (product) topology, and `convexHull ℝ` and `interior` are Mathlib's.
* A polygon is given by the list of its vertices in boundary order.  Vertex
  lookup is total: index `i` denotes the `i`-th entry of the list and an
  out-of-range index denotes the origin.  The triangulation predicate only accepts
  valid indices; that the submitted program never reads an out-of-range vertex is a
  separate safety theorem about it.
* *Simple* is the standard notion, with no general-position hypothesis:
  at least three pairwise distinct vertices, and any two distinct edges meet
  exactly in the endpoints they share.  Collinear consecutive vertices,
  horizontal edges and equal heights are all allowed.
* The *filled region* is the boundary together with every point whose
  connected component in the complement of the boundary is bounded.  (For a
  simple polygon this is the closed region enclosed by the boundary; the
  definition does not presuppose the Jordan curve theorem.)
* A *triangulation* is a list of exactly `n − 2` nondegenerate triangles on
  the input vertices whose union is exactly the filled region, whose interiors
  are pairwise disjoint, and which are *conforming*: any two of them meet
  exactly in the convex hull of their common vertices.
* The machine is described below (`Instr`, `Config`, `step`); every executed
  instruction, including every read of an input coordinate, every `emit` and
  the final `halt`, costs one step (`docs/hardening/unit-cost-convention.md`).
-/

@[expose] public section

namespace Chazelle

/-- A point of the plane. -/
abbrev Point : Type := ℝ × ℝ

/-- The closed segment from `a` to `b`. -/
def segment (a b : Point) : Set Point :=
  {p | ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ p = (a.1 + t * (b.1 - a.1), a.2 + t * (b.2 - a.2))}

/-- Twice the signed area of the triangle `a b c`; nonzero exactly when the
three points are not collinear. -/
def det (a b c : Point) : ℝ :=
  (b.1 - a.1) * (c.2 - a.2) - (c.1 - a.1) * (b.2 - a.2)

/-- A set of points is bounded when it lies in some square centred at the origin. -/
def IsBoundedSet (S : Set Point) : Prop :=
  ∃ R : ℝ, ∀ p ∈ S, |p.1| ≤ R ∧ |p.2| ≤ R

/-- A polygon: its vertices in boundary order. -/
structure Polygon where
  /-- The vertex list `v₀, v₁, …, vₙ₋₁`; edge `i` joins `vᵢ` to `v_{(i+1) mod n}`. -/
  vertices : List Point

namespace Polygon

variable (P : Polygon)

/-- The number of vertices `n`. -/
def n : ℕ := P.vertices.length

/-- Total vertex lookup: `vtx i` is the `i`-th vertex, or the origin if `i ≥ n`. -/
def vtx (i : ℕ) : Point := P.vertices.getD i (0, 0)

/-- Edge `i` is the closed segment from vertex `i` to vertex `(i+1) mod n`. -/
def edge (i : ℕ) : Set Point := segment (P.vtx i) (P.vtx ((i + 1) % P.n))

/-- The boundary: the union of all edges. -/
def boundary : Set Point := {p | ∃ i, i < P.n ∧ p ∈ P.edge i}

/-- The vertex points shared by edges `i` and `j`. -/
def commonEndpoints (i j : ℕ) : Set Point :=
  {p | (p = P.vtx i ∨ p = P.vtx ((i + 1) % P.n)) ∧ (p = P.vtx j ∨ p = P.vtx ((j + 1) % P.n))}

/-- The standard notion of a simple polygon: at least three vertices, pairwise
distinct, and any two distinct edges intersect exactly in their common
endpoints.  No general-position assumption is made.  In particular a vertex may
lie on the segment joining its neighbours (collinear consecutive vertices are
allowed), but no vertex may lie on a non-incident edge and no two edges may
overlap. -/
def Simple : Prop :=
  3 ≤ P.n ∧
  (∀ i j, i < P.n → j < P.n → P.vtx i = P.vtx j → i = j) ∧
  (∀ i j, i < P.n → j < P.n → i ≠ j → P.edge i ∩ P.edge j = P.commonEndpoints i j)

/-- The closed filled region: the boundary together with every point whose
connected component in the complement of the boundary is bounded.  (For a point
of the boundary Mathlib's `connectedComponentIn` is `∅`, which is bounded, so
the explicit union with the boundary is redundant but harmless.) -/
def filled : Set Point :=
  P.boundary ∪ {p | IsBoundedSet (connectedComponentIn P.boundaryᶜ p)}

/-- A triangle is named by three vertex indices. -/
abbrev Triangle : Type := ℕ × ℕ × ℕ

/-- The three vertex points of a triangle. -/
def triVertices (t : Triangle) : Set Point := {P.vtx t.1, P.vtx t.2.1, P.vtx t.2.2}

/-- The closed triangle: the convex hull of its three vertices. -/
def triSet (t : Triangle) : Set Point := convexHull ℝ (P.triVertices t)

/-- A triangle is valid when its indices are in range and its vertices are not
collinear (so it is nondegenerate, and its indices are pairwise distinct). -/
def validTriangle (t : Triangle) : Prop :=
  t.1 < P.n ∧ t.2.1 < P.n ∧ t.2.2 < P.n ∧ det (P.vtx t.1) (P.vtx t.2.1) (P.vtx t.2.2) ≠ 0

/-- `T` triangulates `P`: exactly `n − 2` valid triangles on the vertices of `P`
that cover exactly the filled region, have pairwise disjoint interiors, and are
conforming (any two meet exactly in the convex hull of their common vertices).
The count together with conformity forces every one of the `n` vertices,
including any vertex with a straight angle, to be a corner of some triangle. -/
def Triangulates (T : List Triangle) : Prop :=
  (∀ t ∈ T, P.validTriangle t) ∧
  T.length + 2 = P.n ∧
  {p | ∃ t ∈ T, p ∈ P.triSet t} = P.filled ∧
  T.Pairwise (fun s t => Disjoint (interior (P.triSet s)) (interior (P.triSet t))) ∧
  T.Pairwise (fun s t =>
    P.triSet s ∩ P.triSet t = convexHull ℝ (P.triVertices s ∩ P.triVertices t))

end Polygon

/-! ## The machine

An exact real RAM.  It has natural-number registers and memory (both indexed by
naturals) and real-number registers and memory, a program counter, and an
output list of triangles.  Register names, constants and jump targets are
literal parts of an instruction; memory addresses and input indices are taken
from natural registers.  Real arithmetic is exact; division by zero is a fault
that aborts the run.  There is no floor, no rounding, no conversion between
naturals and reals, no hashing, no natural multiplication or division, and no
geometric primitive: naturals support only constants, copy, addition, truncated
subtraction, load/store and comparison, and the only access to the input is
reading its size or one coordinate of one vertex.  (This is a deliberately
minimal exact real RAM; it only makes the target harder.)
-/

/-- The instruction set.  `r`, `a`, `b`, `c` name registers; `k` is a literal
natural; `z` a literal integer; `l` a literal instruction address. -/
inductive Instr : Type
  /-- Stop; the run has succeeded. -/
  | halt
  /-- `nreg r := n`, the number of input vertices. -/
  | inputSize (r : ℕ)
  /-- `nreg r := k`. -/
  | constN (r k : ℕ)
  /-- `nreg r := nreg a`. -/
  | copyN (r a : ℕ)
  /-- `nreg r := nreg a + nreg b`. -/
  | addN (r a b : ℕ)
  /-- `nreg r := nreg a - nreg b` (truncated at zero). -/
  | subN (r a b : ℕ)
  /-- `nreg r := nmem (nreg a)`. -/
  | loadN (r a : ℕ)
  /-- `nmem (nreg a) := nreg r`. -/
  | storeN (a r : ℕ)
  /-- `rreg r := z`. -/
  | constR (r : ℕ) (z : ℤ)
  /-- `rreg r := rreg a`. -/
  | copyR (r a : ℕ)
  /-- `rreg r := rreg a + rreg b`. -/
  | addR (r a b : ℕ)
  /-- `rreg r := rreg a - rreg b`. -/
  | subR (r a b : ℕ)
  /-- `rreg r := rreg a * rreg b`. -/
  | mulR (r a b : ℕ)
  /-- `rreg r := rreg a / rreg b`; faults if `rreg b = 0`. -/
  | divR (r a b : ℕ)
  /-- `rreg r := rmem (nreg a)`. -/
  | loadR (r a : ℕ)
  /-- `rmem (nreg a) := rreg r`. -/
  | storeR (a r : ℕ)
  /-- `rreg r := x`-coordinate of input vertex number `nreg a` (the origin if
  `nreg a ≥ n`, see `Polygon.vtx`). -/
  | readX (r a : ℕ)
  /-- `rreg r := y`-coordinate of input vertex number `nreg a` (the origin if
  `nreg a ≥ n`, see `Polygon.vtx`). -/
  | readY (r a : ℕ)
  /-- `pc := l`. -/
  | jump (l : ℕ)
  /-- If `nreg a < nreg b` then `pc := l` else continue. -/
  | brLtN (a b l : ℕ)
  /-- If `rreg a < rreg b` then `pc := l` else continue. -/
  | brLtR (a b l : ℕ)
  /-- Append the triangle `(nreg a, nreg b, nreg c)` to the output. -/
  | emit (a b c : ℕ)

/-- A program is a finite list of instructions; instruction addresses are list positions. -/
abbrev Program : Type := List Instr

/-- A machine configuration. -/
structure Config where
  /-- The program counter. -/
  pc : ℕ
  /-- Natural registers. -/
  nreg : ℕ → ℕ
  /-- Real registers. -/
  rreg : ℕ → ℝ
  /-- Natural memory. -/
  nmem : ℕ → ℕ
  /-- Real memory. -/
  rmem : ℕ → ℝ
  /-- The triangles emitted so far, in order. -/
  output : List Polygon.Triangle

/-- The initial configuration: program counter `0`, all registers and memory
cells zero, nothing emitted. -/
def initConfig : Config :=
  { pc := 0, nreg := fun _ => 0, rreg := fun _ => 0, nmem := fun _ => 0, rmem := fun _ => 0,
    output := [] }

/-- Update one entry of a register file or memory. -/
def upd {α : Type} (f : ℕ → α) (i : ℕ) (v : α) : ℕ → α :=
  fun j => if j = i then v else f j

/-- Execute one instruction of `prog` on input `P` from configuration `c`.
Returns `none` on a fault (program counter out of range, or division by zero)
or when the current instruction is `halt`; otherwise the next configuration. -/
noncomputable def step (prog : Program) (P : Polygon) (c : Config) : Option Config :=
  match prog[c.pc]? with
  | none => none
  | some ins =>
    match ins with
    | .halt => none
    | .inputSize r => some { c with pc := c.pc + 1, nreg := upd c.nreg r P.n }
    | .constN r k => some { c with pc := c.pc + 1, nreg := upd c.nreg r k }
    | .copyN r a => some { c with pc := c.pc + 1, nreg := upd c.nreg r (c.nreg a) }
    | .addN r a b => some { c with pc := c.pc + 1, nreg := upd c.nreg r (c.nreg a + c.nreg b) }
    | .subN r a b => some { c with pc := c.pc + 1, nreg := upd c.nreg r (c.nreg a - c.nreg b) }
    | .loadN r a => some { c with pc := c.pc + 1, nreg := upd c.nreg r (c.nmem (c.nreg a)) }
    | .storeN a r => some { c with pc := c.pc + 1, nmem := upd c.nmem (c.nreg a) (c.nreg r) }
    | .constR r z => some { c with pc := c.pc + 1, rreg := upd c.rreg r (z : ℝ) }
    | .copyR r a => some { c with pc := c.pc + 1, rreg := upd c.rreg r (c.rreg a) }
    | .addR r a b => some { c with pc := c.pc + 1, rreg := upd c.rreg r (c.rreg a + c.rreg b) }
    | .subR r a b => some { c with pc := c.pc + 1, rreg := upd c.rreg r (c.rreg a - c.rreg b) }
    | .mulR r a b => some { c with pc := c.pc + 1, rreg := upd c.rreg r (c.rreg a * c.rreg b) }
    | .divR r a b =>
        if c.rreg b = 0 then none
        else some { c with pc := c.pc + 1, rreg := upd c.rreg r (c.rreg a / c.rreg b) }
    | .loadR r a => some { c with pc := c.pc + 1, rreg := upd c.rreg r (c.rmem (c.nreg a)) }
    | .storeR a r => some { c with pc := c.pc + 1, rmem := upd c.rmem (c.nreg a) (c.rreg r) }
    | .readX r a => some { c with pc := c.pc + 1, rreg := upd c.rreg r (P.vtx (c.nreg a)).1 }
    | .readY r a => some { c with pc := c.pc + 1, rreg := upd c.rreg r (P.vtx (c.nreg a)).2 }
    | .jump l => some { c with pc := l }
    | .brLtN a b l => some { c with pc := if c.nreg a < c.nreg b then l else c.pc + 1 }
    | .brLtR a b l => some { c with pc := if c.rreg a < c.rreg b then l else c.pc + 1 }
    | .emit a b c' =>
        some { c with pc := c.pc + 1, output := c.output ++ [(c.nreg a, c.nreg b, c.nreg c')] }

/-- Run `k` instructions, faulting if any step faults. -/
noncomputable def run (prog : Program) (P : Polygon) : ℕ → Config → Option Config
  | 0, c => some c
  | k + 1, c => (step prog P c).bind (run prog P k)

/-- The configuration is at a `halt` instruction. -/
def AtHalt (prog : Program) (c : Config) : Prop := prog[c.pc]? = some Instr.halt

/-- Every natural register and every natural memory cell of `c` is at most `W`. -/
def WordsBounded (W : ℕ) (c : Config) : Prop :=
  (∀ r, c.nreg r ≤ W) ∧ (∀ a, c.nmem a ≤ W)

/-- `prog`, started on input `P` in the initial configuration, executes exactly
`k` instructions without faulting and then sits at `halt`, every configuration
along the way (including the final one) has its natural words bounded by `W`,
and the output at the end is `out`.  The run is charged `k + 1` steps: one for
each executed instruction and one for the final `halt`. -/
def RunsWithin (prog : Program) (P : Polygon) (W : ℕ) (steps : ℕ) (out : List Polygon.Triangle) :
    Prop :=
  ∃ k : ℕ, k + 1 ≤ steps ∧
    (∀ i, i ≤ k → ∃ c, run prog P i initConfig = some c ∧ WordsBounded W c) ∧
    ∃ c, run prog P k initConfig = some c ∧ AtHalt prog c ∧ c.output = out

/-- **The target** (the triangulation conclusion of Chazelle's Theorem 4.3).
There is one fixed program and constants `C, K > 0` such that on every simple
polygon with `n` vertices the program halts within `C·(n+1)` steps, its natural
words never exceed `K·(n+1)`, and its output triangulates the polygon. -/
def LinearTimeTriangulation : Prop :=
  ∃ (prog : Program) (C K : ℕ), 0 < C ∧ 0 < K ∧
    ∀ P : Polygon, P.Simple →
      ∃ out : List Polygon.Triangle,
        RunsWithin prog P (K * (P.n + 1)) (C * (P.n + 1)) out ∧ P.Triangulates out

end Chazelle

end
