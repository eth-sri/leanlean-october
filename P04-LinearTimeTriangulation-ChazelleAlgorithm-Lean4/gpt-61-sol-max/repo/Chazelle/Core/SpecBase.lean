module

public meta import Chazelle.Arithmetic

public import Chazelle.Chain.Sides
public import Chazelle.Merge.Fusion
public import Chazelle.Mountain.Orientation
public import Chazelle.Mountain.Lex
public import Chazelle.Visibility.HSeg

/-!
# Core specification, part 1: the perturbation and the disk models

Interface file for the visibility-map stage (Chazelle §§2–4).  **Definitions and small sanity
lemmas only**; the algorithms and their proofs live in the work packages listed in
`docs/design-chazelle-core.md`.

## The perturbation (design decision D1)

Chazelle assumes distinct vertex heights (p. 488) and tilts internal edges "symbolically"
(p. 519).  We never perturb the input.  Instead every geometric statement of the visibility-map
stage is made about the **sheared polygon** `Q = shear ε P` (`(x, y) ↦ (x, y + ε x)`, a linear map
of determinant `1`) for one input-dependent `ε > 0` that the machine never computes
(`epsOf P`, chosen by `Classical.choose` among the *good* values `GoodShear P ε`):

* `Q` is a genuine simple polygon (shear invariance, `ShearInvarianceSpec`), so the whole
  Euclidean library (`Chazelle.Chain`, `Chazelle.Merge`, `Chazelle.Visibility`, …) applies to it
  verbatim;
* `Q` has pairwise distinct vertex heights (`DistinctHeights`), which is what the paper assumes;
* the height order of `Q` is the `(y, x)`-lexicographic order of `P` (`YlexAgree`), and every
  comparison the algorithm makes (`StableAt`) has the same outcome for all smaller positive
  `ε'`, hence equals a lexicographic sign condition computable exactly from `P`'s coordinates
  (work package WP-A provides the formulas and RAM kernels);
* orientation tests are exact: `det` is shear invariant (`det_shearPt`).

The stage outputs the trapezoid table of `Q` (`Chazelle.Final.IsTrapTable Q`); the final stage
triangulates `Q` reading `P`'s coordinates (legitimate by `det_shearPt` and `YlexAgree`), and a
triangulation of `Q` is one of `P` (`ShearInvarianceSpec`).

## Disk models (design decision D2)

All submap notions (arcs, weights, degree, conformality, granularity) are defined once, for a
**disk model** `M : Model`: an open domain `M.D` and a closed boundary walk `M.W` keeping `M.D`
on its left, with the admissible chords `M.Adm`.  Instances:

* `chainModel C`: the box-and-slit model of a chain (`docs/design-subchain-model.md`), with the
  corrected walk `C.sideWalk C.sideBeta` of `Chazelle.Chain.Sides`; the chain may live in any
  host polygon (the input `Q` in the up phase, a region boundary `R*` in the down phase);
* `interiorModel Q`: the interior of the closed polygon `Q` (the down phase and the output).

A point of a walk is addressed by a **walk position** `WPos` (walk edge, height code); every
chord ever created lies at the height of a vertex of `Q` (design doc §2.3), so heights are stored
as vertex indices.
-/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology
open Chazelle.Chain (IsHChordIn regionsIn TouchesIn SideAttach sideInArc)

/-! ## The shear -/

section
variable (ε : ℝ)
include ε
/-- The shear `(x, y) ↦ (x, y + ε x)`. -/
def shearPt (p : Point) : Point := (p.1, p.2 + ε * p.1)

/-- The sheared polygon: every vertex sheared, same indices. -/
def shear (P : Polygon) : Polygon := ⟨P.vertices.map (shearPt ε)⟩

/-- The shear does not change the number of vertices. -/
theorem shear_n (P : Polygon) : (shear ε P).n = P.n := by
  simp [shear, Polygon.n]


end


/-- Vertex `i` of the sheared polygon is the sheared vertex `i` (for every `i`: the default
vertex `(0, 0)` is fixed by the shear). -/
theorem shear_vtx (ε : ℝ) (P : Polygon) (i : ℕ) : (shear ε P).vtx i = shearPt ε (P.vtx i) := by
  grind [shearPt, Polygon.vtx, shear]

/-- **Orientation tests are exact under the shear**: the shear has determinant `1`. -/
theorem det_shearPt (ε : ℝ) (a b c : Point) :
    det (shearPt ε a) (shearPt ε b) (shearPt ε c) = det a b c := by
  core_grind [det]

/-- The `x`-coordinate of the point of edge `e` of `Q` at the height of vertex `h` of `Q`
(Chazelle's chord endpoints; the vertex itself when `h` is an endpoint of `e`). -/
noncomputable def edgeXAt (Q : Polygon) (e h : ℕ) : ℝ := Chazelle.Visibility.edgeX Q e (Q.vtx h).2

/-- A **symbolic point** of the geometry polygon: a vertex, or the point of an edge at the height
of a vertex.  Every point the visibility-map stage stores or compares is of this form (design doc
§1.3: all chords lie at vertex heights). -/
inductive SymPt where
  /-- Vertex `i`. -/
  | vtx (i : ℕ)
  /-- The point of edge `e` at the height of vertex `h`. -/
  | onEdge (e h : ℕ)
  deriving DecidableEq

/-- The Euclidean point of a symbolic point of `Q`. -/
noncomputable def SymPt.eval (Q : Polygon) : SymPt → Point
  | .vtx i => Q.vtx i
  | .onEdge e h => (edgeXAt Q e h, (Q.vtx h).2)

/-- The indices of a symbolic point are below `n`. -/
def SymPt.Lt (n : ℕ) : SymPt → Prop
  | .vtx i => i < n
  | .onEdge e h => e < n ∧ h < n

/-- Pairwise distinct vertex heights (the paper's assumption, p. 488). -/
def DistinctHeights (Q : Polygon) : Prop :=
  ∀ i j, i < Q.n → j < Q.n → i ≠ j → (Q.vtx i).2 ≠ (Q.vtx j).2

/-- The `(y, x)`-lexicographic order of `P` is the `(y, x)`-lexicographic order of `Q` (for the
shear with distinct heights: the height order of `Q`). -/
def YlexAgree (P Q : Polygon) : Prop :=
  ∀ i j, i < P.n → j < P.n →
    (Chazelle.Mountain.ylexLT (P.vtx i) (P.vtx j) ↔ Chazelle.Mountain.ylexLT (Q.vtx i) (Q.vtx j))

/-- The three sign facts of a triple of points that the algorithm may test: abscissa order,
ordinate order, orientation sign. -/
def SignFacts (a b c : Point) : Prop × Prop × Prop × Prop :=
  (a.1 < b.1, a.2 < b.2, 0 < det a b c, det a b c = 0)

section
variable (P : Polygon)
include P
/-- **Stability of the algorithm's comparisons.**  Every test made by the visibility-map stage
compares abscissae or ordinates of two symbolic points or takes the orientation sign of three
(`SignFacts`); at `ε` each such test has the truth value it has for all smaller positive `ε'`
(hence the limit value, computable from `P` by lexicographic sign rules: WP-A). -/
def StableAt (ε : ℝ) : Prop :=
  ∀ ε', 0 < ε' → ε' ≤ ε → ∀ s₁ s₂ s₃ : SymPt, s₁.Lt P.n → s₂.Lt P.n → s₃.Lt P.n →
    SignFacts (s₁.eval (shear ε P)) (s₂.eval (shear ε P)) (s₃.eval (shear ε P)) =
      SignFacts (s₁.eval (shear ε' P)) (s₂.eval (shear ε' P)) (s₃.eval (shear ε' P))

/-- A good shear parameter for `P`. -/
def GoodShear (ε : ℝ) : Prop :=
  0 < ε ∧ DistinctHeights (shear ε P) ∧ YlexAgree P (shear ε P) ∧ StableAt P ε

/-- The shear parameter used for `P` (a good one whenever one exists, which WP-A proves for
simple polygons: `GoodShearExistsSpec`). -/
noncomputable def epsOf : ℝ := by
  classical
  exact if h : ∃ ε, GoodShear P ε then h.choose else 1

/-- **The geometry polygon** of the visibility-map stage. -/
noncomputable def Qof : Polygon := shear (epsOf P) P


end

/-- The chosen parameter is good as soon as some parameter is. -/
theorem goodShear_epsOf {P : Polygon} (h : ∃ ε, GoodShear P ε) : GoodShear P (epsOf P) := by
  core_grind

/-- `Q` is a shear of `P` by a nonnegative parameter whose height order is `P`'s lexicographic
order.  The final stage accepts tables for any such `Q` (with `Q = P`, `ε = 0`, as a special
case: `shearRel_refl`). -/
def ShearRel (P Q : Polygon) : Prop :=
  ∃ ε : ℝ, 0 ≤ ε ∧ Q = shear ε P ∧ YlexAgree P Q

/-- The geometry polygon is related to the input. -/
theorem shearRel_Qof {P : Polygon} (h : ∃ ε, GoodShear P ε) : ShearRel P (Qof P) := by
  have hg := goodShear_epsOf h
  exact ⟨epsOf P, hg.1.le, rfl, hg.2.2.1⟩

/-- A related polygon has the same number of vertices. -/
theorem ShearRel.n_eq {P Q : Polygon} (h : ShearRel P Q) : Q.n = P.n := by
  obtain ⟨ε, -, rfl, -⟩ := h
  exact shear_n ε P

/-- **WP-A obligation**: every simple polygon has a good shear parameter. -/
def GoodShearExistsSpec : Prop := ∀ P : Polygon, P.Simple → ∃ ε, GoodShear P ε

/-- **WP-A obligation**: the shear preserves simplicity and triangulations (it is a linear
bijection of the plane with determinant `1`, fixing vertical lines). -/
def ShearInvarianceSpec : Prop :=
  ∀ (ε : ℝ) (P : Polygon), (P.Simple → (shear ε P).Simple) ∧
    ∀ T : List Polygon.Triangle, ((shear ε P).Triangulates T ↔ P.Triangulates T)

/-! ## Disk models -/

/-- A disk model: an open domain `D`, a closed walk `W` keeping `D` on its left, the walk edges
counted by weights, the admissible chords, and the full (vertex-chord) visibility map. -/
structure Model where
  /-- The domain. -/
  D : Set Point
  /-- The boundary walk (domain on the left). -/
  W : Polygon
  /-- The walk edges counted by the weight (edges of `∂C`, not box or slit edges). -/
  counted : ℕ → Prop
  /-- The admissible chords (augmented chords of the model). -/
  Adm : Set (Set Point)
  /-- The full (vertex-chord) visibility map of the model. -/
  Full : Set (Set Point)

/-- **The chain model** of a chain `C` of any host polygon: domain `C.dom`, walk
`C.sideWalk C.sideBeta` (walk edges `0 … 4` box, `5` down the slit, `6 … 2m + 5` the double
boundary, `2m + 6` up the slit), admissible chords `Merge.augChords C`, full map `C.chords`. -/
noncomputable def chainModel (C : Chain) : Model where
  D := C.dom
  W := C.sideWalk C.sideBeta
  counted p := 6 ≤ p ∧ p < 2 * C.m + 6
  Adm := Merge.augChords C
  Full := C.chords

/-- The boundary walk of the interior of `Q`, oriented with the interior on its left. -/
noncomputable def interiorWalk (Q : Polygon) : Polygon := by
  classical
  exact if Mountain.LeftInside Q then Q else ⟨Q.vertices.reverse⟩

/-- **The interior model** of a closed polygon `Q`: the interior of `Q`, its boundary walk, all
edges counted, admissible chords the horizontal chords of the interior (vertex chords and
augmented chords alike), full map `Visibility.chords Q` (the interior visibility map). -/
noncomputable def interiorModel (Q : Polygon) : Model where
  D := Q.filled \ Q.boundary
  W := interiorWalk Q
  counted _ := True
  Adm := {c | ∃ y a b : ℝ, IsHChordIn (Q.filled \ Q.boundary) y a b ∧ c = Visibility.hseg y a b}
  Full := Visibility.chords Q

namespace Model

variable (M : Model)

/-! ### Walk positions -/

/-- The start vertex of walk edge `p`. -/
noncomputable def wa (p : ℕ) : Point := M.W.vtx p

/-- The end vertex of walk edge `p`. -/
noncomputable def wb (p : ℕ) : Point := M.W.vtx ((p + 1) % M.W.n)

end Model

/-- A **walk position**: a walk edge and a height code — `0` is the start vertex of the edge,
`h + 1` is the point of the edge at the height of vertex `h` of the height polygon `Q`. -/
structure WPos where
  /-- The walk edge. -/
  edge : ℕ
  /-- The height code. -/
  hgt : ℕ
  deriving DecidableEq

namespace Model

variable (M : Model)

section
variable (Q : Polygon) (x : WPos)
include Q x
/-- The parameter of a walk position on its walk edge. -/
noncomputable def param : ℝ :=
  match x.hgt with
  | 0 => 0
  | h + 1 =>
      if (M.wa x.edge).2 = (M.wb x.edge).2 then 0
      else ((Q.vtx h).2 - (M.wa x.edge).2) / ((M.wb x.edge).2 - (M.wa x.edge).2)

/-- The key of a walk position (`edge + parameter`), which orders positions along the walk. -/
noncomputable def key : ℝ := x.edge + M.param Q x

/-- The point of a walk position. -/
noncomputable def pos : Point :=
  Geometry.lerp (M.wa x.edge) (M.wb x.edge) (M.param Q x)

/-! ### Submaps: regions, cuts, arcs, weights -/


end

section
variable (F : Set (Set Point))
include F
/-- The regions of the submap `F`. -/
def regions : Set (Set Point) := regionsIn M.D F

/-- The degree of a region (its number of exit chords). -/
noncomputable def deg (U : Set Point) : ℕ :=
  {c | c ∈ F ∧ TouchesIn M.D c U}.ncard


end

/-- An admissible chord family with all heights at vertex heights of `Q`. -/
def ChordFamily (Q : Polygon) (F : Set (Set Point)) : Prop :=
  F.Finite ∧ F ⊆ M.Adm ∧
    ∀ c ∈ F, ∃ h, h < Q.n ∧ ∃ a b : ℝ, c = Visibility.hseg (Q.vtx h).2 a b

/-- `x` is the key of a position where some chord of `F` is attached to the walk (side-aware,
`Chazelle.Chain.SideAttach`: the chord leaves the position into its left sector). -/
def IsCut (F : Set (Set Point)) (x : ℝ) : Prop :=
  ∃ c ∈ F, ∃ p : ℕ, ∃ t : ℝ, SideAttach M.W c p t ∧ x = p + t

/-- The walk faces the set `U` at walk edge `p`, parameter `t`: the points pushed slightly to the
left of the walk are in `U`. -/
def Faces (p : ℕ) (t : ℝ) (U : Set Point) : Prop :=
  ∀ᶠ δ in 𝓝[>] (0 : ℝ), Jordan.offset (M.wa p) (M.wb p) t δ ∈ U

/-- **An arc** of the region `U` of `F`: the open key interval from `a` to `b` (cyclic,
`sideInArc`) contains no cut and faces `U` at every non-vertex key; its ends are cuts (or, for
the empty submap, the arc is the whole walk and `a = b = 0`: the key is pinned, since
`sideInArc a a x ↔ x ≠ a` would otherwise make every key the start of an arc — review finding
F1).  Zero-length arcs are not arcs in this
sense (they carry no weight and are represented through the exit chords). -/
def IsArc (F : Set (Set Point)) (U : Set Point) (a b : ℝ) : Prop :=
  0 ≤ a ∧ a < M.W.n ∧ 0 ≤ b ∧ b < M.W.n ∧
    ((M.IsCut F a ∧ M.IsCut F b ∧ a ≠ b) ∨ (F = ∅ ∧ a = 0 ∧ b = 0)) ∧
    (∀ x, sideInArc a b x → ¬ M.IsCut F x) ∧
    (∀ p : ℕ, ∀ t : ℝ, p < M.W.n → 0 < t → t < 1 → sideInArc a b (p + t) → M.Faces p t U)

/-- The number of counted walk edges met by the open key interval `(a, b)`. -/
noncomputable def arcWt (a b : ℝ) : ℕ :=
  {p : ℕ | p < M.W.n ∧ M.counted p ∧ ∃ t : ℝ, 0 < t ∧ t < 1 ∧ sideInArc a b (p + t)}.ncard

section
variable (F : Set (Set Point))
include F
/-- **The weight** of a region (p. 494): the maximum number of counted edges on one of its arcs. -/
noncomputable def weight (U : Set Point) : ℕ :=
  sSup ((fun ab : ℝ × ℝ => M.arcWt ab.1 ab.2) '' {ab | M.IsArc F U ab.1 ab.2})


/-- Regions have at most `d` exit chords (the bounded-degree relaxation used between the fusion
and the restoration of conformality, p. 508). -/
def DegLe (d : ℕ) : Prop := ∀ U ∈ M.regions F, M.deg F U ≤ d

/-- **γ-semigranular** (condition (i), p. 496). -/
def Semigranular (γ : ℕ) : Prop := ∀ U ∈ M.regions F, M.weight F U ≤ γ

/-- **Condition (ii)** of γ-granularity (p. 496): contracting a tree edge incident upon a node of
degree `< 3` produces a region of weight `> γ`. -/
def ContractionCond (γ : ℕ) : Prop :=
  ∀ c ∈ F, ∀ U ∈ M.regions F, ∀ V ∈ M.regions F, U ≠ V → TouchesIn M.D c U →
    TouchesIn M.D c V → (M.deg F U < 3 ∨ M.deg F V < 3) →
      ∀ W' ∈ M.regions (F \ {c}), U ⊆ W' → γ < M.weight (F \ {c}) W'

/-- **γ-granular** (p. 496). -/
def Granular (γ : ℕ) : Prop := M.Semigranular F γ ∧ M.ContractionCond F γ


end

section
variable {F : Set (Set Point)}
theorem Granular.semigranular {γ : ℕ} (h : M.Granular F γ) :
    M.Semigranular F γ := h.1



end

/-- The number of counted walk edges (the size of the curve: `2 m` for a chain, `n` for the
interior of a polygon). -/
noncomputable def size : ℕ := {p : ℕ | p < M.W.n ∧ M.counted p}.ncard

/-- The full visibility map of the model has degree at most `D`, also after adding any finite
admissible family (the augmented map of p. 493); Lemma 3.3 needs this bound. -/
def FullDegLe (Q : Polygon) (D : ℕ) : Prop :=
  ∀ F, M.ChordFamily Q F → M.DegLe (M.Full ∪ F) D

theorem DegLe.mono {F : Set (Set Point)} {d d' : ℕ} (h : M.DegLe F d) (hd : d ≤ d') :
    M.DegLe F d' := fun U hU => (h U hU).trans hd

end Model

end

end Chazelle.Core
