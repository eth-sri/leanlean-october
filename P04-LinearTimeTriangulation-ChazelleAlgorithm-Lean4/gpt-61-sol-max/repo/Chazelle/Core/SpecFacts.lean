module

public import Chazelle.Core.SpecNF

/-!
# Core specification, part 4b: geometric facts about the disk models (work package WP-B)

The purely mathematical obligations on which the procedures rest, stated for every **good model**
(a chain model of a chain of a simple host polygon, or the interior model of a simple polygon).
Each is a `Prop`; WP-B proves them from the existing library (`Chazelle.Chain.*`,
`Chazelle.Merge.*`, `Chazelle.Visibility.*`); the other packages assume them as hypotheses.

* `TopIdxSpec` — `Chain.topIdx` is the *least* index of a topmost vertex (a one-definition change
  in `Chazelle/Chain/Basic.lean`: `Nat.find` instead of `Classical.choose`).  Needed so that the
  machine can compute the walk of a chain whose top is attained twice (host curves of the down
  phase, whose chord edges are horizontal).
* `CutStructureSpec` — the combinatorial Lemmas 2.1–2.2: every non-cut walk position faces exactly
  one region, every region is faced, and two positions face the same region iff no chord
  separates their keys (parenthesis structure).  This is what `BuildNFSpec` computes with a stack.
* `ArcsPerRegionSpec` — a region with `d` exit chords has at most `d + 1` arcs (arcs and exit
  chords alternate; second half of Lemma 2.3 with `Model.weight`).
* `Lemma23Spec` — Lemma 2.3 (count) for every good model, admissible (augmented) families and
  any degree cap `D`, with an explicit constant `c D`.
* `FullDegSpec` — the full (augmented) visibility map of a chain of `Q` and of the interior of `Q`
  has degree at most `4` (distinct heights, p. 495).
* `BoxTransportSpec` — normal-form validity depends on a chain only through its vertex sequence
  (not on the host polygon's bounding box): canonical submaps computed for a sub-chain of `Q` are
  canonical submaps of the same curve seen as a sub-chain of a host curve `R*`.
-/

namespace Chazelle.Core

@[expose] public section

open Chazelle.Chain (SideAttach sideInArc)
open Filter Topology

/-- A good model. -/
def GoodModel (M : Model) : Prop :=
  (∃ C : Chain, C.P.Simple ∧ M = chainModel C) ∨ (∃ Q : Polygon, Q.Simple ∧ M = interiorModel Q)

/-- The chord `c` separates the keys `x` and `x'`: it is attached at two distinct points whose
keys cut the walk into two arcs, one containing `x` and the other `x'`. -/
def Model.Separates (M : Model) (c : Set Point) (x x' : ℝ) : Prop :=
  ∃ (pa pb : ℕ) (ta tb : ℝ), SideAttach M.W c pa ta ∧ SideAttach M.W c pb tb ∧
    Geometry.lerp (M.wa pa) (M.wb pa) ta ≠ Geometry.lerp (M.wa pb) (M.wb pb) tb ∧
    (sideInArc (pa + ta) (pb + tb) x ↔ ¬ sideInArc (pa + ta) (pb + tb) x')

/-- **WP-B: the cut structure** (combinatorial Lemmas 2.1 and 2.2).  The third clause is for
non-cut positions only (review finding B1: a position at a cut key lies in neither arc of a
separating chord, which made the unrestricted statement false). -/
def CutStructureSpec : Prop :=
  ∀ (M : Model) (Q : Polygon) (F : Set (Set Point)), GoodModel M → M.ChordFamily Q F →
    (∀ (p : ℕ) (t : ℝ), p < M.W.n → 0 < t → t < 1 → ¬ M.IsCut F (p + t) →
      ∃! U, U ∈ M.regions F ∧ M.Faces p t U) ∧
    (∀ U ∈ M.regions F, ∃ (p : ℕ) (t : ℝ), p < M.W.n ∧ 0 < t ∧ t < 1 ∧ M.Faces p t U) ∧
    (∀ (p p' : ℕ) (t t' : ℝ) (U U' : Set Point), U ∈ M.regions F → U' ∈ M.regions F →
      p < M.W.n → p' < M.W.n → 0 < t → t < 1 → 0 < t' → t' < 1 →
      ¬ M.IsCut F (p + t) → ¬ M.IsCut F (p' + t') →
      M.Faces p t U → M.Faces p' t' U' →
        (U = U' ↔ ∀ c ∈ F, ¬ M.Separates c (p + t) (p' + t')))

/-- **WP-B: arcs and exit chords alternate** (at most `d + 1` arcs for `d` exit chords). -/
def ArcsPerRegionSpec : Prop :=
  ∀ (M : Model) (Q : Polygon) (F : Set (Set Point)), GoodModel M → M.ChordFamily Q F →
    ∀ U ∈ M.regions F, {ab : ℝ × ℝ | M.IsArc F U ab.1 ab.2}.Finite ∧
      {ab : ℝ × ℝ | M.IsArc F U ab.1 ab.2}.ncard ≤ M.deg F U + 1

/-- **WP-B: Lemma 2.3** (region count) for good models, augmented families, degree cap `D`. -/
def Lemma23Spec : Prop :=
  ∃ c : ℕ → ℕ, ∀ (M : Model) (Q : Polygon) (F : Set (Set Point)) (γ D : ℕ), GoodModel M →
    M.ChordFamily Q F → M.DegLe F D → M.Granular F γ → F.ncard * (γ + 1) ≤ c D * (M.size + 1)

/-- **WP-B: degree `≤ 4`** of the full augmented maps of the geometry polygon (distinct heights). -/
def FullDegSpec : Prop :=
  ∀ P : Polygon, P.Simple → (∃ ε, GoodShear P ε) →
    (∀ C : Chain, C.P = Qof P → (chainModel C).FullDegLe (Qof P) 4) ∧
      (interiorModel (Qof P)).FullDegLe (Qof P) 4

/-! ### Added in review (finding C5): the facts `BuildNFSpec` and `DecompSpec` rest on -/

/-- **WP-B: the two sides of a chord.**  Every chord of an admissible family has two distinct
side regions: the region just above its open part and the region just below; these are exactly
the regions the chord touches. -/
def ChordSidesSpec : Prop :=
  ∀ (M : Model) (Q : Polygon) (F : Set (Set Point)), GoodModel M → M.ChordFamily Q F →
    ∀ c ∈ F, ∃ U V, U ∈ M.regions F ∧ V ∈ M.regions F ∧ U ≠ V ∧
      (∀ z ∈ c, z ∈ M.D → ∀ᶠ δ in 𝓝[>] (0 : ℝ), (z.1, z.2 + δ) ∈ U ∧ (z.1, z.2 - δ) ∈ V) ∧
      (∀ W ∈ M.regions F, Chazelle.Chain.TouchesIn M.D c W ↔ W = U ∨ W = V)

/-- **WP-B: the region–chord graph is a tree** (Lemma 2.2): finitely many regions, one more than
chords, and any two regions are joined by a path of regions consecutive ones sharing a chord. -/
def RegionTreeSpec : Prop :=
  ∀ (M : Model) (Q : Polygon) (F : Set (Set Point)), GoodModel M → M.ChordFamily Q F →
    (M.regions F).Finite ∧ (M.regions F).ncard = F.ncard + 1 ∧
      ∀ U ∈ M.regions F, ∀ V ∈ M.regions F,
        Relation.ReflTransGen (fun A B => ∃ c ∈ F, Chazelle.Chain.TouchesIn M.D c A ∧
          Chazelle.Chain.TouchesIn M.D c B) U V

/-! ### Added in the consolidated revision (findings C9, C10) -/

section
variable (M : Model) (c U : Set Point)
include M c U
/-- `U` contains the points just **above** every point of the chord `c` in the domain. -/
def Model.AboveOf : Prop :=
  ∀ z ∈ c, z ∈ M.D → ∀ᶠ δ in 𝓝[>] (0 : ℝ), ((z.1, z.2 + δ) : Point) ∈ U

/-- `U` contains the points just **below** every point of the chord `c` in the domain. -/
def Model.BelowOf : Prop :=
  ∀ z ∈ c, z ∈ M.D → ∀ᶠ δ in 𝓝[>] (0 : ℝ), ((z.1, z.2 - δ) : Point) ∈ U


end

/-- **WP-B (finding C10): the side faced after an attachment.**  For a chord `c` of an admissible
family `F` of a good model, attached at the walk position `(p, t)` at which no other chord of `F`
is attached, let `U` be the region faced by the walk just after that position and `V` the region
faced just before (cyclically, as in `AttachFaceSpec`).  If the point of the position is the
**left** (lower-`x`) endpoint of `c`, then `U` is the region **below** `c` and `V` the region
**above**; if it is the **right** endpoint, `U` is above and `V` below. -/
def UpSideSpec : Prop :=
  ∀ (M : Model) (Q : Polygon) (F : Set (Set Point)), GoodModel M → M.ChordFamily Q F →
    ∀ c ∈ F, ∀ (p : ℕ) (t : ℝ), SideAttach M.W c p t →
      (∀ c' ∈ F, SideAttach M.W c' p t → c' = c) →
      ∃ U V, U ∈ M.regions F ∧ V ∈ M.regions F ∧ U ≠ V ∧
        (∃ δ > (0 : ℝ), ∀ (p' : ℕ) (t' : ℝ), p' < M.W.n → 0 < t' → t' < 1 →
          ((0 < (p' : ℝ) + t' - (p + t) ∧ (p' : ℝ) + t' - (p + t) < δ) ∨
              (0 < (p' : ℝ) + t' + M.W.n - (p + t) ∧ (p' : ℝ) + t' + M.W.n - (p + t) < δ) →
            M.Faces p' t' U) ∧
          ((0 < (p + t) - ((p' : ℝ) + t') ∧ (p + t) - ((p' : ℝ) + t') < δ) ∨
              (0 < (p + t) + M.W.n - ((p' : ℝ) + t') ∧ (p + t) + M.W.n - ((p' : ℝ) + t') < δ) →
            M.Faces p' t' V)) ∧
        ((∀ z ∈ c, (Geometry.lerp (M.wa p) (M.wb p) t).1 ≤ z.1) → M.BelowOf c U ∧ M.AboveOf c V) ∧
        ((∀ z ∈ c, z.1 ≤ (Geometry.lerp (M.wa p) (M.wb p) t).1) → M.AboveOf c U ∧ M.BelowOf c V)

/-- **WP-B (finding C9, proved as `arcCover`): every chord family of a good model has an arc,
and every cut key is the start of an arc** (of the region the walk faces just after it).  Used by
double identification. -/
def NFLoc.ArcCoverSpec : Prop :=
  ∀ (M : Model) (Q : Polygon) (F : Set (Set Point)), GoodModel M → M.ChordFamily Q F →
    (∃ U ∈ M.regions F, ∃ a b : ℝ, M.IsArc F U a b) ∧
      ∀ y : ℝ, M.IsCut F y → ∃ U ∈ M.regions F, ∃ b : ℝ, M.IsArc F U y b

end

end Chazelle.Core
