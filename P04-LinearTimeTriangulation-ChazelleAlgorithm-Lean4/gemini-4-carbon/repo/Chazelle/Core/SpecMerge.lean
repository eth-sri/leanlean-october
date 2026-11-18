module

public import Chazelle.Core.SpecKernels
public import Chazelle.Core.SpecFacts

/-!
# Core specification, part 4c: merging two submaps (Chazelle §3, Lemmas 3.1–3.5)

RAM-level interfaces of the merge procedures (design doc §4.2–4.5), in the **consolidated
revision** (design doc §10; the merge-layer redesign `docs/design-merge-v2.md`, adopted with the
changes of its independent review `docs/merge-v2-review-independent.md`).  A merge works on a
**junction** `J` (`Chazelle.Merge.Junction`) of two adjacent chains of a host polygon
`J.P = H.poly (Qof P)` (the geometry polygon itself in the up phase, a region boundary `R*` in the
down phase), given by three chain descriptors.  The procedures that shoot rays or cut arcs are
**parametrised by the oracle statements** (`ShooterOK`, `CutterOK`): `mk sh cu` inlines them, and
the specification holds for every oracle meeting its interface, so that WP-D/E/F need not wait for
WP-G/H.

## The merge-layer decision (finding D1)

The formal chain model has no null-length chords, so the fusion of two γ-semigranular submaps is
*not* γ-semigranular (design doc §9.5).  Option 2 of §9.6 is adopted:

* the fusion adds a bounded set of **glue chords** (`glueChords`): the vertex chords at the tops
  of `C₁` and `C₂` (where their slits were) and, when the shared vertex is a local extremum of
  `C`, one **cap chord** shot from the higher arm at the height of the lower neighbour into the
  inner sector;
* the fused submap is then `(γ + fuseLoss)`-semigranular with `fuseLoss = 1`, provided the three
  vertices around the shared vertex have pairwise distinct heights (`SharedGeneric`, automatic
  for chains of the geometry polygon; for the down phase see `DownPhaseSpec`, rule M2);
* a merge therefore requires a target `γ ≥ γ₀ + fuseLoss`, and the canonical granularity schedule
  becomes `gradeGran λ = 2^⌈βλ⌉ + fuseLoss · λ (⌈log₂ λ⌉ + 2)` (`SpecPhases`).

## Contents

* Combinatorial lemmas on arcs (proved): `isCut_mono`, `arcWt_mono`, `sideInArc_split`,
  `arcWt_le_split`, `arcWt_le_split_vertex` — the counting core of the `γ + 1` bound.
* The glue chords: `topChords`, `capChords`, `glueChords`, `SharedGeneric`, `fusion_empty`.
* Mathematical obligations of WP-D: `FusionWeightSpec`, `FusionDegSpec` (finding D4).
* RAM contracts: `SweepSpec` (WP-D, the sweep of pp. 503–507 as a procedure with query points),
  `FuseSpec` (WP-D, Lemma 3.1 with glue chords), `RestoreSpec` (WP-E), `GranularizeSpec` (WP-F),
  `MergeSpec` (WP-F, Lemma 3.5).  All normal-form inputs are readable below the allocator
  (`NFWithin`), all descriptors are well formed and below the allocator (`ChainWF`,
  `ModelDescWF`, `JunctionWF`), and the word bound admits host index arithmetic (`hostWords`)
  (review M1: findings C6–C8 folded in).
-/

namespace Chazelle.Core

@[expose] public section

open Chazelle.Machine (Stmt)
open Chazelle.Chain (SideAttach sideInArc)

/-! ## Combinatorics of arcs -/

namespace Model

variable (M : Model)

/-- More chords, more cuts. -/
theorem isCut_mono {F F' : Set (Set Point)} (h : F ⊆ F') {x : ℝ} (hx : M.IsCut F x) :
    M.IsCut F' x := by
  obtain ⟨c, hc, p, t, ha, rfl⟩ := hx
  exact ⟨c, h hc, p, t, ha, rfl⟩

/-- The set of counted walk edges met by the open key interval `(a, b)`. -/
def arcEdges (a b : ℝ) : Set ℕ :=
  {p : ℕ | p < M.W.n ∧ M.counted p ∧ ∃ t : ℝ, 0 < t ∧ t < 1 ∧ sideInArc a b (p + t)}

theorem arcWt_eq (a b : ℝ) : M.arcWt a b = (M.arcEdges a b).ncard := rfl

theorem arcEdges_finite (a b : ℝ) : (M.arcEdges a b).Finite :=
  (Set.finite_lt_nat M.W.n).subset fun _ hp => hp.1

/-- A smaller key interval meets fewer counted edges. -/
theorem arcWt_mono {a b a' b' : ℝ} (h : ∀ x, sideInArc a' b' x → sideInArc a b x) :
    M.arcWt a' b' ≤ M.arcWt a b := by
  rw [arcWt_eq, arcWt_eq]
  refine Set.ncard_le_ncard ?_ (M.arcEdges_finite a b)
  rintro p ⟨hp, hc, t, ht0, ht1, hx⟩
  exact ⟨hp, hc, t, ht0, ht1, h _ hx⟩

end Model

/-- **Splitting a cyclic interval at an inner key** `g`: a key of `(a, b)` lies in `(a, g)`, is
`g`, or lies in `(g, b)`. -/
theorem sideInArc_split {a b g x : ℝ} (hx : sideInArc a b x) (hg : sideInArc a b g) :
    sideInArc a g x ∨ x = g ∨ sideInArc g b x := by
  unfold sideInArc at *
  by_cases hab : a < b
  · simp only [hab, ↓reduceIte] at hx hg
    rcases lt_trichotomy x g with h | h | h
    · left; simp only [hg.1, ↓reduceIte]; exact ⟨hx.1, h⟩
    · exact Or.inr (Or.inl h)
    · right; right; simp only [hg.2, ↓reduceIte]; exact ⟨h, hx.2⟩
  · simp only [hab, ↓reduceIte] at hx hg
    by_cases hag : a < g
    · have hgb : ¬ g < b := fun h => hab (lt_trans hag h)
      rcases hx with hx | hx
      · rcases lt_trichotomy x g with h | h | h
        · left; simp only [hag, ↓reduceIte]; exact ⟨hx, h⟩
        · exact Or.inr (Or.inl h)
        · right; right; simp only [hgb, ↓reduceIte]; exact Or.inl h
      · right; right; simp only [hgb, ↓reduceIte]; exact Or.inr hx
    · have hgb : g < b := hg.resolve_left hag
      rcases hx with hx | hx
      · left; simp only [hag, ↓reduceIte]; exact Or.inl hx
      · rcases lt_trichotomy x g with h | h | h
        · left; simp only [hag, ↓reduceIte]; exact Or.inr h
        · exact Or.inr (Or.inl h)
        · right; right; simp only [hgb, ↓reduceIte]; exact ⟨h, hx⟩

namespace Model

variable (M : Model)

/-- The walk edges whose open part contains the key `g` (at most one). -/
def keyEdges (g : ℝ) : Set ℕ := {p : ℕ | ∃ t : ℝ, 0 < t ∧ t < 1 ∧ (p : ℝ) + t = g}

/-- A natural key is the open part of no walk edge. -/
theorem keyEdges_natCast (k : ℕ) : keyEdges (k : ℝ) = ∅ := by
  ext p
  simp only [keyEdges, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_and]
  intro t ht0 ht1 hp
  have h1 : (p : ℝ) < k := by linarith
  have h2 : (k : ℝ) < p + 1 := by linarith
  have h1' : p < k := by exact_mod_cast h1
  have h2' : k < p + 1 := by exact_mod_cast h2
  omega

theorem arcEdges_subset_split {a b g : ℝ} (hg : sideInArc a b g) :
    M.arcEdges a b ⊆ M.arcEdges a g ∪ M.arcEdges g b ∪ keyEdges g := by
  rintro p ⟨hp, hc, t, ht0, ht1, hx⟩
  rcases sideInArc_split hx hg with h | h | h
  · exact Or.inl (Or.inl ⟨hp, hc, t, ht0, ht1, h⟩)
  · exact Or.inr ⟨t, ht0, ht1, h⟩
  · exact Or.inl (Or.inr ⟨hp, hc, t, ht0, ht1, h⟩)

/-- **Cutting at a vertex key loses nothing**: for a natural key `k` inside `(a, b)`,
`arcWt a b ≤ arcWt a k + arcWt k b`. -/
theorem arcWt_le_split_vertex {a b : ℝ} {k : ℕ} (hg : sideInArc a b k) :
    M.arcWt a b ≤ M.arcWt a k + M.arcWt k b := by
  rw [arcWt_eq, arcWt_eq, arcWt_eq]
  have hsub := M.arcEdges_subset_split hg
  rw [keyEdges_natCast, Set.union_empty] at hsub
  calc (M.arcEdges a b).ncard ≤ (M.arcEdges a k ∪ M.arcEdges k b).ncard :=
        Set.ncard_le_ncard hsub ((M.arcEdges_finite a k).union (M.arcEdges_finite k b))
    _ ≤ (M.arcEdges a k).ncard + (M.arcEdges k b).ncard := Set.ncard_union_le _ _

end Model

/-! ## The glue chords of a junction -/

section Glue

variable (J : Merge.Junction)

/-- The shared vertex `v = C₁ ∩ C₂` (vertex `m₁` of `C`). -/
noncomputable def sharedV : Point := J.whole.vertex J.m₁

/-- The neighbour of the shared vertex on `C₁` (vertex `m₁ - 1` of `C`). -/
noncomputable def sharedU : Point := J.whole.vertex (J.m₁ - 1)

/-- The neighbour of the shared vertex on `C₂` (vertex `m₁ + 1` of `C`). -/
noncomputable def sharedW : Point := J.whole.vertex (J.m₁ + 1)

/-- **Genericity at the shared vertex**: the shared vertex and its two neighbours have pairwise
distinct heights.  Automatic for chains of the geometry polygon (distinct heights); an
obligation of the down phase for the junctions of region boundaries `R*`. -/
def SharedGeneric : Prop :=
  (sharedU J).2 ≠ (sharedV J).2 ∧ (sharedW J).2 ≠ (sharedV J).2 ∧ (sharedU J).2 ≠ (sharedW J).2

/-- The shared vertex is a local extremum of `C` (both neighbours strictly above, or both
strictly below): then one of its two companions on the walk of `C` (the *inner* one, where the
paper puts a null-length chord) has no horizontal direction in its sector. -/
def SharedExtremum : Prop :=
  0 < ((sharedU J).2 - (sharedV J).2) * ((sharedW J).2 - (sharedV J).2)

/-- The neighbour of the shared vertex nearer in height ("lower arm" of the extremum). -/
noncomputable def capNear : Point :=
  if |(sharedU J).2 - (sharedV J).2| < |(sharedW J).2 - (sharedV J).2| then sharedU J
  else sharedW J

/-- The other neighbour ("higher arm"). -/
noncomputable def capFar : Point :=
  if |(sharedU J).2 - (sharedV J).2| < |(sharedW J).2 - (sharedV J).2| then sharedW J
  else sharedU J

/-- **The origin of the cap chord**: the point of the higher arm `[v, far]` at the height of the
nearer neighbour (an interior point of that edge under `SharedGeneric`, and a symbolic point
`onEdge` of the host). -/
noncomputable def capOrigin : Point :=
  Geometry.lerp (sharedV J) (capFar J)
    (((capNear J).2 - (sharedV J).2) / ((capFar J).2 - (sharedV J).2))

/-- The direction of the cap chord: horizontally from the higher arm towards the nearer
neighbour, i.e. into the inner sector of the extremum. -/
noncomputable def capDir : ℝ := if (capNear J).1 < (capOrigin J).1 then -1 else 1

/-- **The cap chord** (at most one): when the shared vertex is a local extremum of `C`, the chord
of `C` shot from `capOrigin` in direction `capDir`.  It is attached on the walk edge adjacent to
the inner companion of the shared vertex, which bounds the arc through that companion by one
edge on that side (design doc `design-merge-v2.md` §2). -/
def capChords : Set (Set Point) :=
  {d | SharedExtremum J ∧ Merge.FreeAt J.whole (capOrigin J) (capDir J) ∧
    d = Merge.shoot J.whole (capOrigin J) (capDir J)}

/-- The indices (in `C`) of the tops of `C₁` and `C₂`: where their slits were. -/
noncomputable def topIdxs : Finset ℕ := {J.left.topIdx, J.m₁ + J.right.topIdx}

/-- **The top chords**: the vertex chords of `C` at the tops of `C₁` and `C₂` (at most four).  The
copy of a top vertex that carried the slit of `C₁` (resp. `C₂`) is a single walk position of
`C` whose sector contains a free horizontal direction, so these chords make it a cut. -/
def topChords : Set (Set Point) :=
  {d | ∃ k ∈ topIdxs J, ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ J.whole.DirFree k σ ∧
    d = J.whole.chordSet k σ}

/-- **The glue chords** added by the revised fusion. -/
def glueChords : Set (Set Point) := topChords J ∪ capChords J

theorem capChords_subsingleton : (capChords J).Subsingleton := by
  rintro d ⟨-, -, rfl⟩ e ⟨-, -, rfl⟩
  rfl

theorem topChords_subset_chords : topChords J ⊆ J.whole.chords := by
  rintro d ⟨k, hk, σ, hσ, hf, rfl⟩
  refine ⟨k, σ, ?_, hσ, hf, rfl⟩
  simp only [topIdxs, Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with rfl | rfl
  · have := J.left.topIdx_le
    simp only [Merge.Junction.whole_m, Merge.Junction.left_m] at this ⊢
    omega
  · have := J.right.topIdx_le
    simp only [Merge.Junction.whole_m, Merge.Junction.right_m] at this ⊢
    omega

theorem topChords_finite : (topChords J).Finite :=
  J.whole.chords_finite.subset (topChords_subset_chords J)

theorem glueChords_finite : (glueChords J).Finite :=
  (topChords_finite J).union (capChords_subsingleton J).finite

end Glue

/-! ## The revised mathematical obligations of WP-D -/

/-- The additive granularity loss of one fusion (`c₀` of design doc §9.6, option 2). -/
def fuseLoss : ℕ := 1

/-- **WP-D (math), the weight bound of the revised fusion.**  The fusion of a γ-semigranular
submap of `C₁` and one of `C₂`, together with the glue chords, is `(γ + 1)`-semigranular.
Paper proof in `docs/design-merge-v2.md` §2: every arc of the result avoiding the inner companion
of the shared vertex lies, cut for cut, inside an arc of `S₁` or of `S₂`; the arc through the
inner companion is that plus the part of one walk edge up to the cap chord
(`Model.arcWt_le_split_vertex`).  The missing library lemma is a *walk embedding* (design
`design-merge-v2.md` §8, O1).  (Review m1: the former hypothesis `HeightsIn Q J.whole` is not used
by the argument and was dropped.) -/
def FusionWeightSpec : Prop :=
  ∀ (J : Merge.Junction) (Q : Polygon) (S₁ S₂ : Set (Set Point)) (γ : ℕ),
    J.P.Simple → SharedGeneric J →
    (chainModel J.left).ChordFamily Q S₁ → (chainModel J.right).ChordFamily Q S₂ →
    (chainModel J.left).Semigranular S₁ γ → (chainModel J.right).Semigranular S₂ γ →
    (chainModel J.whole).Semigranular (J.fusion S₁ S₂ ∪ glueChords J) (γ + fuseLoss)

/-- **WP-D (math), the degree bound (finding D4).**  The degree of the revised fusion is bounded
by a function of the degree bound of the inputs.  The paper (p. 508) gives two runs of at most
four exit chords each; `docs/design-merge-v2.md` §4 sketches `capF D = 2 D + 13` in the formal
model.  Stated existentially: only `RestoreSpec`'s cost constant `κ d₀ D` depends on it.  (Review m1:
`HeightsIn` dropped; review m3: the sketch covers shared, top and cap chords with both ends on
one side.) -/
def FusionDegSpec : Prop :=
  ∃ capF : ℕ → ℕ, ∀ (J : Merge.Junction) (Q : Polygon) (S₁ S₂ : Set (Set Point)) (D : ℕ),
    J.P.Simple → SharedGeneric J →
    (chainModel J.left).ChordFamily Q S₁ → (chainModel J.right).ChordFamily Q S₂ →
    (chainModel J.left).DegLe S₁ D → (chainModel J.right).DegLe S₂ D →
    (chainModel J.whole).DegLe (J.fusion S₁ S₂ ∪ glueChords J) (capF D)

/-! ## RAM contracts -/

/-- Three chain descriptors describe the left, right and whole chains of a junction. -/
def JunctionAt (m : ℕ → ℕ) (bl br bw : ℕ) (Q : Polygon) (H : Host) (J : Merge.Junction) : Prop :=
  ChainDescAt m bl Q H J.left ∧ ChainDescAt m br Q H J.right ∧ ChainDescAt m bw Q H J.whole

/-- **Well-formed junction descriptors** below `E` (review M1, findings C7/C8): the three chain
descriptors are well formed (`ChainWF`: at most `64` host items, items in range, start in range)
and stored below `E`.  With in-range host items every host point has a vertex height of `Q`, so
the cap chord (at the height of a host neighbour of the shared vertex) has a normal-form record
(M1's counterexample: an item `.pt (.onEdge e h)` with `h ≥ n`). -/
def JunctionWF (P : Polygon) (E : ℕ) (m : ℕ → ℕ) (bl br bw : ℕ) : Prop :=
  ChainWF P E m bl ∧ ChainWF P E m br ∧ ChainWF P E m bw ∧
    ∀ H : Host, HostAt m (m bw) H → HostRegular P.n H

/-- A list of result quadruples `(flag, h, lp, rp)` at `A`, four words each. -/
def ResultListAt (m : ℕ → ℕ) (A : ℕ) (R : List (ℕ × ℕ × ℕ × ℕ)) : Prop :=
  ∀ i, i < R.length →
    m (A + 4 * i) = (R.getD i (0, 0, 0, 0)).1 ∧ m (A + 4 * i + 1) = (R.getD i (0, 0, 0, 0)).2.1 ∧
      m (A + 4 * i + 2) = (R.getD i (0, 0, 0, 0)).2.2.1 ∧
      m (A + 4 * i + 3) = (R.getD i (0, 0, 0, 0)).2.2.2

/-- The chain on side `i` of a junction (`0`: `C₁`, otherwise `C₂`). -/
def sideChain (J : Merge.Junction) (i : ℕ) : Chain := if i = 0 then J.left else J.right

/-- A sweep query `(edge, height code, direction code)`: a walk position of the chain model of
side `i`, with a height code `≥ 1` and a parameter in `[0, 1)` (review finding C2), at a height
not above the top of that chain (so that the chord it sees is an augmented chord of `C`), whose
direction points into the left sector of the walk at the position, i.e. into the query's own
side of the chain (review of the merge redesign, m2: otherwise the local shooting would have to
use the companion walk edge). -/
def QueryOK (J : Merge.Junction) (Q : Polygon) (i : ℕ) (q : ℕ × ℕ × ℕ) : Prop :=
  let M := chainModel (sideChain J i)
  let z := M.pos Q ⟨q.1, q.2.1⟩
  q.1 < M.W.n ∧ 1 ≤ q.2.1 ∧ q.2.1 ≤ Q.n ∧ 0 ≤ M.param Q ⟨q.1, q.2.1⟩ ∧
    M.param Q ⟨q.1, q.2.1⟩ < 1 ∧ z.2 ≤ (sideChain J i).top.2 ∧
    Chazelle.Chain.sideLeft M.W q.1 (M.param Q ⟨q.1, q.2.1⟩) (z.1 + dirOf q.2.2, z.2)

/-- **The endpoint queries of a chord list** (finding S-1): two queries per record, from its left
end to the east (`(lp, h + 1, 1)`) and from its right end to the west (`(rp, h + 1, 0)`). -/
def sweepEndQ (cs : List CRec) : List (ℕ × ℕ × ℕ) :=
  (List.range (2 * cs.length)).map fun j =>
    let r := cs.getD (j / 2) ⟨0, 0, 0, 0, 0⟩
    if j % 2 = 0 then (r.lp, r.h + 1, 1) else (r.rp, r.h + 1, 0)

/-- **What a query point sees in `C`**: the result flag is `1` iff the direction is free for `C`
at the point, and then the triple is a correctly attached record of the chord of `C` seen from
the point (`Merge.shoot`). -/
def SeesInWhole (J : Merge.Junction) (Q : Polygon) (i : ℕ) (q : ℕ × ℕ × ℕ)
    (r : ℕ × ℕ × ℕ × ℕ) : Prop :=
  let z := (chainModel (sideChain J i)).pos Q ⟨q.1, q.2.1⟩
  (r.1 = 1 ↔ Merge.FreeAt J.whole z (dirOf q.2.2)) ∧
    (r.1 = 1 → (recOf r.2).toSet (chainModel J.whole) Q = Merge.shoot J.whole z (dirOf q.2.2) ∧
      (recOf r.2).Attached (chainModel J.whole) Q)

/-- **WP-D: the fusion** (Lemma 3.1 with glue chords).  Registers of band `bFuse`: `0, 1, 2`
junction descriptors, `3, 4` normal forms of `S₁`, `S₂`, `5` a bound `γ` on their weights, `6` a
bound `D` on their degrees, `8` the oracle context handle; output `7`: the normal form of
`J.fusion S₁ S₂ ∪ glueChords J`.  Findings D1–D4:
* the output is `(γ + fuseLoss)`-semigranular (D1), with at most `2 (K₁ + K₂) + 7` chords;
* the degree cap is `capF D` for a fixed function `capF` (D4; `FusionDegSpec`);
* `Ok` for the whole chain and `SharedGeneric J` are assumed (D3; the sweeps only shoot in the
  models of `C₁`, `C₂`);
* the cost uses `⌈log₂ (K₁ + K₂ + 1)⌉` (the sort of `BuildNF`) and a constant `κ D` (D2). -/
def FuseSpec : Prop :=
  ∃ (mk : Stmt → Stmt) (κ capF : ℕ → ℕ), ∀ (sh : Stmt) (Bs : Finset ℕ) (F : ℕ → ℕ)
    (X : MemCtx) (Ok : Polygon → Model → Prop), X.CapLocal → Bs ⊆ oracleBands →
    ShooterOK sh Bs F X Ok →
    Meets (mk sh) (fuseBands ∪ oracleBands)
      (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧
        X.holds P c.nmem (rd c bFuse 8) (c.nreg ALLOC) ∧
        rd c bFuse 5 ≤ X.cap P c.nmem (rd c bFuse 8) ∧
        JunctionWF P (c.nreg ALLOC) c.nmem (rd c bFuse 0) (rd c bFuse 1) (rd c bFuse 2) ∧
        ∃ H J N₁ N₂, JunctionAt c.nmem (rd c bFuse 0) (rd c bFuse 1) (rd c bFuse 2) (Qof P) H J ∧
          J.P.Simple ∧ SharedGeneric J ∧ Ok P (chainModel J.left) ∧ Ok P (chainModel J.right) ∧
          Ok P (chainModel J.whole) ∧
          NFWithin c.nmem (rd c bFuse 3) (c.nreg ALLOC) N₁ ∧
          NFWithin c.nmem (rd c bFuse 4) (c.nreg ALLOC) N₂ ∧
          IsNF (chainModel J.left) (Qof P) N₁ ∧ IsNF (chainModel J.right) (Qof P) N₂ ∧
          (chainModel J.left).DegLe (N₁.F (chainModel J.left) (Qof P)) (rd c bFuse 6) ∧
          (chainModel J.right).DegLe (N₂.F (chainModel J.right) (Qof P)) (rd c bFuse 6) ∧
          (chainModel J.left).Semigranular (N₁.F (chainModel J.left) (Qof P)) (rd c bFuse 5) ∧
          (chainModel J.right).Semigranular (N₂.F (chainModel J.right) (Qof P)) (rd c bFuse 5))
      (fun P c c' => ∀ H J N₁ N₂,
        JunctionAt c.nmem (rd c bFuse 0) (rd c bFuse 1) (rd c bFuse 2) (Qof P) H J →
        NFAt c.nmem (rd c bFuse 3) N₁ → NFAt c.nmem (rd c bFuse 4) N₂ →
        ∃ N, c.nreg ALLOC ≤ rd c' bFuse 7 ∧ NFWithin c'.nmem (rd c' bFuse 7) (c'.nreg ALLOC) N ∧
          IsNF (chainModel J.whole) (Qof P) N ∧
          N.F (chainModel J.whole) (Qof P) =
            J.fusion (N₁.F (chainModel J.left) (Qof P)) (N₂.F (chainModel J.right) (Qof P)) ∪
              glueChords J ∧
          N.nChords ≤ 2 * (N₁.nChords + N₂.nChords) + 7 ∧
          (chainModel J.whole).DegLe (N.F (chainModel J.whole) (Qof P)) (capF (rd c bFuse 6)) ∧
          (chainModel J.whole).Semigranular (N.F (chainModel J.whole) (Qof P))
            (rd c bFuse 5 + fuseLoss))
      (fun _ c => κ (rd c bFuse 6) * (c.nmem (rd c bFuse 3) + c.nmem (rd c bFuse 4) + 1) *
        (F (rd c bFuse 5) + Nat.clog 2 (c.nmem (rd c bFuse 3) + c.nmem (rd c bFuse 4) + 1) + 1))

/-- The host curves on which the merges run: the geometry polygon itself (up phase) or a region
boundary `R*` of the down phase, described by at most `64` items (arcs of a region of degree
`≤ 4` plus the chord edges tilted into the curve, p. 519). -/
def HostOk (H : Host) : Prop := H.length ≤ 64

/-- The models the oracles serve: chain models of chains of simple, regular host curves
(`HostRegular`, review finding G1: a non-regular host edge carries origins that are neither
symbolic nor box points, from which no oracle query can be issued). -/
def OkModel (P : Polygon) (M : Model) : Prop :=
  ∃ (H : Host) (C : Chain), HostOk H ∧ HostRegular (Qof P).n H ∧ C.P = H.poly (Qof P) ∧
    C.P.Simple ∧ M = chainModel C

/-- **WP-E: restoring conformality** (Lemmas 2.4, 3.2, 3.3, 3.4).  Registers of band `bRestore`:
`0` model descriptor (a chain model or the interior model of `Qof P`), `1` normal form, `2` its
degree bound `d₀`, `3` the target cap `D ≥ 4` (the full augmented map of the model has degree
`≤ D`), `4` its semigranularity `γ`, `6` the context handle; output `5`: a normal form of a finer
submap with degree `≤ D`, still γ-semigranular (restoration only adds chords, so the `γ + 1`
loss of the fusion is not increased), with at most `cR d₀ D (K + 1)` chords (finding F-G3: the
merge's granularity step pays for them).  Cost `κ d₀ D (K + 1) F γ · G γ · (H γ + ⌈log₂ γ⌉ + 1)`. -/
def RestoreSpec : Prop :=
  ∃ (mk : Stmt → Stmt → Stmt) (κ cR : ℕ → ℕ → ℕ), ∀ (sh cu : Stmt)
    (Bs Bc : Finset ℕ) (F G H : ℕ → ℕ) (X : MemCtx) (Ok : Polygon → Model → Prop),
    X.CapLocal → X.Halves → (∀ P M, Ok P M → OkModel P M) →
    Bs ⊆ oracleBands → Bc ⊆ oracleBands → ShooterOK sh Bs F X Ok → CutterOK cu Bc G H X Ok →
    Meets (mk sh cu) (restoreBands ∪ oracleBands)
      (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧
        X.holds P c.nmem (rd c bRestore 6) (c.nreg ALLOC) ∧
        rd c bRestore 4 ≤ X.cap P c.nmem (rd c bRestore 6) ∧ 4 ≤ rd c bRestore 3 ∧
        ModelDescWF P (c.nreg ALLOC) c.nmem (rd c bRestore 0) ∧
        (c.nmem (rd c bRestore 0) = 0 → ∀ H C,
          ChainDescAt c.nmem (rd c bRestore 0 + 1) (Qof P) H C → HostRegular (Qof P).n H) ∧
        (c.nmem (rd c bRestore 0) = 0 → ∀ H C,
          ChainDescAt c.nmem (rd c bRestore 0 + 1) (Qof P) H C → C.P.Simple) ∧
        ∃ M N, ModelDescAt c.nmem (rd c bRestore 0) (Qof P) M ∧ GoodModel M ∧ Ok P M ∧
          M.FullDegLe (Qof P) (rd c bRestore 3) ∧
          NFWithin c.nmem (rd c bRestore 1) (c.nreg ALLOC) N ∧ IsNF M (Qof P) N ∧
          M.DegLe (N.F M (Qof P)) (rd c bRestore 2) ∧
          M.Semigranular (N.F M (Qof P)) (rd c bRestore 4))
      (fun P c c' => ∀ M N, ModelDescAt c.nmem (rd c bRestore 0) (Qof P) M →
        NFAt c.nmem (rd c bRestore 1) N →
        ∃ N', c.nreg ALLOC ≤ rd c' bRestore 5 ∧
          NFWithin c'.nmem (rd c' bRestore 5) (c'.nreg ALLOC) N' ∧ IsNF M (Qof P) N' ∧
          N.F M (Qof P) ⊆ N'.F M (Qof P) ∧ M.DegLe (N'.F M (Qof P)) (rd c bRestore 3) ∧
          M.Semigranular (N'.F M (Qof P)) (rd c bRestore 4) ∧
          N'.nChords ≤ cR (rd c bRestore 2) (rd c bRestore 3) * (N.nChords + 1))
      (fun _ c => κ (rd c bRestore 2) (rd c bRestore 3) * (c.nmem (rd c bRestore 1) + 1) *
        F (rd c bRestore 4) * G (rd c bRestore 4) *
        (H (rd c bRestore 4) + Nat.clog 2 (rd c bRestore 4) +
          Nat.clog 2 (c.nmem (rd c bRestore 1) + 1) + 1))

/-- **WP-F: enforcing granularity** (§3.3; a worklist version, since removing a leaf can lower a
neighbour's degree below `3`: design doc §7) and computing the tree decomposition.  Registers of
band `bGran`: `0` model descriptor, `1` normal form, `2` degree cap `D`, `3` target `γ`; output
`4`: a γ-canonical normal form of a coarser submap.  Cost `κ D (K (⌈log₂ K⌉ + 1) + 1)`. -/
def GranularizeSpec : Prop :=
  ∃ (s : Stmt) (κ : ℕ → ℕ), Meets s granBands
    (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧ 1 ≤ rd c bGran 2 ∧
      ModelDescWF P (c.nreg ALLOC) c.nmem (rd c bGran 0) ∧
      ∃ M N, ModelDescAt c.nmem (rd c bGran 0) (Qof P) M ∧ GoodModel M ∧
        NFWithin c.nmem (rd c bGran 1) (c.nreg ALLOC) N ∧ IsNF M (Qof P) N ∧
        M.DegLe (N.F M (Qof P)) (rd c bGran 2) ∧
        M.Semigranular (N.F M (Qof P)) (rd c bGran 3))
    (fun P c c' => ∀ M N, ModelDescAt c.nmem (rd c bGran 0) (Qof P) M → NFAt c.nmem (rd c bGran 1) N →
      ∃ N', c.nreg ALLOC ≤ rd c' bGran 4 ∧ NFWithin c'.nmem (rd c' bGran 4) (c'.nreg ALLOC) N' ∧
        N'.F M (Qof P) ⊆ N.F M (Qof P) ∧
        IsCanonicalNF M (Qof P) N' (rd c bGran 3) (rd c bGran 2))
    (fun _ c => κ (rd c bGran 2) *
      (c.nmem (rd c bGran 1) * (Nat.clog 2 (c.nmem (rd c bGran 1)) + 1) + 1))

/-- **WP-F: the merge** (Lemma 3.5).  Registers of band `bMerge`: `0, 1, 2` junction descriptors,
`3, 4` γ₁- and γ₂-canonical normal forms of the two chains, `5` a bound `γ₀ ≥ γ₁, γ₂` (review
finding F9: Lemma 3.5 is symmetric), `6` the target `γ ≥ γ₀ + fuseLoss` (the fusion loses
`fuseLoss`, and granularity enforcement only removes chords), `7` the degree cap `D ≥ 4` (the full
augmented map of the union has degree `≤ D`), `9` the oracle context handle; output `8`: a
γ-canonical normal form of the union.  The oracles must serve arcs of weight `γ₀ + fuseLoss`
(restoration runs on the fused map), and the junction is generic at the shared vertex.  Cost
`κ D (K₁ + K₂ + 1) F(γ₀+1) · G(γ₀+1) · (H(γ₀+1) + ⌈log₂ (m + 1)⌉ + 1)` (the inputs are canonical,
so Lemma 2.3 bounds `K₁ + K₂` by `c(D)(m + 1)` and `log K` by `log m + O_D(1)`). -/
def MergeSpec : Prop :=
  ∃ (mk : Stmt → Stmt → Stmt) (κ : ℕ → ℕ), ∀ (sh cu : Stmt)
    (Bs Bc : Finset ℕ) (F G H : ℕ → ℕ) (X : MemCtx) (Ok : Polygon → Model → Prop),
    X.CapLocal → X.Halves → (∀ P M, Ok P M → OkModel P M) → Monotone F → Monotone G →
    Monotone H →
    Bs ⊆ oracleBands → Bc ⊆ oracleBands → ShooterOK sh Bs F X Ok → CutterOK cu Bc G H X Ok →
    Meets (mk sh cu) (mergeBands ∪ oracleBands)
      (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧
        X.holds P c.nmem (rd c bMerge 9) (c.nreg ALLOC) ∧
        rd c bMerge 5 + fuseLoss ≤ X.cap P c.nmem (rd c bMerge 9) ∧ 4 ≤ rd c bMerge 7 ∧
        rd c bMerge 5 + fuseLoss ≤ rd c bMerge 6 ∧
        JunctionWF P (c.nreg ALLOC) c.nmem (rd c bMerge 0) (rd c bMerge 1) (rd c bMerge 2) ∧
        ∃ Hs J N₁ N₂, JunctionAt c.nmem (rd c bMerge 0) (rd c bMerge 1) (rd c bMerge 2) (Qof P) Hs J ∧
          J.P.Simple ∧ SharedGeneric J ∧ Ok P (chainModel J.left) ∧ Ok P (chainModel J.right) ∧
          Ok P (chainModel J.whole) ∧ (chainModel J.whole).FullDegLe (Qof P) (rd c bMerge 7) ∧
          NFWithin c.nmem (rd c bMerge 3) (c.nreg ALLOC) N₁ ∧
          NFWithin c.nmem (rd c bMerge 4) (c.nreg ALLOC) N₂ ∧
          (∃ γ₁, γ₁ ≤ rd c bMerge 5 ∧
            IsCanonicalNF (chainModel J.left) (Qof P) N₁ γ₁ (rd c bMerge 7)) ∧
          (∃ γ₂, γ₂ ≤ rd c bMerge 5 ∧
            IsCanonicalNF (chainModel J.right) (Qof P) N₂ γ₂ (rd c bMerge 7)))
      (fun P c c' => ∀ Hs J N₁ N₂,
        JunctionAt c.nmem (rd c bMerge 0) (rd c bMerge 1) (rd c bMerge 2) (Qof P) Hs J →
        NFAt c.nmem (rd c bMerge 3) N₁ → NFAt c.nmem (rd c bMerge 4) N₂ →
        ∃ N, c.nreg ALLOC ≤ rd c' bMerge 8 ∧ NFWithin c'.nmem (rd c' bMerge 8) (c'.nreg ALLOC) N ∧
          IsCanonicalNF (chainModel J.whole) (Qof P) N (rd c bMerge 6) (rd c bMerge 7))
      (fun _ c => κ (rd c bMerge 7) * (c.nmem (rd c bMerge 3) + c.nmem (rd c bMerge 4) + 1) *
        F (rd c bMerge 5 + fuseLoss) * G (rd c bMerge 5 + fuseLoss) *
        (H (rd c bMerge 5 + fuseLoss) + Nat.clog 2 (c.nmem (rd c bMerge 2 + 2) + 1) + 1))

end

end Chazelle.Core
