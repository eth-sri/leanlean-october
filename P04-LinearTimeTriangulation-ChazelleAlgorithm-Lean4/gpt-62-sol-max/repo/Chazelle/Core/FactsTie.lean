module

public import Chazelle.Core.Facts2

/-!
# WP-C (BuildNF): two chords attached at one walk position (the tie fact)

`BuildNF` sorts the `2K` attachment positions of the chords along the walk and runs a stack over
them (parenthesis structure).  Two chords of one family can be attached at the **same** walk
position (review finding B2): a walk vertex `v` whose left sector contains both horizontal
directions, with one chord leaving `v` eastward and one westward.  Their keys tie, and
`AttachFaceSpec`/`UpSideSpec` do not apply.  This file settles the tie.

## Results (for every walk-axiom model, hence every good model)

* `WalkAx.no_cross`: two distinct chords of an admissible family never cross on the walk (the
  attachment keys of one chord lie in one closed arc of the other), which makes the sorted
  attachment sequence a parenthesis word.
* `WalkAx.tie_pair`, `WalkAx.tie_shape`, `WalkAx.attach_east_unique`, `WalkAx.attach_west_unique`:
  if two distinct chords of `F` are attached at the same position `(p, t)`, they leave its point
  `v` in opposite horizontal directions, `t = 0` (a walk vertex), the walk edge `p` leaving it is
  not horizontal, and every chord of `F` attached there is one of the two (two chords attached at
  one position with the same direction are equal).  Hence at most two chords are attached at one
  position.
* `WalkAx.tie_down` / `WalkAx.tie_up`: the **nesting order and the facing regions** at a tie.
  Let `ce` (east) and `cw` (west) be attached at the walk vertex `v = W p`, with other ends at the
  keys `ke`, `kw`, and `k = p`.
  - If the walk edge `p` goes **down** from `v`: going along the walk from `k`, the key `ke` comes
    before `kw` (`sideInArc k kw ke`); the walk faces the region **below `ce`** just after `v` and
    the region **below `cw`** just before `v`, and one region lies **above both** chords.
  - If it goes **up**: `kw` comes before `ke` (`sideInArc k ke kw`); just after `v` the walk
    faces the region **above `cw`**, just before `v` the region **above `ce`**, and one region lies
    **below both**.
* `TieSpec` and `tieFact : TieSpec`, `NoCrossSpec` and `noCross : NoCrossSpec`: the good-model
  forms of the above.

**Use in `BuildNF`** (secondary sort key).  At a tie at key `k`, the event of the chord whose other
end comes *later* along the walk after `k` must come first in the sorted sequence (it is the outer
parenthesis).  So at a walk vertex whose leaving edge goes down (direction code `2`), the event of
the west chord (the chord whose *right* endpoint is `v`, i.e. its `rpos` event) comes first; when
the edge goes up (code `1`), the event of the east chord (its `lpos` event) comes first.  One
height test of the leaving edge (`WalkKey.dirCode`) decides it.  In the region assignment, the
zero-length gap between the two events is the region above both chords (down) or below both (up);
for each of the two chords the `up`/`dn` assignment is the one of `UpSideSpec` (the region faced
just before a left endpoint and just after a right endpoint is `up`).
-/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sideInArc sidePt sideLeft sideLeftOf sideCcw sideCross sideDot
  SideClean ChordSystem freeIn regionsIn TouchesIn sideKey_inj)
open Chazelle.Jordan (offset nrm)
open Chazelle.Geometry (lerp point_ext lerp_mem_segment)

namespace Tie

/-! ## Directions in the left sector of a walk vertex -/

theorem sideCcw_neg (B X A : Point) : sideCcw (-B) (-X) (-A) ↔ sideCcw B X A := by
  have h1 : ∀ u v : Point, sideCross (-u) (-v) = sideCross u v := by
    simp [sideCross, Prod.fst_neg, Prod.snd_neg]
  have h2 : ∀ u v : Point, sideDot (-u) (-v) = sideDot u v := by
    intro u v; simp only [sideDot, Prod.fst_neg, Prod.snd_neg]; ring
  unfold sideCcw
  rw [h1, h1, h1, h2, h2]

/-- Both horizontal directions in the left sector of a corner: the leaving direction `B` is not
horizontal, and the corner is not a straight angle. -/
theorem ccw_ew {B A : Point} {s s' : ℝ} (hs : 0 < s) (hs' : 0 < s')
    (hE : sideCcw B (s, 0) A) (hW : sideCcw B (-s', 0) A) :
    B.2 ≠ 0 ∧ ¬ (sideCross B A = 0 ∧ sideDot B A < 0) := by
  unfold sideCcw at hE hW
  simp only [sideCross, sideDot] at hE hW ⊢
  constructor
  · intro hB
    rw [hB] at hE hW
    rcases hE with ⟨-, h, -⟩ | ⟨h1, h | h⟩ | ⟨-, -, h⟩ | ⟨h1, -, h | h⟩ <;>
      rcases hW with ⟨-, h', -⟩ | ⟨h1', h' | h'⟩ | ⟨-, -, h'⟩ | ⟨h1', -, h' | h'⟩ <;>
      first
        | (simp at h; done)
        | (simp at h'; done)
        | nlinarith
  · rintro ⟨h1, h2⟩
    rcases hE with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, -, h⟩ | ⟨-, h, -⟩ <;>
      rcases hW with ⟨h', -⟩ | ⟨h', -⟩ | ⟨-, -, h'⟩ | ⟨-, h', -⟩ <;> nlinarith

/-- **Leaving edge going down** (`B.2 < 0`) with the west direction in the sector: the arriving
direction `A` also points down, and the sector contains every direction `X` that is strictly left
of `B`, or points up, or is strictly right of `A`. -/
theorem ccw_down {B A : Point} {s : ℝ} (hs : 0 < s) (hB : B.2 < 0) (hW : sideCcw B (-s, 0) A) :
    A.2 < 0 ∧ ∀ X : Point, (0 < sideCross B X ∨ 0 < X.2 ∨ 0 < sideCross X A) → sideCcw B X A := by
  unfold sideCcw at hW
  simp only [sideCross, sideDot] at hW
  rcases hW with ⟨-, h, -⟩ | ⟨h1, h | h⟩ | ⟨-, -, h⟩ | ⟨h1, h2, -⟩
  · nlinarith
  · nlinarith
  · -- reflex corner, `A` points down
    have hA : A.2 < 0 := by nlinarith
    refine ⟨hA, fun X hX => Or.inr (Or.inl ⟨by assumption, ?_⟩)⟩
    simp only [sideCross]
    rcases hX with hX | hX | hX
    · left; simpa [sideCross] using hX
    · by_contra hno
      push Not at hno
      nlinarith [mul_pos hX (neg_pos.2 hA), mul_pos hX (neg_pos.2 hB),
        mul_nonneg (neg_nonneg.2 hA.le) (sub_nonneg.2 hno.1),
        mul_nonneg (neg_nonneg.2 hB.le) (sub_nonneg.2 hno.2)]
    · right; simpa [sideCross] using hX
  · nlinarith
  · -- full turn: `A` has the direction of `B`
    have hA : A.2 < 0 := by
      by_contra hA
      push Not at hA
      have e : B.2 * (B.1 * A.1 + B.2 * A.2) = (B.1 ^ 2 + B.2 ^ 2) * A.2 := by
        linear_combination (-B.1) * h1
      have := mul_neg_of_neg_of_pos hB h2
      nlinarith [mul_nonneg (add_nonneg (sq_nonneg B.1) (sq_nonneg B.2)) hA]
    refine ⟨hA, fun X hX => Or.inr (Or.inr (Or.inr ⟨by assumption,
      by assumption, ?_⟩))⟩
    simp only [sideCross, sideDot]
    rcases hX with hX | hX | hX
    · left; simp only [sideCross] at hX; linarith
    · by_cases hc : B.1 * X.2 - B.2 * X.1 = 0
      · right
        have e : B.2 * (B.1 * X.1 + B.2 * X.2) = (B.1 ^ 2 + B.2 ^ 2) * X.2 := by
          linear_combination (-B.1) * hc
        have h3 : 0 < (B.1 ^ 2 + B.2 ^ 2) * X.2 :=
          mul_pos (by nlinarith [sq_nonneg B.1, sq_pos_of_neg hB]) hX
        by_contra h4
        push Not at h4
        nlinarith [mul_nonpos_of_nonpos_of_nonneg hB.le h4]
      · left; exact hc
    · left
      intro hc
      simp only [sideCross] at hX
      have e : B.2 * (X.1 * A.2 - X.2 * A.1) = 0 := by
        linear_combination X.2 * h1 - A.2 * hc
      have := mul_neg_of_neg_of_pos hB hX
      linarith

/-- **Leaving edge going up** (`0 < B.2`) with the east direction in the sector (mirror of
`ccw_down` by the half-turn). -/
theorem ccw_up {B A : Point} {s : ℝ} (hs : 0 < s) (hB : 0 < B.2) (hE : sideCcw B (s, 0) A) :
    0 < A.2 ∧ ∀ X : Point, (0 < sideCross B X ∨ X.2 < 0 ∨ 0 < sideCross X A) → sideCcw B X A := by
  have hE' : sideCcw (-B) (-s, 0) (-A) := by
    have : ((-s, 0) : Point) = -((s, 0) : Point) := by ext <;> simp
    rwa [this, sideCcw_neg]
  obtain ⟨hA, hX⟩ := ccw_down hs (by simp_all) hE'
  refine ⟨by simp_all [Prod.snd_neg] , fun X h => ?_⟩
  rw [← sideCcw_neg]
  apply hX
  have e1 : sideCross (-B) (-X) = sideCross B X := by simp only [sideCross]; simp
  have e2 : sideCross (-X) (-A) = sideCross X A := by simp only [sideCross]; simp
  rw [e1, e2, Prod.snd_neg]
  rcases h with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl (by linarith))
  · exact Or.inr (Or.inr h)

/-! ## A cyclic fact -/

/-- If `y ≠ a` is neither strictly between `a` and `b` nor strictly between `c` and `a` (all
cyclically, three distinct keys), then `b` is strictly between `a` and `c`. -/
theorem cyc_cover {a b c y : ℝ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hya : y ≠ a)
    (h1 : ¬ sideInArc a b y) (h2 : ¬ sideInArc c a y) : sideInArc a c b := by
  unfold sideInArc at *
  by_contra h3
  rcases lt_or_gt_of_ne hya with hy | hy <;>
  rcases lt_or_gt_of_ne hab with hb | hb <;> rcases lt_or_gt_of_ne hac with hc | hc <;>
  rcases lt_or_gt_of_ne hbc with hbc' | hbc' <;>
  simp only [hb, hc, hbc', hy, not_lt.2 hb.le, not_lt.2 hc.le,
    not_lt.2 hbc'.le, true_and, and_true] at h1 h2 h3 <;>
  first
    | linarith
    | (rcases lt_or_ge y b with h | h <;> rcases lt_or_ge y c with h' | h' <;>
        simp_all <;> linarith)

end Tie

/-! ## The conclusions at a tie -/

/-- **The tie at a vertex whose leaving edge goes down.**  For the east chord `ce` and the west
chord `cw` attached at the walk vertex `v = W p` (position `(p, 0)`): the walk faces the region
below `ce` just after `v` (on edge `p`) and the region below `cw` just before `v` (on the arriving
edge `(p + n - 1) mod n`, near its end), one region lies above both chords, and going along the
walk from the key `p` the other end of `ce` comes before the other end of `cw`. -/
def Model.TieDown (M : Model) (F : Set (Set Point)) (ce cw : Set Point) (p : ℕ) : Prop :=
  ∃ U V R, U ∈ M.regions F ∧ V ∈ M.regions F ∧ R ∈ M.regions F ∧
    M.BelowOf ce U ∧ M.BelowOf cw V ∧ M.AboveOf ce R ∧ M.AboveOf cw R ∧
    (∃ δ > (0 : ℝ), ∀ t', 0 < t' → t' < δ → M.Faces p t' U) ∧
    (∃ δ > (0 : ℝ), ∀ t', 1 - δ < t' → t' < 1 → M.Faces ((p + M.W.n - 1) % M.W.n) t' V) ∧
    ∀ (pe pw : ℕ) (te tw : ℝ), SideAttach M.W ce pe te → sidePt M.W pe te ≠ M.W.vtx p →
      SideAttach M.W cw pw tw → sidePt M.W pw tw ≠ M.W.vtx p →
        sideInArc (p : ℝ) (pw + tw) (pe + te)

/-- **The tie at a vertex whose leaving edge goes up** (the mirror of `Model.TieDown`): the walk
faces the region above `cw` just after `v` and the region above `ce` just before `v`, one region
lies below both chords, and going along the walk from the key `p` the other end of `cw` comes
before the other end of `ce`. -/
def Model.TieUp (M : Model) (F : Set (Set Point)) (ce cw : Set Point) (p : ℕ) : Prop :=
  ∃ U V R, U ∈ M.regions F ∧ V ∈ M.regions F ∧ R ∈ M.regions F ∧
    M.AboveOf cw U ∧ M.AboveOf ce V ∧ M.BelowOf ce R ∧ M.BelowOf cw R ∧
    (∃ δ > (0 : ℝ), ∀ t', 0 < t' → t' < δ → M.Faces p t' U) ∧
    (∃ δ > (0 : ℝ), ∀ t', 1 - δ < t' → t' < 1 → M.Faces ((p + M.W.n - 1) % M.W.n) t' V) ∧
    ∀ (pe pw : ℕ) (te tw : ℝ), SideAttach M.W ce pe te → sidePt M.W pe te ≠ M.W.vtx p →
      SideAttach M.W cw pw tw → sidePt M.W pw tw ≠ M.W.vtx p →
        sideInArc (p : ℝ) (pe + te) (pw + tw)

/-! ## Chords at a walk position -/

namespace WalkAx

variable {M : Model}

section

variable (hM : WalkAx M) {c : Set Point} (hc : c ∈ M.Adm) {p : ℕ}

include hM hc p in
/-- **The other end of an attached admissible chord**: the chord is the segment from the point
`v` of the attachment to a point `e ≠ v` at the same height, off the domain, whose open part is in
the domain; every attachment of the chord at a point other than `v` is at `e`. -/
theorem attach_other_end {t : ℝ}
    (hA : SideAttach M.W c p t) :
    ∃ e : Point, e ≠ sidePt M.W p t ∧ e.2 = (sidePt M.W p t).2 ∧
      c = Chazelle.segment (sidePt M.W p t) e ∧
      (∀ s ∈ Ioo (0 : ℝ) 1, lerp (sidePt M.W p t) e s ∈ M.D) ∧ e ∉ M.D ∧
      ∀ (p' : ℕ) (t' : ℝ), SideAttach M.W c p' t' → sidePt M.W p' t' ≠ sidePt M.W p t →
        sidePt M.W p' t' = e := by
  obtain ⟨a, b, hab, hcab, hy, hopen, ha, hb⟩ := hM.ends c hc
  have hnotD : ∀ q, WalkEnd M.W c q → q ∉ M.D := by
    rintro q ⟨⟨p', t', h', rfl⟩, -⟩
    exact hM.trace p' h'.1 t' h'.2.1 h'.2.2.1.le
  have hA' := hA
  rw [hcab] at hA'
  have hother : ∀ e, (sidePt M.W p t = a ∧ e = b ∨ sidePt M.W p t = b ∧ e = a) →
      ∀ (p' : ℕ) (t' : ℝ), SideAttach M.W c p' t' → sidePt M.W p' t' ≠ sidePt M.W p t →
        sidePt M.W p' t' = e := by
    intro e he p' t' hA2 hne
    have hA2' := hA2
    rw [hcab] at hA2'
    rcases he with ⟨h1, rfl⟩ | ⟨h1, rfl⟩ <;>
      rcases hM.attach_endpoint hopen hA2' with h2 | h2
    · exact absurd (h2.trans h1.symm) hne
    · exact h2
    · exact h2
    · exact absurd (h2.trans h1.symm) hne
  rcases hM.attach_endpoint hopen hA' with h | h
  · refine ⟨b, by rw [h]; exact hab.symm, by rw [h]; exact hy.symm, by rwa [h],
      by rwa [h], hnotD b hb, hother b (Or.inl ⟨h, rfl⟩)⟩
  · refine ⟨a, by rwa [h], by rwa [h], (by rwa [h, Geometry.segment_comm]), by rw [h]; exact open_rev hopen, hnotD a ha, hother a (Or.inr ⟨h, rfl⟩)⟩

/-- Distance from the start of a segment to a point of it. -/
theorem dist_lerp_left (v e : Point) {s : ℝ} (hs : 0 ≤ s) : dist (lerp v e s) v = s * dist v e := by
  rw [dist_comm, dist_eq_norm, dist_eq_norm]
  have : v - lerp v e s = s • (v - e) := by
    apply point_ext <;> simp [lerp] <;> ring
  rw [this, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs]

/-- Points of an attached chord close to its attachment are in the left sector there. -/
theorem exists_left_on_chord {c : Set Point} {p : ℕ} {t : ℝ} (hA : SideAttach M.W c p t)
    {e : Point} (hce : c = Chazelle.segment (sidePt M.W p t) e) (he : e ≠ sidePt M.W p t)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ s : ℝ, 0 < s ∧ s < 1 ∧ dist (lerp (sidePt M.W p t) e s) (sidePt M.W p t) < ρ ∧
      sideLeft M.W p t (lerp (sidePt M.W p t) e s) := by
  obtain ⟨-, -, -, -, r₀, hr₀, hatt⟩ := hA
  set v := sidePt M.W p t
  set r := min r₀ ρ with hr
  have hr0 := lt_min hr₀ hρ
  have hn : 0 < dist v e + 1 := by positivity
  set s := min (r / (dist v e + 1)) (1 / 2) with hs
  have hs0 : 0 < s := lt_min (div_pos hr0 hn) (by norm_num)
  have hs1 : s < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hd : dist (lerp v e s) v < r := by
    rw [dist_lerp_left v e hs0.le]
    have h1 : s ≤ r / (dist v e + 1) := min_le_left _ _
    calc s * dist v e < s * (dist v e + 1) := by nlinarith
      _ ≤ r / (dist v e + 1) * (dist v e + 1) := mul_le_mul_of_nonneg_right h1 hn.le
      _ = r := div_mul_cancel₀ _ hn.ne'
  refine ⟨s, hs0, hs1, hd.trans_le (min_le_right _ _),
    hatt _ (by rw [hce]; exact lerp_mem_segment _ _ hs0.le hs1.le)
    (Chazelle.Jordan.lerp_ne_left (Ne.symm he) hs0) (hd.trans_le (min_le_left _ _))⟩

include hM hc p in
/-- **Every chord attached at a position leaves it horizontally, east or west.** -/
theorem attach_dir {t : ℝ}
    (hA : SideAttach M.W c p t) :
    (∀ z ∈ c, (sidePt M.W p t).1 ≤ z.1) ∨ (∀ z ∈ c, z.1 ≤ (sidePt M.W p t).1) := by
  obtain ⟨e, -, -, hce, -⟩ := hM.attach_other_end hc hA
  rcases le_total (sidePt M.W p t).1 e.1 with h | h
  · left
    rw [hce]
    rintro z ⟨s, hs0, hs1, rfl⟩
    simp only
    nlinarith
  · right
    rw [hce]
    rintro z ⟨s, hs0, hs1, rfl⟩
    simp only
    nlinarith

/-- The open portion of the longer of two collinear segments on the same ray
contains the end of the shorter one. -/
private theorem open_lerp_of_signed_lt {v a b : Point} {σ : ℝ} (hσ : σ ≠ 0)
    (ha : a.2 = v.2) (hb : b.2 = v.2) (hpa : 0 < σ * (a.1 - v.1))
    (hab : σ * (a.1 - v.1) < σ * (b.1 - v.1)) :
    ∃ s ∈ Ioo (0 : ℝ) 1, a = lerp v b s := by
  have hp := hpa.trans hab
  have hb' : b.1 - v.1 ≠ 0 := by intro h; simp [h] at hp
  refine ⟨σ * (a.1 - v.1) / (σ * (b.1 - v.1)),
    ⟨div_pos hpa hp, (div_lt_one hp).2 hab⟩, point_ext ?_ ?_⟩
  · simp only [Geometry.lerp_fst]
    field_simp
    ring
  · simp [Geometry.lerp_snd, ha, hb]

/-- Two chords attached in the same horizontal direction must have the same far end. -/
private theorem attach_signed_unique (hM : WalkAx M) {c c' : Set Point}
    (hc : c ∈ M.Adm) (hc' : c' ∈ M.Adm) {p : ℕ} {t σ : ℝ} (hσ : σ ≠ 0)
    (hA : SideAttach M.W c p t) (hA' : SideAttach M.W c' p t)
    (hE : ∀ z ∈ c, 0 ≤ σ * (z.1 - (sidePt M.W p t).1))
    (hE' : ∀ z ∈ c', 0 ≤ σ * (z.1 - (sidePt M.W p t).1)) : c = c' := by
  obtain ⟨e, hev, hey, hce, hopen, heD, -⟩ := hM.attach_other_end hc hA
  obtain ⟨f, hfv, hfy, hcf, hOpen, hfD, -⟩ := hM.attach_other_end hc' hA'
  set v := sidePt M.W p t
  have hpos {z : Point} (hne : z ≠ v) (hy : z.2 = v.2) (h : 0 ≤ σ * (z.1 - v.1)) :
      0 < σ * (z.1 - v.1) :=
    lt_of_le_of_ne h fun h0 => hne (point_ext
      (sub_eq_zero.mp ((mul_eq_zero.mp h0.symm).resolve_left hσ)) hy)
  have he := hpos hev hey (hE e (hce ▸ Geometry.right_mem_segment v e))
  have hf := hpos hfv hfy (hE' f (hcf ▸ Geometry.right_mem_segment v f))
  rcases lt_trichotomy (σ * (e.1 - v.1)) (σ * (f.1 - v.1)) with h | h | h
  · obtain ⟨s, hs, hs'⟩ := open_lerp_of_signed_lt hσ hey hfy he h
    exact (heD (hs' ▸ hOpen s hs)).elim
  · have hxy := mul_left_cancel₀ hσ h
    rw [hce, hcf, point_ext (sub_left_inj.mp hxy) (hey.trans hfy.symm)]
  · obtain ⟨s, hs, hs'⟩ := open_lerp_of_signed_lt hσ hfy hey hf h
    exact (hfD (hs' ▸ hopen s hs)).elim

/-- Two chords attached at one position both to the east are equal. -/
theorem attach_east_unique (hM : WalkAx M) {F : Set (Set Point)} (hF : F ⊆ M.Adm)
    {c c' : Set Point} (hc : c ∈ F) (hc' : c' ∈ F) {p : ℕ} {t : ℝ} (hA : SideAttach M.W c p t)
    (hA' : SideAttach M.W c' p t) (hE : ∀ z ∈ c, (sidePt M.W p t).1 ≤ z.1)
    (hE' : ∀ z ∈ c', (sidePt M.W p t).1 ≤ z.1) : c = c' :=
  attach_signed_unique hM (hF hc) (hF hc') one_ne_zero hA hA'
    (fun z hz => by simpa using sub_nonneg.mpr (hE z hz))
    (fun z hz => by simpa using sub_nonneg.mpr (hE' z hz))

/-- Two chords attached at one position both to the west are equal. -/
theorem attach_west_unique (hM : WalkAx M) {F : Set (Set Point)} (hF : F ⊆ M.Adm)
    {c c' : Set Point} (hc : c ∈ F) (hc' : c' ∈ F) {p : ℕ} {t : ℝ} (hA : SideAttach M.W c p t)
    (hA' : SideAttach M.W c' p t) (hW : ∀ z ∈ c, z.1 ≤ (sidePt M.W p t).1)
    (hW' : ∀ z ∈ c', z.1 ≤ (sidePt M.W p t).1) : c = c' :=
  attach_signed_unique hM (hF hc) (hF hc') (neg_ne_zero.mpr one_ne_zero) hA hA'
    (fun z hz => by simpa using hW z hz) (fun z hz => by simpa using hW' z hz)

/-! ## Non-crossing -/

/-- **Two distinct chords of an admissible family do not cross on the walk**: if an attachment
key of `d` is strictly inside the arc from `A` to `B` of `c`, no attachment key of `d` is strictly
inside the arc from `B` to `A`. -/
theorem no_cross (hM : WalkAx M) {F : Set (Set Point)} (hF : F ⊆ M.Adm) (hfin : F.Finite)
    {c d : Set Point} (hc : c ∈ F) (hd : d ∈ F) (hcd : c ≠ d) {pa pb pc pd : ℕ}
    {ta tb tc td : ℝ} (hA : SideAttach M.W c pa ta) (hB : SideAttach M.W c pb tb)
    (hAB : sidePt M.W pa ta ≠ sidePt M.W pb tb) (hC : SideAttach M.W d pc tc)
    (hD : SideAttach M.W d pd td) :
    ¬ (sideInArc (pa + ta) (pb + tb) (pc + tc) ∧ sideInArc (pb + tb) (pa + ta) (pd + td)) := by
  rintro ⟨h1, h2⟩
  have hsys := hM.sys F hF hfin
  obtain ⟨K₁, K₂, hne, ⟨k₁, rfl⟩, ⟨k₂, rfl⟩, hK₁, hK₂⟩ := hM.split (hF hc) hA hB hAB
  -- a point of `d ∩ D` in a component, near an attachment of `d`
  have hpt : ∀ {q : ℕ} {τ : ℝ} {k : Point}, SideAttach M.W d q τ →
      Chazelle.Chain.SideSectorIn M.W (connectedComponentIn (M.D \ c) k) q τ →
      ∃ x ∈ d ∩ M.D, x ∈ connectedComponentIn (M.D \ c) k := by
    intro q τ k hQ hsec
    obtain ⟨r, hr, hsecr⟩ := hsec
    obtain ⟨e, hev, -, hde, hopen, -⟩ := hM.attach_other_end (hF hd) hQ
    obtain ⟨s, hs0, hs1, hdist, hleft⟩ := exists_left_on_chord hQ hde hev hr
    refine ⟨_, ⟨by rw [hde]; exact lerp_mem_segment _ _ hs0.le hs1.le, hopen s ⟨hs0, hs1⟩⟩,
      hsecr _ (by assumption) hleft⟩
  obtain ⟨x₁, hx₁d, hx₁K⟩ := hpt hC (hK₁ pc hC.1 tc hC.2.1 hC.2.2.1 h1)
  obtain ⟨x₂, hx₂d, hx₂K⟩ := hpt hD (hK₂ pd hD.1 td hD.2.1 hD.2.2.1 h2)
  have hsub : d ∩ M.D ⊆ M.D \ c := fun x hx =>
    ⟨hx.2, fun hxc => hsys.inter_subset_compl hd hc (Ne.symm hcd) ⟨hx.1, hxc⟩ hx.2⟩
  have hcon := (hsys.chord_inter_nonempty_isPreconnected hd).2.subset_connectedComponentIn
    hx₁d hsub
  apply hne
  rw [connectedComponentIn_eq hx₁K, connectedComponentIn_eq hx₂K,
    connectedComponentIn_eq (hcon hx₂d)]

/-! ## The setup of a tie -/

/-- **At a tie the position is a walk vertex, and both horizontal directions lie in its left
sector.**  For chords `ce` (east) and `cw` (west) of the admissible set attached at the same
position `(p, t)`: `t = 0`, and with `B` the direction of the leaving walk edge and `A` that of the
arriving one, both `(s₁, 0)` and `(-s₂, 0)` (for some `s₁, s₂ > 0`) are strictly inside the
counterclockwise sector from `B` to `A`. -/
theorem tie_setup (hM : WalkAx M) {ce cw : Set Point} (hce : ce ∈ M.Adm) (hcw : cw ∈ M.Adm)
    {p : ℕ} {t : ℝ} (hAe : SideAttach M.W ce p t) (hAw : SideAttach M.W cw p t)
    (hE : ∀ z ∈ ce, (sidePt M.W p t).1 ≤ z.1) (hW : ∀ z ∈ cw, z.1 ≤ (sidePt M.W p t).1) :
    t = 0 ∧ ∃ s₁ s₂ : ℝ, 0 < s₁ ∧ 0 < s₂ ∧
      sideCcw (M.wb p - M.wa p) (s₁, 0) (M.W.vtx ((p + M.W.n - 1) % M.W.n) - M.wa p) ∧
      sideCcw (M.wb p - M.wa p) (-s₂, 0) (M.W.vtx ((p + M.W.n - 1) % M.W.n) - M.wa p) := by
  obtain ⟨we, hwev, hwey, hceq, -⟩ := hM.attach_other_end hce hAe
  obtain ⟨uw, huwv, huwy, hcwq, -⟩ := hM.attach_other_end hcw hAw
  set v := sidePt M.W p t with hv
  have hlte : v.1 < we.1 := lt_of_le_of_ne
    (hE we (by rw [hceq]; exact Geometry.right_mem_segment _ _))
    (fun h => hwev (point_ext h.symm hwey))
  have hltw : uw.1 < v.1 := lt_of_le_of_ne
    (hW uw (by rw [hcwq]; exact Geometry.right_mem_segment _ _))
    (fun h => huwv (point_ext h huwy))
  obtain ⟨s, hs0, hs1, -, hL⟩ := exists_left_on_chord hAe hceq hwev one_pos
  obtain ⟨s', hs0', hs1', -, hL'⟩ := exists_left_on_chord hAw hcwq huwv one_pos
  have hsnd : ∀ (e : Point) (σ : ℝ), e.2 = v.2 → (lerp v e σ).2 = v.2 := by
    intro e σ he; simp only [Geometry.lerp_snd, he]; ring
  have ht0 : t = 0 := by
    by_contra ht
    have ht' : t ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_ne hAe.2.1 (Ne.symm ht), hAe.2.2.1⟩
    rw [Chazelle.Chain.sideLeft_edge (hM.nd p hAe.1) ht'] at hL hL'
    set a := M.W.vtx p
    set b := M.W.vtx ((p + 1) % M.W.n)
    have hva : v = lerp a b t := rfl
    have key : ∀ (e : Point) (σ : ℝ), e.2 = v.2 →
        det a b (lerp v e σ) = -(σ * (e.1 - v.1)) * (b.2 - a.2) := by
      intro e σ he
      have h2 := hsnd e σ he
      unfold det
      rw [h2]
      simp only [Geometry.lerp_fst, hva, Geometry.lerp_snd]
      ring
    rw [key we s hwey] at hL
    rw [key uw s' huwy] at hL'
    have h1 : 0 < s * (we.1 - v.1) := mul_pos hs0 (by linarith)
    have h2 : 0 < s' * (v.1 - uw.1) := mul_pos hs0' (by linarith)
    nlinarith
  subst ht0
  have hv0 : v = M.W.vtx p := Chazelle.Chain.sidePt_zero M.W p
  refine ⟨rfl, s * (we.1 - v.1), s' * (v.1 - uw.1), mul_pos hs0 (by linarith),
    mul_pos hs0' (by linarith), ?_, ?_⟩
  · rw [Chazelle.Chain.sideLeft_zero] at hL
    unfold sideLeftOf at hL
    have e1 : lerp v we s - M.W.vtx p = (s * (we.1 - v.1), 0) := by
      rw [← hv0]
      apply point_ext
      · simp [Geometry.lerp_fst]
      · simp only [Prod.snd_sub, hsnd we s hwey, sub_self]
    rw [e1] at hL
    exact hL
  · rw [Chazelle.Chain.sideLeft_zero] at hL'
    unfold sideLeftOf at hL'
    have e1 : lerp v uw s' - M.W.vtx p = (-(s' * (v.1 - uw.1)), 0) := by
      rw [← hv0]
      apply point_ext
      · simp [Geometry.lerp_fst]; ring
      · simp only [Prod.snd_sub, hsnd uw s' huwy, sub_self]
    rw [e1] at hL'
    exact hL'

/-! ## Local regions at a walk vertex -/

/-- **Near a walk vertex, the left sector off the vertex height is free**: there is `r > 0` such
that every point of the ball of radius `r` around the vertex `W p` that lies in the left sector
of the position `(p, 0)` and not at the height of the vertex is in the free set of `F`. -/
theorem local_free (hM : WalkAx M) {F : Set (Set Point)} (hF : F ⊆ M.Adm) (hfin : F.Finite)
    {p : ℕ} (hp : p < M.W.n) :
    ∃ r > 0, ∀ x ∈ ball (M.W.vtx p) r, sideLeft M.W p 0 x → x.2 ≠ (M.W.vtx p).2 →
      x ∈ freeIn M.D F := by
  have hsys := hM.sys F hF hfin
  obtain ⟨r₁, hr₁, hcl⟩ := hM.clean p hp 0 le_rfl zero_lt_one
  rw [Chazelle.Chain.sidePt_zero] at hcl
  set G := {c ∈ F | M.W.vtx p ∉ c} with hG
  have hGF : G ⊆ F := fun c hc => hc.1
  have hGc := hsys.isClosed_sUnion hGF
  have hvG : M.W.vtx p ∉ ⋃₀ G := fun ⟨c, hc, hvc⟩ => hc.2 hvc
  obtain ⟨r₂, hr₂, hb₂⟩ := Metric.isOpen_iff.1 hGc.isOpen_compl _ hvG
  refine ⟨min r₁ r₂, lt_min hr₁ hr₂, fun x hx hL hy => ⟨?_, ?_⟩⟩
  · by_contra hxD
    exact hcl x (ball_subset_ball (min_le_left _ _) hx) hxD hL
  · rintro ⟨c, hc, hxc⟩
    by_cases hvc : M.W.vtx p ∈ c
    · exact hy (hsys.snd_eq hc hxc hvc)
    · exact hb₂ (ball_subset_ball (min_le_right _ _) hx) ⟨c, ⟨hc, hvc⟩, hxc⟩

/-- A nonempty preconnected subset of the free set lies in one region. -/
theorem exists_region_of_free {F : Set (Set Point)} {S : Set Point} (hS : IsPreconnected S)
    (hne : S.Nonempty) (hSF : S ⊆ freeIn M.D F) : ∃ U ∈ M.regions F, S ⊆ U := by
  obtain ⟨x, hx⟩ := hne
  exact ⟨_, ⟨x, hSF hx, rfl⟩, hS.subset_connectedComponentIn hx hSF⟩

/-- Signed version of `AboveOf` and `BelowOf`. -/
private def chordSide (M : Model) (σ : ℝ) (c U : Set Point) : Prop :=
  ∀ z ∈ c, z ∈ M.D → ∀ᶠ δ in 𝓝[>] (0 : ℝ), ((z.1, z.2 + σ * δ) : Point) ∈ U

/-- Identifying the side region at one chord point identifies it along the whole chord. -/
private theorem side_of_meets (hM : WalkAx M) {F : Set (Set Point)} (hF : F ⊆ M.Adm) (hfin : F.Finite)
    {c : Set Point} (hc : c ∈ F) {U : Set Point} (hU : U ∈ M.regions F) {z : Point} (hz : z ∈ c)
    (hzD : z ∈ M.D) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (h : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ((z.1, z.2 + σ * δ) : Point) ∈ U) : chordSide M σ c U := by
  obtain ⟨Up, Dn, hUp, hDn, -, hside, -⟩ := chordSides_of_system (hM.sys F hF hfin) hc
  suffices ∃ V ∈ M.regions F, chordSide M σ c V by
    obtain ⟨V, hV, hv⟩ := this
    exact (Chazelle.Chain.regionsIn_eq_of_eventually_mem hU hV h (hv z hz hzD)).symm ▸ hv
  rcases hσ with rfl | rfl
  · exact ⟨Up, hUp, fun w hw hD => (hside w hw hD).mono fun δ hh => by simpa using hh.1⟩
  · exact ⟨Dn, hDn, fun w hw hD => (hside w hw hD).mono fun δ hh => by simpa [sub_eq_add_neg] using hh.2⟩

/-- Vertical displacements of a point of an open set stay in it for small displacements. -/
theorem eventually_vert {O : Set Point} (hO : IsOpen O) {z : Point} (hz : z ∈ O) (σ : ℝ) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ), ((z.1, z.2 + σ * δ) : Point) ∈ O := by
  have hc : Continuous fun δ : ℝ => ((z.1, z.2 + σ * δ) : Point) := by fun_prop
  have h0 : ((z.1, z.2 + σ * 0) : Point) = z := by simp
  have := hc.tendsto 0
  rw [h0] at this
  exact (this.eventually (hO.mem_nhds hz)).filter_mono nhdsWithin_le_nhds

/-- **A local region piece at a walk vertex.**  Let `O` be an open convex set inside the free
radius `r` of the vertex `v = W p` (`local_free`), such that the points of `O` strictly on the
`σ`-side of the height of `v` (`σ = ±1`) are in the left sector of `(p, 0)`.  Then those points
lie in one region `U`, which contains the vertical displacements `(z.1, z.2 + σ δ)` (small
`δ > 0`) of every point `z ∈ O` at the height of `v`. -/
theorem region_of_piece {F : Set (Set Point)} {p : ℕ} {r : ℝ}
    (hfree : ∀ x ∈ ball (M.W.vtx p) r, sideLeft M.W p 0 x → x.2 ≠ (M.W.vtx p).2 →
      x ∈ freeIn M.D F)
    {O : Set Point} (hOo : IsOpen O) (hOc : Convex ℝ O) (hOb : O ⊆ ball (M.W.vtx p) r)
    {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hsec : ∀ x ∈ O, 0 < σ * (x.2 - (M.W.vtx p).2) → sideLeft M.W p 0 x)
    {z : Point} (hz : z ∈ O) (hzv : z.2 = (M.W.vtx p).2) :
    ∃ U ∈ M.regions F, (∀ x ∈ O, 0 < σ * (x.2 - (M.W.vtx p).2) → x ∈ U) ∧
      ∀ z' ∈ O, z'.2 = (M.W.vtx p).2 → ∀ᶠ δ in 𝓝[>] (0 : ℝ), ((z'.1, z'.2 + σ * δ) : Point) ∈ U := by
  set v := M.W.vtx p
  have hσσ : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  set S := O ∩ {x : Point | 0 < σ * det v (v.1 + 1, v.2) x} with hS
  have hdet : ∀ x : Point, det v (v.1 + 1, v.2) x = x.2 - v.2 := by
    simp [det]
  have hSc : Convex ℝ S := hOc.inter (Chazelle.Jordan.convex_det_pos _ _ σ)
  have hSF : S ⊆ freeIn M.D F := by
    rintro x ⟨hxO, hx⟩
    simp only [mem_ofPred_eq, hdet] at hx
    refine hfree x (hOb hxO) (hsec x hxO hx) (fun h => ?_)
    rw [h, sub_self, mul_zero] at hx
    exact lt_irrefl _ hx
  have hev : ∀ z' ∈ O, z'.2 = v.2 → ∀ᶠ δ in 𝓝[>] (0 : ℝ), ((z'.1, z'.2 + σ * δ) : Point) ∈ S := by
    intro z' hz' hz'v
    filter_upwards [eventually_vert hOo hz' σ, self_mem_nhdsWithin] with δ h1 h2
    refine ⟨h1, ?_⟩
    simp only [mem_ofPred_eq, hdet, hz'v]
    have : σ * (v.2 + σ * δ - v.2) = δ := by rw [add_sub_cancel_left, ← mul_assoc, hσσ, one_mul]
    rwa [this]
  obtain ⟨δ₀, hδ₀⟩ := (hev z hz hzv).exists
  obtain ⟨U, hU, hSU⟩ := exists_region_of_free hSc.isPreconnected ⟨_, hδ₀⟩ hSF
  refine ⟨U, hU, fun x hx h => hSU ⟨hx, ?_⟩, fun z' hz' hz'v => (hev z' hz' hz'v).mono
    fun δ h => hSU h⟩
  simp only [mem_ofPred_eq, hdet]; exact h

/-- If the edge is near its endpoint and on the required side of the endpoint height,
a sufficiently small left offset stays near that endpoint and on that same side. -/
private theorem eventually_offset_at {a b v : Point} {U : Set Point} {r σ : ℝ} {f : ℝ → ℝ}
    (hr : 0 < r) (hne : a ≠ b) (ht : Tendsto (fun t => lerp a b (f t)) (𝓝[>] 0) (𝓝 v))
    (hy : ∀ t > 0, 0 < σ * ((lerp a b (f t)).2 - v.2))
    (hU : ∀ x ∈ ball v r, 0 < det a b x → 0 < σ * (x.2 - v.2) → x ∈ U) :
    ∃ d > 0, ∀ t, 0 < t → t < d → ∀ᶠ δ in 𝓝[>] (0 : ℝ), offset a b (f t) δ ∈ U := by
  let O : Set Point := ball v r ∩ {x | 0 < σ * (x.2 - v.2)}
  have hO : IsOpen O := isOpen_ball.inter (isOpen_lt continuous_const (by fun_prop))
  obtain ⟨d, hd, hball⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp (ht.eventually (ball_mem_nhds _ hr))
  refine ⟨d, hd, fun t h0 htd => ?_⟩
  have htO : lerp a b (f t) ∈ O := ⟨hball ⟨h0, htd⟩, hy t h0⟩
  filter_upwards [Jordan.eventually_offset_mem 1 hO htO, self_mem_nhdsWithin] with δ hδ (hpos : 0 < δ)
  rw [one_mul] at hδ
  exact hU _ hδ.1 (by rw [Jordan.det_offset]; exact mul_pos hpos (Jordan.sqLen_pos hne)) hδ.2

/-- The walk just after a vertex faces the region on the left of the leaving edge
and strictly on the indicated side of the vertex height. -/
theorem faces_after_of {p : ℕ} {U : Set Point} {r σ : ℝ} (hr : 0 < r) (_hσ : σ = 1 ∨ σ = -1)
    (hB : 0 < σ * ((M.wb p).2 - (M.wa p).2))
    (hU : ∀ x ∈ ball (M.wa p) r, 0 < sideCross (M.wb p - M.wa p) (x - M.wa p) →
      0 < σ * (x.2 - (M.wa p).2) → x ∈ U) :
    ∃ δ₁ > (0 : ℝ), ∀ t', 0 < t' → t' < δ₁ → M.Faces p t' U := by
  refine eventually_offset_at (f := id) (σ := σ) hr (by intro e; simp [e] at hB)
    (Jordan.tendsto_lerp_zero _ _) ?_ ?_
  · intro t ht
    simp only [id_eq, Geometry.lerp_snd, add_sub_cancel_left]
    nlinarith [mul_pos ht hB]
  · intro x hx hc hy
    exact hU x hx (by simp only [sideCross, Prod.fst_sub, Prod.snd_sub, det] at *; linarith) hy

/-- The walk just before a vertex faces the region on the left of the arriving edge
and strictly on the indicated side of the vertex height. -/
theorem faces_before_of {q : ℕ} {V : Set Point} {r σ : ℝ} (hr : 0 < r) (_hσ : σ = 1 ∨ σ = -1)
    (hA : 0 < σ * ((M.wa q).2 - (M.wb q).2))
    (hV : ∀ x ∈ ball (M.wb q) r, 0 < sideCross (x - M.wb q) (M.wa q - M.wb q) →
      0 < σ * (x.2 - (M.wb q).2) → x ∈ V) :
    ∃ δ₁ > (0 : ℝ), ∀ t', 1 - δ₁ < t' → t' < 1 → M.Faces q t' V := by
  have hheight (t : ℝ) (ht : 0 < t) :
      0 < σ * ((lerp (M.wa q) (M.wb q) (1 - t)).2 - (M.wb q).2) := by
    simp only [Geometry.lerp_snd]
    nlinarith [mul_pos ht hA]
  have hU (x : Point) (hx : x ∈ ball (M.wb q) r) (hc : 0 < det (M.wa q) (M.wb q) x)
      (hy : 0 < σ * (x.2 - (M.wb q).2)) : x ∈ V := by
    apply hV _ hx ?_ hy
    convert hc using 1
    simp [sideCross, det]
    ring
  obtain ⟨d, hd, hf⟩ := eventually_offset_at hr (by intro e; simp [e] at hA)
    (Jordan.tendsto_lerp_one_sub (M.wa q) (M.wb q)) hheight hU
  refine ⟨d, hd, fun t h1 h2 => ?_⟩
  have H := hf (1 - t) (by linarith) (by linarith)
  rw [show 1 - (1 - t) = t by ring] at H
  exact H

/-- The arriving edge of a walk vertex ends at it. -/
theorem prev_succ {p n : ℕ} (hp : p < n) : ((p + n - 1) % n + 1) % n = p := by
  rcases p with _ | k
  · have hn : n - 1 < n := by omega
    rw [Nat.zero_add, Nat.mod_eq_of_lt hn, Nat.sub_add_cancel (by omega), Nat.mod_self]
  · have e : k + 1 + n - 1 = k + n := by omega
    have h1 : (k + 1 + n - 1) % n = k := by
      rw [e, Nat.add_mod_right]; exact Nat.mod_eq_of_lt (by omega)
    rw [h1]; exact Nat.mod_eq_of_lt hp

include hM hc p in
/-- The far endpoint and a nearby interior point of an attached horizontal chord, with
horizontal displacement measured in direction `τ`. -/
private theorem tie_end
    (hA : SideAttach M.W c p 0) {τ : ℝ} (hτ : τ ≠ 0)
    (hdir : ∀ z ∈ c, 0 ≤ τ * (z.1 - (sidePt M.W p 0).1)) {r : ℝ} (hr : 0 < r) :
    let v := M.W.vtx p
    ∃ w z : Point, w.2 = v.2 ∧ 0 < τ * (w.1 - v.1) ∧ c = Chazelle.segment v w ∧
      (∀ s ∈ Ioo (0 : ℝ) 1, lerp v w s ∈ M.D) ∧
      (∀ q t, SideAttach M.W c q t → sidePt M.W q t ≠ v → sidePt M.W q t = w) ∧
      z ∈ c ∧ z ∈ M.D ∧ z.2 = v.2 ∧ 0 < τ * (z.1 - v.1) ∧ z ∈ ball v r := by
  obtain ⟨w, hwv, hwy, hcw, hopen, -, hfar⟩ := hM.attach_other_end hc hA
  obtain ⟨s, hs0, hs1, hd, -⟩ := exists_left_on_chord hA hcw hwv hr
  rw [Chazelle.Chain.sidePt_zero] at hwv hwy hcw hopen hfar hd hdir
  dsimp only
  set v := M.W.vtx p
  have hw : 0 < τ * (w.1 - v.1) := lt_of_le_of_ne
    (hdir w (hcw ▸ Geometry.right_mem_segment _ _))
    (Ne.symm (mul_ne_zero hτ (fun hh => hwv (point_ext (sub_eq_zero.1 hh) hwy))))
  refine ⟨w, lerp v w s, hwy, hw, hcw, hopen, hfar, ?_, hopen s ⟨hs0, hs1⟩, ?_, ?_, hd⟩
  · rw [hcw]; exact lerp_mem_segment _ _ hs0.le hs1.le
  · simp only [Geometry.lerp_snd, hwy]; ring
  · simp only [Geometry.lerp_fst]
    nlinarith only [mul_pos hs0 hw]

end

private theorem chordSide_offset {c U : Set Point} {a b : Point} {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hU : chordSide M σ c U) (hc : c = Chazelle.segment a b)
    (hy : a.2 = b.2) (hd : lerp a b (1 / 2) ∈ M.D) (hw : 0 < σ * (b.1 - a.1)) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ), offset a b (1 / 2) δ ∈ U := by
  have hm : lerp a b (1 / 2) ∈ c := hc ▸ lerp_mem_segment _ _ (by norm_num) (by norm_num)
  refine (eventually_mul_pos (hU _ hm hd) hw).mono fun δ h => ?_
  rw [offset_mid_ab hy]
  convert h using 2
  rcases hσ with rfl | rfl <;> ring

section

variable (hM : WalkAx M) {F : Set (Set Point)} (hF : F ⊆ M.Adm)
include hM hF

/-- The two versions of the tie use the same three regions: the regions on the `σ` side of
 the outgoing and incoming half-planes, and a common region on the other side. Here `cf`
 is the chord faced first (after the vertex), and `cb` is the one faced before. -/
private theorem signed_tie (hfin : F.Finite)
    {cf cb : Set Point} (hcf : cf ∈ F) (hcb : cb ∈ F) {p : ℕ}
    (hAf : SideAttach M.W cf p 0) (hAb : SideAttach M.W cb p 0) {σ : ℝ}
    (hFwd : ∀ z ∈ cf, 0 ≤ -σ * (z.1 - (sidePt M.W p 0).1))
    (hBwd : ∀ z ∈ cb, 0 ≤ σ * (z.1 - (sidePt M.W p 0).1)) (hσ : σ = 1 ∨ σ = -1)
    (hB : 0 < σ * (M.wb p - M.wa p).2)
    (hA : 0 < σ * (M.W.vtx ((p + M.W.n - 1) % M.W.n) - M.wa p).2)
    (hsec : let B := M.wb p - M.wa p
            let A := M.W.vtx ((p + M.W.n - 1) % M.W.n) - M.wa p
            ∀ x : Point, (0 < sideCross B x ∨ 0 < -σ * x.2 ∨ 0 < sideCross x A) → sideCcw B x A) :
    ∃ U V R, U ∈ M.regions F ∧ V ∈ M.regions F ∧ R ∈ M.regions F ∧
      chordSide M σ cf U ∧ chordSide M σ cb V ∧ chordSide M (-σ) cf R ∧ chordSide M (-σ) cb R ∧
      (∃ δ > (0 : ℝ), ∀ t', 0 < t' → t' < δ → M.Faces p t' U) ∧
      (∃ δ > (0 : ℝ), ∀ t', 1 - δ < t' → t' < 1 → M.Faces ((p + M.W.n - 1) % M.W.n) t' V) ∧
      ∀ (pf pb : ℕ) (tf tb : ℝ), SideAttach M.W cf pf tf → sidePt M.W pf tf ≠ M.W.vtx p →
        SideAttach M.W cb pb tb → sidePt M.W pb tb ≠ M.W.vtx p → sideInArc (p : ℝ) (pb + tb) (pf + tf) := by
  obtain ⟨r, hr, hfree⟩ := hM.local_free hF hfin hAf.1
  have hσ₀ : σ ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
  have hσ' : -σ = 1 ∨ -σ = -1 := by rcases hσ with rfl | rfl <;> norm_num
  obtain ⟨wf, zf, hwfy, hwf, hcfq, hopenf, hfarf, hzfc, hzfD, hzfy, hzf, hzfr⟩ :=
    tie_end hM (hF hcf) hAf (neg_ne_zero.2 hσ₀) hFwd hr
  obtain ⟨wb, zb, hwby, hwb, hcbq, hopenb, hfarb, hzbc, hzbD, hzby, hzb, hzbr⟩ :=
    tie_end hM (hF hcb) hAb hσ₀ hBwd hr
  let v := M.W.vtx p
  let q := (p + M.W.n - 1) % M.W.n
  let a := M.wa q
  let B : Point := M.wb p - v
  let A : Point := a - v
  have hvq : M.wb q = v := by
    change M.W.vtx ((q + 1) % M.W.n) = M.W.vtx p
    rw [prev_succ hAf.1]
  have hcrossB (x : Point) : sideCross B (x - v) = det v (M.wb p) x :=
    Chazelle.Chain.sideCross_out _ _ _
  have hcrossA (x : Point) : sideCross (x - v) A = det a v x :=
    Chazelle.Chain.sideCross_in _ _ _
  have hleft (x : Point) (hx : 0 < sideCross B (x - v) ∨ 0 < -σ * (x - v).2 ∨ 0 < sideCross (x - v) A) :
      sideLeft M.W p 0 x := by
    rw [Chazelle.Chain.sideLeft_zero]
    exact hsec _ hx
  let Of := ball v r ∩ {x | 0 < 1 * det v (M.wb p) x}
  let Ob := ball v r ∩ {x | 0 < 1 * det a v x}
  change 0 < σ * B.2 at hB
  change 0 < σ * A.2 at hA
  have hzfO : zf ∈ Of := by
    refine ⟨hzfr, ?_⟩
    change 0 < 1 * det v (M.wb p) zf
    rw [one_mul, ← hcrossB]
    simp only [sideCross, Prod.fst_sub, Prod.snd_sub, hzfy]
    rcases hσ with rfl | rfl <;> nlinarith only [mul_pos hzf hB]
  have hzbO : zb ∈ Ob := by
    refine ⟨hzbr, ?_⟩
    change 0 < 1 * det a v zb
    rw [one_mul, ← hcrossA]
    simp only [sideCross, Prod.fst_sub, Prod.snd_sub, hzby]
    rcases hσ with rfl | rfl <;> nlinarith only [mul_pos hzb hA]
  obtain ⟨U, hU, hUin, hUev⟩ := region_of_piece hfree
    (isOpen_ball.inter (Chazelle.Jordan.isOpen_det_pos v (M.wb p) 1))
    ((convex_ball _ _).inter (Chazelle.Jordan.convex_det_pos _ _ 1)) inter_subset_left hσ
    (fun x hx _ => hleft x (Or.inl (by simpa only [hcrossB, mem_ofPred_eq, one_mul] using hx.2))) hzfO hzfy
  obtain ⟨V, hV, hVin, hVev⟩ := region_of_piece hfree
    (isOpen_ball.inter (Chazelle.Jordan.isOpen_det_pos a v 1))
    ((convex_ball _ _).inter (Chazelle.Jordan.convex_det_pos _ _ 1)) inter_subset_left hσ
    (fun x hx _ => hleft x (Or.inr (Or.inr (by simpa only [hcrossA, mem_ofPred_eq, one_mul] using hx.2))))
    hzbO hzby
  obtain ⟨R, hR, -, hRev⟩ := region_of_piece hfree isOpen_ball (convex_ball _ _) subset_rfl hσ'
    (fun x _ hx => hleft x (Or.inr (Or.inl hx))) hzfr hzfy
  have hRf := side_of_meets hM hF hfin hcf hR hzfc hzfD hσ' (hRev zf hzfr hzfy)
  have hRb := side_of_meets hM hF hfin hcb hR hzbc hzbD hσ' (hRev zb hzbr hzby)
  refine ⟨U, V, R, hU, hV, hR,
    side_of_meets hM hF hfin hcf hU hzfc hzfD hσ (hUev zf hzfO hzfy),
    side_of_meets hM hF hfin hcb hV hzbc hzbD hσ (hVev zb hzbO hzby), hRf, hRb, ?_, ?_, ?_⟩
  · refine faces_after_of hr hσ hB fun x hx h1 h2 => hUin x ⟨hx, ?_⟩ h2
    change 0 < sideCross B (x - v) at h1
    simpa only [mem_ofPred_eq, one_mul, ← hcrossB] using h1
  · refine faces_before_of hr hσ (by rw [hvq]; exact hA) fun x hx h1 h2 => ?_
    rw [hvq] at hx h1 h2
    exact hVin x ⟨hx, by simpa only [mem_ofPred_eq, one_mul, ← hcrossA] using h1⟩ h2
  · intro pf pb tf tb hFf hnF hBb hnB
    have hv0 := Chazelle.Chain.sidePt_zero M.W p
    have hef := hfarf pf tf hFf hnF
    have heb := hfarb pb tb hBb hnB
    have hneF : sidePt M.W p 0 ≠ sidePt M.W pf tf := hv0 ▸ hnF.symm
    have hneB : sidePt M.W pb tb ≠ sidePt M.W p 0 := hv0 ▸ hnB
    have hneFB : sidePt M.W pf tf ≠ sidePt M.W pb tb := by
      rw [hef, heb]; intro he
      rw [he] at hwf
      linarith only [hwf, hwb]
    obtain ⟨py, ty, hpy, hty0, hty1, hf⟩ := hM.exists_faces hF hfin hR
    have hya : (py : ℝ) + ty ≠ p := by
      intro h
      have := (sideKey_inj hty0.le hty1 le_rfl zero_lt_one (by simpa using h)).2
      linarith
    refine Tie.cyc_cover (by simpa using key_ne_of_pt_ne hAf hFf hneF)
      (by simpa using key_ne_of_pt_ne hAb hBb hneB.symm)
      (key_ne_of_pt_ne hFf hBb hneFB) hya (fun hin => ?_) (fun hin => ?_)
    · refine hM.not_left_of_after hF hcf hAf hFf hneF hR hpy ⟨hty0, hty1⟩ (by simpa using hin) hf ?_
      rw [hv0, hef]
      exact chordSide_offset hσ' hRf hcfq hwfy.symm (hopenf _ ⟨by norm_num, by norm_num⟩) hwf
    · refine hM.not_left_of_after hF hcb hBb hAb hneB hR hpy ⟨hty0, hty1⟩ (by simpa using hin) hf ?_
      rw [hv0, heb]
      exact chordSide_offset hσ' hRb (hcbq.trans (Geometry.segment_comm _ _)) hwby
        (open_rev hopenb _ ⟨by norm_num, by norm_num⟩) (by linarith only [hwb])

/-- The tie at a vertex with downward leaving edge. -/
theorem tie_down (hfin : F.Finite)
    {ce cw : Set Point} (hce : ce ∈ F) (hcw : cw ∈ F) {p : ℕ} {t : ℝ}
    (hAe : SideAttach M.W ce p t) (hAw : SideAttach M.W cw p t)
    (hE : ∀ z ∈ ce, (sidePt M.W p t).1 ≤ z.1) (hW : ∀ z ∈ cw, z.1 ≤ (sidePt M.W p t).1)
    (hdown : (M.wb p).2 < (M.wa p).2) :
    t = 0 ∧ M.TieDown F ce cw p := by
  obtain ⟨rfl, _, s, -, hs, -, hW'⟩ := hM.tie_setup (hF hce) (hF hcw) hAe hAw hE hW
  have hb : 0 < -1 * ((M.wb p - M.wa p).2) := by simp only [Prod.snd_sub]; linarith
  obtain ⟨ha, hsec⟩ := Tie.ccw_down hs (by simpa using hb) hW'
  refine ⟨rfl, ?_⟩
  simpa [Model.TieDown, chordSide, Model.AboveOf, Model.BelowOf, sub_eq_add_neg] using
    signed_tie hM hF hfin hce hcw hAe hAw (fun z hz => by simpa using sub_nonneg.2 (hE z hz))
      (fun z hz => by have := hW z hz; linarith) (Or.inr rfl) hb (by simpa using ha)
      (fun x h => hsec _ (by simpa using h))

/-- The tie at a vertex with upward leaving edge. -/
theorem tie_up (hfin : F.Finite)
    {ce cw : Set Point} (hce : ce ∈ F) (hcw : cw ∈ F) {p : ℕ} {t : ℝ}
    (hAe : SideAttach M.W ce p t) (hAw : SideAttach M.W cw p t)
    (hE : ∀ z ∈ ce, (sidePt M.W p t).1 ≤ z.1) (hW : ∀ z ∈ cw, z.1 ≤ (sidePt M.W p t).1)
    (hup : (M.wa p).2 < (M.wb p).2) :
    t = 0 ∧ M.TieUp F ce cw p := by
  obtain ⟨rfl, s, _, hs, -, hE', -⟩ := hM.tie_setup (hF hce) (hF hcw) hAe hAw hE hW
  have hb : 0 < (M.wb p - M.wa p).2 := sub_pos.2 hup
  obtain ⟨ha, hsec⟩ := Tie.ccw_up hs hb hE'
  obtain ⟨U, V, R, hU, hV, hR, h₁, h₂, h₃, h₄, hf, hb, ho⟩ :=
    signed_tie hM hF hfin hcw hce hAw hAe (fun z hz => by have := hW z hz; linarith)
      (fun z hz => by simpa using sub_nonneg.2 (hE z hz)) (Or.inl rfl) (by simpa using hb)
      (by simpa using ha) (fun x h => hsec _ (by simpa using h))
  exact ⟨rfl, U, V, R, hU, hV, hR, by simpa [chordSide, Model.AboveOf] using h₁,
    by simpa [chordSide, Model.AboveOf] using h₂, by simpa [chordSide, Model.BelowOf, sub_eq_add_neg] using h₄,
    by simpa [chordSide, Model.BelowOf, sub_eq_add_neg] using h₃, hf, hb,
    fun pe pw te tw he he' hw hw' => ho pw pe tw te hw hw' he he'⟩

/-- **Two distinct chords of `F` at one position go opposite ways.** -/
theorem tie_pair {c c' : Set Point}
    (hc : c ∈ F) (hc' : c' ∈ F) (hne : c ≠ c') {p : ℕ} {t : ℝ} (hA : SideAttach M.W c p t)
    (hA' : SideAttach M.W c' p t) :
    ((∀ z ∈ c, (sidePt M.W p t).1 ≤ z.1) ∧ (∀ z ∈ c', z.1 ≤ (sidePt M.W p t).1)) ∨
      ((∀ z ∈ c, z.1 ≤ (sidePt M.W p t).1) ∧ (∀ z ∈ c', (sidePt M.W p t).1 ≤ z.1)) := by
  rcases hM.attach_dir (hF hc) hA with h | h <;> rcases hM.attach_dir (hF hc') hA' with h' | h'
  · exact absurd (hM.attach_east_unique hF hc hc' hA hA' h h') hne
  · exact Or.inl ⟨h, h'⟩
  · tauto
  · exact absurd (hM.attach_west_unique hF hc hc' hA hA' h h') hne

/-- **The shape of a tie**: for an east chord `ce` and a west chord `cw` of `F` attached at the
same position `(p, t)`, `t = 0`, the leaving walk edge is not horizontal, and every chord of `F`
attached at that position is `ce` or `cw` (so at most two chords are attached at one
position). -/
theorem tie_shape {ce cw : Set Point}
    (hce : ce ∈ F) (hcw : cw ∈ F) {p : ℕ} {t : ℝ} (hAe : SideAttach M.W ce p t)
    (hAw : SideAttach M.W cw p t) (hE : ∀ z ∈ ce, (sidePt M.W p t).1 ≤ z.1)
    (hW : ∀ z ∈ cw, z.1 ≤ (sidePt M.W p t).1) :
    t = 0 ∧ (M.wb p).2 ≠ (M.wa p).2 ∧ ∀ c ∈ F, SideAttach M.W c p t → c = ce ∨ c = cw := by
  obtain ⟨ht, s₁, s₂, hs₁, hs₂, hsE, hsW⟩ := hM.tie_setup (hF hce) (hF hcw) hAe hAw hE hW
  refine ⟨ht, fun h => (Tie.ccw_ew hs₁ hs₂ hsE hsW).1 (by simp [Prod.snd_sub, h, sub_self]),
    fun c hc hA => ?_⟩
  rcases hM.attach_dir (hF hc) hA with h | h
  · exact Or.inl (hM.attach_east_unique hF hc hce hA hAe h hE)
  · exact Or.inr (hM.attach_west_unique hF hc hcw hA hAw h hW)

end

end WalkAx

/-! ## The good-model form -/

end

end Chazelle.Core
