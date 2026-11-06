module

public import Chazelle.Golf

public import Chazelle.Golf

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
    intro u v; simp only [sideCross, Prod.fst_neg, Prod.snd_neg]; ring
  have h2 : ∀ u v : Point, sideDot (-u) (-v) = sideDot u v := by
    intro u v; simp only [sideDot, Prod.fst_neg, Prod.snd_neg]; ring
  unfold sideCcw
  Ξ h1, h1, h1, h2, h2

/-- Both horizontal directions in the left sector of a corner: the leaving direction `B` is not
horizontal, and the corner is not a straight angle. -/
theorem ccw_ew {B A : Point} {s s' : ℝ} (hs : 0 < s) (hs' : 0 < s')
    (hE : sideCcw B (s, 0) A) (hW : sideCcw B (-s', 0) A) :
    B.2 ≠ 0 ∧ ¬ (sideCross B A = 0 ∧ sideDot B A < 0) := by
  unfold sideCcw at hE hW
  ϴ' sideCross, sideDot at hE hW ⊢
  constructor
  · intro hB
    Ξ' hB at hE hW
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
  ϴ' sideCross, sideDot at hW
  rcases hW with ⟨-, h, -⟩ | ⟨h1, h | h⟩ | ⟨-, -, h⟩ | ⟨h1, h2, -⟩
  · nlinarith
  · nlinarith
  · -- reflex corner, `A` points down
    have hA : A.2 < 0 := ⊞
    refine ⟨hA, fun X hX => Or.inr (Or.inl ⟨by simp only [sideCross]; linarith, ?_⟩)⟩
    ϴ sideCross
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
    refine ⟨hA, fun X hX => Or.inr (Or.inr (Or.inr ⟨by simp only [sideCross]; linarith,
      by simp only [sideDot]; linarith, ?_⟩))⟩
    ϴ sideCross, sideDot
    rcases hX with hX | hX | hX
    · left; ϴ' sideCross at hX; linarith
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
      ϴ' sideCross at hX
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
    rw [this, sideCcw_neg]; exact hE
  obtain ⟨hA, hX⟩ := ccw_down hs (by simp only [Prod.snd_neg]; linarith) hE'
  refine ⟨by simp only [Prod.snd_neg] at hA; linarith, fun X h => ?_⟩
  Ξ ← sideCcw_neg
  apply hX
  have e1 : sideCross (-B) (-X) = sideCross B X := by simp only [sideCross]; simp
  have e2 : sideCross (-X) (-A) = sideCross X A := by simp only [sideCross]; simp
  Ξ e1, e2, Prod.snd_neg
  rcases h with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl (⟡))
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

/-- **The other end of an attached admissible chord**: the chord is the segment from the point
`v` of the attachment to a point `e ≠ v` at the same height, off the domain, whose open part is in
the domain; every attachment of the chord at a point other than `v` is at `e`. -/
theorem attach_other_end (hM : WalkAx M) {c : Set Point} (hc : c ∈ M.Adm) {p : ℕ} {t : ℝ}
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
  Ξ' hcab at hA'
  have hother : ∀ e, (sidePt M.W p t = a ∧ e = b ∨ sidePt M.W p t = b ∧ e = a) →
      ∀ (p' : ℕ) (t' : ℝ), SideAttach M.W c p' t' → sidePt M.W p' t' ≠ sidePt M.W p t →
        sidePt M.W p' t' = e := by
    intro e he p' t' hA2 hne
    have hA2' := hA2
    Ξ' hcab at hA2'
    rcases he with ⟨h1, rfl⟩ | ⟨h1, rfl⟩ <;>
      rcases hM.attach_endpoint hopen hA2' with h2 | h2
    · exact absurd (h2.trans h1.symm) hne
    · exact h2
    · exact h2
    · exact absurd (h2.trans h1.symm) hne
  rcases hM.attach_endpoint hopen hA' with h | h
  · refine ⟨b, by rw [h]; exact hab.symm, by rw [h]; exact hy.symm, by rw [h]; exact hcab,
      by rw [h]; exact hopen, hnotD b hb, hother b (Or.inl ⟨h, rfl⟩)⟩
  · refine ⟨a, by rw [h]; exact hab, by rw [h]; exact hy, (by rw [h, Geometry.segment_comm]; exact hcab), by rw [h]; exact open_rev hopen, hnotD a ha, hother a (Or.inr ⟨h, rfl⟩)⟩

/-- Distance from the start of a segment to a point of it. -/
theorem dist_lerp_left (v e : Point) {s : ℝ} (hs : 0 ≤ s) : dist (lerp v e s) v = s * dist v e := by
  Ξ dist_comm, dist_eq_norm, dist_eq_norm
  have : v - lerp v e s = s • (v - e) := by
    apply point_ext <;> simp [lerp] <;> ring
  Ξ this, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs

/-- Points of an attached chord close to its attachment are in the left sector there. -/
theorem exists_left_on_chord {c : Set Point} {p : ℕ} {t : ℝ} (hA : SideAttach M.W c p t)
    {e : Point} (hce : c = Chazelle.segment (sidePt M.W p t) e) (he : e ≠ sidePt M.W p t)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ s : ℝ, 0 < s ∧ s < 1 ∧ dist (lerp (sidePt M.W p t) e s) (sidePt M.W p t) < ρ ∧
      sideLeft M.W p t (lerp (sidePt M.W p t) e s) := by
  obtain ⟨-, -, -, -, r₀, hr₀, hatt⟩ := hA
  set v := sidePt M.W p t
  set r := min r₀ ρ with hr
  have hr0 : 0 < r := lt_min hr₀ hρ
  have hn : 0 < dist v e + 1 := ⟢
  set s := min (r / (dist v e + 1)) (1 / 2) with hs
  have hs0 : 0 < s := lt_min (div_pos hr0 hn) (⊛)
  have hs1 : s < 1 := lt_of_le_of_lt (min_le_right _ _) (⊛)
  have hd : dist (lerp v e s) v < r := by
    Ξ dist_lerp_left v e hs0.le
    have h1 : s ≤ r / (dist v e + 1) := min_le_left _ _
    calc s * dist v e < s * (dist v e + 1) := ⊞
      _ ≤ r / (dist v e + 1) * (dist v e + 1) := mul_le_mul_of_nonneg_right h1 hn.le
      _ = r := div_mul_cancel₀ _ hn.ne'
  refine ⟨s, hs0, hs1, hd.trans_le (min_le_right _ _),
    hatt _ (by rw [hce]; exact lerp_mem_segment _ _ hs0.le hs1.le)
    (Chazelle.Jordan.lerp_ne_left (Ne.symm he) hs0) (hd.trans_le (min_le_left _ _))⟩

/-- **Every chord attached at a position leaves it horizontally, east or west.** -/
theorem attach_dir (hM : WalkAx M) {c : Set Point} (hc : c ∈ M.Adm) {p : ℕ} {t : ℝ}
    (hA : SideAttach M.W c p t) :
    (∀ z ∈ c, (sidePt M.W p t).1 ≤ z.1) ∨ (∀ z ∈ c, z.1 ≤ (sidePt M.W p t).1) := by
  obtain ⟨e, -, -, hce, -⟩ := hM.attach_other_end hc hA
  rcases le_total (sidePt M.W p t).1 e.1 with h | h
  · left
    Ξ hce
    rintro z ⟨s, hs0, hs1, rfl⟩
    simp only
    nlinarith
  · right
    Ξ hce
    rintro z ⟨s, hs0, hs1, rfl⟩
    simp only
    nlinarith

/-- **Two chords of `F` attached at one position in the same direction are equal** (east). -/
theorem attach_east_unique (hM : WalkAx M) {F : Set (Set Point)} (hF : F ⊆ M.Adm)
    {c c' : Set Point} (hc : c ∈ F) (hc' : c' ∈ F) {p : ℕ} {t : ℝ} (hA : SideAttach M.W c p t)
    (hA' : SideAttach M.W c' p t) (hE : ∀ z ∈ c, (sidePt M.W p t).1 ≤ z.1)
    (hE' : ∀ z ∈ c', (sidePt M.W p t).1 ≤ z.1) : c = c' := by
  obtain ⟨e, hev, hey, hce, hopen, heD, -⟩ := hM.attach_other_end (hF hc) hA
  obtain ⟨e', hev', hey', hce', hopen', heD', -⟩ := hM.attach_other_end (hF hc') hA'
  set v := sidePt M.W p t
  have h1 := lt_of_le_of_ne (hE e (by rw [hce]; exact Geometry.right_mem_segment _ _))
    (fun h => hev (point_ext h.symm hey))
  have h1' := lt_of_le_of_ne
    (hE' e' (by rw [hce']; exact Geometry.right_mem_segment _ _))
    (fun h => hev' (point_ext h.symm hey'))
  rcases lt_trichotomy e.1 e'.1 with h | h | h
  · exfalso
    apply heD
    have e1 : e = lerp v e' ((e.1 - v.1) / (e'.1 - v.1)) := by
      apply point_ext
      · simp only [Geometry.lerp_fst]; rw [div_mul_cancel₀ _ (sub_pos.2 h1').ne']; ring
      · simp only [Geometry.lerp_snd]; rw [hey, hey']; ring
    Ξ e1
    exact hopen' _ ⟨div_pos (⟡) (⟡), (div_lt_one (⟡)).2 (⟡)⟩
  · Ξ hce, hce', point_ext h (hey.trans hey'.symm)
  · exfalso
    apply heD'
    have e1 : e' = lerp v e ((e'.1 - v.1) / (e.1 - v.1)) := by
      apply point_ext
      · simp only [Geometry.lerp_fst]; rw [div_mul_cancel₀ _ (sub_pos.2 h1).ne']; ring
      · simp only [Geometry.lerp_snd]; rw [hey, hey']; ring
    Ξ e1
    exact hopen _ ⟨div_pos (⟡) (⟡), (div_lt_one (⟡)).2 (⟡)⟩

/-- **Two chords of `F` attached at one position in the same direction are equal** (west). -/
theorem attach_west_unique (hM : WalkAx M) {F : Set (Set Point)} (hF : F ⊆ M.Adm)
    {c c' : Set Point} (hc : c ∈ F) (hc' : c' ∈ F) {p : ℕ} {t : ℝ} (hA : SideAttach M.W c p t)
    (hA' : SideAttach M.W c' p t) (hW : ∀ z ∈ c, z.1 ≤ (sidePt M.W p t).1)
    (hW' : ∀ z ∈ c', z.1 ≤ (sidePt M.W p t).1) : c = c' := by
  obtain ⟨e, hev, hey, hce, hopen, heD, -⟩ := hM.attach_other_end (hF hc) hA
  obtain ⟨e', hev', hey', hce', hopen', heD', -⟩ := hM.attach_other_end (hF hc') hA'
  set v := sidePt M.W p t
  have h1 := lt_of_le_of_ne (hW e (by rw [hce]; exact Geometry.right_mem_segment _ _))
    (fun h => hev (point_ext h hey))
  have h1' := lt_of_le_of_ne
    (hW' e' (by rw [hce']; exact Geometry.right_mem_segment _ _))
    (fun h => hev' (point_ext h hey'))
  rcases lt_trichotomy e.1 e'.1 with h | h | h
  · exfalso
    apply heD'
    have e1 : e' = lerp v e ((v.1 - e'.1) / (v.1 - e.1)) := by
      apply point_ext
      · ϴ Geometry.lerp_fst
        Ξ show e.1 - v.1 = -(v.1 - e.1) by ring, mul_neg, div_mul_cancel₀ _ (sub_pos.2 h1).ne'
        ring
      · simp only [Geometry.lerp_snd]; rw [hey, hey']; ring
    Ξ e1
    exact hopen _ ⟨div_pos (⟡) (⟡), (div_lt_one (⟡)).2 (⟡)⟩
  · Ξ hce, hce', point_ext h (hey.trans hey'.symm)
  · exfalso
    apply heD
    have e1 : e = lerp v e' ((v.1 - e.1) / (v.1 - e'.1)) := by
      apply point_ext
      · ϴ Geometry.lerp_fst
        Ξ show e'.1 - v.1 = -(v.1 - e'.1) by ring, mul_neg, div_mul_cancel₀ _ (sub_pos.2 h1').ne'
        ring
      · simp only [Geometry.lerp_snd]; rw [hey, hey']; ring
    Ξ e1
    exact hopen' _ ⟨div_pos (⟡) (⟡), (div_lt_one (⟡)).2 (⟡)⟩

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
      hsecr _ (by rw [mem_ball]; exact hdist) hleft⟩
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
  have hlte := lt_of_le_of_ne
    (hE we (by rw [hceq]; exact Geometry.right_mem_segment _ _))
    (fun h => hwev (point_ext h.symm hwey))
  have hltw := lt_of_le_of_ne
    (hW uw (by rw [hcwq]; exact Geometry.right_mem_segment _ _))
    (fun h => huwv (point_ext h huwy))
  obtain ⟨s, hs0, hs1, -, hL⟩ := exists_left_on_chord hAe hceq hwev one_pos
  obtain ⟨s', hs0', hs1', -, hL'⟩ := exists_left_on_chord hAw hcwq huwv one_pos
  have hsnd : ∀ (e : Point) (σ : ℝ), e.2 = v.2 → (lerp v e σ).2 = v.2 := by
    intro e σ he; simp only [Geometry.lerp_snd, he]; ring
  have ht0 : t = 0 := by
    by_contra ht
    have ht' : t ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_ne hAe.2.1 (Ne.symm ht), hAe.2.2.1⟩
    Ξ' Chazelle.Chain.sideLeft_edge (hM.nd p hAe.1) ht' at hL hL'
    set a := M.W.vtx p
    set b := M.W.vtx ((p + 1) % M.W.n)
    have hva : v = lerp a b t := rfl
    have key : ∀ (e : Point) (σ : ℝ), e.2 = v.2 →
        det a b (lerp v e σ) = -(σ * (e.1 - v.1)) * (b.2 - a.2) := by
      intro e σ he
      have h2 := hsnd e σ he
      unfold det
      Ξ h2
      ϴ Geometry.lerp_fst, hva, Geometry.lerp_snd
      ring
    Ξ' key we s hwey at hL
    Ξ' key uw s' huwy at hL'
    have h1 : 0 < s * (we.1 - v.1) := mul_pos hs0 (⟡)
    have h2 : 0 < s' * (v.1 - uw.1) := mul_pos hs0' (⟡)
    nlinarith
  subst ht0
  have hv0 : v = M.W.vtx p := Chazelle.Chain.sidePt_zero M.W p
  refine ⟨rfl, s * (we.1 - v.1), s' * (v.1 - uw.1), mul_pos hs0 (⟡),
    mul_pos hs0' (⟡), ?_, ?_⟩
  · Ξ' Chazelle.Chain.sideLeft_zero at hL
    unfold sideLeftOf at hL
    have e1 : lerp v we s - M.W.vtx p = (s * (we.1 - v.1), 0) := by
      Ξ ← hv0
      apply point_ext
      · Θ Geometry.lerp_fst
      · ϴ Prod.snd_sub, hsnd we s hwey, sub_self
    Ξ' e1 at hL
    exact hL
  · Ξ' Chazelle.Chain.sideLeft_zero at hL'
    unfold sideLeftOf at hL'
    have e1 : lerp v uw s' - M.W.vtx p = (-(s' * (v.1 - uw.1)), 0) := by
      Ξ ← hv0
      apply point_ext
      · simp [Geometry.lerp_fst]; ring
      · ϴ Prod.snd_sub, hsnd uw s' huwy, sub_self
    Ξ' e1 at hL'
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
  Ξ' Chazelle.Chain.sidePt_zero at hcl
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

/-- A region containing the points just below one point of a chord is the region below it. -/
theorem below_of_meets (hM : WalkAx M) {F : Set (Set Point)} (hF : F ⊆ M.Adm) (hfin : F.Finite)
    {c : Set Point} (hc : c ∈ F) {U : Set Point} (hU : U ∈ M.regions F) {z : Point} (hz : z ∈ c)
    (hzD : z ∈ M.D) (h : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ((z.1, z.2 - δ) : Point) ∈ U) : M.BelowOf c U := by
  obtain ⟨Up, Dn, -, hDn, -, hside, -⟩ := chordSides_of_system (hM.sys F hF hfin) hc
  obtain ⟨δ, h1, -, h2⟩ := (h.and (hside z hz hzD)).exists
  have hUD : U = Dn := by
    rcases Chazelle.Chain.regionsIn_eq_or_disjoint hU hDn with h' | h'
    · exact h'
    · exact absurd (h'.le_bot ⟨h1, h2⟩) (fun h => h)
  Ξ hUD
  exact fun z hz hzD => (hside z hz hzD).mono fun _ h => h.2

/-- A region containing the points just above one point of a chord is the region above it. -/
theorem above_of_meets (hM : WalkAx M) {F : Set (Set Point)} (hF : F ⊆ M.Adm) (hfin : F.Finite)
    {c : Set Point} (hc : c ∈ F) {U : Set Point} (hU : U ∈ M.regions F) {z : Point} (hz : z ∈ c)
    (hzD : z ∈ M.D) (h : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ((z.1, z.2 + δ) : Point) ∈ U) : M.AboveOf c U := by
  obtain ⟨Up, Dn, hUp, -, -, hside, -⟩ := chordSides_of_system (hM.sys F hF hfin) hc
  obtain ⟨δ, h1, h2, -⟩ := (h.and (hside z hz hzD)).exists
  have hUD : U = Up := by
    rcases Chazelle.Chain.regionsIn_eq_or_disjoint hU hUp with h' | h'
    · exact h'
    · exact absurd (h'.le_bot ⟨h1, h2⟩) (fun h => h)
  Ξ hUD
  exact fun z hz hzD => (hside z hz hzD).mono fun _ h => h.1

/-- Vertical displacements of a point of an open set stay in it for small displacements. -/
theorem eventually_vert {O : Set Point} (hO : IsOpen O) {z : Point} (hz : z ∈ O) (σ : ℝ) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ), ((z.1, z.2 + σ * δ) : Point) ∈ O := by
  have hc : Continuous fun δ : ℝ => ((z.1, z.2 + σ * δ) : Point) := by fun_prop
  have h0 : ((z.1, z.2 + σ * 0) : Point) = z := ✓
  have := hc.tendsto 0
  Ξ' h0 at this
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
    intro x; simp only [det]; ring
  have hSc : Convex ℝ S := hOc.inter (Chazelle.Jordan.convex_det_pos _ _ σ)
  have hSF : S ⊆ freeIn M.D F := by
    rintro x ⟨hxO, hx⟩
    ϴ' mem_ofPred_eq, hdet at hx
    refine hfree x (hOb hxO) (hsec x hxO hx) (fun h => ?_)
    Ξ' h, sub_self, mul_zero at hx
    exact lt_irrefl _ hx
  have hev : ∀ z' ∈ O, z'.2 = v.2 → ∀ᶠ δ in 𝓝[>] (0 : ℝ), ((z'.1, z'.2 + σ * δ) : Point) ∈ S := by
    intro z' hz' hz'v
    filter_upwards [eventually_vert hOo hz' σ, self_mem_nhdsWithin] with δ h1 h2
    refine ⟨h1, ?_⟩
    ϴ mem_ofPred_eq, hdet, hz'v
    have : σ * (v.2 + σ * δ - v.2) = δ := Ρ add_sub_cancel_left, ← mul_assoc, hσσ, one_mul
    rw [this]; exact h2
  obtain ⟨δ₀, hδ₀⟩ := (hev z hz hzv).exists
  obtain ⟨U, hU, hSU⟩ := exists_region_of_free hSc.isPreconnected ⟨_, hδ₀⟩ hSF
  refine ⟨U, hU, fun x hx h => hSU ⟨hx, ?_⟩, fun z' hz' hz'v => (hev z' hz' hz'v).mono
    fun δ h => hSU h⟩
  simp only [mem_ofPred_eq, hdet]; exact h

/-- **The walk just after a vertex** faces the region containing the points of the ball around
the vertex that are left of the leaving edge and strictly on its side (`σ = ±1`) of the vertex
height. -/
theorem faces_after_of {p : ℕ} {U : Set Point} {r σ : ℝ} (hr : 0 < r) (hσ : σ = 1 ∨ σ = -1)
    (hB : 0 < σ * ((M.wb p).2 - (M.wa p).2))
    (hU : ∀ x ∈ ball (M.wa p) r, 0 < sideCross (M.wb p - M.wa p) (x - M.wa p) →
      0 < σ * (x.2 - (M.wa p).2) → x ∈ U) :
    ∃ δ₁ > (0 : ℝ), ∀ t', 0 < t' → t' < δ₁ → M.Faces p t' U := by
  set v := M.wa p
  set B : Point := M.wb p - v with hBdef
  have hB1 : B.1 = (M.wb p).1 - v.1 := rfl
  have hB2 : B.2 = (M.wb p).2 - v.2 := rfl
  Ξ' ← hB2 at hB
  have hσB : -|B.1| ≤ σ * B.1 := by
    rcases hσ with rfl | rfl
    · simp only [one_mul]; exact neg_abs_le B.1
    · simp only [neg_one_mul, neg_le_neg_iff]; exact le_abs_self B.1
  have hB2ne : B.2 ≠ 0 := by intro h; Ξ' h, mul_zero at hB; exact lt_irrefl _ hB
  set K := |B.1| + |B.2| + 1 with hK
  have hK0 : 0 < K := ⟢
  refine ⟨r / (2 * K), ⟢, fun t' ht0 ht1 => ?_⟩
  have hpos : 0 < min t' (t' * (σ * B.2) / K) := lt_min ht0 (⟢)
  unfold Model.Faces
  filter_upwards [Ioo_mem_nhdsGT hpos] with δ hδ
  have hδ0 := hδ.1
  have hδ1 : δ < t' := hδ.2.trans_le (min_le_left _ _)
  have hδ2 : δ * K < t' * (σ * B.2) := by
    have := hδ.2.trans_le (min_le_right _ _)
    rwa [lt_div_iff₀ hK0] at this
  set x := offset (M.wa p) (M.wb p) t' δ
  have hx1 : x.1 - v.1 = t' * B.1 - δ * B.2 := by
    ϴ x, offset, nrm, Geometry.add_fst, Geometry.smul_fst, Geometry.lerp_fst, hB1, hB2
    ring
  have hx2 : x.2 - v.2 = t' * B.2 + δ * B.1 := by
    ϴ x, offset, nrm, Geometry.add_snd, Geometry.smul_snd, Geometry.lerp_snd, hB1, hB2
    ring
  have hK2 : (t' + δ) * K < r := by
    have h1 : t' < r / (2 * K) := ht1
    Ξ' lt_div_iff₀ (⟢) at h1
    nlinarith
  have a1 := le_abs_self B.1
  have a2 := neg_abs_le B.1
  have a3 := le_abs_self B.2
  have a4 := neg_abs_le B.2
  have p1 := mul_le_mul_of_nonneg_left a1 ht0.le
  have p2 := mul_le_mul_of_nonneg_left a2 ht0.le
  have p3 := mul_le_mul_of_nonneg_left a3 ht0.le
  have p4 := mul_le_mul_of_nonneg_left a4 ht0.le
  have q1 := mul_le_mul_of_nonneg_left a1 hδ0.le
  have q2 := mul_le_mul_of_nonneg_left a2 hδ0.le
  have q3 := mul_le_mul_of_nonneg_left a3 hδ0.le
  have q4 := mul_le_mul_of_nonneg_left a4 hδ0.le
  have hKe : (t' + δ) * K = t' * |B.1| + t' * |B.2| + δ * |B.1| + δ * |B.2| + (t' + δ) := by
    rw [hK]; ring
  apply hU
  · Ξ mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq, max_lt_iff, abs_lt, abs_lt, hx1, hx2
    refine ⟨⟨⟡, ⟡⟩, ⟨⟡, ⟡⟩⟩
  · have : sideCross B (x - v) = δ * (B.1 ^ 2 + B.2 ^ 2) := by
      simp only [sideCross, Prod.fst_sub, Prod.snd_sub, hx1, hx2]; ring
    Ξ this
    exact mul_pos hδ0 (⟢)
  · Ξ hx2
    have : δ * |B.1| ≤ δ * K := mul_le_mul_of_nonneg_left (by rw [hK]; linarith [abs_nonneg B.2])
      hδ0.le
    have h3 : -(δ * |B.1|) ≤ δ * (σ * B.1) := ⊞
    nlinarith

/-- **The walk just before a vertex** (on the arriving edge `q`, near its end) faces the region
containing the points of the ball around the vertex that are right of the arriving direction and
strictly on its side (`σ = ±1`) of the vertex height. -/
theorem faces_before_of {q : ℕ} {V : Set Point} {r σ : ℝ} (hr : 0 < r) (hσ : σ = 1 ∨ σ = -1)
    (hA : 0 < σ * ((M.wa q).2 - (M.wb q).2))
    (hV : ∀ x ∈ ball (M.wb q) r, 0 < sideCross (x - M.wb q) (M.wa q - M.wb q) →
      0 < σ * (x.2 - (M.wb q).2) → x ∈ V) :
    ∃ δ₁ > (0 : ℝ), ∀ t', 1 - δ₁ < t' → t' < 1 → M.Faces q t' V := by
  set v := M.wb q
  set A : Point := M.wa q - v with hAdef
  have hA1 : A.1 = (M.wa q).1 - v.1 := rfl
  have hA2 : A.2 = (M.wa q).2 - v.2 := rfl
  Ξ' ← hA2 at hA
  have hσA : σ * A.1 ≤ |A.1| := by
    rcases hσ with rfl | rfl
    · simp only [one_mul]; exact le_abs_self A.1
    · simp only [neg_one_mul]; exact neg_le_abs A.1
  have hA2ne : A.2 ≠ 0 := by intro h; Ξ' h, mul_zero at hA; exact lt_irrefl _ hA
  set K := |A.1| + |A.2| + 1 with hK
  have hK0 : 0 < K := ⟢
  refine ⟨r / (2 * K), ⟢, fun t' ht0 ht1 => ?_⟩
  set u := 1 - t' with hu
  have hu0 : 0 < u := by rw [hu]; linarith
  have hu1 : u < r / (2 * K) := by rw [hu]; linarith
  have hpos : 0 < min u (u * (σ * A.2) / K) := lt_min hu0 (⟢)
  unfold Model.Faces
  filter_upwards [Ioo_mem_nhdsGT hpos] with δ hδ
  have hδ0 := hδ.1
  have hδ1 : δ < u := hδ.2.trans_le (min_le_left _ _)
  have hδ2 : δ * K < u * (σ * A.2) := by
    have := hδ.2.trans_le (min_le_right _ _)
    rwa [lt_div_iff₀ hK0] at this
  set x := offset (M.wa q) (M.wb q) t' δ
  have hx1 : x.1 - v.1 = u * A.1 + δ * A.2 := by
    ϴ x, offset, nrm, Geometry.add_fst, Geometry.smul_fst, Geometry.lerp_fst, hA1, hA2, hu
    ring
  have hx2 : x.2 - v.2 = u * A.2 - δ * A.1 := by
    ϴ x, offset, nrm, Geometry.add_snd, Geometry.smul_snd, Geometry.lerp_snd, hA1, hA2, hu
    ring
  have hK2 : (u + δ) * K < r := by
    Ξ' lt_div_iff₀ (⟢) at hu1
    nlinarith
  have a1 := le_abs_self A.1
  have a2 := neg_abs_le A.1
  have a3 := le_abs_self A.2
  have a4 := neg_abs_le A.2
  have p1 := mul_le_mul_of_nonneg_left a1 hu0.le
  have p2 := mul_le_mul_of_nonneg_left a2 hu0.le
  have p3 := mul_le_mul_of_nonneg_left a3 hu0.le
  have p4 := mul_le_mul_of_nonneg_left a4 hu0.le
  have q1 := mul_le_mul_of_nonneg_left a1 hδ0.le
  have q2 := mul_le_mul_of_nonneg_left a2 hδ0.le
  have q3 := mul_le_mul_of_nonneg_left a3 hδ0.le
  have q4 := mul_le_mul_of_nonneg_left a4 hδ0.le
  have hKe : (u + δ) * K = u * |A.1| + u * |A.2| + δ * |A.1| + δ * |A.2| + (u + δ) := by
    rw [hK]; ring
  apply hV
  · Ξ mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq, max_lt_iff, abs_lt, abs_lt, hx1, hx2
    refine ⟨⟨⟡, ⟡⟩, ⟨⟡, ⟡⟩⟩
  · have : sideCross (x - v) A = δ * (A.1 ^ 2 + A.2 ^ 2) := by
      simp only [sideCross, Prod.fst_sub, Prod.snd_sub, hx1, hx2]; ring
    Ξ this
    exact mul_pos hδ0 (⟢)
  · Ξ hx2
    have : δ * |A.1| ≤ δ * K := mul_le_mul_of_nonneg_left (by rw [hK]; linarith [abs_nonneg A.2])
      hδ0.le
    have h3 : δ * (σ * A.1) ≤ δ * |A.1| := mul_le_mul_of_nonneg_left hσA hδ0.le
    have e : σ * (u * A.2 - δ * A.1) = u * (σ * A.2) - δ * (σ * A.1) := ⋆
    Ξ e
    linarith

/-- The arriving edge of a walk vertex ends at it. -/
theorem prev_succ {p n : ℕ} (hp : p < n) : ((p + n - 1) % n + 1) % n = p := by
  rcases p with _ | k
  · have hn : n - 1 < n := ⋄
    Ξ Nat.zero_add, Nat.mod_eq_of_lt hn, Nat.sub_add_cancel (⋄), Nat.mod_self
  · have e : k + 1 + n - 1 = k + n := ⋄
    have h1 : (k + 1 + n - 1) % n = k := by
      rw [e, Nat.add_mod_right]; exact Nat.mod_eq_of_lt (⋄)
    rw [h1]; exact Nat.mod_eq_of_lt hp

/-- Common data of a tie at a vertex: the other ends of the two chords and points of the chords
near the vertex, in the domain, within a given distance. -/
theorem tie_ends (hM : WalkAx M) {ce cw : Set Point} (hce : ce ∈ M.Adm) (hcw : cw ∈ M.Adm)
    {p : ℕ} (hAe : SideAttach M.W ce p 0) (hAw : SideAttach M.W cw p 0)
    (hE : ∀ z ∈ ce, (sidePt M.W p 0).1 ≤ z.1) (hW : ∀ z ∈ cw, z.1 ≤ (sidePt M.W p 0).1)
    {r : ℝ} (hr : 0 < r) :
    ∃ we uw ze zw : Point, we.2 = (M.W.vtx p).2 ∧ uw.2 = (M.W.vtx p).2 ∧
      (M.W.vtx p).1 < we.1 ∧ uw.1 < (M.W.vtx p).1 ∧
      ce = Chazelle.segment (M.W.vtx p) we ∧ cw = Chazelle.segment (M.W.vtx p) uw ∧
      (∀ s ∈ Ioo (0 : ℝ) 1, lerp (M.W.vtx p) we s ∈ M.D) ∧
      (∀ s ∈ Ioo (0 : ℝ) 1, lerp (M.W.vtx p) uw s ∈ M.D) ∧
      (∀ (p' : ℕ) (t' : ℝ), SideAttach M.W ce p' t' → sidePt M.W p' t' ≠ M.W.vtx p →
        sidePt M.W p' t' = we) ∧
      (∀ (p' : ℕ) (t' : ℝ), SideAttach M.W cw p' t' → sidePt M.W p' t' ≠ M.W.vtx p →
        sidePt M.W p' t' = uw) ∧
      ze ∈ ce ∧ ze ∈ M.D ∧ ze.2 = (M.W.vtx p).2 ∧ (M.W.vtx p).1 < ze.1 ∧
        dist ze (M.W.vtx p) < r ∧
      zw ∈ cw ∧ zw ∈ M.D ∧ zw.2 = (M.W.vtx p).2 ∧ zw.1 < (M.W.vtx p).1 ∧
        dist zw (M.W.vtx p) < r := by
  have hv0 := Chazelle.Chain.sidePt_zero M.W p
  obtain ⟨we, hwev, hwey, hceq, hopene, -, hothe⟩ := hM.attach_other_end hce hAe
  obtain ⟨uw, huwv, huwy, hcwq, hopenw, -, hothw⟩ := hM.attach_other_end hcw hAw
  obtain ⟨se, hse0, hse1, hsed, -⟩ := exists_left_on_chord hAe hceq hwev hr
  obtain ⟨sw, hsw0, hsw1, hswd, -⟩ := exists_left_on_chord hAw hcwq huwv hr
  Ξ' hv0 at hE hW hwev hwey hceq hopene hothe huwv huwy hcwq hopenw hothw hsed hswd
  set v := M.W.vtx p
  have hlte := lt_of_le_of_ne
    (hE we (by rw [hceq]; exact Geometry.right_mem_segment _ _))
    (fun h => hwev (point_ext h.symm hwey))
  have hltw := lt_of_le_of_ne
    (hW uw (by rw [hcwq]; exact Geometry.right_mem_segment _ _))
    (fun h => huwv (point_ext h huwy))
  refine ⟨we, uw, lerp v we se, lerp v uw sw, hwey, huwy, hlte, hltw, hceq, hcwq, hopene, hopenw,
    hothe, hothw, by rw [hceq]; exact lerp_mem_segment _ _ hse0.le hse1.le,
    hopene se ⟨hse0, hse1⟩, by simp only [Geometry.lerp_snd, hwey]; ring,
    by simp only [Geometry.lerp_fst]; nlinarith, hsed,
    by rw [hcwq]; exact lerp_mem_segment _ _ hsw0.le hsw1.le,
    hopenw sw ⟨hsw0, hsw1⟩, by simp only [Geometry.lerp_snd, huwy]; ring,
    by simp only [Geometry.lerp_fst]; nlinarith, hswd⟩

/-- An open half-plane `{0 < det a b x}` is open. -/
theorem isOpen_det_pos (a b : Point) : IsOpen {x : Point | 0 < 1 * det a b x} :=
  isOpen_lt continuous_const (by unfold det; fun_prop)

/-- **The tie, leaving edge down.** -/
theorem tie_down (hM : WalkAx M) {F : Set (Set Point)} (hF : F ⊆ M.Adm) (hfin : F.Finite)
    {ce cw : Set Point} (hce : ce ∈ F) (hcw : cw ∈ F) {p : ℕ} {t : ℝ}
    (hAe : SideAttach M.W ce p t) (hAw : SideAttach M.W cw p t)
    (hE : ∀ z ∈ ce, (sidePt M.W p t).1 ≤ z.1) (hW : ∀ z ∈ cw, z.1 ≤ (sidePt M.W p t).1)
    (hdown : (M.wb p).2 < (M.wa p).2) :
    t = 0 ∧ M.TieDown F ce cw p := by
  obtain ⟨rfl, s₁, s₂, hs₁, hs₂, -, hsW⟩ := hM.tie_setup (hF hce) (hF hcw) hAe hAw hE hW
  refine ⟨rfl, ?_⟩
  have hp := hAe.1
  have hv0 : sidePt M.W p 0 = M.W.vtx p := Chazelle.Chain.sidePt_zero M.W p
  obtain ⟨r, hr, hfree⟩ := hM.local_free hF hfin hp
  obtain ⟨we, uw, ze, zw, hwey, huwy, hlte, hltw, hceq, hcwq, hopene, hopenw, hothe, hothw,
    hzec, hzeD, hzey, hzex, hzed, hzwc, hzwD, hzwy, hzwx, hzwd⟩ :=
    hM.tie_ends (hF hce) (hF hcw) hAe hAw hE hW hr
  set v := M.W.vtx p with hv
  have hwa : M.wa p = v := rfl
  set B : Point := M.wb p - v with hB
  set a := M.W.vtx ((p + M.W.n - 1) % M.W.n) with ha
  set A : Point := a - v with hA
  have hB2 : B.2 < 0 := by simp only [hB, Prod.snd_sub]; rw [← hwa]; linarith
  obtain ⟨hA2, hsec⟩ := Tie.ccw_down hs₂ hB2 hsW
  have hA2' : A.2 < 0 := hA2
  have hleft : ∀ x : Point, (0 < sideCross B (x - v) ∨ 0 < (x - v).2 ∨ 0 < sideCross (x - v) A) →
      sideLeft M.W p 0 x := by
    intro x hx
    Ξ Chazelle.Chain.sideLeft_zero
    exact hsec _ hx
  have hcrossB : ∀ x : Point, sideCross B (x - v) = det v (M.wb p) x :=
    fun x => Chazelle.Chain.sideCross_out v (M.wb p) x
  have hcrossA : ∀ x : Point, sideCross (x - v) A = det a v x :=
    fun x => Chazelle.Chain.sideCross_in a v x
  -- the region below `ce` (after `v`)
  obtain ⟨U, hU, hUin, hUev⟩ := region_of_piece (σ := -1) hfree
    ((isOpen_ball).inter (isOpen_det_pos v (M.wb p)))
    ((convex_ball _ _).inter (Chazelle.Jordan.convex_det_pos _ _ 1)) inter_subset_left
    (Or.inr rfl) (fun x hx hy => hleft x (Or.inl (by
      rw [hcrossB]; have := hx.2; ϴ' mem_ofPred_eq, one_mul at this; exact this)))
    (z := ze) ⟨by rw [mem_ball]; exact hzed, by
      ϴ mem_ofPred_eq, one_mul
      Ξ ← hcrossB
      ϴ sideCross, Prod.fst_sub, Prod.snd_sub, hzey, sub_self, mul_zero, zero_sub
      nlinarith⟩ hzey
  have hUbelow : M.BelowOf ce U := hM.below_of_meets hF hfin hce hU hzec hzeD
    ((hUev ze ⟨by rw [mem_ball]; exact hzed, by
      ϴ mem_ofPred_eq, one_mul
      Ξ ← hcrossB
      ϴ sideCross, Prod.fst_sub, Prod.snd_sub, hzey, sub_self, mul_zero, zero_sub
      nlinarith⟩ hzey).mono fun δ h => by rwa [neg_one_mul, ← sub_eq_add_neg] at h)
  -- the region below `cw` (before `v`)
  obtain ⟨V, hV, hVin, hVev⟩ := region_of_piece (σ := -1) hfree
    ((isOpen_ball).inter (isOpen_det_pos a v))
    ((convex_ball _ _).inter (Chazelle.Jordan.convex_det_pos _ _ 1)) inter_subset_left
    (Or.inr rfl) (fun x hx hy => hleft x (Or.inr (Or.inr (by
      rw [hcrossA]; have := hx.2; ϴ' mem_ofPred_eq, one_mul at this; exact this))))
    (z := zw) ⟨by rw [mem_ball]; exact hzwd, by
      ϴ mem_ofPred_eq, one_mul
      Ξ ← hcrossA
      ϴ sideCross, Prod.fst_sub, Prod.snd_sub, hzwy, sub_self, zero_mul, sub_zero
      exact mul_pos_of_neg_of_neg (⟡) hA2'⟩ hzwy
  have hVbelow : M.BelowOf cw V := hM.below_of_meets hF hfin hcw hV hzwc hzwD
    ((hVev zw ⟨by rw [mem_ball]; exact hzwd, by
      ϴ mem_ofPred_eq, one_mul
      Ξ ← hcrossA
      ϴ sideCross, Prod.fst_sub, Prod.snd_sub, hzwy, sub_self, zero_mul, sub_zero
      exact mul_pos_of_neg_of_neg (⟡) hA2'⟩ hzwy).mono fun δ h => by rwa [neg_one_mul, ← sub_eq_add_neg] at h)
  -- the region above both
  obtain ⟨R, hR, -, hRev⟩ := region_of_piece (σ := 1) hfree isOpen_ball (convex_ball _ _)
    subset_rfl (Or.inl rfl) (fun x hx hy => hleft x (Or.inr (Or.inl (by
      simp only [Prod.snd_sub]; linarith))))
    (z := ze) (by rw [mem_ball]; exact hzed) hzey
  have hRe : M.AboveOf ce R := hM.above_of_meets hF hfin hce hR hzec hzeD
    ((hRev ze (by rw [mem_ball]; exact hzed) hzey).mono fun δ h => by rwa [one_mul] at h)
  have hRw : M.AboveOf cw R := hM.above_of_meets hF hfin hcw hR hzwc hzwD
    ((hRev zw (by rw [mem_ball]; exact hzwd) hzwy).mono fun δ h => by rwa [one_mul] at h)
  refine ⟨U, V, R, hU, hV, hR, hUbelow, hVbelow, hRe, hRw, ?_, ?_, ?_⟩
  · -- just after `v`
    refine faces_after_of hr (Or.inr rfl) (⟡) (fun x hx h1 h2 => hUin x
      ⟨hx, ?_⟩ h2)
    simp only [mem_ofPred_eq, one_mul]; rw [← hcrossB]; exact h1
  · -- just before `v`
    set q := (p + M.W.n - 1) % M.W.n
    have hwbq : M.wb q = v := by
      show M.W.vtx ((q + 1) % M.W.n) = M.W.vtx p
      Ξ prev_succ hp
    have hwaq : M.wa q = a := rfl
    have hA2'' : 0 < -1 * ((M.wa q).2 - (M.wb q).2) := by
      rw [hwbq, hwaq]; have : A.2 = a.2 - v.2 := rfl; linarith
    refine faces_before_of hr (Or.inr rfl) hA2'' (fun x hx h1 h2 => hVin x ⟨by rw [hwbq] at hx; exact hx, ?_⟩ (by rw [hwbq] at h2; exact h2))
    simp only [mem_ofPred_eq, one_mul]; rw [← hcrossA]; Ξ' hwbq, hwaq at h1; exact h1
  · -- the nesting order
    intro pe pw te tw hBe hBe' hBw hBw'
    have hpe : sidePt M.W pe te = we := hothe pe te hBe hBe'
    have hpw : sidePt M.W pw tw = uw := hothw pw tw hBw hBw'
    obtain ⟨py, ty, hpy, hty0, hty1, hRf⟩ := hM.exists_faces hF hfin hR
    have hne1 : sidePt M.W p 0 ≠ sidePt M.W pe te := by rw [hv0]; exact Ne.symm hBe'
    have hne2 : sidePt M.W pw tw ≠ sidePt M.W p 0 := by rw [hv0]; exact hBw'
    have hab : (p : ℝ) ≠ pe + te := by
      have := key_ne_of_pt_ne hAe hBe hne1; rwa [add_zero] at this
    have hac : (p : ℝ) ≠ pw + tw := by
      have := key_ne_of_pt_ne hAw hBw (Ne.symm hne2); rwa [add_zero] at this
    have hbc : (pe : ℝ) + te ≠ pw + tw := key_ne_of_pt_ne hBe hBw (by
      rw [hpe, hpw]; intro h; Ξ' h at hlte; linarith)
    have hya : (py : ℝ) + ty ≠ p := by
      intro h
      have := (sideKey_inj hty0.le hty1 le_rfl zero_lt_one (by rw [add_zero]; exact h)).2
      linarith
    refine Tie.cyc_cover hab hac hbc hya (fun hin => ?_) (fun hin => ?_)
    · refine hM.not_left_of_after hF hce hAe hBe hne1 hR hpy ⟨hty0, hty1⟩
        (by rw [add_zero]; exact hin) hRf ?_
      Ξ hv0, hpe
      have hm : lerp v we (1 / 2) ∈ ce := by
        rw [hceq]; exact lerp_mem_segment _ _ (⊛) (⊛)
      refine (eventually_mul_pos (hRe _ hm (hopene _ ⟨⊛, ⊛⟩))
        (sub_pos.2 hlte)).mono fun δ h => ?_
      rw [Chazelle.Core.offset_mid_ab hwey.symm]; exact h
    · refine hM.not_left_of_after hF hcw hBw hAw hne2 hR hpy ⟨hty0, hty1⟩
        (by rw [add_zero]; exact hin) hRf ?_
      Ξ hv0, hpw
      have hm : lerp uw v (1 / 2) ∈ cw := by
        rw [hcwq, Geometry.segment_comm]; exact lerp_mem_segment _ _ (⊛) (⊛)
      refine (eventually_mul_pos (hRw _ hm (open_rev hopenw _ ⟨⊛, ⊛⟩))
        (sub_pos.2 hltw)).mono fun δ h => ?_
      rw [Chazelle.Core.offset_mid_ab huwy]; exact h

/-- **The tie, leaving edge up.** -/
theorem tie_up (hM : WalkAx M) {F : Set (Set Point)} (hF : F ⊆ M.Adm) (hfin : F.Finite)
    {ce cw : Set Point} (hce : ce ∈ F) (hcw : cw ∈ F) {p : ℕ} {t : ℝ}
    (hAe : SideAttach M.W ce p t) (hAw : SideAttach M.W cw p t)
    (hE : ∀ z ∈ ce, (sidePt M.W p t).1 ≤ z.1) (hW : ∀ z ∈ cw, z.1 ≤ (sidePt M.W p t).1)
    (hup : (M.wa p).2 < (M.wb p).2) :
    t = 0 ∧ M.TieUp F ce cw p := by
  obtain ⟨rfl, s₁, s₂, hs₁, hs₂, hsE, -⟩ := hM.tie_setup (hF hce) (hF hcw) hAe hAw hE hW
  refine ⟨rfl, ?_⟩
  have hp := hAe.1
  have hv0 : sidePt M.W p 0 = M.W.vtx p := Chazelle.Chain.sidePt_zero M.W p
  obtain ⟨r, hr, hfree⟩ := hM.local_free hF hfin hp
  obtain ⟨we, uw, ze, zw, hwey, huwy, hlte, hltw, hceq, hcwq, hopene, hopenw, hothe, hothw,
    hzec, hzeD, hzey, hzex, hzed, hzwc, hzwD, hzwy, hzwx, hzwd⟩ :=
    hM.tie_ends (hF hce) (hF hcw) hAe hAw hE hW hr
  set v := M.W.vtx p with hv
  have hwa : M.wa p = v := rfl
  set B : Point := M.wb p - v with hB
  set a := M.W.vtx ((p + M.W.n - 1) % M.W.n) with ha
  set A : Point := a - v with hA
  have hB2 : 0 < B.2 := by simp only [hB, Prod.snd_sub]; rw [← hwa]; linarith
  obtain ⟨hA2, hsec⟩ := Tie.ccw_up hs₁ hB2 hsE
  have hA2' : 0 < A.2 := hA2
  have hleft : ∀ x : Point, (0 < sideCross B (x - v) ∨ (x - v).2 < 0 ∨ 0 < sideCross (x - v) A) →
      sideLeft M.W p 0 x := by
    intro x hx
    Ξ Chazelle.Chain.sideLeft_zero
    exact hsec _ hx
  have hcrossB : ∀ x : Point, sideCross B (x - v) = det v (M.wb p) x :=
    fun x => Chazelle.Chain.sideCross_out v (M.wb p) x
  have hcrossA : ∀ x : Point, sideCross (x - v) A = det a v x :=
    fun x => Chazelle.Chain.sideCross_in a v x
  have hzwB : zw ∈ ball v r ∩ {x | 0 < 1 * det v (M.wb p) x} := ⟨by rw [mem_ball]; exact hzwd, by
      ϴ mem_ofPred_eq, one_mul
      Ξ ← hcrossB
      ϴ sideCross, Prod.fst_sub, Prod.snd_sub, hzwy, sub_self, mul_zero, zero_sub
      nlinarith⟩
  have hzeA : ze ∈ ball v r ∩ {x | 0 < 1 * det a v x} := ⟨by rw [mem_ball]; exact hzed, by
      ϴ mem_ofPred_eq, one_mul
      Ξ ← hcrossA
      ϴ sideCross, Prod.fst_sub, Prod.snd_sub, hzey, sub_self, zero_mul, sub_zero
      exact mul_pos (⟡) hA2'⟩
  -- the region above `cw` (after `v`)
  obtain ⟨U, hU, hUin, hUev⟩ := region_of_piece (σ := 1) hfree
    ((isOpen_ball).inter (isOpen_det_pos v (M.wb p)))
    ((convex_ball _ _).inter (Chazelle.Jordan.convex_det_pos _ _ 1)) inter_subset_left
    (Or.inl rfl) (fun x hx hy => hleft x (Or.inl (by
      rw [hcrossB]; have := hx.2; ϴ' mem_ofPred_eq, one_mul at this; exact this)))
    hzwB hzwy
  have hUabove : M.AboveOf cw U := hM.above_of_meets hF hfin hcw hU hzwc hzwD
    ((hUev zw hzwB hzwy).mono fun δ h => by rwa [one_mul] at h)
  -- the region above `ce` (before `v`)
  obtain ⟨V, hV, hVin, hVev⟩ := region_of_piece (σ := 1) hfree
    ((isOpen_ball).inter (isOpen_det_pos a v))
    ((convex_ball _ _).inter (Chazelle.Jordan.convex_det_pos _ _ 1)) inter_subset_left
    (Or.inl rfl) (fun x hx hy => hleft x (Or.inr (Or.inr (by
      rw [hcrossA]; have := hx.2; ϴ' mem_ofPred_eq, one_mul at this; exact this))))
    hzeA hzey
  have hVabove : M.AboveOf ce V := hM.above_of_meets hF hfin hce hV hzec hzeD
    ((hVev ze hzeA hzey).mono fun δ h => by rwa [one_mul] at h)
  -- the region below both
  obtain ⟨R, hR, -, hRev⟩ := region_of_piece (σ := -1) hfree isOpen_ball (convex_ball _ _)
    subset_rfl (Or.inr rfl) (fun x hx hy => hleft x (Or.inr (Or.inl (by
      simp only [Prod.snd_sub]; linarith))))
    (z := ze) (by rw [mem_ball]; exact hzed) hzey
  have hRe : M.BelowOf ce R := hM.below_of_meets hF hfin hce hR hzec hzeD
    ((hRev ze (by rw [mem_ball]; exact hzed) hzey).mono fun δ h => by
      rwa [neg_one_mul, ← sub_eq_add_neg] at h)
  have hRw : M.BelowOf cw R := hM.below_of_meets hF hfin hcw hR hzwc hzwD
    ((hRev zw (by rw [mem_ball]; exact hzwd) hzwy).mono fun δ h => by
      rwa [neg_one_mul, ← sub_eq_add_neg] at h)
  refine ⟨U, V, R, hU, hV, hR, hUabove, hVabove, hRe, hRw, ?_, ?_, ?_⟩
  · -- just after `v`
    refine faces_after_of hr (Or.inl rfl) (⟡) (fun x hx h1 h2 => hUin x
      ⟨hx, ?_⟩ h2)
    simp only [mem_ofPred_eq, one_mul]; rw [← hcrossB]; exact h1
  · -- just before `v`
    set q := (p + M.W.n - 1) % M.W.n
    have hwbq : M.wb q = v := by
      show M.W.vtx ((q + 1) % M.W.n) = M.W.vtx p
      Ξ prev_succ hp
    have hwaq : M.wa q = a := rfl
    have hA2'' : 0 < 1 * ((M.wa q).2 - (M.wb q).2) := by
      rw [hwbq, hwaq]; have : A.2 = a.2 - v.2 := rfl; linarith
    refine faces_before_of hr (Or.inl rfl) hA2'' (fun x hx h1 h2 =>
      hVin x ⟨by rw [hwbq] at hx; exact hx, ?_⟩ (by rw [hwbq] at h2; exact h2))
    simp only [mem_ofPred_eq, one_mul]; rw [← hcrossA]; Ξ' hwbq, hwaq at h1; exact h1
  · -- the nesting order
    intro pe pw te tw hBe hBe' hBw hBw'
    have hpe : sidePt M.W pe te = we := hothe pe te hBe hBe'
    have hpw : sidePt M.W pw tw = uw := hothw pw tw hBw hBw'
    obtain ⟨py, ty, hpy, hty0, hty1, hRf⟩ := hM.exists_faces hF hfin hR
    have hne1 : sidePt M.W p 0 ≠ sidePt M.W pw tw := by rw [hv0]; exact Ne.symm hBw'
    have hne2 : sidePt M.W pe te ≠ sidePt M.W p 0 := by rw [hv0]; exact hBe'
    have hab : (p : ℝ) ≠ pw + tw := by
      have := key_ne_of_pt_ne hAw hBw hne1; rwa [add_zero] at this
    have hac : (p : ℝ) ≠ pe + te := by
      have := key_ne_of_pt_ne hAe hBe (Ne.symm hne2); rwa [add_zero] at this
    have hbc : (pw : ℝ) + tw ≠ pe + te := key_ne_of_pt_ne hBw hBe (by
      rw [hpe, hpw]; intro h; Ξ' ← h at hlte; linarith)
    have hya : (py : ℝ) + ty ≠ p := by
      intro h
      have := (sideKey_inj hty0.le hty1 le_rfl zero_lt_one (by rw [add_zero]; exact h)).2
      linarith
    refine Tie.cyc_cover hab hac hbc hya (fun hin => ?_) (fun hin => ?_)
    · refine hM.not_left_of_after hF hcw hAw hBw hne1 hR hpy ⟨hty0, hty1⟩
        (by rw [add_zero]; exact hin) hRf ?_
      Ξ hv0, hpw
      have hm : lerp v uw (1 / 2) ∈ cw := by
        rw [hcwq]; exact lerp_mem_segment _ _ (⊛) (⊛)
      refine (eventually_mul_pos (hRw _ hm (hopenw _ ⟨⊛, ⊛⟩))
        (sub_pos.2 hltw)).mono fun δ h => ?_
      Ξ Chazelle.Core.offset_mid_ab huwy.symm
      convert h using 2; ring
    · refine hM.not_left_of_after hF hce hBe hAe hne2 hR hpy ⟨hty0, hty1⟩
        (by rw [add_zero]; exact hin) hRf ?_
      Ξ hv0, hpe
      have hm : lerp we v (1 / 2) ∈ ce := by
        rw [hceq, Geometry.segment_comm]; exact lerp_mem_segment _ _ (⊛) (⊛)
      refine (eventually_mul_pos (hRe _ hm (open_rev hopene _ ⟨⊛, ⊛⟩))
        (sub_pos.2 hlte)).mono fun δ h => ?_
      Ξ Chazelle.Core.offset_mid_ab hwey
      convert h using 2; ring

/-- **Two distinct chords of `F` at one position go opposite ways.** -/
theorem tie_pair (hM : WalkAx M) {F : Set (Set Point)} (hF : F ⊆ M.Adm) {c c' : Set Point}
    (hc : c ∈ F) (hc' : c' ∈ F) (hne : c ≠ c') {p : ℕ} {t : ℝ} (hA : SideAttach M.W c p t)
    (hA' : SideAttach M.W c' p t) :
    ((∀ z ∈ c, (sidePt M.W p t).1 ≤ z.1) ∧ (∀ z ∈ c', z.1 ≤ (sidePt M.W p t).1)) ∨
      ((∀ z ∈ c, z.1 ≤ (sidePt M.W p t).1) ∧ (∀ z ∈ c', (sidePt M.W p t).1 ≤ z.1)) := by
  rcases hM.attach_dir (hF hc) hA with h | h <;> rcases hM.attach_dir (hF hc') hA' with h' | h'
  · exact absurd (hM.attach_east_unique hF hc hc' hA hA' h h') hne
  · exact Or.inl ⟨h, h'⟩
  · exact Or.inr ⟨h, h'⟩
  · exact absurd (hM.attach_west_unique hF hc hc' hA hA' h h') hne

/-- **The shape of a tie**: for an east chord `ce` and a west chord `cw` of `F` attached at the
same position `(p, t)`, `t = 0`, the leaving walk edge is not horizontal, and every chord of `F`
attached at that position is `ce` or `cw` (so at most two chords are attached at one
position). -/
theorem tie_shape (hM : WalkAx M) {F : Set (Set Point)} (hF : F ⊆ M.Adm) {ce cw : Set Point}
    (hce : ce ∈ F) (hcw : cw ∈ F) {p : ℕ} {t : ℝ} (hAe : SideAttach M.W ce p t)
    (hAw : SideAttach M.W cw p t) (hE : ∀ z ∈ ce, (sidePt M.W p t).1 ≤ z.1)
    (hW : ∀ z ∈ cw, z.1 ≤ (sidePt M.W p t).1) :
    t = 0 ∧ (M.wb p).2 ≠ (M.wa p).2 ∧ ∀ c ∈ F, SideAttach M.W c p t → c = ce ∨ c = cw := by
  obtain ⟨ht, s₁, s₂, hs₁, hs₂, hsE, hsW⟩ := hM.tie_setup (hF hce) (hF hcw) hAe hAw hE hW
  refine ⟨ht, fun h => (Tie.ccw_ew hs₁ hs₂ hsE hsW).1 (⍟ Prod.snd_sub, h, sub_self),
    fun c hc hA => ?_⟩
  rcases hM.attach_dir (hF hc) hA with h | h
  · exact Or.inl (hM.attach_east_unique hF hc hce hA hAe h hE)
  · exact Or.inr (hM.attach_west_unique hF hc hcw hA hAw h hW)

end WalkAx

/-! ## The good-model form -/

end

end Chazelle.Core
