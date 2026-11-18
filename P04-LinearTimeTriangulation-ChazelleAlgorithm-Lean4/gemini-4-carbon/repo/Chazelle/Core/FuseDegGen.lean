module

public import Chazelle.Core.WalkEmbed

/-!
# The degree of the revised fusion, part 1: exit chords seen from the walk (general models)

Facts about one admissible family `F` of a model with the walk axioms, used to bound degrees by
walk combinatorics.

* `sep_false`: a region cannot face the walk on both sides of one of its chords' key pairs.
* `faced_after`, `faced_before`: the positions just after the start (before the end) of an arc
  face its region.
* `one_chord_interior`: at a position inside a walk edge at most one chord is attached.
* `sides_single`: if `e` is the only chord at one of its attachments, a region touching `e` is
  faced just after or just before that attachment.
* `edge_two`: at most two exit chords of a region are attached inside one walk edge (the
  *wall-gap* argument of the review).
-/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sideInArc sidePt sidePrev sideNext sideLeft sideLeftOf sideCcw
  sideCross sideDot TouchesIn freeIn regionsIn)
open Chazelle.Geometry (lerp)

namespace FuseDeg

variable {M : Model}

/-- The exit chords of a region. -/
def exits (M : Model) (F : Set (Set Point)) (R : Set Point) : Set (Set Point) :=
  {c | c ∈ F ∧ TouchesIn M.D c R}

/-- A region is faced just after the key `k`. -/
def FacedAfter (M : Model) (R : Set Point) (p : ℕ) (t : ℝ) : Prop :=
  ∀ᶠ s in 𝓝[>] (0 : ℝ), M.Faces p (t + s) R

/-- A region is faced just before the key `k`. -/
def FacedBefore (M : Model) (R : Set Point) (p : ℕ) (t : ℝ) : Prop :=
  ∀ᶠ s in 𝓝[>] (0 : ℝ), M.Faces p (t - s) R

/-- **A region is on one side of each chord**: it cannot face positions on both sides of the two
attachments of a chord. -/
theorem sep_false (hM : WalkAx M) {F : Set (Set Point)} {c : Set Point} (hc : c ∈ F)
    (hcA : c ∈ M.Adm) {pa pb : ℕ} {ta tb : ℝ} (hA : SideAttach M.W c pa ta)
    (hB : SideAttach M.W c pb tb) (hAB : sidePt M.W pa ta ≠ sidePt M.W pb tb) {R : Set Point}
    (hR : R ∈ M.regions F) {p p' : ℕ} {t t' : ℝ} (hp : p < M.W.n) (ht : t ∈ Ioo (0 : ℝ) 1)
    (hin : sideInArc (pa + ta) (pb + tb) (p + t)) (hf : M.Faces p t R) (hp' : p' < M.W.n)
    (ht' : t' ∈ Ioo (0 : ℝ) 1) (hin' : sideInArc (pb + tb) (pa + ta) (p' + t'))
    (hf' : M.Faces p' t' R) : False := by
  obtain ⟨K₁, K₂, hne, ⟨k₁, rfl⟩, ⟨k₂, rfl⟩, hK₁, hK₂⟩ := hM.split hcA hA hB hAB
  have hU1 := hM.region_subset_of_sector hc hR hp ht hf (hK₁ p hp t ht.1.le ht.2 hin)
  have hU2 := hM.region_subset_of_sector hc hR hp' ht' hf' (hK₂ p' hp' t' ht'.1.le ht'.2 hin')
  obtain ⟨u, hu⟩ := Chazelle.Chain.regionsIn_nonempty hR
  exact hne ((connectedComponentIn_eq (hU1 hu)).trans (connectedComponentIn_eq (hU2 hu)).symm)

/-- The keys just before the end of an interval are inside it. -/
theorem eventually_before_end {l r : ℝ} (_hlr : l ≠ r) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), sideInArc l r (r - ε) := by
  unfold sideInArc
  split_ifs with h
  · filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (show (0 : ℝ) < r - l by linarith)]
      with ε hε hε'
    have : (0 : ℝ) < ε := hε
    exact ⟨by linarith [hε'.2], by linarith⟩
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have : (0 : ℝ) < ε := hε
    right; linarith

theorem faced_after {F : Set (Set Point)} {R : Set Point} {p : ℕ} {t r : ℝ} (hp : p < M.W.n)
    (ht : 0 ≤ t) (ht1 : t < 1) (harc : M.IsArc F R (p + t) r) (hne : (p : ℝ) + t ≠ r) :
    FacedAfter M R p t := by
  unfold FacedAfter
  filter_upwards [WalkAx.exists_pos_after ht ht1, WalkAx.eventually_after_start hne]
    with s h1 h2
  exact harc.2.2.2.2.2.2 p (t + s) hp h1.1 h1.2 (by rw [← add_assoc]; exact h2)

theorem faced_before {F : Set (Set Point)} {R : Set Point} {p : ℕ} {t l : ℝ} (hp : p < M.W.n)
    (ht : 0 < t) (ht1 : t < 1) (harc : M.IsArc F R l (p + t)) (hne : l ≠ (p : ℝ) + t) :
    FacedBefore M R p t := by
  unfold FacedBefore
  filter_upwards [eventually_before_end hne, Ioo_mem_nhdsGT ht] with s h1 h2
  refine harc.2.2.2.2.2.2 p (t - s) hp (by linarith [h2.2]) (by linarith [h2.1]) ?_
  rw [show (p : ℝ) + (t - s) = p + t - s by ring]; exact h1

/-! ## Chords at one position -/

/-- An attached admissible chord from the point `a` in the horizontal direction of `x`. -/
theorem sameDir_eq (hM : WalkAx M) {c c' : Set Point} (hc : c ∈ M.Adm) (hc' : c' ∈ M.Adm)
    {p p' : ℕ} {t t' : ℝ} (hA : SideAttach M.W c p t) (hA' : SideAttach M.W c' p' t')
    (hpt : sidePt M.W p t = sidePt M.W p' t')
    (hdir : ∀ q q' : Point, q ∈ c → q' ∈ c' → q ≠ sidePt M.W p t → q' ≠ sidePt M.W p t →
      ((sidePt M.W p t).1 < q.1 ↔ (sidePt M.W p t).1 < q'.1)) : c = c' := by
  obtain ⟨e₁, hce₁, hne₁, hy₁, hop₁, hD₁⟩ := hM.chord_from hc hA
  obtain ⟨e₂, hce₂, hne₂, hy₂, hop₂, hD₂⟩ := hM.chord_from hc' hA'
  rw [← hpt] at hce₂ hne₂ hy₂ hop₂
  set a := sidePt M.W p t
  have key : ∀ {f f' : Point},
      (∀ s ∈ Ioo (0 : ℝ) 1, lerp a f s ∈ M.D) → f' ∉ M.D → f.2 = a.2 → f'.2 = a.2 →
      ((a.1 < f'.1 ∧ f'.1 < f.1) ∨ (f.1 < f'.1 ∧ f'.1 < a.1)) → False := by
    intro f f' hop hD hf hf' hbtw
    apply hD
    have e1 : f' = lerp a f ((f'.1 - a.1) / (f.1 - a.1)) := by
      have hfe : f.1 - a.1 ≠ 0 := by
        rcases hbtw with h | h <;> intro h' <;> linarith [h.1, h.2]
      apply Geometry.point_ext
      · simp only [Geometry.lerp_fst]; field_simp; ring
      · simp only [Geometry.lerp_snd]; rw [hf, hf']; ring
    rw [e1]
    apply hop
    rcases hbtw with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨div_pos (by linarith) (by linarith), (div_lt_one (by linarith)).2 (by linarith)⟩
    · exact ⟨div_pos_of_neg_of_neg (by linarith) (by linarith),
        (div_lt_one_of_neg (by linarith)).2 (by linarith)⟩
  have hsame := hdir e₁ e₂ (by rw [hce₁]; exact Geometry.right_mem_segment _ _)
    (by rw [hce₂]; exact Geometry.right_mem_segment _ _) hne₁ hne₂
  have hx₁ : e₁.1 ≠ a.1 := fun h => hne₁ (Geometry.point_ext h hy₁)
  have hx₂ : e₂.1 ≠ a.1 := fun h => hne₂ (Geometry.point_ext h hy₂)
  have heq : e₁ = e₂ := by
    apply Geometry.point_ext _ (hy₁.trans hy₂.symm)
    rcases lt_or_gt_of_ne hx₁ with h₁ | h₁
    · have h₂ : e₂.1 < a.1 := by
        rcases lt_or_gt_of_ne hx₂ with h | h
        · exact h
        · exact absurd (hsame.2 h) (not_lt.2 h₁.le)
      rcases lt_trichotomy e₁.1 e₂.1 with h | h | h
      · exact (key hop₁ hD₂ hy₁ hy₂ (Or.inr ⟨h, h₂⟩)).elim
      · exact h
      · exact (key hop₂ hD₁ hy₂ hy₁ (Or.inr ⟨h, h₁⟩)).elim
    · have h₂ : a.1 < e₂.1 := hsame.1 h₁
      rcases lt_trichotomy e₁.1 e₂.1 with h | h | h
      · exact (key hop₂ hD₁ hy₂ hy₁ (Or.inl ⟨h₁, h⟩)).elim
      · exact h
      · exact (key hop₁ hD₂ hy₁ hy₂ (Or.inl ⟨h₂, h⟩)).elim
  rw [hce₁, hce₂, heq]

/-- The far point of an attached chord leaves the position into its left sector. -/
theorem sideLeft_far (hM : WalkAx M) {c : Set Point} (hc : c ∈ M.Adm) {p : ℕ} {t : ℝ}
    (hA : SideAttach M.W c p t) {q : Point} (hq : q ∈ c) (hqa : q ≠ sidePt M.W p t) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), sideLeft M.W p t (lerp (sidePt M.W p t) q s) := by
  obtain ⟨e₁, hce₁, hne₁, -, -, -⟩ := hM.chord_from hc hA
  obtain ⟨-, -, -, -, r, hr, hl⟩ := hA
  have hqs : ∀ s ∈ Icc (0 : ℝ) 1, lerp (sidePt M.W p t) q s ∈ c := by
    intro s hs
    have hq' := hq
    rw [hce₁] at hq' ⊢
    obtain ⟨u, hu0, hu1, hqu⟩ := Geometry.mem_segment_iff_lerp.1 hq'
    have : lerp (sidePt M.W p t) q s = lerp (sidePt M.W p t) e₁ (s * u) := by
      rw [hqu]; apply Geometry.point_ext <;> simp [lerp] <;> ring
    rw [this]
    exact Geometry.lerp_mem_segment _ _ (by nlinarith [hs.1]) (by nlinarith [hs.2])
  have hd : 0 < dist q (sidePt M.W p t) := dist_pos.2 hqa
  filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (show (0 : ℝ) < min 1 (r / dist q
    (sidePt M.W p t)) from lt_min one_pos (div_pos hr hd))] with s hs hs'
  have hs0 : (0 : ℝ) < s := hs
  refine hl _ (hqs s ⟨hs0.le, (hs'.2.trans_le (min_le_left _ _)).le⟩) ?_ ?_
  · intro h
    have : lerp (sidePt M.W p t) q s = lerp (sidePt M.W p t) q 0 := by rw [Geometry.lerp_zero]; exact h
    have := Geometry.lerp_injective (Ne.symm hqa) this
    linarith
  · have e : dist (lerp (sidePt M.W p t) q s) (sidePt M.W p t) = s * dist q (sidePt M.W p t) := by
      rw [dist_comm, dist_eq_norm, dist_eq_norm]
      have : sidePt M.W p t - lerp (sidePt M.W p t) q s = s • (sidePt M.W p t - q) := by
        apply Geometry.point_ext <;> simp [lerp] <;> ring
      rw [this, norm_smul, Real.norm_eq_abs, abs_of_pos hs0, norm_sub_rev]
    rw [e]
    have h2 : s < r / dist q (sidePt M.W p t) := hs'.2.trans_le (min_le_right _ _)
    calc s * dist q (sidePt M.W p t) < r / dist q (sidePt M.W p t) * dist q (sidePt M.W p t) :=
          mul_lt_mul_of_pos_right h2 hd
      _ = r := div_mul_cancel₀ _ hd.ne'

/-- **At a position inside a walk edge at most one chord is attached.** -/
theorem one_chord_interior (hM : WalkAx M) {F : Set (Set Point)} (hF : F ⊆ M.Adm) {c c' : Set Point}
    (hc : c ∈ F) (hc' : c' ∈ F) {p : ℕ} {t : ℝ} (ht : 0 < t) (hA : SideAttach M.W c p t)
    (hA' : SideAttach M.W c' p t) : c = c' := by
  have hp := hA.1
  have ht1 := hA.2.2.1
  have hne := hM.nd p hp
  set u := M.W.vtx p
  set v := M.W.vtx ((p + 1) % M.W.n)
  -- the side of a point of a chord leaving the position
  have hside : ∀ d ∈ M.Adm, SideAttach M.W d p t → ∀ q ∈ d, q ≠ sidePt M.W p t →
      0 < -((q.1 - (sidePt M.W p t).1) * (v.2 - u.2)) := by
    intro d hd hAd q hq hqa
    obtain ⟨e₁, hce₁, hne₁, hy₁, -, -⟩ := hM.chord_from hd hAd
    have hqy : q.2 = (sidePt M.W p t).2 := by
      rw [hce₁] at hq
      obtain ⟨s, -, -, rfl⟩ := Geometry.mem_segment_iff_lerp.1 hq
      simp only [Geometry.lerp_snd]; rw [hy₁]; ring
    obtain ⟨s, hs1, hs2⟩ := ((sideLeft_far hM hd hAd hq hqa).and self_mem_nhdsWithin).exists
    rw [Chazelle.Chain.sideLeft_edge hne ⟨ht, ht1⟩] at hs1
    have hs0 : (0 : ℝ) < s := hs2
    have hpt : sidePt M.W p t = lerp u v t := rfl
    have e : det u v (lerp (sidePt M.W p t) q s) =
        s * -((q.1 - (sidePt M.W p t).1) * (v.2 - u.2)) := by
      unfold det
      simp only [Geometry.lerp_fst, Geometry.lerp_snd]
      rw [hqy, hpt]
      simp only [Geometry.lerp_fst, Geometry.lerp_snd]
      ring
    rw [e] at hs1
    exact pos_of_mul_pos_right hs1 hs0.le
  refine sameDir_eq hM (hF hc) (hF hc') hA hA' rfl fun q q' hq hq' hqa hq'a => ?_
  have h1 := hside c (hF hc) hA q hq hqa
  have h2 := hside c' (hF hc') hA' q' hq' hq'a
  constructor
  · intro h
    by_contra h'
    push Not at h'
    rcases h'.lt_or_eq with h'' | h''
    · nlinarith
    · rw [h'', sub_self, zero_mul, neg_zero] at h2; exact lt_irrefl _ h2
  · intro h
    by_contra h'
    push Not at h'
    rcases h'.lt_or_eq with h'' | h''
    · nlinarith
    · rw [h'', sub_self, zero_mul, neg_zero] at h1; exact lt_irrefl _ h1

/-- **A region touching the only chord at an attachment is faced next to it.** -/
theorem sides_single (hM : WalkAx M) {F : Set (Set Point)} (hF : F ⊆ M.Adm) (hfin : F.Finite)
    {e : Set Point} (he : e ∈ F) {p : ℕ} {t : ℝ} (hA : SideAttach M.W e p t)
    (hsole : ∀ c' ∈ F, SideAttach M.W c' p t → c' = e) {R : Set Point} (hR : R ∈ M.regions F)
    (hRe : TouchesIn M.D e R) :
    (∃ r, M.IsArc F R (p + t) r) ∨ (∃ l, M.IsArc F R l (p + t)) := by
  obtain ⟨U, V, l, r, hU, hV, hUV, harcU, harcV, htouch⟩ := hM.attach_face hF hfin he hA
  obtain ⟨hUe, hVe⟩ := htouch hsole
  obtain ⟨Up, Dn, -, -, -, -, hiff⟩ := chordSides_of_system (hM.sys F hF hfin) he
  have hR' := (hiff R hR).1 hRe
  have hU' := (hiff U hU).1 hUe
  have hV' := (hiff V hV).1 hVe
  rcases hR' with rfl | rfl <;> rcases hU' with rfl | rfl <;> rcases hV' with rfl | rfl
  · exact absurd rfl hUV
  · exact Or.inl ⟨r, harcU⟩
  · exact Or.inr ⟨l, harcV⟩
  · exact absurd rfl hUV
  · exact absurd rfl hUV
  · exact Or.inr ⟨l, harcV⟩
  · exact Or.inl ⟨r, harcU⟩
  · exact absurd rfl hUV

/-! ## Two chords at a walk vertex: the wedge -/

/-- Near a point, the chords of a finite admissible family lie on the horizontal line of the
point. -/
theorem chords_off_line (hM : WalkAx M) {F : Set (Set Point)} (hF : F ⊆ M.Adm) (hfin : F.Finite)
    (a : Point) : ∃ r > 0, ∀ x ∈ ball a r, x.2 ≠ a.2 → x ∉ ⋃₀ F := by
  have hev : ∀ᶠ x in 𝓝 a, ∀ c ∈ F, a ∉ c → x ∉ c := by
    refine (Filter.eventually_all_finite hfin).2 fun c hc => ?_
    by_cases hac : a ∈ c
    · exact Filter.Eventually.of_forall fun _ h => absurd hac h
    · obtain ⟨u, w, -, rfl, -, -, -, -⟩ := hM.ends c (hF hc)
      have hcl : IsClosed (Chazelle.segment u w) := Geometry.isClosed_segment _ _
      filter_upwards [hcl.isOpen_compl.mem_nhds hac] with x hx _ using hx
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  refine ⟨r, hr, fun x hx hxy ⟨c, hc, hxc⟩ => ?_⟩
  by_cases hac : a ∈ c
  · obtain ⟨u, w, -, rfl, huw, -, -, -⟩ := hM.ends c (hF hc)
    have hy : ∀ z ∈ Chazelle.segment u w, z.2 = u.2 := by
      intro z hz
      obtain ⟨s, -, -, rfl⟩ := Geometry.mem_segment_iff_lerp.1 hz
      simp only [Geometry.lerp_snd]; rw [huw]; ring
    exact hxy ((hy x hxc).trans (hy a hac).symm)
  · exact hball x hx c hc hac hxc

/-- **A sector part of a walk corner is a preconnected free set** when it lies in the left
sector of the walk at a vertex and off the horizontal line of the vertex. -/
theorem sector_side (hM : WalkAx M) {F : Set (Set Point)} (hF : F ⊆ M.Adm) (hfin : F.Finite)
    {p : ℕ} (hp : p < M.W.n) {a' b' : Point} (ha' : a' ≠ M.W.vtx p) (hb' : b' ≠ M.W.vtx p)
    (hsub : ∀ X : Point, sideCcw (b' - M.W.vtx p) X (a' - M.W.vtx p) →
      sideCcw (sideNext M.W p - M.W.vtx p) X (sidePrev M.W p 0 - M.W.vtx p) ∧ X.2 ≠ 0) :
    ∃ Sg : Set Point, Chazelle.Jordan.SectorSide (freeIn M.D F)ᶜ Sg a' (M.W.vtx p) b' 1 := by
  set a := M.W.vtx p
  obtain ⟨r₁, hr₁, hcl⟩ := hM.clean p hp 0 le_rfl one_pos
  obtain ⟨r₂, hr₂, hch⟩ := chords_off_line hM hF hfin a
  have hpt : sidePt M.W p 0 = a := Chazelle.Chain.sidePt_zero _ _
  refine ⟨_, Chazelle.Chain.sideSector ha' hb' (lt_min hr₁ hr₂) fun x hx hxS hl => hxS ?_⟩
  obtain ⟨hw, hne⟩ := hsub (x - a) hl
  have hx1 : x ∈ ball (sidePt M.W p 0) r₁ := by
    rw [hpt]; exact ball_subset_ball (min_le_left _ _) hx
  have hx2 : x ∈ ball a r₂ := ball_subset_ball (min_le_right _ _) hx
  have hxD : x ∈ M.D := by
    by_contra hnd
    apply hcl x hx1 hnd
    unfold sideLeft sideLeftOf
    rw [hpt]; exact hw
  refine ⟨hxD, fun hxF => hch x hx2 (fun h => hne ?_) hxF⟩
  simp only [Prod.snd_sub]; rw [h]; ring

/-- Regions meeting both ends of a sector part coincide. -/
theorem sector_regions_eq {F : Set (Set Point)} {Sg : Set Point} {a' v b' : Point}
    (hSg : Chazelle.Jordan.SectorSide (freeIn M.D F)ᶜ Sg a' v b' 1) {X Y : Set Point}
    (hX : X ∈ M.regions F) (hY : Y ∈ M.regions F)
    (hXo : ∀ᶠ s in 𝓝[>] (0 : ℝ), ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      Chazelle.Jordan.offset a' v (1 - s) δ ∈ X)
    (hYo : ∀ᶠ s in 𝓝[>] (0 : ℝ), ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      Chazelle.Jordan.offset v b' s δ ∈ Y) : X = Y := by
  obtain ⟨hSgS, hSgc, hoff⟩ := hSg
  have hSgF : Sg ⊆ freeIn M.D F := fun x hx => by simpa using hSgS hx
  obtain ⟨s, ⟨h1, h2⟩, h3⟩ := ((hoff.and hXo).and hYo).exists
  obtain ⟨δ, ⟨⟨d1, d2⟩, d3⟩, d4⟩ := ((h1.and h2).and h3).exists
  rw [one_mul] at d1 d2
  have hSgX : Sg ⊆ X := Chazelle.Chain.subset_regionsIn_of_inter hX hSgc hSgF ⟨_, d1, d3⟩
  have hSgY : Sg ⊆ Y := Chazelle.Chain.subset_regionsIn_of_inter hY hSgc hSgF ⟨_, d2, d4⟩
  rcases Chazelle.Chain.regionsIn_eq_or_disjoint hX hY with h | h
  · exact h
  · exact absurd (h.le_bot ⟨hSgX d1, hSgY d1⟩) (fun h => h)

/-- Offsets of a horizontal segment are vertical translates of its points. -/
theorem offset_horiz {u v : Point} (huv : u.2 = v.2) (t δ : ℝ) :
    Chazelle.Jordan.offset u v t δ =
      ((lerp u v t).1, (lerp u v t).2 + δ * (v.1 - u.1)) := by
  apply Geometry.point_ext
  · rw [Chazelle.Jordan.offset_fst]; simp only [Geometry.lerp_fst]; rw [huv]; ring
  · rw [Chazelle.Jordan.offset_snd]; simp only [Geometry.lerp_snd]

/-- **The offsets of a horizontal chord piece lie in its side regions.** -/
theorem offsets_side {d Up Dn : Set Point}
    (hside : ∀ z ∈ d, z ∈ M.D → ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      ((z.1, z.2 + δ) : Point) ∈ Up ∧ ((z.1, z.2 - δ) : Point) ∈ Dn)
    {u v : Point} (huv : u.2 = v.2) (hseg : ∀ s ∈ Ioo (0 : ℝ) 1, lerp u v s ∈ d ∧ lerp u v s ∈ M.D)
    {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    (0 < v.1 - u.1 → ∀ᶠ δ in 𝓝[>] (0 : ℝ), Chazelle.Jordan.offset u v s δ ∈ Up) ∧
      (v.1 - u.1 < 0 → ∀ᶠ δ in 𝓝[>] (0 : ℝ), Chazelle.Jordan.offset u v s δ ∈ Dn) := by
  obtain ⟨hzd, hzD⟩ := hseg s hs
  have h := hside _ hzd hzD
  refine ⟨fun hw => ?_, fun hw => ?_⟩
  · filter_upwards [eventually_mul_pos (h.mono fun _ h => h.1) hw] with δ hδ
    rw [offset_horiz huv]; exact hδ
  · filter_upwards [eventually_mul_pos (h.mono fun _ h => h.2) (neg_pos.2 hw)] with δ hδ
    rw [offset_horiz huv]
    convert hδ using 2; ring

/-- The sign case at a vertex whose left sector contains both horizontal directions. -/
theorem sign_case {b c E W : Point} (hE2 : E.2 = 0) (hE1 : 0 < E.1) (hW2 : W.2 = 0) (hW1 : W.1 < 0)
    (hbE : sideCcw b E c) (hbW : sideCcw b W c) (hb : b ≠ 0) (_hc : c ≠ 0) :
    (b.2 < 0 ∧ c.2 < 0) ∨ (0 < b.2 ∧ 0 < c.2) := by
  have hbb := Chazelle.Chain.sideDot_self_pos hb
  unfold sideCcw sideCross sideDot at *
  rw [hE2] at hbE
  rw [hW2] at hbW
  have hbq : 0 < b.1 ^ 2 + b.2 ^ 2 := by nlinarith
  have I1 : c.2 * (b.1 ^ 2 + b.2 ^ 2) =
      (b.1 * c.1 + b.2 * c.2) * b.2 + b.1 * (b.1 * c.2 - b.2 * c.1) := by ring
  rcases lt_trichotomy b.2 0 with hb2 | hb2 | hb2
  · left
    refine ⟨hb2, ?_⟩
    rcases hbW with ⟨-, h2, -⟩ | ⟨-, h2 | h2⟩ | ⟨-, -, h3⟩ | ⟨h1, h2, -⟩
    · nlinarith
    · nlinarith
    · nlinarith
    · nlinarith
    · rw [h1, mul_zero, add_zero] at I1
      by_contra hc2; push Not at hc2; nlinarith
  · exfalso
    rw [hb2] at hbE hbW I1
    have hE' : (b.1 * c.2 - 0 * c.1 < 0 ∧ 0 < c.2) ∨
        (b.1 * c.2 - 0 * c.1 = 0 ∧ 0 < b.1 * c.1 + 0 * c.2 ∧ b.1 < 0) := by
      rcases hbE with ⟨-, h2, -⟩ | ⟨h1, h2 | h2⟩ | ⟨-, -, h3⟩ | ⟨h1, h2, h3⟩
      · exfalso; linarith
      · exfalso; linarith
      · left; exact ⟨h1, by nlinarith⟩
      · exfalso; linarith
      · right; refine ⟨h1, h2, ?_⟩
        rcases h3 with h3 | h3
        · exfalso; apply h3; ring
        · nlinarith
    have hW' : (b.1 * c.2 - 0 * c.1 < 0 ∧ c.2 < 0) ∨
        (b.1 * c.2 - 0 * c.1 = 0 ∧ 0 < b.1 * c.1 + 0 * c.2 ∧ 0 < b.1) := by
      rcases hbW with ⟨-, h2, -⟩ | ⟨h1, h2 | h2⟩ | ⟨-, -, h3⟩ | ⟨h1, h2, h3⟩
      · exfalso; linarith
      · exfalso; linarith
      · left; exact ⟨h1, by nlinarith⟩
      · exfalso; linarith
      · right; refine ⟨h1, h2, ?_⟩
        rcases h3 with h3 | h3
        · exfalso; apply h3; ring
        · nlinarith
    rcases hE' with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ <;> rcases hW' with ⟨k1, k2⟩ | ⟨k1, k2, k3⟩ <;> linarith
  · right
    refine ⟨hb2, ?_⟩
    rcases hbE with ⟨-, h2, -⟩ | ⟨-, h2 | h2⟩ | ⟨-, -, h3⟩ | ⟨h1, h2, -⟩
    · nlinarith
    · nlinarith
    · nlinarith
    · nlinarith
    · rw [h1, mul_zero, add_zero] at I1
      by_contra hc2; push Not at hc2; nlinarith

/-- **Two chords at a walk vertex: the wedge.**  Let the chords `dE` (to the east) and `dW` (to
the west) be attached at the walk vertex `p`.  Then, for `τ = 1` (wedge above) or `τ = -1`
(wedge below), the regions touching either chord are the region `X` between them on the side
`τ`, and the regions `U`, `V` faced just after and just before the vertex; `X` contains the
points just on the side `τ` of both chords, and the half-disk on the side `τ` near the vertex
lies in the domain. -/
theorem wedge_core (hM : WalkAx M) {F : Set (Set Point)} (hF : F ⊆ M.Adm) (hfin : F.Finite)
    {dE dW : Set Point} (hdE : dE ∈ F) (hdW : dW ∈ F) {p : ℕ}
    (hAE : SideAttach M.W dE p 0) (hAW : SideAttach M.W dW p 0) {qE qW : Point}
    (hcE : dE = Chazelle.segment (M.W.vtx p) qE) (hcW : dW = Chazelle.segment (M.W.vtx p) qW)
    (hyE : qE.2 = (M.W.vtx p).2) (hyW : qW.2 = (M.W.vtx p).2)
    (hopE : ∀ s ∈ Ioo (0 : ℝ) 1, lerp (M.W.vtx p) qE s ∈ M.D)
    (hopW : ∀ s ∈ Ioo (0 : ℝ) 1, lerp (M.W.vtx p) qW s ∈ M.D)
    (hlt : qW.1 < (M.W.vtx p).1) (hgt : (M.W.vtx p).1 < qE.1) :
    ∃ τ : ℝ, (τ = 1 ∨ τ = -1) ∧ ∃ (X U V : Set Point) (l r : ℝ), X ∈ M.regions F ∧
      M.IsArc F U (p + 0) r ∧ M.IsArc F V l (p + 0) ∧
      TouchesIn M.D dE X ∧ TouchesIn M.D dW X ∧
      (TouchesIn M.D dE U ∨ TouchesIn M.D dW U) ∧ (TouchesIn M.D dE V ∨ TouchesIn M.D dW V) ∧
      (∀ R ∈ M.regions F, TouchesIn M.D dE R → R = X ∨ R = U ∨ R = V) ∧
      (∀ R ∈ M.regions F, TouchesIn M.D dW R → R = X ∨ R = U ∨ R = V) ∧
      (∀ z ∈ dE ∪ dW, z ∈ M.D → ∀ᶠ δ in 𝓝[>] (0 : ℝ), ((z.1, z.2 + τ * δ) : Point) ∈ X) ∧
      ∃ r' > 0, ∀ x ∈ ball (M.W.vtx p) r', 0 < τ * (x.2 - (M.W.vtx p).2) → x ∈ M.D := by
  set a := M.W.vtx p with ha
  have hp := hAE.1
  have hn : 0 < M.W.n := by omega
  have hpt : sidePt M.W p 0 = a := Chazelle.Chain.sidePt_zero _ _
  set nx := sideNext M.W p with hnx
  set pv := sidePrev M.W p 0 with hpv
  have hpv' : pv = M.W.vtx ((p + M.W.n - 1) % M.W.n) := by
    rw [hpv]; unfold sidePrev; rw [ite_eq_left rfl]
  have hmodp : ((p + M.W.n - 1) % M.W.n + 1) % M.W.n = p := by
    rw [Nat.mod_add_mod, show p + M.W.n - 1 + 1 = p + M.W.n by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt hp]
  have hnxa : nx ≠ a := fun h => hM.nd p hp h.symm
  have hpva : pv ≠ a := by
    rw [hpv']; intro h
    have := hM.nd ((p + M.W.n - 1) % M.W.n) (Nat.mod_lt _ hn)
    rw [hmodp] at this
    exact this h
  set B := nx - a
  set Av := pv - a
  set E := qE - a
  set Wv := qW - a
  have hE2 : E.2 = 0 := by simp [E, hyE]
  have hE1 : 0 < E.1 := by simp only [E, Prod.fst_sub]; linarith
  have hW2 : Wv.2 = 0 := by simp [Wv, hyW]
  have hW1 : Wv.1 < 0 := by simp only [Wv, Prod.fst_sub]; linarith
  have hB0 : B ≠ 0 := sub_ne_zero.2 hnxa
  have hA0 : Av ≠ 0 := sub_ne_zero.2 hpva
  have hE0 : E ≠ 0 := fun h => by rw [h] at hE1; simp at hE1
  have hW0 : Wv ≠ 0 := fun h => by rw [h] at hW1; simp at hW1
  have hqEa : qE ≠ a := fun h => by rw [h] at hgt; exact lt_irrefl _ hgt
  have hqWa : qW ≠ a := fun h => by rw [h] at hlt; exact lt_irrefl _ hlt
  -- both horizontal directions lie in the left sector of the walk
  have hdir : ∀ {d : Set Point} {q : Point}, d ∈ F → SideAttach M.W d p 0 →
      d = Chazelle.segment a q → q ≠ a → sideCcw B (q - a) Av := by
    intro d q hd hAd hcd hqa
    have hqd : q ∈ d := by rw [hcd]; exact Geometry.right_mem_segment _ _
    obtain ⟨s, hs1, hs2⟩ := ((sideLeft_far hM (hF hd) hAd hqd (by rw [hpt]; exact hqa)).and
      self_mem_nhdsWithin).exists
    have hs0 : (0 : ℝ) < s := hs2
    unfold sideLeft sideLeftOf at hs1
    rw [hpt] at hs1
    have e : lerp a q s - a = s • (q - a) := by
      apply Geometry.point_ext <;> simp [lerp]
    rw [e, Chazelle.Chain.sideCcw_smul hs0] at hs1
    exact hs1
  have hBE : sideCcw B E Av := hdir hdE hAE hcE hqEa
  have hBW : sideCcw B Wv Av := hdir hdW hAW hcW hqWa
  -- the region faces and sides
  obtain ⟨U, V, l, r, hU, hV, -, harcU, harcV, -⟩ := hM.attach_face hF hfin hdE hAE
  have hne : F.Nonempty := ⟨dE, hdE⟩
  have hUa := faced_after hp le_rfl one_pos harcU (WalkAx.arc_cuts hne harcU).2.2
  have hVne : l ≠ (p : ℝ) + 0 := (WalkAx.arc_cuts hne harcV).2.2
  -- the positions just before the vertex face `V`
  have hVb : ∀ᶠ s in 𝓝[>] (0 : ℝ), M.Faces ((p + M.W.n - 1) % M.W.n) (1 - s) V := by
    rcases Nat.eq_zero_or_pos p with h0 | h0
    · have hl0 : 0 ≤ l := harcV.1
      have hln : l < M.W.n := harcV.2.1
      have hl0' : 0 < l := lt_of_le_of_ne hl0 (fun h => hVne (by rw [← h, h0]; simp))
      filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (show (0 : ℝ) < min 1 (M.W.n - l) from
        lt_min one_pos (by linarith))] with s hs hs'
      have hs0 : (0 : ℝ) < s := hs
      have hs1 : s < 1 := hs'.2.trans_le (min_le_left _ _)
      have hs2 : s < M.W.n - l := hs'.2.trans_le (min_le_right _ _)
      have e : (0 + M.W.n - 1) % M.W.n = M.W.n - 1 := by
        rw [Nat.mod_eq_of_lt (show 0 + M.W.n - 1 < M.W.n by omega)]; omega
      rw [h0, e]
      refine harcV.2.2.2.2.2.2 _ _ (by omega) (by linarith) (by linarith) ?_
      have hc : ((M.W.n - 1 : ℕ) : ℝ) = M.W.n - 1 := by rw [Nat.cast_sub (by omega)]; simp
      rw [hc, h0]
      unfold sideInArc
      rw [ite_eq_right (by push_cast; linarith)]
      left; linarith
    · filter_upwards [eventually_before_end hVne, Ioo_mem_nhdsGT one_pos] with s h1 h2
      have e : (p + M.W.n - 1) % M.W.n = p - 1 := by
        rw [show p + M.W.n - 1 = p - 1 + M.W.n by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt (by omega)]
      rw [e]
      refine harcV.2.2.2.2.2.2 _ _ (by omega) (by linarith [h2.2]) (by linarith [h2.1]) ?_
      have hc : ((p - 1 : ℕ) : ℝ) = p - 1 := by rw [Nat.cast_sub (by omega)]; simp
      rw [hc, show (p : ℝ) - 1 + (1 - s) = p + 0 - s by ring]
      exact h1
  obtain ⟨UpE, DnE, hUpE, hDnE, -, hsideE, hiffE⟩ := chordSides_of_system (hM.sys F hF hfin) hdE
  obtain ⟨UpW, DnW, hUpW, hDnW, -, hsideW, hiffW⟩ := chordSides_of_system (hM.sys F hF hfin) hdW
  -- points of the chords
  have hsegE : ∀ s ∈ Ioo (0 : ℝ) 1, lerp a qE s ∈ dE ∧ lerp a qE s ∈ M.D := fun s hs =>
    ⟨by rw [hcE]; exact Geometry.lerp_mem_segment _ _ hs.1.le hs.2.le, hopE s hs⟩
  have hsegW : ∀ s ∈ Ioo (0 : ℝ) 1, lerp a qW s ∈ dW ∧ lerp a qW s ∈ M.D := fun s hs =>
    ⟨by rw [hcW]; exact Geometry.lerp_mem_segment _ _ hs.1.le hs.2.le, hopW s hs⟩
  have hsegE' : ∀ s ∈ Ioo (0 : ℝ) 1, lerp qE a s ∈ dE ∧ lerp qE a s ∈ M.D := fun s hs => by
    rw [Geometry.lerp_symm]; exact hsegE (1 - s) ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have hsegW' : ∀ s ∈ Ioo (0 : ℝ) 1, lerp qW a s ∈ dW ∧ lerp qW a s ∈ M.D := fun s hs => by
    rw [Geometry.lerp_symm]; exact hsegW (1 - s) ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have ev1 : ∀ᶠ s in 𝓝[>] (0 : ℝ), s ∈ Ioo (0 : ℝ) 1 := by
    filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT one_pos] with s hs hs'
    exact ⟨hs, hs'.2⟩
  have ev2 : ∀ᶠ s in 𝓝[>] (0 : ℝ), 1 - s ∈ Ioo (0 : ℝ) 1 := by
    filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT one_pos] with s hs hs'
    have : (0 : ℝ) < s := hs
    exact ⟨by linarith [hs'.2], by linarith⟩
  -- walk offsets
  have hwa : M.wa p = a := rfl
  have hwb : M.wb p = nx := rfl
  have hwa' : M.wa ((p + M.W.n - 1) % M.W.n) = pv := hpv'.symm
  have hwb' : M.wb ((p + M.W.n - 1) % M.W.n) = a := by
    show M.W.vtx (((p + M.W.n - 1) % M.W.n + 1) % M.W.n) = a; rw [hmodp]
  have hUo : ∀ᶠ s in 𝓝[>] (0 : ℝ), ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      Chazelle.Jordan.offset a nx s δ ∈ U := by
    filter_upwards [hUa] with s hs
    rw [zero_add] at hs
    unfold Model.Faces at hs; rw [hwa, hwb] at hs; exact hs
  have hVo : ∀ᶠ s in 𝓝[>] (0 : ℝ), ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      Chazelle.Jordan.offset pv a (1 - s) δ ∈ V := by
    filter_upwards [hVb] with s hs
    unfold Model.Faces at hs; rw [hwa', hwb'] at hs; exact hs
  -- the clean half-disk
  obtain ⟨r₁, hr₁, hcl⟩ := hM.clean p hp 0 le_rfl one_pos
  have hhalf : ∀ X : Point, sideCcw B X Av → ∀ x ∈ ball a r₁, x - a = X → x ∈ M.D := by
    intro X hX x hx hxX
    by_contra hnd
    apply hcl x (by rw [hpt]; exact hx) hnd
    unfold sideLeft sideLeftOf; rw [hpt, hxX]; exact hX
  rcases sign_case hE2 hE1 hW2 hW1 hBE hBW hB0 hA0 with ⟨hb2, hc2⟩ | ⟨hb2, hc2⟩
  · -- wedge above
    have hup : ∀ X : Point, 0 < X.2 → sideCcw B X Av := by
      intro X hX
      refine Chazelle.Chain.sideCcw_sub_right hB0 hE0 hA0 hBE ?_
      unfold sideCcw sideCross; rw [hE2]
      right; left; exact ⟨by nlinarith, Or.inl (by nlinarith)⟩
    -- the wedge sector
    obtain ⟨Sw, hSw⟩ := sector_side hM hF hfin hp hqWa hqEa fun X hX => by
      have hX2 : 0 < X.2 := by
        unfold sideCcw sideCross sideDot at hX
        rw [hE2, hW2] at hX
        rcases hX with ⟨h1, -, -⟩ | ⟨h1, -⟩ | ⟨-, -, h3⟩ | ⟨-, h2, -⟩
        · simp at h1
        · simp at h1
        · nlinarith
        · nlinarith
      exact ⟨hup X hX2, hX2.ne'⟩
    have hUpEW : UpW = UpE := by
      refine sector_regions_eq hSw hUpW hUpE ?_ ?_
      · filter_upwards [ev2] with s hs
        exact (offsets_side hsideW hyW hsegW' hs).1 (by linarith)
      · filter_upwards [ev1] with s hs
        exact (offsets_side hsideE hyE.symm hsegE hs).1 (by linarith)
    -- the corner after the vertex: below `dE`, then the walk edge
    obtain ⟨Sa, hSa⟩ := sector_side hM hF hfin hp hqEa hnxa fun X hX => by
      refine ⟨Chazelle.Chain.sideCcw_sub_left hB0 hBE hX, ?_⟩
      unfold sideCcw sideCross at hX
      rw [hE2] at hX
      rcases hX with ⟨-, -, h3⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ <;> nlinarith
    have hDnEU : DnE = U := by
      refine sector_regions_eq hSa hDnE hU ?_ hUo
      filter_upwards [ev2] with s hs
      exact (offsets_side hsideE hyE hsegE' hs).2 (by linarith)
    -- the corner before the vertex: the walk edge, then below `dW`
    obtain ⟨Sb, hSb⟩ := sector_side hM hF hfin hp hpva hqWa fun X hX => by
      refine ⟨Chazelle.Chain.sideCcw_sub_right hB0 hW0 hA0 hBW hX, ?_⟩
      unfold sideCcw sideCross at hX
      rw [hW2] at hX
      rcases hX with ⟨-, h2, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ <;> nlinarith
    have hVDnW : V = DnW := by
      refine sector_regions_eq hSb hV hDnW hVo ?_
      filter_upwards [ev1] with s hs
      exact (offsets_side hsideW hyW.symm hsegW hs).2 (by linarith)
    refine ⟨1, Or.inl rfl, UpE, U, V, l, r, hUpE, harcU, harcV, (hiffE _ hUpE).2 (Or.inl rfl),
      (hiffW _ hUpE).2 (Or.inl hUpEW.symm), Or.inl ((hiffE _ hU).2 (Or.inr hDnEU.symm)),
      Or.inr ((hiffW _ hV).2 (Or.inr hVDnW)), fun R hR h => ?_, fun R hR h => ?_, ?_,
      r₁, hr₁, fun x hx hx2 => hhalf (x - a) (hup _ (by simp only [Prod.snd_sub]; linarith)) x hx rfl⟩
    · rcases (hiffE R hR).1 h with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl hDnEU)
    · rcases (hiffW R hR).1 h with rfl | rfl
      · exact Or.inl hUpEW
      · exact Or.inr (Or.inr hVDnW.symm)
    · rintro z (hz | hz) hzD
      · filter_upwards [hsideE z hz hzD] with δ hδ
        rw [one_mul]; exact hδ.1
      · filter_upwards [hsideW z hz hzD] with δ hδ
        rw [one_mul, ← hUpEW]; exact hδ.1
  · -- wedge below
    have hdown : ∀ X : Point, X.2 < 0 → sideCcw B X Av := by
      intro X hX
      refine Chazelle.Chain.sideCcw_sub_right hB0 hW0 hA0 hBW ?_
      unfold sideCcw sideCross; rw [hW2]
      right; left; exact ⟨by nlinarith, Or.inl (by nlinarith)⟩
    -- the wedge sector
    obtain ⟨Sw, hSw⟩ := sector_side hM hF hfin hp hqEa hqWa fun X hX => by
      have hX2 : X.2 < 0 := by
        unfold sideCcw sideCross sideDot at hX
        rw [hE2, hW2] at hX
        rcases hX with ⟨h1, -, -⟩ | ⟨h1, -⟩ | ⟨-, -, h3⟩ | ⟨-, h2, -⟩
        · simp at h1
        · simp at h1
        · nlinarith
        · nlinarith
      exact ⟨hdown X hX2, hX2.ne⟩
    have hDnEW : DnE = DnW := by
      refine sector_regions_eq hSw hDnE hDnW ?_ ?_
      · filter_upwards [ev2] with s hs
        exact (offsets_side hsideE hyE hsegE' hs).2 (by linarith)
      · filter_upwards [ev1] with s hs
        exact (offsets_side hsideW hyW.symm hsegW hs).2 (by linarith)
    -- the corner after the vertex: above `dW`, then the walk edge
    obtain ⟨Sa, hSa⟩ := sector_side hM hF hfin hp hqWa hnxa fun X hX => by
      refine ⟨Chazelle.Chain.sideCcw_sub_left hB0 hBW hX, ?_⟩
      unfold sideCcw sideCross at hX
      rw [hW2] at hX
      rcases hX with ⟨-, -, h3⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ <;> nlinarith
    have hUpWU : UpW = U := by
      refine sector_regions_eq hSa hUpW hU ?_ hUo
      filter_upwards [ev2] with s hs
      exact (offsets_side hsideW hyW hsegW' hs).1 (by linarith)
    -- the corner before the vertex: the walk edge, then above `dE`
    obtain ⟨Sb, hSb⟩ := sector_side hM hF hfin hp hpva hqEa fun X hX => by
      refine ⟨Chazelle.Chain.sideCcw_sub_right hB0 hE0 hA0 hBE hX, ?_⟩
      unfold sideCcw sideCross at hX
      rw [hE2] at hX
      rcases hX with ⟨-, h2, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ <;> nlinarith
    have hVUpE : V = UpE := by
      refine sector_regions_eq hSb hV hUpE hVo ?_
      filter_upwards [ev1] with s hs
      exact (offsets_side hsideE hyE.symm hsegE hs).1 (by linarith)
    refine ⟨-1, Or.inr rfl, DnE, U, V, l, r, hDnE, harcU, harcV, (hiffE _ hDnE).2 (Or.inr rfl),
      (hiffW _ hDnE).2 (Or.inr hDnEW), Or.inr ((hiffW _ hU).2 (Or.inl hUpWU.symm)),
      Or.inl ((hiffE _ hV).2 (Or.inl hVUpE)), fun R hR h => ?_, fun R hR h => ?_, ?_,
      r₁, hr₁, fun x hx hx2 => hhalf (x - a) (hdown _ (by simp only [Prod.snd_sub]; linarith)) x hx rfl⟩
    · rcases (hiffE R hR).1 h with rfl | rfl
      · exact Or.inr (Or.inr hVUpE.symm)
      · exact Or.inl rfl
    · rcases (hiffW R hR).1 h with rfl | rfl
      · exact Or.inr (Or.inl hUpWU)
      · exact Or.inl hDnEW.symm
    · rintro z (hz | hz) hzD
      · filter_upwards [hsideE z hz hzD] with δ hδ
        rw [show z.2 + -1 * δ = z.2 - δ by ring]; exact hδ.2
      · filter_upwards [hsideW z hz hzD] with δ hδ
        rw [show z.2 + -1 * δ = z.2 - δ by ring, hDnEW]; exact hδ.2

/-! ## Attachments and faced regions -/

/-- Two distinct chords attached at one walk vertex leave it in opposite horizontal directions. -/
theorem opposite_dirs (hM : WalkAx M) {F : Set (Set Point)} (hF : F ⊆ M.Adm) {e e' : Set Point}
    (he : e ∈ F) (he' : e' ∈ F) {p : ℕ} (hA : SideAttach M.W e p 0) (hA' : SideAttach M.W e' p 0)
    (hne : e' ≠ e) :
    ∃ q q' : Point, e = Chazelle.segment (M.W.vtx p) q ∧ e' = Chazelle.segment (M.W.vtx p) q' ∧
      q.2 = (M.W.vtx p).2 ∧ q'.2 = (M.W.vtx p).2 ∧
      (∀ s ∈ Ioo (0 : ℝ) 1, lerp (M.W.vtx p) q s ∈ M.D) ∧
      (∀ s ∈ Ioo (0 : ℝ) 1, lerp (M.W.vtx p) q' s ∈ M.D) ∧ q ∉ M.D ∧ q' ∉ M.D ∧
      ((q.1 < (M.W.vtx p).1 ∧ (M.W.vtx p).1 < q'.1) ∨
        (q'.1 < (M.W.vtx p).1 ∧ (M.W.vtx p).1 < q.1)) := by
  have hpt : sidePt M.W p 0 = M.W.vtx p := Chazelle.Chain.sidePt_zero _ _
  obtain ⟨q, hce, hqa, hqy, hqo, hqD⟩ := hM.chord_from (hF he) hA
  obtain ⟨q', hce', hqa', hqy', hqo', hqD'⟩ := hM.chord_from (hF he') hA'
  rw [hpt] at hce hqa hqy hqo hce' hqa' hqy' hqo'
  refine ⟨q, q', hce, hce', hqy, hqy', hqo, hqo', hqD, hqD', ?_⟩
  set a := M.W.vtx p
  have hx : q.1 ≠ a.1 := fun h => hqa (Geometry.point_ext h hqy)
  have hx' : q'.1 ≠ a.1 := fun h => hqa' (Geometry.point_ext h hqy')
  have hside : ∀ {c : Set Point} {f : Point}, c = Chazelle.segment a f → ∀ z ∈ c, z ≠ a →
      (a.1 < z.1 ↔ a.1 < f.1) := by
    intro c f hc z hz hza
    rw [hc] at hz
    obtain ⟨s, hs0, hs1, rfl⟩ := Geometry.mem_segment_iff_lerp.1 hz
    have hs : s ≠ 0 := by rintro rfl; exact hza (by rw [Geometry.lerp_zero])
    have hs' : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hs)
    simp only [Geometry.lerp_fst]
    constructor
    · intro h; by_contra h'; push Not at h'; nlinarith
    · intro h; nlinarith
  by_contra hno
  apply hne
  refine (sameDir_eq hM (hF he) (hF he') hA hA' rfl fun z z' hz hz' hza hza' => ?_).symm
  rw [hpt] at hza hza' ⊢
  rw [hside hce z hz hza, hside hce' z' hz' hza']
  rcases lt_or_gt_of_ne hx with h | h <;> rcases lt_or_gt_of_ne hx' with h' | h'
  · exact ⟨fun h2 => absurd h2 (not_lt.2 h.le), fun h2 => absurd h2 (not_lt.2 h'.le)⟩
  · exact absurd (Or.inl ⟨h, h'⟩) hno
  · exact absurd (Or.inr ⟨h', h⟩) hno
  · exact ⟨fun _ => h', fun _ => h⟩

/-- **A region touching an attached chord** is faced next to the attachment (it has an arc
starting or ending there), or the attachment is a walk vertex carrying a second chord in the
opposite direction, and the region is the wedge on one side `τ` of both chords. -/
theorem adj_or_wedge (hM : WalkAx M) {F : Set (Set Point)} (hF : F ⊆ M.Adm) (hfin : F.Finite)
    {e : Set Point} (he : e ∈ F) {p : ℕ} {t : ℝ} (hA : SideAttach M.W e p t) {R : Set Point}
    (hR : R ∈ M.regions F) (hRe : TouchesIn M.D e R) :
    ((∃ r, M.IsArc F R (p + t) r) ∨ (∃ l, M.IsArc F R l (p + t))) ∨
    (t = 0 ∧ ∃ e' ∈ F, e' ≠ e ∧ SideAttach M.W e' p 0 ∧ TouchesIn M.D e' R ∧
      ∃ τ : ℝ, (τ = 1 ∨ τ = -1) ∧
      (∀ z ∈ e ∪ e', z ∈ M.D → ∀ᶠ δ in 𝓝[>] (0 : ℝ), ((z.1, z.2 + τ * δ) : Point) ∈ R) ∧
      ∃ r' > 0, ∀ x ∈ ball (M.W.vtx p) r', 0 < τ * (x.2 - (M.W.vtx p).2) → x ∈ M.D) := by
  by_cases hsole : ∀ c' ∈ F, SideAttach M.W c' p t → c' = e
  · exact Or.inl (sides_single hM hF hfin he hA hsole hR hRe)
  push Not at hsole
  obtain ⟨e', he', hA', hne⟩ := hsole
  have ht : t = 0 := by
    by_contra h
    exact hne (one_chord_interior hM hF he' he (lt_of_le_of_ne hA.2.1 (Ne.symm h)) hA' hA)
  subst ht
  obtain ⟨q, q', hce, hce', hqy, hqy', hqo, hqo', -, -, hdir⟩ :=
    opposite_dirs hM hF he he' hA hA' hne
  rcases hdir with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · obtain ⟨τ, hτ, X, U, V, l, r, -, harcU, harcV, hEX, -, -, -, -, hallW, hside, r', hr', hball⟩ :=
      wedge_core hM hF hfin he' he hA' hA hce' hce hqy' hqy hqo' hqo h1 h2
    rcases hallW R hR hRe with rfl | rfl | rfl
    · refine Or.inr ⟨rfl, e', he', hne, hA', hEX, τ, hτ, fun z hz hzD => hside z ?_ hzD, r', hr', hball⟩
      rcases hz with h | h
      · exact Or.inr h
      · exact Or.inl h
    · exact Or.inl (Or.inl ⟨r, harcU⟩)
    · exact Or.inl (Or.inr ⟨l, harcV⟩)
  · obtain ⟨τ, hτ, X, U, V, l, r, -, harcU, harcV, -, hWX, -, -, hallE, -, hside, r', hr', hball⟩ :=
      wedge_core hM hF hfin he he' hA hA' hce hce' hqy hqy' hqo hqo' h1 h2
    rcases hallE R hR hRe with rfl | rfl | rfl
    · exact Or.inr ⟨rfl, e', he', hne, hA', hWX, τ, hτ, hside, r', hr', hball⟩
    · exact Or.inl (Or.inl ⟨r, harcU⟩)
    · exact Or.inl (Or.inr ⟨l, harcV⟩)

/-- An arc starting or ending at a key inside a walk edge makes its region faced just after or
just before that key. -/
theorem faced_of_arc {F : Set (Set Point)} (hne : F.Nonempty) {R : Set Point} {p : ℕ} {t : ℝ}
    (hp : p < M.W.n) (ht : t ∈ Ioo (0 : ℝ) 1)
    (h : (∃ r, M.IsArc F R (p + t) r) ∨ (∃ l, M.IsArc F R l (p + t))) :
    FacedAfter M R p t ∨ FacedBefore M R p t := by
  rcases h with ⟨r, harc⟩ | ⟨l, harc⟩
  · exact Or.inl (faced_after hp ht.1.le ht.2 harc (WalkAx.arc_cuts hne harc).2.2)
  · exact Or.inr (faced_before hp ht.1 ht.2 harc (WalkAx.arc_cuts hne harc).2.2)

/-- A chord is not attached twice inside one walk edge. -/
theorem attach_other_edge (hM : WalkAx M) {c : Set Point} (hc : c ∈ M.Adm) {p pb : ℕ}
    {t tb : ℝ} (hA : SideAttach M.W c p t) (hB : SideAttach M.W c pb tb)
    (hne : sidePt M.W p t ≠ sidePt M.W pb tb) : pb ≠ p := by
  rintro rfl
  obtain ⟨q, hcq, hqa, -, hop, -⟩ := hM.chord_from hc hA
  have hqb : sidePt M.W pb tb = q := by
    have hmem := hB.2.2.2.1
    rw [hcq] at hmem
    obtain ⟨s, hs0, hs1, hs⟩ := Geometry.mem_segment_iff_lerp.1 hmem
    rcases hs0.lt_or_eq with h0 | h0
    · rcases hs1.lt_or_eq with h1 | h1
      · exact absurd (hs ▸ hop s ⟨h0, h1⟩) (hM.trace pb hB.1 tb hB.2.1 hB.2.2.1.le)
      · rw [hs, h1, Geometry.lerp_one]
    · exact absurd (by rw [hs, ← h0, Geometry.lerp_zero]) hne
  have hmid : lerp (sidePt M.W pb t) q (1 / 2) = sidePt M.W pb ((t + tb) / 2) := by
    rw [← hqb]; unfold sidePt; apply Geometry.point_ext <;> simp [lerp] <;> ring
  exact hM.trace pb hB.1 _ (by linarith [hA.2.1, hB.2.1]) (by linarith [hA.2.2.1, hB.2.2.1])
    (hmid ▸ hop (1 / 2) ⟨by norm_num, by norm_num⟩)

/-- The keys of one walk edge around a key of it, against a key of another walk edge. -/
theorem key_sides {p pb : ℕ} (hpb : pb ≠ p) {tb t : ℝ} (htb : 0 ≤ tb) (htb1 : tb < 1)
    (ht0 : 0 ≤ t) (ht1 : t < 1) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    (t < u → sideInArc (p + t) (pb + tb) (p + u)) ∧
      (u < t → sideInArc (pb + tb) (p + t) (p + u)) := by
  rcases lt_or_gt_of_ne hpb with h | h
  · have h' : (pb : ℝ) + 1 ≤ p := by exact_mod_cast h
    refine ⟨fun htu => ?_, fun htu => ?_⟩ <;> unfold sideInArc <;> split_ifs <;>
      first | (constructor! <;> linarith)
  · have h' : (p : ℝ) + 1 ≤ pb := by exact_mod_cast h
    refine ⟨fun htu => ?_, fun htu => ?_⟩ <;> unfold sideInArc <;> split_ifs <;>
      first | (constructor! <;> linarith) | (right; linarith)

/-- A set of reals without three increasing elements has at most two elements. -/
theorem ncard_le_two_of_no_three {S : Set ℝ}
    (h : ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x < y → y < z → False) : S.ncard ≤ 2 := by
  by_contra hlt
  push Not at hlt
  have hfin : S.Finite := Set.finite_of_ncard_pos (by omega)
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := (Set.two_lt_ncard_iff hfin).1 hlt
  rcases lt_or_gt_of_ne hab with h1 | h1 <;> rcases lt_or_gt_of_ne hac with h2 | h2 <;>
    rcases lt_or_gt_of_ne hbc with h3 | h3
  · exact h a ha b hb c hc h1 h3
  · exact h a ha c hc b hb h2 h3
  · linarith
  · exact h c hc a ha b hb h2 h1
  · exact h b hb a ha c hc h1 h2
  · linarith
  · exact h b hb c hc a ha h3 h2
  · exact h c hc b hb a ha h3 h1

/-- **The wall-gap argument** (review, "at most two (β) chords per wall"): at most two positions
inside one walk edge carry exit chords of a region. -/
theorem edge_two (hM : WalkAx M) {F : Set (Set Point)} (hF : F ⊆ M.Adm) (hfin : F.Finite)
    {R : Set Point} (hR : R ∈ M.regions F) (p : ℕ) :
    {t : ℝ | 0 < t ∧ ∃ c ∈ exits M F R, SideAttach M.W c p t}.ncard ≤ 2 := by
  refine ncard_le_two_of_no_three ?_
  rintro t₁ ⟨h₁0, c₁, ⟨hc₁, hc₁R⟩, hA₁⟩ t₂ ⟨h₂0, c₂, ⟨hc₂, hc₂R⟩, hA₂⟩ t₃ ⟨h₃0, c₃, ⟨hc₃, hc₃R⟩, hA₃⟩
    h12 h23
  have hp := hA₂.1
  have hne : F.Nonempty := ⟨c₁, hc₁⟩
  have hface : ∀ {c : Set Point} {t : ℝ}, c ∈ F → TouchesIn M.D c R → 0 < t →
      SideAttach M.W c p t → FacedAfter M R p t ∨ FacedBefore M R p t := by
    intro c t hc hcR ht hA
    refine faced_of_arc hne hp ⟨ht, hA.2.2.1⟩ (sides_single hM hF hfin hc hA ?_ hR hcR)
    intro c' hc' hA'
    exact one_chord_interior hM hF hc' hc ht hA' hA
  -- a faced position near `t` in a given interval around it
  have hnear : ∀ {t a b : ℝ}, FacedAfter M R p t ∨ FacedBefore M R p t → a < t → t < b →
      ∃ u ∈ Ioo a b, M.Faces p u R := by
    intro t a b h ha hb
    rcases h with h | h
    · obtain ⟨s, hs, hs'⟩ := (h.and (Ioo_mem_nhdsGT (show (0 : ℝ) < b - t by linarith))).exists
      exact ⟨t + s, ⟨by linarith [hs'.1], by linarith [hs'.2]⟩, hs⟩
    · obtain ⟨s, hs, hs'⟩ := (h.and (Ioo_mem_nhdsGT (show (0 : ℝ) < t - a by linarith))).exists
      exact ⟨t - s, ⟨by linarith [hs'.2], by linarith [hs'.1]⟩, hs⟩
  obtain ⟨pb, tb, hB, hBne⟩ := hM.other_attach (hF hc₂) hA₂
  have hpb := attach_other_edge hM (hF hc₂) hA₂ hB (Ne.symm hBne)
  obtain ⟨u₁, hu₁, hf₁⟩ := hnear (hface hc₁ hc₁R h₁0 hA₁) (show 0 < t₁ from h₁0) h12
  obtain ⟨u₃, hu₃, hf₃⟩ := hnear (hface hc₃ hc₃R h₃0 hA₃) h23 hA₃.2.2.1
  have hu₁' : u₁ ∈ Ioo (0 : ℝ) 1 := ⟨hu₁.1, by linarith [hu₁.2, hA₂.2.2.1]⟩
  have hu₃' : u₃ ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hu₃.1], hu₃.2⟩
  have hsep := fun {u u' : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (hin : sideInArc (p + t₂) (pb + tb) (p + u))
      (hf : M.Faces p u R) (hu' : u' ∈ Ioo (0 : ℝ) 1)
      (hin' : sideInArc (pb + tb) (p + t₂) (p + u')) (hf' : M.Faces p u' R) =>
    sep_false hM hc₂ (hF hc₂) hA₂ hB (Ne.symm hBne) hR hp hu hin hf hp hu' hin' hf'
  have hks := fun {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) =>
    key_sides hpb hB.2.1 hB.2.2.1 h₂0.le hA₂.2.2.1 hu.1.le hu.2
  rcases hface hc₂ hc₂R h₂0 hA₂ with h | h
  · obtain ⟨s, hs, hs'⟩ := (h.and (Ioo_mem_nhdsGT (show (0 : ℝ) < t₃ - t₂ by linarith))).exists
    have hu₂ : t₂ + s ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hs'.1], by linarith [hs'.2, hA₃.2.2.1]⟩
    exact hsep hu₂ ((hks hu₂).1 (by linarith [hs'.1])) hs hu₁' ((hks hu₁').2 hu₁.2) hf₁
  · obtain ⟨s, hs, hs'⟩ := (h.and (Ioo_mem_nhdsGT (show (0 : ℝ) < t₂ - t₁ by linarith))).exists
    have hu₂ : t₂ - s ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hs'.2], by linarith [hs'.1, hA₂.2.2.1]⟩
    exact hsep hu₃' ((hks hu₃').1 hu₃.1) hf₃ hu₂ ((hks hu₂).2 (by linarith [hs'.1])) hs

/-! ## Sides of chords and strips -/

/-- The region `R` lies on the side `τ` of the chord `e`: the points just on that side of the
chord are in `R`. -/
def SideIn (M : Model) (R e : Set Point) (τ : ℝ) : Prop :=
  ∀ z ∈ e, z ∈ M.D → ∀ᶠ δ in 𝓝[>] (0 : ℝ), ((z.1, z.2 + τ * δ) : Point) ∈ R

/-- The open half-ball on the side `τ` of the point `z` near `z` lies in `A`. -/
def HalfIn (A : Set Point) (τ : ℝ) (z : Point) : Prop :=
  ∃ r > 0, ∀ y ∈ ball z r, 0 < τ * (y.2 - z.2) → y ∈ A

/-- The region `R` is faced next to the key of the position `(p, t)`: it has an arc starting or
ending there. -/
def Adj (M : Model) (F : Set (Set Point)) (R : Set Point) (p : ℕ) (t : ℝ) : Prop :=
  (∃ r, M.IsArc F R (p + t) r) ∨ (∃ l, M.IsArc F R l (p + t))

theorem halfIn_of_mem {A : Set Point} (hA : IsOpen A) (τ : ℝ) {z : Point} (hz : z ∈ A) :
    HalfIn A τ z := by
  obtain ⟨r, hr, hb⟩ := Metric.isOpen_iff.1 hA z hz
  exact ⟨r, hr, fun y hy _ => hb hy⟩

/-- **A region is on one side of a chord only.** -/
theorem side_unique (hM : WalkAx M) {F : Set (Set Point)} (hF : F ⊆ M.Adm) (hfin : F.Finite)
    {e : Set Point} (he : e ∈ F) {R : Set Point} (hR : R ∈ M.regions F) {z : Point} (hz : z ∈ e)
    (hzD : z ∈ M.D) {τ τ' : ℝ} (hτ : τ = 1 ∨ τ = -1) (hτ' : τ' = 1 ∨ τ' = -1)
    (h : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ((z.1, z.2 + τ * δ) : Point) ∈ R)
    (h' : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ((z.1, z.2 + τ' * δ) : Point) ∈ R) : τ = τ' := by
  obtain ⟨Up, Dn, hUp, hDn, hne, hside, -⟩ := chordSides_of_system (hM.sys F hF hfin) he
  have hmeet : ∀ {X : Set Point}, X ∈ M.regions F → ∀ {σ : ℝ},
      (∀ᶠ δ in 𝓝[>] (0 : ℝ), ((z.1, z.2 + σ * δ) : Point) ∈ R) →
      (∀ᶠ δ in 𝓝[>] (0 : ℝ), ((z.1, z.2 + σ * δ) : Point) ∈ X) → R = X := by
    intro X hX σ h1 h2
    obtain ⟨δ, h3, h4⟩ := (h1.and h2).exists
    exact (Chazelle.Chain.regionsIn_eq_or_disjoint hR hX).resolve_right
      (fun hd => hd.le_bot ⟨h3, h4⟩)
  have hup : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ((z.1, z.2 + 1 * δ) : Point) ∈ Up := by
    filter_upwards [hside z hz hzD] with δ hδ; rw [one_mul]; exact hδ.1
  have hdn : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ((z.1, z.2 + -1 * δ) : Point) ∈ Dn := by
    filter_upwards [hside z hz hzD] with δ hδ
    rw [show z.2 + -1 * δ = z.2 - δ by ring]; exact hδ.2
  rcases hτ with rfl | rfl <;> rcases hτ' with rfl | rfl
  · rfl
  · exact absurd ((hmeet hUp h hup).symm.trans (hmeet hDn h' hdn)) hne
  · exact absurd ((hmeet hUp h' hup).symm.trans (hmeet hDn h hdn)) hne
  · rfl

/-- The open half-ball is preconnected. -/
theorem isPreconnected_half (z : Point) (r τ : ℝ) :
    IsPreconnected {y | y ∈ ball z r ∧ 0 < τ * (y.2 - z.2)} := by
  have hc : Convex ℝ {y : Point | 0 < τ * (y.2 - z.2)} := by
    intro y hy w hw a b ha hb hab
    simp only [mem_ofPred_eq, Prod.snd_add, Prod.smul_snd, smul_eq_mul] at hy hw ⊢
    have e : τ * (a * y.2 + b * w.2 - z.2) = a * (τ * (y.2 - z.2)) + b * (τ * (w.2 - z.2)) := by
      linear_combination (τ * z.2) * hab
    rw [e]
    rcases ha.lt_or_eq with ha' | ha'
    · have := mul_pos ha' hy
      have := mul_nonneg hb hw.le
      linarith
    · rw [← ha', zero_add] at hab
      rw [← ha', hab]; linarith
  exact ((convex_ball z r).inter hc).isPreconnected

/-- **The strip argument**: if every point of a horizontal segment has its open half-ball on the
side `τ` inside `A`, the points just on that side of its two ends lie in one component of `A`. -/
theorem strip_const {A : Set Point} {h τ : ℝ} (hτ : τ = 1 ∨ τ = -1) {x₀ x₁ : ℝ} (hx : x₀ ≤ x₁)
    (hgood : ∀ x ∈ Icc x₀ x₁, HalfIn A τ ((x, h) : Point)) :
    ∃ w ∈ A, (∀ᶠ δ in 𝓝[>] (0 : ℝ), ((x₀, h + τ * δ) : Point) ∈ connectedComponentIn A w) ∧
      (∀ᶠ δ in 𝓝[>] (0 : ℝ), ((x₁, h + τ * δ) : Point) ∈ connectedComponentIn A w) := by
  have hτa : |τ| = 1 := by rcases hτ with rfl | rfl <;> simp
  let P : ℝ → ℝ → Prop := fun x y => ∃ w ∈ A,
    (∀ᶠ δ in 𝓝[>] (0 : ℝ), ((x, h + τ * δ) : Point) ∈ connectedComponentIn A w) ∧
      (∀ᶠ δ in 𝓝[>] (0 : ℝ), ((y, h + τ * δ) : Point) ∈ connectedComponentIn A w)
  -- the side points of `y` near `x` are in the half-ball at `x`
  have hnear : ∀ {x r y : ℝ}, |y - x| < r → ∀ δ, 0 < δ → δ < r →
      ((y, h + τ * δ) : Point) ∈ {q | q ∈ ball ((x, h) : Point) r ∧ 0 < τ * (q.2 - h)} := by
    intro x r y hy δ hδ hδr
    refine ⟨?_, ?_⟩
    · rw [mem_ball, Prod.dist_eq]
      simp only [Real.dist_eq]
      rw [show h + τ * δ - h = τ * δ by ring, abs_mul, hτa, one_mul, abs_of_pos hδ]
      exact max_lt hy hδr
    · show 0 < τ * (h + τ * δ - h)
      rw [show τ * (h + τ * δ - h) = (τ * τ) * δ by ring]
      rcases hτ with rfl | rfl <;> norm_num <;> exact hδ
  have hloc : ∀ x ∈ Icc x₀ x₁, ∀ᶠ y in 𝓝[Icc x₀ x₁] x, P x y := by
    intro x hx
    obtain ⟨r, hr, hsub⟩ := hgood x hx
    set H := {q : Point | q ∈ ball ((x, h) : Point) r ∧ 0 < τ * (q.2 - h)}
    have hHA : H ⊆ A := fun q hq => hsub q hq.1 hq.2
    have hw : ((x, h + τ * (r / 2)) : Point) ∈ H := hnear (by simp [hr]) _ (by linarith)
      (by linarith)
    have hHc : H ⊆ connectedComponentIn A ((x, h + τ * (r / 2)) : Point) :=
      (isPreconnected_half ((x, h) : Point) r τ).subset_connectedComponentIn hw hHA
    have hev : ∀ {y : ℝ}, |y - x| < r →
        ∀ᶠ δ in 𝓝[>] (0 : ℝ), ((y, h + τ * δ) : Point) ∈
          connectedComponentIn A ((x, h + τ * (r / 2)) : Point) := by
      intro y hy
      filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT hr] with δ hδ hδ'
      exact hHc (hnear hy δ hδ hδ'.2)
    filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds x hr)] with y hy
    exact ⟨_, hHA hw, hev (by simp [hr]), hev (by rw [← Real.dist_eq]; exact hy)⟩
  refine (isPreconnected_Icc.induction₂ P hloc ?_ ?_ ⟨le_rfl, hx⟩ ⟨hx, le_rfl⟩)
  · rintro x y z - - - ⟨w, hw, h1, h2⟩ ⟨w', hw', h3, h4⟩
    obtain ⟨δ, h5, h6⟩ := (h2.and h3).exists
    refine ⟨w, hw, h1, ?_⟩
    rw [(connectedComponentIn_eq h5).trans (connectedComponentIn_eq h6).symm]
    exact h4
  · rintro x y - - ⟨w, hw, h1, h2⟩
    exact ⟨w, hw, h2, h1⟩

/-! ## Chains of wedges -/

/-- An admissible chord from its end in the direction `σ` back to its other end. -/
theorem sigma_end (hM : WalkAx M) {e : Set Point} (he : e ∈ M.Adm) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) :
    ∃ w q : Point, e = Chazelle.segment w q ∧ q.2 = w.2 ∧ σ * q.1 < σ * w.1 ∧
      (∀ s ∈ Ioo (0 : ℝ) 1, lerp w q s ∈ M.D) ∧ WalkEnd M.W e w ∧ q ∉ M.D := by
  obtain ⟨a, b, hab, hce, hy, hop, ha, hb⟩ := hM.ends e he
  have hnD : ∀ {x : Point}, WalkEnd M.W e x → x ∉ M.D := by
    rintro x ⟨⟨p, t, hA, rfl⟩, -⟩
    exact hM.trace p hA.1 t hA.2.1 hA.2.2.1.le
  have hx : a.1 ≠ b.1 := fun h => hab (Geometry.point_ext h hy)
  have hσx : σ * a.1 ≠ σ * b.1 := by
    rcases hσ with rfl | rfl <;> intro h <;> apply hx <;> linarith
  rcases lt_or_gt_of_ne hσx with h | h
  · exact ⟨b, a, hce.trans (Geometry.segment_comm _ _), hy, h, WalkAx.open_rev hop, hb, hnD ha⟩
  · exact ⟨a, b, hce, hy.symm, h, hop, ha, hnD hb⟩

/-- The points of a horizontal segment lie between its ends. -/
theorem mem_seg_sigma {w q : Point} (hy : q.2 = w.2) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hqw : σ * q.1 < σ * w.1) {y : Point} (hyc : y ∈ Chazelle.segment w q) :
    y.2 = w.2 ∧ σ * q.1 ≤ σ * y.1 ∧ σ * y.1 ≤ σ * w.1 := by
  obtain ⟨s, hs0, hs1, rfl⟩ := Geometry.mem_segment_iff_lerp.1 hyc
  simp only [Geometry.lerp_fst, Geometry.lerp_snd]
  refine ⟨by rw [hy]; ring, ?_, ?_⟩ <;> rcases hσ with rfl | rfl <;> nlinarith

/-- The points strictly between the ends of a horizontal segment are open points of it. -/
theorem open_pt {D : Set Point} {w q : Point} (hy : q.2 = w.2) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hop : ∀ s ∈ Ioo (0 : ℝ) 1, lerp w q s ∈ D) {x : ℝ} (h1 : σ * q.1 < σ * x)
    (h2 : σ * x < σ * w.1) :
    ((x, w.2) : Point) ∈ Chazelle.segment w q ∧ ((x, w.2) : Point) ∈ D := by
  have hne : q.1 - w.1 ≠ 0 := by
    intro h; rcases hσ with rfl | rfl <;> linarith
  set s := (x - w.1) / (q.1 - w.1) with hs
  have hpt : lerp w q s = ((x, w.2) : Point) := by
    apply Geometry.point_ext
    · simp only [Geometry.lerp_fst]; rw [hs]; field_simp; ring
    · simp only [Geometry.lerp_snd]; rw [hy]; ring
  have hs01 : s ∈ Ioo (0 : ℝ) 1 := by
    rcases hσ with rfl | rfl
    · simp only [one_mul] at h1 h2
      exact ⟨div_pos_of_neg_of_neg (by linarith) (by linarith),
        (div_lt_one_of_neg (by linarith)).2 (by linarith)⟩
    · simp only [neg_mul, one_mul, neg_lt_neg_iff] at h1 h2
      exact ⟨div_pos (by linarith) (by linarith), (div_lt_one (by linarith)).2 (by linarith)⟩
  rw [← hpt]
  exact ⟨Geometry.lerp_mem_segment _ _ hs01.1.le hs01.2.le, hop s hs01⟩

/-- The chords beyond `e` in the direction `σ`. -/
def beyond (F : Set (Set Point)) (e : Set Point) (σ : ℝ) : Set (Set Point) :=
  {g | g ∈ F ∧ ∃ x ∈ g, ∀ y ∈ e, σ * y.1 < σ * x.1}

/-- The conclusion of `chain_end`. -/
def ChainOut (M : Model) (F : Set (Set Point)) (R : Set Point) (τ σ : ℝ) (e : Set Point) : Prop :=
  ∃ f ∈ F, TouchesIn M.D f R ∧ (∃ p t, SideAttach M.W f p t ∧ Adj M F R p t) ∧
    SideIn M R f τ ∧ ∃ z₀ ∈ e, z₀ ∈ M.D ∧ ∃ z₁ ∈ f, z₁ ∈ M.D ∧ z₁.2 = z₀.2 ∧
      σ * z₀.1 ≤ σ * z₁.1 ∧ ∀ x : ℝ, σ * z₀.1 ≤ σ * x → σ * x ≤ σ * z₁.1 →
        HalfIn M.D τ ((x, z₀.2) : Point)

/-- **Following a chain of wedges.**  Let the region `R` lie on the side `τ` of a chord `e`.
Going from `e` in the direction `σ` through the wedge vertices of `R`, one reaches a chord `f`
at which `R` is faced next to an attachment; all points of the horizontal segment from a point
of `e` to a point of `f` have their half-balls on the side `τ` in the domain. -/
theorem chain_end (hM : WalkAx M) {F : Set (Set Point)} (hF : F ⊆ M.Adm) (hfin : F.Finite)
    {R : Set Point} (hR : R ∈ M.regions F) {τ σ : ℝ} (hτ : τ = 1 ∨ τ = -1)
    (hσ : σ = 1 ∨ σ = -1) :
    ∀ n : ℕ, ∀ e ∈ F, TouchesIn M.D e R → SideIn M R e τ → (beyond F e σ).ncard ≤ n →
      ChainOut M F R τ σ e := by
  have hσσ : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hσinj : ∀ {x y : ℝ}, σ * x = σ * y → x = y := fun {x y} h => by
    have := congrArg (σ * ·) h; simp only [← mul_assoc, hσσ, one_mul] at this; exact this
  intro n
  induction n with
  | zero => ?_
  | succ n ih => ?_
  all_goals
    intro e he hRe hside hn
    obtain ⟨w, q, hce, hqy, hqw, hop, hwe, hqD⟩ := sigma_end hM (hF he) hσ
    obtain ⟨⟨p, t, hA, hAw⟩, -⟩ := hwe
    -- a middle point of `e`
    set m : Point := ((σ * σ * ((w.1 + q.1) / 2)), w.2) with hm
    have hm1 : σ * q.1 < σ * m.1 := by rw [hm]; dsimp only; rw [hσσ, one_mul]; linarith
    have hm2 : σ * m.1 < σ * w.1 := by rw [hm]; dsimp only; rw [hσσ, one_mul]; linarith
    obtain ⟨hme, hmD⟩ := open_pt hqy hσ hop hm1 hm2
    rw [← hce] at hme
    rcases adj_or_wedge hM hF hfin he hA hR hRe with hadj | ⟨ht0, e', he', hne, hA', hRe', τ', hτ',
      hside', r', hr', hball⟩
    · refine ⟨e, he, hRe, ⟨p, t, hA, hadj⟩, hside, _, hme, hmD, _, hme, hmD, rfl, le_rfl,
        fun x h1 h2 => ?_⟩
      have hx : x = m.1 := hσinj (le_antisymm h2 h1)
      rw [hx]
      exact halfIn_of_mem hM.isOpen τ hmD
    subst ht0
    have hwv : w = M.W.vtx p := by rw [← hAw, Chazelle.Chain.sidePt_zero]
    have hττ : τ = τ' :=
      side_unique hM hF hfin he hR hme hmD hτ hτ' (hside m hme hmD) (hside' m (Or.inl hme) hmD)
    subst hττ
    obtain ⟨q₁, q', hce₁, hce', -, hqy', -, hop', -, hqD', hdir⟩ :=
      opposite_dirs hM hF he he' hA hA' hne
    rw [← hwv] at hce₁ hce' hqy' hop'
    have hq₁ : σ * q₁.1 < σ * w.1 := by
      have hq₁e : q₁ ∈ e := by rw [hce₁]; exact Geometry.right_mem_segment _ _
      rw [hce] at hq₁e
      obtain ⟨-, -, h2⟩ := mem_seg_sigma hqy hσ hqw hq₁e
      rcases h2.lt_or_eq with h | h
      · exact h
      · rw [← hwv] at hdir
        have := hσinj h
        rcases hdir with ⟨h1, -⟩ | ⟨-, h1⟩ <;> linarith
    have hq' : σ * w.1 < σ * q'.1 := by
      rw [← hwv] at hdir
      rcases hσ with rfl | rfl <;> simp only [one_mul, neg_mul, neg_lt_neg_iff] at hq₁ ⊢ <;>
        rcases hdir with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
    have hce'' : e' = Chazelle.segment q' w := hce'.trans (Geometry.segment_comm _ _)
    have hwq' : w.2 = q'.2 := hqy'.symm
    -- `e'` is beyond `e`, and fewer chords are beyond `e'`
    have hmemw : ∀ y ∈ e, σ * y.1 ≤ σ * w.1 := fun y hy => by
      rw [hce] at hy; exact (mem_seg_sigma hqy hσ hqw hy).2.2
    have hmemw' : ∀ y ∈ e', σ * w.1 ≤ σ * y.1 := fun y hy => by
      rw [hce''] at hy; exact (mem_seg_sigma hwq' hσ hq' hy).2.1
    have hwe' : w ∈ e' := by rw [hce']; exact Geometry.left_mem_segment _ _
    have hsub : beyond F e' σ ⊂ beyond F e σ := by
      constructor
      · rintro g ⟨hg, x, hx, hlt⟩
        exact ⟨hg, x, hx, fun y hy => (hmemw y hy).trans_lt (hlt w hwe')⟩
      · intro h
        obtain ⟨-, x, hx, hlt⟩ := h ⟨he', q', by rw [hce']; exact Geometry.right_mem_segment _ _,
          fun y hy => (hmemw y hy).trans_lt hq'⟩
        exact lt_irrefl _ (hlt x hx)
    have hlt := Set.ncard_lt_ncard hsub (hfin.subset fun g hg => hg.1)
    have hIH : ChainOut M F R τ σ e' := by
      first
        | exact absurd hlt (by omega)
        | exact ih e' he' hRe' (fun z hz hzD => hside' z (Or.inr hz) hzD) (by omega)
    obtain ⟨f, hf, hRf, hadjf, hsidef, z₀', hz₀', hz₀'D, z₁, hz₁, hz₁D, hz₁y, hz₀₁, hgood⟩ := hIH
    have hz₀'s : z₀'.2 = w.2 ∧ σ * w.1 ≤ σ * z₀'.1 ∧ σ * z₀'.1 ≤ σ * q'.1 := by
      rw [hce''] at hz₀'
      obtain ⟨h1, h2, h3⟩ := mem_seg_sigma hwq' hσ hq' hz₀'
      exact ⟨h1.trans hwq'.symm, h2, h3⟩
    have hz₀'q : σ * z₀'.1 < σ * q'.1 := by
      rcases hz₀'s.2.2.lt_or_eq with h | h
      · exact h
      · exfalso
        have hx := hσinj h
        have : z₀' = q' := Geometry.point_ext hx (hz₀'s.1.trans hwq')
        exact hqD' (this ▸ hz₀'D)
    have hmw : m.2 = w.2 := rfl
    refine ⟨f, hf, hRf, hadjf, hsidef, m, hme, hmD, z₁, hz₁, hz₁D, by rw [hz₁y, hz₀'s.1],
      by linarith [hz₀'s.2.1], fun x h1 h2 => ?_⟩
    rw [hmw]
    rcases lt_trichotomy (σ * x) (σ * w.1) with h | h | h
    · exact halfIn_of_mem hM.isOpen τ (open_pt hqy hσ hop (hm1.trans_le h1) h).2
    · have hx : ((x, w.2) : Point) = M.W.vtx p := by
        rw [← hwv]; exact Geometry.point_ext (hσinj h) rfl
      rw [hx]
      exact ⟨r', hr', hball⟩
    · rcases lt_or_ge (σ * x) (σ * z₀'.1) with h' | h'
      · have := (open_pt hwq' hσ (WalkAx.open_rev hop') h (h'.trans hz₀'q)).2
        rw [← hwq'] at this
        exact halfIn_of_mem hM.isOpen τ this
      · have := hgood x h' h2
        rwa [hz₀'s.1] at this

/-! ## Counting chords at points and positions -/

/-- An admissible chord through a point off the domain is a segment from that point. -/
theorem chord_through (hM : WalkAx M) {c : Set Point} (hc : c ∈ M.Adm) {v : Point} (hv : v ∈ c)
    (hvD : v ∉ M.D) :
    ∃ q : Point, c = Chazelle.segment v q ∧ q ≠ v ∧ q.2 = v.2 ∧
      (∀ s ∈ Ioo (0 : ℝ) 1, lerp v q s ∈ M.D) ∧ q ∉ M.D := by
  obtain ⟨a, b, hab, hce, hy, hop, ha, hb⟩ := hM.ends c hc
  have hnD : ∀ {x : Point}, WalkEnd M.W c x → x ∉ M.D := by
    rintro x ⟨⟨p, t, hA, rfl⟩, -⟩
    exact hM.trace p hA.1 t hA.2.1 hA.2.2.1.le
  rw [hce] at hv
  obtain ⟨s, hs0, hs1, rfl⟩ := Geometry.mem_segment_iff_lerp.1 hv
  rcases hs0.lt_or_eq with h0 | h0
  · rcases hs1.lt_or_eq with h1 | h1
    · exact absurd (hop s ⟨h0, h1⟩) hvD
    · subst h1
      rw [Geometry.lerp_one]
      exact ⟨a, hce.trans (Geometry.segment_comm _ _), hab, hy, WalkAx.open_rev hop, hnD ha⟩
  · subst h0
    rw [Geometry.lerp_zero]
    exact ⟨b, hce, hab.symm, hy.symm, hop, hnD hb⟩

/-- **At most two chords of `F` pass through a point off the domain** (one to the east, one to
the west). -/
theorem ncard_through_le (hM : WalkAx M) {F : Set (Set Point)} (hF : F ⊆ M.Adm) {v : Point}
    (hvD : v ∉ M.D) : {c | c ∈ F ∧ v ∈ c}.ncard ≤ 2 := by
  classical
  let dir : Set Point → Bool := fun c => decide (∃ x ∈ c, v.1 < x.1)
  have hdir : ∀ c : Set Point, ∀ e', c = Chazelle.segment v e' → (dir c = true ↔ v.1 < e'.1) := by
    intro c e' hce
    simp only [dir, decide_eq_true_eq]
    constructor
    · rintro ⟨x, hx, hlt⟩
      rw [hce] at hx
      obtain ⟨s, hs0, hs1, rfl⟩ := Geometry.mem_segment_iff_lerp.1 hx
      simp only [Geometry.lerp_fst] at hlt
      by_contra hle; push Not at hle; nlinarith
    · intro hlt
      exact ⟨e', by rw [hce]; exact Geometry.right_mem_segment _ _, hlt⟩
  have key : ∀ {f f' : Point}, (∀ s ∈ Ioo (0 : ℝ) 1, lerp v f s ∈ M.D) → f' ∉ M.D →
      f.2 = v.2 → f'.2 = v.2 → (v.1 < f'.1 ∧ f'.1 < f.1 ∨ f.1 < f'.1 ∧ f'.1 < v.1) → False := by
    intro f f' hop hD hf hf' hbtw
    apply hD
    have hfe : f.1 - v.1 ≠ 0 := by
      rcases hbtw with h | h <;> intro h' <;> linarith [h.1, h.2]
    have e1 : f' = lerp v f ((f'.1 - v.1) / (f.1 - v.1)) := by
      apply Geometry.point_ext
      · simp only [Geometry.lerp_fst]; field_simp; ring
      · simp only [Geometry.lerp_snd]; rw [hf, hf']; ring
    rw [e1]
    apply hop
    rcases hbtw with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨div_pos (by linarith) (by linarith), (div_lt_one (by linarith)).2 (by linarith)⟩
    · exact ⟨div_pos_of_neg_of_neg (by linarith) (by linarith),
        (div_lt_one_of_neg (by linarith)).2 (by linarith)⟩
  have hinj : InjOn dir {c | c ∈ F ∧ v ∈ c} := by
    intro c hc c' hc' hdd
    obtain ⟨e₁, hce₁, hne₁, hy₁, hop₁, hD₁⟩ := chord_through hM (hF hc.1) hc.2 hvD
    obtain ⟨e₂, hce₂, hne₂, hy₂, hop₂, hD₂⟩ := chord_through hM (hF hc'.1) hc'.2 hvD
    have hsame : v.1 < e₁.1 ↔ v.1 < e₂.1 := by
      rw [← hdir c e₁ hce₁, ← hdir c' e₂ hce₂, hdd]
    have hx₁ : e₁.1 ≠ v.1 := fun h => hne₁ (Geometry.point_ext h hy₁)
    have hx₂ : e₂.1 ≠ v.1 := fun h => hne₂ (Geometry.point_ext h hy₂)
    have heq : e₁ = e₂ := by
      apply Geometry.point_ext _ (hy₁.trans hy₂.symm)
      rcases lt_or_gt_of_ne hx₁ with h₁ | h₁
      · have h₂ : e₂.1 < v.1 := by
          rcases lt_or_gt_of_ne hx₂ with h | h
          · exact h
          · exact absurd (hsame.2 h) (not_lt.2 h₁.le)
        rcases lt_trichotomy e₁.1 e₂.1 with h | h | h
        · exact (key hop₁ hD₂ hy₁ hy₂ (Or.inr ⟨h, h₂⟩)).elim
        · exact h
        · exact (key hop₂ hD₁ hy₂ hy₁ (Or.inr ⟨h, h₁⟩)).elim
      · have h₂ : v.1 < e₂.1 := hsame.1 h₁
        rcases lt_trichotomy e₁.1 e₂.1 with h | h | h
        · exact (key hop₂ hD₁ hy₂ hy₁ (Or.inl ⟨h₁, h⟩)).elim
        · exact h
        · exact (key hop₁ hD₂ hy₁ hy₂ (Or.inl ⟨h₂, h⟩)).elim
    rw [hce₁, hce₂, heq]
  calc {c | c ∈ F ∧ v ∈ c}.ncard ≤ (Set.univ : Set Bool).ncard :=
        ncard_le_ncard_of_injOn dir (fun _ _ => mem_univ _) hinj
    _ = 2 := by rw [ncard_univ, Nat.card_eq_fintype_card]; rfl

/-- At most two chords of `F` are attached at any position. -/
theorem ncard_at_le (hM : WalkAx M) {F : Set (Set Point)} (hF : F ⊆ M.Adm) (hfin : F.Finite)
    (p : ℕ) (t : ℝ) : {c | c ∈ F ∧ SideAttach M.W c p t}.ncard ≤ 2 := by
  by_cases hp : p < M.W.n ∧ 0 ≤ t ∧ t ≤ 1
  · refine le_trans (Set.ncard_le_ncard (t := {c | c ∈ F ∧ sidePt M.W p t ∈ c}) ?_
      (hfin.subset fun c hc => hc.1)) (ncard_through_le hM hF
        (hM.trace p hp.1 t hp.2.1 hp.2.2))
    exact fun c hc => ⟨hc.1, hc.2.2.2.2.1⟩
  · have : {c | c ∈ F ∧ SideAttach M.W c p t} = ∅ := by
      ext c
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro _ hA
      exact hp ⟨hA.1, hA.2.1, hA.2.2.1.le⟩
    rw [this, Set.ncard_empty]; omega

end FuseDeg

end

end Chazelle.Core
