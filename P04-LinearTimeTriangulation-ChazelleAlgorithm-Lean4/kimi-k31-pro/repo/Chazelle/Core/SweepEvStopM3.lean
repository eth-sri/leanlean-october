module

public import Chazelle.Core.SweepEvStopL

/-!
# The sweep (WP-D), stage 2: the attachments of a stop chord and its auxiliary data (mathematics)

For an admissible code `(kind, k, b)` with a free direction, the stop chord `e` has exactly two
attachments: the arrival position of its origin `a` (direction `-σ`) and that of its far end `w`
(direction `σ`) (`orig_attach`).  Hence (`anc_iff`, `pocket_iff`) `e` is anchored (a bracket)
iff one of them (none of them) is at offset `< Lst`, and it is a pocket iff one of them is at
offset `0`.  The parent of `e` (`parent_*`): the chord `k` for a wall piece; for the shared and
top chords the chord of `N₂` with its end in the direction `σ` at the origin.
-/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology
open Chazelle.Chain (SideAttach sidePt sideLeft)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
open Chazelle.Merge (FreeAt)
open WalkEmbed

namespace SweepStop

open Sweep SweepEv

variable {P : Polygon} {J : Merge.Junction} {N : NF}

/-- The data of an admissible code with a free direction. -/
structure OrgD (P : Polygon) (J : Merge.Junction) (N : NF) (kind k b : ℕ) : Prop where
  ok : StOK P J N kind k b
  free : FreeAt J.whole (stOrig J (Qof P) N kind k b) (dirOf b)

variable (hP : J.P.Simple) (hN : IsNF (chainModel J.right) (Qof P) N)
include hP hN

/-- **The attachments of a stop chord.** -/
theorem orig_attach {kind k b : ℕ} (hD : OrgD P J N kind k b) :
    (∀ p t, Arrival (chainModel J.whole).W (stOrig J (Qof P) N kind k b) (-dirOf b) p t →
      SideAttach (chainModel J.whole).W (stopSet J (Qof P) N kind k b) p t ∧
      sidePt (chainModel J.whole).W p t = (if b = 1 then Merge.lend (stopSet J (Qof P) N kind k b)
        else Merge.rend (stopSet J (Qof P) N kind k b))) ∧
    (∀ p t, Arrival (chainModel J.whole).W
        (farPt J.whole (stOrig J (Qof P) N kind k b) (dirOf b)) (dirOf b) p t →
      SideAttach (chainModel J.whole).W (stopSet J (Qof P) N kind k b) p t ∧
      sidePt (chainModel J.whole).W p t = (if 1 - b = 1 then
        Merge.lend (stopSet J (Qof P) N kind k b) else Merge.rend (stopSet J (Qof P) N kind k b))) ∧
    (∀ p t, SideAttach (chainModel J.whole).W (stopSet J (Qof P) N kind k b) p t →
      Arrival (chainModel J.whole).W (stOrig J (Qof P) N kind k b) (-dirOf b) p t ∨
      Arrival (chainModel J.whole).W
        (farPt J.whole (stOrig J (Qof P) N kind k b) (dirOf b)) (dirOf b) p t) := by
  obtain ⟨hok, hf⟩ := hD
  obtain ⟨haD, ha2, -, -, -⟩ := stOrig_facts hP hN hok
  have ha  := le_trans ha2 J.right_top_le
  have hb := hok.2.1
  have hσ := dirOf_cases' b
  rw [stopSet_eq]
  set a := stOrig J (Qof P) N kind k b
  obtain ⟨hT, -, -⟩ := Merge.hit_of_freeAt J.whole ha hσ hf
  have hends : (if b = 1 then Merge.lend (Merge.shoot J.whole a (dirOf b))
        else Merge.rend (Merge.shoot J.whole a (dirOf b))) = a ∧
      (if 1 - b = 1 then Merge.lend (Merge.shoot J.whole a (dirOf b))
        else Merge.rend (Merge.shoot J.whole a (dirOf b))) = farPt J.whole a (dirOf b) := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hb with rfl | rfl
    · rw [dirOf_zero] at hT ⊢
      obtain ⟨h1, h2⟩ := ends_shoot_neg J.whole hT.le
      simp [h1, h2]
    · rw [dirOf_one] at hT ⊢
      obtain ⟨h1, h2⟩ := ends_shoot_pos J.whole hT.le
      simp [h1, h2]
  refine ⟨fun p t hA => ⟨attach_of_origin hP ha haD hσ hf hA, by rw [hends.1]; exact hA.2.2.2.1⟩,
    fun p t hA => ⟨attach_of_far hP ha haD hσ hf hA, by rw [hends.2]; exact hA.2.2.2.1⟩,
    fun p t hA => ?_⟩
  rcases attach_cases hP ha hσ hf hA with ⟨-, h⟩ | ⟨-, h⟩
  · exact Or.inl h
  · exact Or.inr h

/-- **The two attachments** of a stop chord: any attachment is the arrival position of the
origin or that of the far end. -/
theorem attach_two {kind k b : ℕ} (hD : OrgD P J N kind k b) {p₀ p₁ : ℕ} {t₀ t₁ : ℝ}
    (h₀ : Arrival (chainModel J.whole).W (stOrig J (Qof P) N kind k b) (-dirOf b) p₀ t₀)
    (h₁ : Arrival (chainModel J.whole).W
      (farPt J.whole (stOrig J (Qof P) N kind k b) (dirOf b)) (dirOf b) p₁ t₁)
    {q : ℕ} {s : ℝ} (hA : SideAttach (chainModel J.whole).W (stopSet J (Qof P) N kind k b) q s) :
    (q = p₀ ∧ s = t₀) ∨ (q = p₁ ∧ s = t₁) := by
  obtain ⟨i1, i2, i3⟩ := orig_attach hP hN hD
  have hM  := FactsChain.walkAx J.whole hP
  have hm := (stop_mem hP hN hD.ok hD.free).1
  have ha  := F₂plus_subset J hN.1.2.1 hm
  rcases i3 q s hA with h | h
  · exact Or.inl (hM.attach_unique ha hA (i1 p₀ t₀ h₀).1 (by rw [h.2.2.2.1, h₀.2.2.2.1]))
  · exact Or.inr (hM.attach_unique ha hA (i2 p₁ t₁ h₁).1 (by rw [h.2.2.2.1, h₁.2.2.2.1]))

/-- **Anchored, pocket**: from the offsets of the two attachments. -/
theorem anc_pocket_iff {kind k b : ℕ} (hD : OrgD P J N kind k b) {p₀ p₁ : ℕ} {t₀ t₁ : ℝ}
    (h₀ : Arrival (chainModel J.whole).W (stOrig J (Qof P) N kind k b) (-dirOf b) p₀ t₀)
    (h₁ : Arrival (chainModel J.whole).W
      (farPt J.whole (stOrig J (Qof P) N kind k b) (dirOf b)) (dirOf b) p₁ t₁) :
    (¬ EvBrk J (stopSet J (Qof P) N kind k b) ↔
      oW J (p₀ + t₀) < Lst J ∨ oW J (p₁ + t₁) < Lst J) ∧
    ((∀ (q : ℕ) (s : ℝ), SideAttach (chainModel J.whole).W (stopSet J (Qof P) N kind k b) q s →
      oW J (q + s) ≠ 0) ↔ oW J (p₀ + t₀) ≠ 0 ∧ oW J (p₁ + t₁) ≠ 0) := by
  obtain ⟨i1, i2, -⟩ := orig_attach hP hN hD
  have hA₀ := (i1 p₀ t₀ h₀).1
  have hA₁ := (i2 p₁ t₁ h₁).1
  refine ⟨⟨fun h => ?_, fun h hb => ?_⟩, ⟨fun h => ⟨h _ _ hA₀, h _ _ hA₁⟩, fun h q s hA => ?_⟩⟩
  · unfold EvBrk at h
    push Not at h
    obtain ⟨q, s, hA, hlt⟩ := h
    rcases attach_two hP hN hD h₀ h₁ hA with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl hlt
    · exact Or.inr hlt
  · rcases h with h | h
    · exact absurd (hb _ _ hA₀) (not_le.2 h)
    · exact absurd (hb _ _ hA₁) (not_le.2 h)
  · rcases attach_two hP hN hD h₀ h₁ hA with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h.1
    · exact h.2

/-- The origin and the far end of a stop chord are distinct points of it. -/
theorem orig_far_ne {kind k b : ℕ} (hD : OrgD P J N kind k b) :
    stOrig J (Qof P) N kind k b ≠ farPt J.whole (stOrig J (Qof P) N kind k b) (dirOf b) ∧
      stOrig J (Qof P) N kind k b ∈ stopSet J (Qof P) N kind k b ∧
      farPt J.whole (stOrig J (Qof P) N kind k b) (dirOf b) ∈ stopSet J (Qof P) N kind k b := by
  obtain ⟨hok, hf⟩ := hD
  obtain ⟨-, ha2, -, -, -⟩ := stOrig_facts hP hN hok
  have ha  := le_trans ha2 J.right_top_le
  have hσ := dirOf_cases' b
  obtain ⟨hT, -, -⟩ := Merge.hit_of_freeAt J.whole ha hσ hf
  rw [stopSet_eq]
  refine ⟨fun h => ?_, ?_, rayPt_mem_shoot _ _ _ hT.le le_rfl⟩
  · have := congrArg Prod.fst h
    unfold farPt at this
    simp only [rayPt_fst] at this
    rcases hσ with h' | h' <;> rw [h'] at this hT <;> linarith
  · have := rayPt_mem_shoot J.whole (stOrig J (Qof P) N kind k b) (dirOf b) le_rfl hT.le
    rwa [show rayPt (stOrig J (Qof P) N kind k b) (dirOf b) 0 = stOrig J (Qof P) N kind k b by
      apply Geometry.point_ext <;> simp [rayPt]] at this

/-- **At most one parent**: two chords of `S₂` containing a stop chord are equal. -/
theorem parent_eq {kind k b : ℕ} (hD : OrgD P J N kind k b) {c c' : Set Point}
    (hc : c ∈ N.F (chainModel J.right) (Qof P)) (hc' : c' ∈ N.F (chainModel J.right) (Qof P))
    (h : stopSet J (Qof P) N kind k b ⊆ c) (h' : stopSet J (Qof P) N kind k b ⊆ c') : c = c' := by
  obtain ⟨hne, h1, h2⟩ := orig_far_ne hP hN hD
  exact parent_unique hN.1.2.1 hc hc' hne (h h1) (h h2) (h' h1) (h' h2)

omit hP hN in
/-- **The parent of a wall piece** is its chord. -/
theorem parent_wall (_hP : J.P.Simple) (hN : IsNF (chainModel J.right) (Qof P) N) {k b : ℕ}
    (hD : OrgD P J N 1 k b) :
    stopSet J (Qof P) N 1 k b ⊆ (N.chord k).toSet (chainModel J.right) (Qof P) := by
  obtain ⟨-, hb, hw, -⟩ := hD.ok
  obtain ⟨hk, -⟩ := hw rfl
  obtain ⟨-, hcase⟩ := stOrig_wall (Q := Qof P) hN hk hb
  rw [stopSet_eq]
  refine shoot_sub_end hN.1.2.1 (chord_mem hk) ?_
  rcases hcase with ⟨rfl, h⟩ | ⟨rfl, h⟩
  · exact Or.inl ⟨dirOf_one, h⟩
  · exact Or.inr ⟨dirOf_zero, h⟩

omit hP in
omit hN in
/-- **The parent of a shared or top chord**: a chord `c` of `S₂` contains it iff its end in the
direction `σ` is the origin. -/
theorem parent_vt_iff (_hP : J.P.Simple) {S₂ : Set (Set Point)} (hS₂ : S₂ ⊆ Merge.augChords J.right)
    {a : Point}
    (haR : a ∈ J.right.set) {b : ℕ} (hb : b ≤ 1)
    (hf : FreeAt J.whole a (dirOf b)) {c : Set Point} (hc : c ∈ S₂) :
    Merge.shoot J.whole a (dirOf b) ⊆ c ↔
      (b = 1 ∧ Merge.lend c = a) ∨ (b = 0 ∧ Merge.rend c = a) := by
  have hσ := dirOf_cases' b
  have ha  := le_trans (J.right.snd_le_top_of_mem_set haR) J.right_top_le
  obtain ⟨hT, -, -⟩ := Merge.hit_of_freeAt J.whole ha hσ hf
  constructor
  · intro hsub
    obtain ⟨y, l, r, hH, -, rfl, hl, hr⟩ := Merge.augChords_spec (hS₂ hc)
    have ha0 : a ∈ Visibility.hseg y l r := hsub (by
      have := rayPt_mem_shoot J.whole a (dirOf b) le_rfl hT.le
      rwa [show rayPt a (dirOf b) 0 = a by apply Geometry.point_ext <;> simp [rayPt]] at this)
    have haD : a ∉ J.right.dom := fun hd => J.right.not_mem_set_of_mem_dom hd haR
    obtain ⟨hay, hal, har⟩ := ha0
    -- `a` is an end of the chord
    have hend : a.1 = l ∨ a.1 = r := by
      by_contra hne
      push Not at hne
      exact haD (by
        have := hH.open_mem a.1 (lt_of_le_of_ne hal (Ne.symm hne.1)) (lt_of_le_of_ne har hne.2)
        rwa [show ((a.1, y) : Point) = a from Prod.ext rfl hay.symm] at this)
    -- the points just after `a` along the ray are in the chord
    set s : ℝ := min (J.whole.hitParam a (dirOf b)) ((r - l) / 2) with hs
    have hs0 : 0 < s := lt_min hT (by linarith [hH.lt])
    have hmem := hsub (rayPt_mem_shoot J.whole a (dirOf b) hs0.le (min_le_left _ _))
    obtain ⟨-, h1, h2⟩ := hmem
    simp only [rayPt_fst] at h1 h2
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hb with rfl | rfl
    · rw [dirOf_zero] at h1 h2
      right; refine ⟨rfl, ?_⟩
      rw [hr]; refine Prod.ext ?_ hay.symm
      rcases hend with h | h
      · exfalso; linarith
      · exact h.symm
    · rw [dirOf_one] at h1 h2
      left; refine ⟨rfl, ?_⟩
      rw [hl]; refine Prod.ext ?_ hay.symm
      rcases hend with h | h
      · exact h.symm
      · exfalso; linarith
  · rintro (⟨rfl, h⟩ | ⟨rfl, h⟩)
    · exact shoot_sub_end hS₂ hc (Or.inl ⟨dirOf_one, h.symm⟩)
    · exact shoot_sub_end hS₂ hc (Or.inr ⟨dirOf_zero, h.symm⟩)

end SweepStop

end

end Chazelle.Core
