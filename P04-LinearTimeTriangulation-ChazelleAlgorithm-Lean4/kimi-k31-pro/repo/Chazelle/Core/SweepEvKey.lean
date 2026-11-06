module

public import Chazelle.Core.SweepEvGL
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.MiscTactics

/-!
# The sweep (WP-D), stage 3: the local structure at a key

At a cut key `(p, t)` of a chord family at most two chords are attached.  `keyStruct` packages the
local picture (`after_side`, `before_side`, `after_side_tie`, `faced_or_middle`): there are chords
`X` (bounding the region faced just before the key, on its side `dX`) and `Y` (bounding the region
faced just after it, on its side `-dY`), `dX`, `dY` the directions in which they leave the key,
every chord at the key is `X` or `Y`, and if `X ≠ Y` (a tie) the region on the side `dY` of `Y` is
the region on the side `-dX` of `X` (the middle region).

Also: `side_regions_ne` (the two sides of a chord are distinct regions), `before_region_exists'`
(a region faced just before a key of positive offset, with cut-free positions just before it),
`faced_both_arcs` (a region is not faced in both arcs of a chord).
-/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sidePt sideInArc SideSectorIn)
open WalkEmbed

namespace Sweep

/-- The direction `d` (`1` east, `-1` west) in which a chord leaves the position `(p, t)`. -/
def DirAt (W : Polygon) (e : Set Point) (p : ℕ) (t d : ℝ) : Prop :=
  (d = 1 ∧ ∀ z ∈ e, (sidePt W p t).1 ≤ z.1) ∨ (d = -1 ∧ ∀ z ∈ e, z.1 ≤ (sidePt W p t).1)

theorem DirAt.cases {W : Polygon} {e : Set Point} {p : ℕ} {t d : ℝ} (h : DirAt W e p t d) :
    d = 1 ∨ d = -1 := by
  rcases h with ⟨h, -⟩ | ⟨h, -⟩
  · exact Or.inl h
  · exact Or.inr h

section Key

variable {M : Model}

/-- Every attached chord leaves its position in some direction. -/
theorem dirAt_exists (hM : WalkAx M) {c : Set Point} (hc : c ∈ M.Adm) {p : ℕ} {t : ℝ}
    (hA : SideAttach M.W c p t) : ∃ d, DirAt M.W c p t d := by
  rcases hM.attach_dir hc hA with h | h
  · exact ⟨1, Or.inl ⟨rfl, h⟩⟩
  · exact ⟨-1, Or.inr ⟨rfl, h⟩⟩

/-- **The two sides of a chord are distinct regions.** -/
theorem side_regions_ne (hM : WalkAx M) {F : Set (Set Point)} (hF : F ⊆ M.Adm) (hfin : F.Finite)
    {c : Set Point} (hc : c ∈ F) {p : ℕ} {t : ℝ} (hA : SideAttach M.W c p t) {U V : Set Point}
    (hU : U ∈ M.regions F) (hV : V ∈ M.regions F) (hSU : SideOf M 1 c U)
    (hSV : SideOf M (-1) c V) : U ≠ V := by
  obtain ⟨U', V', hU', hV', hne, hside, -⟩ := chordSides_of_system (hM.sys F hF hfin) hc
  obtain ⟨z, hz, hzD⟩ := exists_mem_dom hM (hF hc) hA
  have hS1 : SideOf M 1 c U' := fun z hz hzD => (hside z hz hzD).mono fun δ h => by simpa using h.1
  have hS2 : SideOf M (-1) c V' := fun z hz hzD => (hside z hz hzD).mono fun δ h => by
    simpa [sub_eq_add_neg] using h.2
  rw [sideOf_eq hU hU' hSU hS1 hz hzD, sideOf_eq hV hV' hSV hS2 hz hzD]
  exact hne

/-- **The local structure at a key.** -/
theorem keyStruct {Q : Polygon} {F : Set (Set Point)} (hGM : GoodModel M)
    (hFam : M.ChordFamily Q F) {e : Set Point} (he : e ∈ F) {p : ℕ} {t : ℝ}
    (hA : SideAttach M.W e p t) :
    ∃ (X Y : Set Point) (dX dY : ℝ), X ∈ F ∧ Y ∈ F ∧ SideAttach M.W X p t ∧
      SideAttach M.W Y p t ∧ DirAt M.W X p t dX ∧ DirAt M.W Y p t dY ∧
      (∀ c ∈ F, SideAttach M.W c p t → c = X ∨ c = Y) ∧
      (∀ R ∈ M.regions F, AfterFaces M p t R → SideOf M (-dY) Y R) ∧
      (∀ R ∈ M.regions F, BeforeFaces M p t R → SideOf M dX X R) ∧
      (X ≠ Y → ∀ R ∈ M.regions F, (SideOf M dY Y R ↔ SideOf M (-dX) X R)) ∧
      (X = Y → dX = dY) := by
  have hM := walkAx_of_goodModel hGM
  have hF  := hFam.2.1
  by_cases htie : ∃ e' ∈ F, e' ≠ e ∧ SideAttach M.W e' p t
  · obtain ⟨e', he', hne, hA'⟩ := htie
    -- the east chord and the west chord
    obtain ⟨ce, cw, hce, hcw, hAe, hAw, hE, hW, hnew⟩ : ∃ ce cw : Set Point, ce ∈ F ∧ cw ∈ F ∧
        SideAttach M.W ce p t ∧ SideAttach M.W cw p t ∧ (∀ z ∈ ce, (sidePt M.W p t).1 ≤ z.1) ∧
        (∀ z ∈ cw, z.1 ≤ (sidePt M.W p t).1) ∧ cw ≠ ce := by
      rcases hM.tie_pair hF he he' hne.symm hA hA' with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨e, e', he, he', hA, hA', h1, h2, hne⟩
      · exact ⟨e', e, he', he, hA', hA, h2, h1, hne.symm⟩
    obtain ⟨-, hhor, hall⟩ := hM.tie_shape hF hce hcw hAe hAw hE hW
    have hT := fun {G} (hG : G ∈ M.regions F) => after_side_tie hGM hFam hce hcw hnew hAe hAw hE hW hG
    have mid := fun {ρ U} (hρ : ρ = 1 ∨ ρ = -1) (hU : U ∈ M.regions F) (hS : SideOf M ρ ce U) =>
      (faced_or_middle hGM hFam hce hAe hρ hU hS (Or.inl ⟨rfl, hE⟩)).2 cw hcw hnew hAw
    have mid' := fun {ρ U} (hρ : ρ = 1 ∨ ρ = -1) (hU : U ∈ M.regions F) (hS : SideOf M ρ cw U) =>
      (faced_or_middle hGM hFam hcw hAw hρ hU hS (Or.inr ⟨rfl, hW⟩)).2 ce hce hnew.symm hAe
    rcases lt_or_gt_of_ne hhor with hdn | hup
    · -- descending: `Y = ce`, `X = cw`
      refine ⟨cw, ce, -1, 1, hcw, hce, hAw, hAe, Or.inr ⟨rfl, hW⟩, Or.inl ⟨rfl, hE⟩,
        fun c hc hc' => (hall c hc hc').symm, fun R hR hR' => (hT hR).1 hdn hR',
        fun R hR hR' => (hT hR).2.1 hdn hR', fun _ R hR => ?_, fun h => absurd h hnew⟩
      rw [neg_neg]
      exact ⟨fun h => ((mid (Or.inl rfl) hR h).2.2.1 hdn).1 rfl,
        fun h => ((mid' (Or.inl rfl) hR h).2.2.1 hdn).1 rfl⟩
    · -- ascending: `Y = cw`, `X = ce`
      refine ⟨ce, cw, 1, -1, hce, hcw, hAe, hAw, Or.inl ⟨rfl, hE⟩, Or.inr ⟨rfl, hW⟩,
        fun c hc hc' => hall c hc hc', fun R hR hR' => by rw [neg_neg]; exact (hT hR).2.2.1 hup hR',
        fun R hR hR' => (hT hR).2.2.2 hup hR', fun _ R hR => ?_, fun h => absurd h.symm hnew⟩
      exact ⟨fun h => ((mid' (Or.inr rfl) hR h).2.2.2 hup).1 rfl,
        fun h => ((mid (Or.inr rfl) hR h).2.2.2 hup).1 rfl⟩
  · push Not at htie
    have huniq : ∀ e' ∈ F, SideAttach M.W e' p t → e' = e := by
      intro e' he' hA'
      by_contra hne
      exact htie e' he' hne hA'
    obtain ⟨d, hd⟩ := dirAt_exists hM (hF he) hA
    exact ⟨e, e, d, d, he, he, hA, hA, hd, hd, fun c hc hc' => Or.inl (huniq c hc hc'),
      fun R hR hR' => after_side hGM hFam he hA huniq hd hR hR',
      fun R hR hR' => before_side hGM hFam he hA huniq hd hR hR', fun h => absurd rfl h,
      fun _ => rfl⟩

/-- **A region is not faced in both arcs of a chord.** -/
theorem faced_both_arcs (hM : WalkAx M) {F : Set (Set Point)} (hF : F ⊆ M.Adm) {c : Set Point}
    (hc : c ∈ F) {pa pb : ℕ} {ta tb : ℝ} (hA : SideAttach M.W c pa ta)
    (hB : SideAttach M.W c pb tb) (hAB : sidePt M.W pa ta ≠ sidePt M.W pb tb) {R : Set Point}
    (hR : R ∈ M.regions F) {p q : ℕ} {t s : ℝ} (hp : p < M.W.n) (hq : q < M.W.n)
    (ht : t ∈ Ioo (0 : ℝ) 1) (hs : s ∈ Ioo (0 : ℝ) 1)
    (h1 : sideInArc (pa + ta) (pb + tb) (p + t)) (h2 : sideInArc (pb + tb) (pa + ta) (q + s))
    (hf1 : M.Faces p t R) (hf2 : M.Faces q s R) : False := by
  obtain ⟨K₁, K₂, hne, ⟨c₁, rfl⟩, ⟨c₂, rfl⟩, k₁, k₂⟩ := hM.split (hF hc) hA hB hAB
  have hR1 := hM.region_subset_of_sector hc hR hp ht hf1 (k₁ p hp t ht.1.le ht.2 h1)
  have hR2 := hM.region_subset_of_sector hc hR hq hs hf2 (k₂ q hq s hs.1.le hs.2 h2)
  obtain ⟨w, hw⟩ := Chazelle.Chain.regionsIn_nonempty hR
  exact hne ((connectedComponentIn_eq (hR1 hw)).trans (connectedComponentIn_eq (hR2 hw)).symm)

end Key

section Junction

variable {J : Merge.Junction}

/-- **`faced_both_arcs` in offsets.** -/
theorem faced_both_off (hP : J.P.Simple) {S₂ : Set (Set Point)}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hS₂f : S₂.Finite) {c : Set Point}
    (hc : c ∈ F₂plus J S₂) {pa pb : ℕ} {ta tb : ℝ}
    (hA : SideAttach (chainModel J.whole).W c pa ta) (hB : SideAttach (chainModel J.whole).W c pb tb)
    (hAB : oW J (pa + ta) < oW J (pb + tb)) {R : Set Point}
    (hR : R ∈ (chainModel J.whole).regions (F₂plus J S₂)) {p q : ℕ} {t s : ℝ}
    (hp : p < (chainModel J.whole).W.n) (hq : q < (chainModel J.whole).W.n)
    (ht : t ∈ Ioo (0 : ℝ) 1) (hs : s ∈ Ioo (0 : ℝ) 1)
    (h1 : oW J (pa + ta) < oW J (p + t)) (h1' : oW J (p + t) < oW J (pb + tb))
    (h2 : oW J (q + s) < oW J (pa + ta) ∨ oW J (pb + tb) < oW J (q + s))
    (hf1 : (chainModel J.whole).Faces p t R) (hf2 : (chainModel J.whole).Faces q s R) : False := by
  have hC := corr_right0 J hP hS₂ hS₂f
  have hg0 : (0 : ℝ) ≤ ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) := Nat.cast_nonneg _
  have hgn : ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) < (chainModel J.whole).W.n := by
    exact_mod_cast hC.hg
  obtain ⟨a0, a1⟩ := Corr.key_mem hA.1 hA.2.1 hA.2.2.1
  obtain ⟨b0, b1⟩ := Corr.key_mem hB.1 hB.2.1 hB.2.2.1
  obtain ⟨x0, x1⟩ := Corr.key_mem hp ht.1.le ht.2
  obtain ⟨y0, y1⟩ := Corr.key_mem hq hs.1.le hs.2
  exact faced_both_arcs hC.hM hC.hF hc hA hB (pt_ne_of_off_ne hP hS₂ hS₂f hc hA hB hAB.ne) hR hp hq
    ht hs ((sideInArc_iff_off hg0 hgn a0 a1 b0 b1 x0 x1 hAB).2 ⟨h1, h1'⟩)
    ((sideInArc_rev_iff_off hg0 hgn a0 a1 b0 b1 y0 y1 hAB).2 h2) hf1 hf2

/-- **A region faced just before a key of positive offset**, with non-cut positions facing it
arbitrarily close before the key and no cut in between. -/
theorem before_region_exists' (hP : J.P.Simple) {S₂ : Set (Set Point)}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hS₂f : S₂.Finite) {p : ℕ} {t : ℝ}
    (hp : p < (chainModel J.whole).W.n) (ht0 : 0 ≤ t) (ht1 : t < 1) (hpos : 0 < oW J (p + t))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R ∈ (chainModel J.whole).regions (F₂plus J S₂), BeforeFaces (chainModel J.whole) p t R ∧
      ∃ (q : ℕ) (u : ℝ), q < (chainModel J.whole).W.n ∧ u ∈ Ioo (0 : ℝ) 1 ∧
        ¬ (chainModel J.whole).IsCut (F₂plus J S₂) (q + u) ∧ (chainModel J.whole).Faces q u R ∧
        oW J (p + t) - ε < oW J (q + u) ∧ oW J (q + u) < oW J (p + t) ∧
        ∀ x, (chainModel J.whole).IsCut (F₂plus J S₂) x → 0 ≤ x →
          x < (chainModel J.whole).W.n → ¬ (oW J (q + u) < oW J x ∧ oW J x < oW J (p + t)) := by
  have hC := corr_right0 J hP hS₂ hS₂f
  have hM := hC.hM
  set n := (chainModel J.whole).W.n with hndef
  have hg  := hC.hg
  have hg0 : (0 : ℝ) ≤ ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) := Nat.cast_nonneg _
  have hgn : ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) < n := by exact_mod_cast hg
  have hn0 : 0 < n := by omega
  obtain ⟨k0, k1⟩ := Corr.key_mem hp ht0 ht1
  -- the key just before `(p, t)`: `X - s`
  set X : ℝ := if 0 < t ∨ 1 ≤ p then (p : ℝ) + t else (n : ℝ) with hX
  -- the position at distance `s` before the key
  have hw : ∀ s, 0 < s → s < 1 → (0 < t → s < t) →
      ∃ (q : ℕ) (u : ℝ), q < n ∧ u ∈ Ioo (0 : ℝ) 1 ∧ (q : ℝ) + u = X - s ∧
        oW J (q + u) = oW J (p + t) - s := by
    intro s hs0 hs1 hst
    rcases ht0.lt_or_eq with htp | rfl
    · refine ⟨p, t - s, hp, ⟨by linarith [hst htp], by linarith⟩, ?_, ?_⟩
      · rwring [hX, ite_eq_left (Or.inl htp)]
      · exact off_before_edge hg hp hs0 (hst htp) ht1
    · refine ⟨(p + n - 1) % n, 1 - s, Nat.mod_lt _ hn0, ⟨by linarith, by linarith⟩, ?_,
        off_before_vertex hg hp hs0 hs1 hpos⟩
      rcases Nat.eq_zero_or_pos p with rfl | hp1
      · rw [hX, ite_eq_right (by simp), show (0 + n - 1) % n = n - 1 by
          rwo [Nat.mod_eq_of_lt (by omega)], Nat.cast_sub (by omega)]
        pcr
      · rw [hX, ite_eq_left (Or.inr (show 1 ≤ p by omega)), show (p + n - 1) % n = p - 1 by
          rw [show p + n - 1 = (p - 1) + n by omega, Nat.add_mod_right,
            Nat.mod_eq_of_lt (by omega)], Nat.cast_sub (by omega)]
        pcr
  obtain ⟨δ₀, hδ₀, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1
    (eventually_not_cut_before hM hC.hF hC.hfin X)
  have hδ₀' : (0 : ℝ) < δ₀ := hδ₀
  set δ := min (min δ₀ ε) (min 1 (if 0 < t then t else 1)) with hδ
  have hT : 0 < (if 0 < t then t else 1) := by split_ifs with h <;> linarith
  have hδ0 : 0 < δ := lt_min (lt_min hδ₀' hε) (lt_min one_pos hT)
  have hδ1 : δ ≤ δ₀ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hδ2 : δ ≤ ε := le_trans (min_le_left _ _) (min_le_right _ _)
  have hδ3 : δ ≤ 1 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hδ4 : 0 < t → δ ≤ t := fun h => by
    have := le_trans (min_le_right (min δ₀ ε) _) (min_le_right 1 (if 0 < t then t else 1))
    rw [ite_eq_left h] at this
    rwx [hδ, ite_eq_left h]
  have hnc : ∀ s, 0 < s → s < δ → ∀ (q : ℕ) (u : ℝ), (q : ℝ) + u = X - s →
      ¬ (chainModel J.whole).IsCut (F₂plus J S₂) (q + u) := by
    intro s hs0 hs1 q u hqu
    have := hsub ⟨hs0, lt_of_lt_of_le hs1 hδ1⟩
    rw [Set.mem_ofPred_eq] at this
    rwa [hqu]
  -- the position at `δ / 2`
  obtain ⟨q, u, hq, hu, hqu, hoff⟩ := hw (δ / 2) (by linarith) (by linarith)
    (fun h => by linarith [hδ4 h])
  have hnc0 := hnc (δ / 2) (by linarith) (by linarith) q u hqu
  obtain ⟨R, hR, hfR⟩ := hM.exists_faces_of_not_cut hC.hF hC.hfin hq hu hnc0
  have hgap : ∀ x, (chainModel J.whole).IsCut (F₂plus J S₂) x → 0 ≤ x →
      x < n → ¬ (oW J (q + u) < oW J x ∧ oW J x < oW J (p + t)) := by
    rintro x hx hx0 hxn ⟨h1, h2⟩
    set s' := oW J (p + t) - oW J x with hs'
    obtain ⟨q', u', hq', hu', hqu', hoff'⟩ := hw s' (by linarith) (by linarith)
      (fun h => by linarith [hδ4 h])
    have hk := Corr.key_mem hq' hu'.1.le hu'.2
    have hxeq : x = (q' : ℝ) + u' :=
      off_inj hg0 hgn hx0 hxn hk.1 hk.2 (by rwring [← oW_eq, ← oW_eq, hoff', hs'])
    exact hnc s' (by linarith) (by linarith) q' u' hqu' (hxeq ▸ hx)
  refine ⟨R, hR, before_faces_of_gap hM hC.hF hC.hfin hg0 hgn hR hq hu hnc0 hfR hp ht0 ht1
    (by rwli [← oW_eq, ← oW_eq, hoff]) hgap, q, u, hq, hu, hnc0, hfR,
    by rwli [hoff], by rwli [hoff], hgap⟩

end Junction

end Sweep

end

end Chazelle.Core
