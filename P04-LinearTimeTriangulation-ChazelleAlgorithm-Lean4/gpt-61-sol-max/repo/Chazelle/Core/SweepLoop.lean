module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.SweepTop
public import Chazelle.Core.SweepChainT2

/-!
# The sweep (WP-D), part 11: the event-loop invariant (stack rule for wall pieces)

* `side_region_exists`, `after_side`, `before_side`, `after_side_tie`: the region faced just after
  (before) a cut key lies on a side of a chord attached there (event-loop item (c)).
* `transparent_closed`, `composite_transparent`: a closed block of keys is transparent; in
  particular two wall pieces of one wall-to-wall chord of `S₂` meeting at a vertex of `C₁` form a
  transparent bracket (the stack rule, design §10.t).
* `Valid`: the invariant of the sweep's label `λ` for the current region `G` of `F₂⁺`: every
  label of `G` is `λ`, and if `G` has no label, `λ` is a virtual label of `G` or `G` is the middle
  region of a tie leaving the stretch.
* `valid_of_vlabel`, `valid_of_rlabel`, `valid_of_tieOut`: the rules of the event loop establish
  `Valid`; `detect_valid`: from a valid state, the next stretch-anchored cut is found.
* `F₂plus_cases`, `shared_tie_partner`: event-loop item (b).

## RAM obligations (accepted design, §10.t and round 8)

* **Wall pieces (stack rule).**  Both attachments of every piece seen from a box-wall endpoint of
  a chord of `S₂` are precomputed stops.  At the first one the label is pushed, at the second one
  it is popped (`bracket_transparent`, `composite_transparent`), except when the attachment on
  `C₁` is a tie with a stretch-anchored piece of the same chord, where the fused rule of that
  piece applies.  The precomputation shoots from the wall point `b` in the model of `C₁` at the
  arcs of the region of `S₁` of `b`, **splitting the subarc at the key of `b`** so that the origin
  is not on the target subarc (`ShooterOK`, finding E2).
* **Queries at the shared vertex** are answered by the shared chord in the query's direction
  (when free); no shot is made in the model of `C₂` (E2).
* **Detection shots** are made from endpoints of exit chords of the label that are neither the
  shared vertex (shared chords are always candidates) nor on the box (wall pieces are stops) nor
  on the slit of `C₁` (such a chord is at or above the top of `C₁` and meets `C₁` at most at its
  top vertex, a vertex case; otherwise the shot is skipped).
-/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sideInArc sidePt sideLeft sideKey_inj)
open WalkEmbed

namespace Sweep

/-! ## The region after a cut key (item (c)) -/

/-- Every chord of a finite admissible family has a region on each side. -/
theorem side_region_exists {M : Model} (hM : WalkAx M) {F : Set (Set Point)} (hF : F ⊆ M.Adm)
    (hfin : F.Finite) {c : Set Point} (hc : c ∈ F) {ρ : ℝ} (hρ : ρ = 1 ∨ ρ = -1) :
    ∃ U ∈ M.regions F, SideOf M ρ c U := by
  obtain ⟨Up, Dn, hUp, hDn, -, hside, -⟩ := chordSides_of_system (hM.sys F hF hfin) hc
  rcases hρ with rfl | rfl
  · exact ⟨Up, hUp, fun z hz hzD => (hside z hz hzD).mono fun δ h => by grind⟩
  · exact ⟨Dn, hDn, fun z hz hzD => (hside z hz hzD).mono fun δ h => by
      grind [sub_eq_add_neg]⟩

section
variable {M : Model} {F : Set (Set Point)} {p : ℕ} {t : ℝ}
/-- Two regions faced just after the same position are equal. -/
theorem after_unique (ht1 : t < 1)
    {U U' : Set Point} (hU : U ∈ M.regions F) (hU' : U' ∈ M.regions F)
    (h : AfterFaces M p t U) (h' : AfterFaces M p t U') : U = U' := by
  obtain ⟨δ, hδ, h1⟩ := h
  obtain ⟨δ', hδ', h2⟩ := h'
  set s := min (min δ δ') (1 - t) / 2 with hs
  have hs0 : 0 < s := by
    grind
  have hs1 : s < δ := by
    grind
  have hs2 : s < δ' := by
    grind
  have hs3 : t + s < 1 := by grind
  exact WalkAx.faces_unique hU hU' (h1 s hs0 hs1 hs3) (h2 s hs0 hs2 hs3)

/-- Two regions faced just before the same position are equal. -/
theorem before_unique (ht0 : 0 ≤ t)
    {U U' : Set Point} (hU : U ∈ M.regions F) (hU' : U' ∈ M.regions F)
    (h : BeforeFaces M p t U) (h' : BeforeFaces M p t U') : U = U' := by
  obtain ⟨δ, hδ, h1a, h1b⟩ := h
  obtain ⟨δ', hδ', h2a, h2b⟩ := h'
  rcases ht0.lt_or_eq with htp | ht00
  · set s := min (min δ δ') t / 2 with hs
    have hs0 : 0 < s := by
      grind
    have hs1 : s < δ := by
      grind
    have hs2 : s < δ' := by
      grind
    have hs3 : s < t := by grind
    exact WalkAx.faces_unique hU hU' (h1a htp s hs0 hs1 hs3) (h2a htp s hs0 hs2 hs3)
  · subst ht00
    set s := min δ δ' / 2 with hs
    have hs0 : 0 < s := by positivity
    have hs1 : s < δ := by have := min_le_left δ δ'; linarith
    have hs2 : s < δ' := by grind
    exact WalkAx.faces_unique hU hU' (h1b rfl s hs0 hs1) (h2b rfl s hs0 hs2)


end

section
variable {M : Model} {Q : Polygon} {F : Set (Set Point)} (hGM : GoodModel M) (hFam : M.ChordFamily Q F) {e : Set Point} (he : e ∈ F) {p : ℕ} {t : ℝ} (hA : SideAttach M.W e p t) (huniq : ∀ e' ∈ F, SideAttach M.W e' p t → e' = e) {dir : ℝ} (hdir : (dir = 1 ∧ ∀ z ∈ e, (sidePt M.W p t).1 ≤ z.1) ∨
      (dir = -1 ∧ ∀ z ∈ e, z.1 ≤ (sidePt M.W p t).1)) {G : Set Point} (hG : G ∈ M.regions F)
include Q F hGM hFam he hA huniq hdir hG
/-- **The region faced just after a uniquely attached chord** lies on its side `-dir` (item
(c)). -/
theorem after_side (hW : AfterFaces M p t G) : SideOf M (-dir) e G := by
  have hM := walkAx_of_goodModel hGM
  have hρ : -dir = 1 ∨ -dir = -1 := by
    grind
  obtain ⟨U, hU, hS⟩ := side_region_exists hM hFam.2.1 hFam.1 he hρ
  have hfac := (faced_or_middle hGM hFam he hA hρ hU hS hdir).1 huniq
  have hd2 : -dir * dir = -1 := by grind
  rw [after_unique hA.2.2.1 hG hU hW (hfac.1 hd2)]
  exact hS

/-- **The region faced just before a uniquely attached chord** lies on its side `dir` (item
(c)). -/
theorem before_side (hW : BeforeFaces M p t G) : SideOf M dir e G := by
  have hM := walkAx_of_goodModel hGM
  have hρ : dir = 1 ∨ dir = -1 := by
    grind
  obtain ⟨U, hU, hS⟩ := side_region_exists hM hFam.2.1 hFam.1 he hρ
  have hfac := (faced_or_middle hGM hFam he hA hρ hU hS hdir).1 huniq
  have hd2 : dir * dir = 1 := by grind
  rw [before_unique hA.2.1 hG hU hW (hfac.2 hd2)]
  exact hS


end

/-- **The regions faced around a tie** (item (c)): at a tie whose leaving edge goes down, the
region faced just after is below the east chord and the region faced just before is below the
west chord; when the edge goes up, the region faced just after is above the west chord and the
region faced just before is above the east chord. -/
theorem after_side_tie {M : Model} {Q : Polygon} {F : Set (Set Point)} (hGM : GoodModel M)
    (hFam : M.ChordFamily Q F) {ce cw : Set Point} (hce : ce ∈ F) (hcw : cw ∈ F)
    (hne : cw ≠ ce) {p : ℕ} {t : ℝ} (hAe : SideAttach M.W ce p t)
    (hAw : SideAttach M.W cw p t) (hE : ∀ z ∈ ce, (sidePt M.W p t).1 ≤ z.1)
    (hWd : ∀ z ∈ cw, z.1 ≤ (sidePt M.W p t).1) {G : Set Point} (hG : G ∈ M.regions F) :
    ((M.wb p).2 < (M.wa p).2 → AfterFaces M p t G → SideOf M (-1) ce G) ∧
    ((M.wb p).2 < (M.wa p).2 → BeforeFaces M p t G → SideOf M (-1) cw G) ∧
    ((M.wa p).2 < (M.wb p).2 → AfterFaces M p t G → SideOf M 1 cw G) ∧
    ((M.wa p).2 < (M.wb p).2 → BeforeFaces M p t G → SideOf M 1 ce G) := by
  have hM := walkAx_of_goodModel hGM
  have hF : F ⊆ M.Adm := hFam.2.1
  have hfin : F.Finite := hFam.1
  obtain ⟨Ue, hUe, hSe⟩ := side_region_exists hM hF hfin hce (Or.inr rfl : (-1 : ℝ) = 1 ∨ _)
  obtain ⟨Uw, hUw, hSw⟩ := side_region_exists hM hF hfin hcw (Or.inr rfl : (-1 : ℝ) = 1 ∨ _)
  obtain ⟨Ue', hUe', hSe'⟩ := side_region_exists hM hF hfin hce (Or.inl rfl : (1 : ℝ) = 1 ∨ _)
  obtain ⟨Uw', hUw', hSw'⟩ := side_region_exists hM hF hfin hcw (Or.inl rfl : (1 : ℝ) = 1 ∨ _)
  have fe := fun {ρ U} (hρ : ρ = 1 ∨ ρ = -1) (hU : U ∈ M.regions F) (hS : SideOf M ρ ce U) =>
    (faced_or_middle hGM hFam hce hAe hρ hU hS (Or.inl ⟨rfl, hE⟩)).2 cw hcw hne hAw
  have fw := fun {ρ U} (hρ : ρ = 1 ∨ ρ = -1) (hU : U ∈ M.regions F) (hS : SideOf M ρ cw U) =>
    (faced_or_middle hGM hFam hcw hAw hρ hU hS (Or.inr ⟨rfl, hWd⟩)).2 ce hce hne.symm hAe
  refine ⟨fun hdn hW => ?_, fun hdn hW => ?_, fun hup hW => ?_, fun hup hW => ?_⟩
  · obtain ⟨-, -, h, -⟩ := fe (Or.inr rfl) hUe hSe
    have hfac := (h hdn).2 rfl
    rw [after_unique hAe.2.2.1 hG hUe hW (hfac.1 (by norm_num))]; exact hSe
  · obtain ⟨-, -, h, -⟩ := fw (Or.inr rfl) hUw hSw
    have hfac := (h hdn).2 rfl
    rw [before_unique hAw.2.1 hG hUw hW (hfac.2 (by norm_num))]; exact hSw
  · obtain ⟨-, -, -, h⟩ := fw (Or.inl rfl) hUw' hSw'
    have hfac := (h hup).2 rfl
    rw [after_unique hAw.2.2.1 hG hUw' hW (hfac.1 (by norm_num))]; exact hSw'
  · obtain ⟨-, -, -, h⟩ := fe (Or.inl rfl) hUe' hSe'
    have hfac := (h hup).2 rfl
    rw [before_unique hAe.2.1 hG hUe' hW (hfac.2 (by norm_num))]; exact hSe'

/-! ## Transparent blocks (the stack rule) -/

/-! ## The invariant -/

section Inv

variable (J : Merge.Junction)

section
variable (S₂ : Set (Set Point))
include S₂
/-- **The middle region of a tie of top chords leaving the stretch** (case G, above the two top
chords at the split vertex): two distinct chords of `F₂⁺` through the top of `C₂` attached at a
vertex position inside the right stretch (not its base), with far attachments off the stretch,
and `G` on the same side of both. -/
def TieOut (G : Set Point) : Prop :=
  ∃ (e e' : Set Point) (d : ℕ) (pb pb' : ℕ) (tb tb' : ℝ) (ρ : ℝ),
    e ∈ F₂plus J S₂ ∧ e' ∈ F₂plus J S₂ ∧ e' ≠ e ∧ d ≠ 0 ∧ d < rL1 J + rL2 J ∧
    SideAttach (chainModel J.whole).W e ((6 + tpos J.whole J.m₁ + d) % (chainModel J.whole).W.n) 0 ∧
    SideAttach (chainModel J.whole).W e'
      ((6 + tpos J.whole J.m₁ + d) % (chainModel J.whole).W.n) 0 ∧
    SideAttach (chainModel J.whole).W e pb tb ∧ SideAttach (chainModel J.whole).W e' pb' tb' ∧
    sidePt (chainModel J.whole).W pb tb ≠ sidePt (chainModel J.whole).W
      ((6 + tpos J.whole J.m₁ + d) % (chainModel J.whole).W.n) 0 ∧
    sidePt (chainModel J.whole).W pb' tb' ≠ sidePt (chainModel J.whole).W
      ((6 + tpos J.whole J.m₁ + d) % (chainModel J.whole).W.n) 0 ∧
    ¬ (0 < off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pb + tb) ∧
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pb + tb) <
        ((rL1 J + rL2 J : ℕ) : ℝ)) ∧
    ¬ (0 < off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pb' + tb') ∧
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pb' + tb') <
        ((rL1 J + rL2 J : ℕ) : ℝ)) ∧
    (ρ = 1 ∨ ρ = -1) ∧ SideOf (chainModel J.whole) ρ e G ∧ SideOf (chainModel J.whole) ρ e' G ∧
    J.right.top ∈ e ∧ J.right.top ∈ e'

/-- **The invariant of the sweep's label** `λ` for the current region `G`: every label of `G` is
`λ`; if `G` has no label, `λ` is a virtual label of `G` or `G` is the middle region of a tie
leaving the stretch (the cases in which the next stretch-anchored cut is found). -/
def Valid (G L : Set Point) : Prop :=
  (∀ V ∈ (chainModel J.right).regions S₂, RLabel J S₂ G V → LabS J S₂ L V) ∧
    ((∀ V, ¬ RLabel J S₂ G V) → VLabel J S₂ G L ∨ TieOut J S₂ G)


end

/-- **Rule for fused chords, events after the stack pops of tie partners** (λ := the recorded side
of the chord of `S₂`): a virtual label is valid. -/
theorem valid_of_vlabel (hP : J.P.Simple) {Q : Polygon}
    {S₂ : Set (Set Point)} (hS₂ : (chainModel J.right).ChordFamily Q S₂)
    (hF : (chainModel J.whole).ChordFamily Q (F₂plus J S₂)) {G L : Set Point}
    (hG : G ∈ (chainModel J.whole).regions (F₂plus J S₂))
    (hL : L ∈ (chainModel J.right).regions S₂) (hVL : VLabel J S₂ G L) : Valid J S₂ G L :=
  ⟨fun V hV hR => by
    rcases label_of_vlabel J hP hS₂ hF hG hL hV hVL hR with h | ⟨h, -⟩
    all_goals core_grind, fun _ => Or.inl hVL⟩

/-- **Rule for faced sides** (top chords, shared chords, the start; λ := the region located in
`N₂`): a label is valid. -/
theorem valid_of_rlabel (hP : J.P.Simple) {S₂ : Set (Set Point)}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hS₂f : S₂.Finite) {G L : Set Point}
    (hG : G ∈ (chainModel J.whole).regions (F₂plus J S₂))
    (hL : L ∈ (chainModel J.right).regions S₂) (hR : RLabel J S₂ G L) : Valid J S₂ G L :=
  ⟨fun V hV hR' => by
    rcases label_right3 J hP hS₂ hS₂f hG hV hL hR' hR with h | ⟨h, -⟩
    all_goals core_grind,
    fun hU => absurd hR (hU L)⟩

section
variable (hP : J.P.Simple) {Q : Polygon} {S₂ : Set (Set Point)} (hS₂ : (chainModel J.right).ChordFamily Q S₂) (hF : (chainModel J.whole).ChordFamily Q (F₂plus J S₂))
include hP Q hS₂ hF
/-- **The middle region of a tie leaving the stretch** is valid for every `λ`. -/
theorem valid_of_tieOut {G : Set Point}
    (hG : G ∈ (chainModel J.whole).regions (F₂plus J S₂)) (hT : TieOut J S₂ G) (L : Set Point) :
    Valid J S₂ G L := by
  obtain ⟨e, e', d, pb, pb', tb, tb', ρ, he, he', hne, hd0, hd, hA, hA', hB, hB', hBne, hBne',
    hout, hout', hρ, hS, hS', ht, ht'⟩ := hT
  have hU := tie_unlabelled J hP hS₂ hF he he' hne hd0 hd hA hA' hB hB' hBne hBne' hout hout'
    hρ hG hS hS'
  exact ⟨fun V _ hR => absurd hR (hU V), fun _ => Or.inr ⟨e, e', d, pb, pb', tb, tb', ρ, he, he',
    hne, hd0, hd, hA, hA', hB, hB', hBne, hBne', hout, hout', hρ, hS, hS', ht, ht'⟩⟩

/-- **Detection from a valid state.**  Let the sweep be at a non-cut position of the `C₁` part
facing `G` with a valid label `λ`.  Then:
* if `G` has a label, every fused chord `h ⊆ c'` attached at a stretch position (not the base or
  the split vertex) with `G` on its side has `c'` touching `λ` (so `h` is a candidate);
* if `G` has no label, either the bracket conclusion holds with `λ` (the next stretch-anchored
  cut is made by a chord of a chord of `S₂` touching `λ`, or at the shared vertex), or `G` is the
  middle of a tie leaving the stretch (the next stretch-anchored cut is made by one of its two
  chords, a top chord in the case of the top of `C₂`). -/
theorem detect_valid {G L : Set Point}
    (hG : G ∈ (chainModel J.whole).regions (F₂plus J S₂))
    (hL : L ∈ (chainModel J.right).regions S₂) (hvalid : Valid J S₂ G L)
    {p₀ : ℕ} {t₀ : ℝ} (hp₀ : p₀ < (chainModel J.whole).W.n) (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1)
    (hnc₀ : ¬ (chainModel J.whole).IsCut (F₂plus J S₂) (p₀ + t₀))
    (hfG₀ : (chainModel J.whole).Faces p₀ t₀ G)
    (ho₀ : ((rL1 J + rL2 J : ℕ) : ℝ) <
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (p₀ + t₀)) :
    ((∃ V₀ ∈ (chainModel J.right).regions S₂, RLabel J S₂ G V₀) →
      ∀ (h c' V' : Set Point) (ρ' : ℝ) (d : ℕ) (t : ℝ), (ρ' = 1 ∨ ρ' = -1) →
        h ∈ F₂plus J S₂ → c' ∈ S₂ → h ⊆ c' → d < rL1 J + rL2 J → 0 ≤ t → t < 1 →
        (t = 0 → d ≠ 0 ∧ d ≠ rL1 J) →
        SideAttach (chainModel J.whole).W h
          ((6 + tpos J.whole J.m₁ + d) % (chainModel J.whole).W.n) t →
        SideOf (chainModel J.whole) ρ' h G → V' ∈ (chainModel J.right).regions S₂ →
        SideOf (chainModel J.right) ρ' c' V' →
        LabS J S₂ L V' ∧ Chazelle.Chain.TouchesIn (chainModel J.right).D c' V') ∧
    ((∀ V, ¬ RLabel J S₂ G V) →
      (∃ ρ : ℝ, (ρ = 1 ∨ ρ = -1) ∧ BracketConcl2 J S₂ ρ L
        (off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (p₀ + t₀))) ∨
      TieOut J S₂ G) := by
  refine ⟨fun ⟨V₀, hV₀, hR⟩ h c' V' ρ' d t hρ' hh hc' hhc hd ht0 ht1 hsec hhA hGs hV' hVs => ?_,
    fun hU => ?_⟩
  · have h1 := hvalid.1 V₀ hV₀ hR
    have h2 := label_side_gen2 J hP hS₂ hF hd ht0 ht1 hsec hh hc' hhc hhA hρ' hG
      hV' hV₀ hGs hVs hR
    exact ⟨labS_trans J h1 h2, touches_of_sideOf J hS₂.2.1 hc' hVs⟩
  · rcases hvalid.2 hU with h1 | h1
    · exact Or.inl (detect_unlabelled J hP hS₂ hF hG hL hU h1 hp₀ ht₀ hnc₀ hfG₀ ho₀)
    simp_all

/-! ## Item (b): the partner at a tie of a shared-vertex chord -/


end

/-- **The kinds of chords of `F₂⁺`**: contained in a chord of `S₂`, horizontal through the shared
vertex (the shared chords), or horizontal through the top of `C₂` (the top chords). -/
theorem F₂plus_cases {S₂ : Set (Set Point)} (hS₂ : S₂ ⊆ Merge.augChords J.right) {e : Set Point}
    (he : e ∈ F₂plus J S₂) :
    (∃ c ∈ S₂, e ⊆ c) ∨ (J.shared ∈ e ∧ ∀ z ∈ e, z.2 = J.shared.2) ∨
      (J.right.top ∈ e ∧ ∀ z ∈ e, z.2 = J.right.top.2) := by
  have hvert : ∀ (k : ℕ) (σ : ℝ), J.whole.vertex k ∈ J.whole.chordSet k σ ∧
      ∀ z ∈ J.whole.chordSet k σ, z.2 = (J.whole.vertex k).2 := by
    intro k σ
    refine ⟨Geometry.left_mem_segment _ _, fun z hz => ?_⟩
    rw [Chain.chordSet_eq_hseg] at hz
    exact hz.1
  rcases he with he | ⟨σ, -, -, rfl⟩
  · rcases J.fusion_subset_image ∅ S₂ he with (⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩) | hsh
    · rw [empty_union] at hc
      left
      refine ⟨c, hc, ?_⟩
      obtain ⟨y, a, b, hH, -, hcdef, hl, hr⟩ := Merge.augChords_spec (hS₂ hc)
      obtain ⟨-, -, -, hrd⟩ := J.ends_right (hS₂ hc)
      show Merge.shoot J.whole (Merge.lend c) 1 ⊆ c
      rw [hl, hcdef]
      rw [hr] at hrd
      exact Merge.shoot_subset_pos J.whole hH.lt hrd
    · rw [empty_union] at hc
      left
      refine ⟨c, hc, ?_⟩
      obtain ⟨y, a, b, hH, -, hcdef, hl, hr⟩ := Merge.augChords_spec (hS₂ hc)
      obtain ⟨-, hld, -, -⟩ := J.ends_right (hS₂ hc)
      show Merge.shoot J.whole (Merge.rend c) (-1) ⊆ c
      rw [hr, hcdef]
      rw [hl] at hld
      exact Merge.shoot_subset_neg J.whole hH.lt hld
    · obtain ⟨σ, -, -, rfl⟩ := hsh
      right; left
      obtain ⟨h1, h2⟩ := hvert J.m₁ σ
      have hv : J.whole.vertex J.m₁ = J.shared := rfl
      grind
  · right; right
    obtain ⟨h1, h2⟩ := hvert (J.m₁ + J.right.topIdx) σ
    have hv : J.whole.vertex (J.m₁ + J.right.topIdx) = J.right.top := by
      rw [Merge.Junction.whole_vertex_add]; rfl
    grind

end Inv

end Sweep

end

end Chazelle.Core
