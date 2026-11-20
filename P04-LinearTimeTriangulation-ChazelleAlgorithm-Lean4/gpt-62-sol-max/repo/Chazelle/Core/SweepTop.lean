module

public import Chazelle.Core.SweepBracketT

/-!
# The sweep (WP-D), part 10: labels from faced sides (top chords, shared chords, the start)

The label rule for chords of `F₂⁺` that are not contained in a chord of `S₂` (the top chords at
the top of `C₂`, the shared chords at the shared vertex) and the initial label of the sweep are
read off the walk of `C₂` directly: if the region `G` of `F₂⁺` is faced just after (before) a
position of the right stretch, its label is the region of `S₂` faced just after (before) the
corresponding position of the walk of `C₂` (`rlabel_after`, `rlabel_before0`).  Which side of a
chord is faced near its attachment is `faced_or_middle`; the middle region of a tie whose two
chords leave the right stretch has no label (`tie_unlabelled`).

* `rlabel_before0`: `RLabel` from the positions just before a vertex position of the stretch,
  including the split vertex and the end of the stretch (read in the walk of `C₂` just before
  the position following the predecessor).
* `rlabel_of_faced`, `label_faced`, `label_faced_tie`: the label of the faced side of a chord.
* `tie_unlabelled`: the middle region of a tie with both far attachments off the stretch.
-/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sideInArc sidePt sideLeft sideKey_inj)
open Chazelle.Jordan (offset)
open Chazelle.Geometry (lerp)
open WalkEmbed

namespace Sweep

section Top

variable (J : Merge.Junction)

/-- **The label of a faced side.**  If the region `G` is the faced side `ρ` of a chord going in
direction `dir` at a position of the right stretch, its label is the region of `S₂` faced on the
same side of the corresponding position of the walk of `C₂` (just after it if `ρ · dir = -1`,
just before it if `ρ · dir = 1`; at a vertex position, just before the position following the
counterpart of the predecessor). -/
theorem rlabel_of_faced (hP : J.P.Simple) {S₂ : Set (Set Point)}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hS₂f : S₂.Finite) {d : ℕ}
    (hd : d < rL1 J + rL2 J) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) {ρ dir : ℝ} {G : Set Point}
    (hfac : FacedSide J.wholeModel
      ((6 + tpos J.whole J.m₁ + d) % J.wholeModel.W.n) t ρ dir G) :
    (ρ * dir = -1 → ∀ V, AfterFaces J.rightModel
      ((6 + tpos J.right 0 + dq (rL1 J) (rδ J) d) % J.rightModel.W.n) t V →
        RLabel J S₂ G V) ∧
    (ρ * dir = 1 → ∀ V,
      (0 < t → BeforeFaces J.rightModel
        ((6 + tpos J.right 0 + dq (rL1 J) (rδ J) d) % J.rightModel.W.n) t V →
          RLabel J S₂ G V) ∧
      (t = 0 → 1 ≤ d → BeforeFaces J.rightModel
        ((6 + tpos J.right 0 + (dq (rL1 J) (rδ J) (d - 1) + 1)) % J.rightModel.W.n) 0 V →
          RLabel J S₂ G V)) := by
  refine ⟨fun h V hV => rlabel_after J hP hS₂ hS₂f hd ht0 ht1 (hfac.1 h) hV,
    fun h V => ⟨fun htp hV => ?_, fun ht hd1 hV => ?_⟩⟩
  · exact rlabel_before J hP hS₂ hS₂f hd ht0 ht1 (fun h0 => absurd h0 htp.ne') (hfac.2 h) hV
  · subst ht
    exact rlabel_before0 J hP hS₂ hS₂f hd1 hd.le (hfac.2 h) hV

section

variable (hP : J.P.Simple) {Q : Polygon}
    {S₂ : Set (Set Point)} (hS₂ : J.rightModel.ChordFamily Q S₂)

include hP hS₂ in
/-- **The middle region of a tie leaving the stretch has no label.**  Let two distinct chords of
`F₂⁺` be attached at a vertex position inside the right stretch (not its base), with far
attachments off the stretch, and let `G` be on the same side `ρ` of both.  Then `G` has no
label. -/
theorem tie_unlabelled
    (_hF : J.wholeModel.ChordFamily Q (F₂plus J S₂)) {e e' : Set Point}
    (he : e ∈ F₂plus J S₂) (he' : e' ∈ F₂plus J S₂) (hne : e' ≠ e) {d : ℕ}
    (hd0 : d ≠ 0) (hd : d < rL1 J + rL2 J)
    (heA : SideAttach J.wholeModel.W e
      ((6 + tpos J.whole J.m₁ + d) % J.wholeModel.W.n) 0)
    (heA' : SideAttach J.wholeModel.W e'
      ((6 + tpos J.whole J.m₁ + d) % J.wholeModel.W.n) 0)
    {pb pb' : ℕ} {tb tb' : ℝ} (hB : SideAttach J.wholeModel.W e pb tb)
    (hB' : SideAttach J.wholeModel.W e' pb' tb')
    (hBne : sidePt J.wholeModel.W pb tb ≠ sidePt J.wholeModel.W
      ((6 + tpos J.whole J.m₁ + d) % J.wholeModel.W.n) 0)
    (hBne' : sidePt J.wholeModel.W pb' tb' ≠ sidePt J.wholeModel.W
      ((6 + tpos J.whole J.m₁ + d) % J.wholeModel.W.n) 0)
    (hout : ¬ (0 < off J.wholeModel.W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pb + tb) ∧
      off J.wholeModel.W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pb + tb) <
        ((rL1 J + rL2 J : ℕ) : ℝ)))
    (hout' : ¬ (0 < off J.wholeModel.W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pb' + tb') ∧
      off J.wholeModel.W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pb' + tb') <
        ((rL1 J + rL2 J : ℕ) : ℝ)))
    {ρ : ℝ} (hρ : ρ = 1 ∨ ρ = -1) {G : Set Point}
    (hG : G ∈ J.wholeModel.regions (F₂plus J S₂))
    (hS : SideOf J.wholeModel ρ e G) (hS' : SideOf J.wholeModel ρ e' G) :
    ∀ V, ¬ RLabel J S₂ G V := by
  rintro V ⟨d'', hd'', t'', ht'', hnc, hfG, -⟩
  have hC := corr_right0 J hP hS₂.2.1 hS₂.1
  have hM := hC.hM
  have hFs := hC.hF
  set W := J.wholeModel.W with hWdef
  set g := 6 + tpos J.whole J.m₁ with hgdef
  set A := (g + d) % W.n with hAdef
  have hg0 : (0 : ℝ) ≤ (g : ℝ) := Nat.cast_nonneg _
  have hgn : (g : ℝ) < W.n := by exact_mod_cast hC.hg
  obtain ⟨θ, hθ, hori, hori'⟩ := tie_signs hρ (tie_opposite hM hFs he he' hne heA heA' hB hB' hBne hBne')
  have hθ' : -θ = 1 ∨ -θ = -1 := by rcases hθ with rfl | rfl <;> norm_num
  have hA0 := hC.off_M_pos hd le_rfl zero_lt_one fun _ => hd0
  have hAL := hC.off_M_lt hd le_rfl zero_lt_one
  have hpre : ∀ {q : ℕ} {s : ℝ}, ¬ (0 < off W.n (g : ℝ) (q + s) ∧
      off W.n (g : ℝ) (q + s) < ((rL1 J + rL2 J : ℕ) : ℝ)) →
      ((rL1 J + rL2 J : ℕ) : ℝ) ≤ off W.n (g : ℝ) (q + s) ∨ off W.n (g : ℝ) (q + s) ≤ 0 := by
    intro q s h
    by_contra hc
    push Not at hc
    exact h ⟨hc.2, hc.1⟩
  have hb1 := chord_bound hM hFs he heA hB (Ne.symm hBne) hρ hG hS hθ hori hg0 hgn hA0 hAL
    (fun _ _ _ _ _ _ _ _ => Or.inr (hpre hout))
  have hb2 := chord_bound hM hFs he' heA' hB' (Ne.symm hBne') hρ hG hS' hθ' hori' hg0 hgn hA0
    hAL (fun _ _ _ _ _ _ _ _ => Or.inr (hpre hout'))
  have hpos := hC.off_M_pos hd'' ht''.1.le ht''.2 fun h => (ht''.1.ne' h).elim
  have hlt := hC.off_M_lt hd'' ht''.1.le ht''.2
  have x1 := hb1 _ t'' (Nat.mod_lt _ hC.n_pos) ht'' hnc hfG hpos hlt
  have x2 := hb2 _ t'' (Nat.mod_lt _ hC.n_pos) ht'' hnc hfG hpos hlt
  linarith

/-! ## The start of the sweep -/

/-! ## Detection -/

/-- **A virtual label** of a region `G` of `F₂⁺`: a region `V` of `S₂` on the side `ρ` of a chord
`c ∈ S₂` containing a chord of `F₂⁺` attached at a position of the right stretch (not the base or
the split vertex) with `G` on its side `ρ`.  This is what the sweep's label is after an event on
such a chord. -/
def VLabel (S₂ : Set (Set Point)) (G V : Set Point) : Prop :=
  ∃ (e c : Set Point) (ρ : ℝ) (d : ℕ) (t : ℝ), e ∈ F₂plus J S₂ ∧ c ∈ S₂ ∧ e ⊆ c ∧
    (ρ = 1 ∨ ρ = -1) ∧ d < rL1 J + rL2 J ∧ 0 ≤ t ∧ t < 1 ∧ (t = 0 → d ≠ 0 ∧ d ≠ rL1 J) ∧
    SideAttach J.wholeModel.W e
      ((6 + tpos J.whole J.m₁ + d) % J.wholeModel.W.n) t ∧
    SideOf J.wholeModel ρ e G ∧ SideOf J.rightModel ρ c V

include hP hS₂ in
/-- **A virtual label is the label** whenever the region has one (lemma (E)). -/
theorem label_of_vlabel
    (hF : J.wholeModel.ChordFamily Q (F₂plus J S₂)) {G V V' : Set Point}
    (hG : G ∈ J.wholeModel.regions (F₂plus J S₂))
    (hV : V ∈ J.rightModel.regions S₂) (hV' : V' ∈ J.rightModel.regions S₂)
    (hVL : VLabel J S₂ G V) (hL : RLabel J S₂ G V') :
    V' = V ∨ (GapLab J S₂ V' ∧ GapLab J S₂ V) := by
  obtain ⟨e, c, ρ, d, t, he, hc, hec, hρ, hd, ht0, ht1, hsec, heA, hGs, hVs⟩ := hVL
  exact label_side_gen2 J hP hS₂ hF hd ht0 ht1 hsec he hc hec heA hρ hG hV hV' hGs hVs hL

/-- A region on a side of a chord of `S₂` touches it: the chord is an exit chord of the
region. -/
theorem touches_of_sideOf {S₂ : Set (Set Point)} (hS₂ : S₂ ⊆ Merge.augChords J.right)
    {c V : Set Point} (hc : c ∈ S₂) {ρ : ℝ} (hVs : SideOf J.rightModel ρ c V) :
    Chazelle.Chain.TouchesIn J.rightModel.D c V := by
  obtain ⟨y, a, b, hH, -, hcdef, -, -⟩ := Merge.augChords_spec (hS₂ hc)
  have hab := hH.lt
  have hz : (((a + b) / 2, y) : Point) ∈ c := by
    rw [hcdef]; exact ⟨rfl, by simp only; linarith, by simp only; linarith⟩
  have hzD : (((a + b) / 2, y) : Point) ∈ J.rightModel.D :=
    hH.open_mem _ (by linarith) (by linarith)
  exact touches_of_side hz hzD (hVs _ hz hzD)

include hP hS₂ in
/-- **Detection in an unlabelled region** (the bracket lemma in terms of virtual labels): for a
region without a label with a virtual label `V`, and a non-cut position of the `C₁` part facing
it, the next chord of `F₂⁺` with an attachment inside the right stretch is a chord in a chord of
`S₂` with `V` on the side of the region, or ends at the shared vertex. -/
theorem detect_unlabelled
    (hF : J.wholeModel.ChordFamily Q (F₂plus J S₂)) {G V : Set Point}
    (hG : G ∈ J.wholeModel.regions (F₂plus J S₂))
    (hV : V ∈ J.rightModel.regions S₂) (hU : ∀ V', ¬ RLabel J S₂ G V')
    (hVL : VLabel J S₂ G V) {p₀ : ℕ} {t₀ : ℝ} (hp₀ : p₀ < J.wholeModel.W.n)
    (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) (hnc₀ : ¬ J.wholeModel.IsCut (F₂plus J S₂) (p₀ + t₀))
    (hfG₀ : J.wholeModel.Faces p₀ t₀ G)
    (ho₀ : ((rL1 J + rL2 J : ℕ) : ℝ) <
      off J.wholeModel.W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (p₀ + t₀)) :
    ∃ ρ : ℝ, (ρ = 1 ∨ ρ = -1) ∧ BracketConcl2 J S₂ ρ V
      (off J.wholeModel.W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (p₀ + t₀)) := by
  obtain ⟨e, c, ρ, d, t, he, hc, hec, hρ, hd, ht0, ht1, hsec, heA, hGs, hVs⟩ := hVL
  exact ⟨ρ, hρ, bracket2 J hP hS₂ hF hρ hG hV hU he hc hec hd ht0 ht1 hsec heA hGs hVs hp₀ ht₀
    hnc₀ hfG₀ ho₀⟩

include hP hS₂ in
/-- **The bracket of a tie leaving the stretch** (the two top chords at the split vertex in
case G): for a tie at a position inside the right stretch whose two chords have their far
attachments off the stretch, with `G` on the same side of both (`fb` oriented by `-1`, `ff` by
`1`), and a non-cut position of the `C₁` part facing `G`: the far attachment of `ff` is after
that position (or at offset `0`), and no chord of `F₂⁺` with an attachment inside the stretch
(not at offset `0`) is attached between them. -/
theorem bracket_tie
    (hF : J.wholeModel.ChordFamily Q (F₂plus J S₂)) {ρ : ℝ} (hρ : ρ = 1 ∨ ρ = -1)
    {G : Set Point} (hG : G ∈ J.wholeModel.regions (F₂plus J S₂))
    {fb ff : Set Point} (hfb : fb ∈ F₂plus J S₂) (hff : ff ∈ F₂plus J S₂) (hbf : fb ≠ ff)
    {pa : ℕ}
    (hAL : off J.wholeModel.W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pa + 0) <
      ((rL1 J + rL2 J : ℕ) : ℝ))
    (hbA : SideAttach J.wholeModel.W fb pa 0)
    (hfA : SideAttach J.wholeModel.W ff pa 0) {pbb pff : ℕ} {tbb tff : ℝ}
    (hbB : SideAttach J.wholeModel.W fb pbb tbb)
    (hfF : SideAttach J.wholeModel.W ff pff tff)
    (hbne : sidePt J.wholeModel.W pa 0 ≠ sidePt J.wholeModel.W pbb tbb)
    (hfne : sidePt J.wholeModel.W pa 0 ≠ sidePt J.wholeModel.W pff tff)
    (hbS : SideOf J.wholeModel ρ fb G) (hfS : SideOf J.wholeModel ρ ff G)
    (hbo : 0 < -1 * ρ * ((sidePt J.wholeModel.W pa 0).1 -
      (sidePt J.wholeModel.W pbb tbb).1))
    (hfo : 0 < 1 * ρ * ((sidePt J.wholeModel.W pa 0).1 -
      (sidePt J.wholeModel.W pff tff).1))
    (hbout : ¬ (0 < off J.wholeModel.W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pbb + tbb) ∧
      off J.wholeModel.W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pbb + tbb) <
        ((rL1 J + rL2 J : ℕ) : ℝ)))
    (hfout : ¬ (0 < off J.wholeModel.W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pff + tff) ∧
      off J.wholeModel.W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pff + tff) <
        ((rL1 J + rL2 J : ℕ) : ℝ)))
    {p₀ : ℕ} {t₀ : ℝ} (hp₀ : p₀ < J.wholeModel.W.n) (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1)
    (hnc₀ : ¬ J.wholeModel.IsCut (F₂plus J S₂) (p₀ + t₀))
    (hfG₀ : J.wholeModel.Faces p₀ t₀ G)
    (ho₀ : ((rL1 J + rL2 J : ℕ) : ℝ) <
      off J.wholeModel.W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (p₀ + t₀)) :
    (off J.wholeModel.W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pff + tff) = 0 ∨
      (((rL1 J + rL2 J : ℕ) : ℝ) ≤
          off J.wholeModel.W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pff + tff) ∧
        off J.wholeModel.W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (p₀ + t₀) <
          off J.wholeModel.W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pff + tff))) ∧
    ∀ e ∈ F₂plus J S₂, ∀ (pw : ℕ) (tw : ℝ) (pb : ℕ) (tb : ℝ),
      SideAttach J.wholeModel.W e pw tw → SideAttach J.wholeModel.W e pb tb →
      sidePt J.wholeModel.W pw tw ≠ sidePt J.wholeModel.W pb tb →
      off J.wholeModel.W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (p₀ + t₀) <
        off J.wholeModel.W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pw + tw) →
      (off J.wholeModel.W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pff + tff) = 0 ∨
        off J.wholeModel.W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pw + tw) <
          off J.wholeModel.W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pff + tff)) →
      off J.wholeModel.W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pb + tb) <
        ((rL1 J + rL2 J : ℕ) : ℝ) →
      off J.wholeModel.W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pb + tb) ≠ 0 → False := by
  have hC := corr_right0 J hP hS₂.2.1 hS₂.1
  have hM := hC.hM
  have hFs := hC.hF
  have hg0 : (0 : ℝ) ≤ ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) := Nat.cast_nonneg _
  have hgn : ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) < J.wholeModel.W.n := by
    exact_mod_cast hC.hg
  set o := off J.wholeModel.W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) with hodef
  obtain ⟨hLb, hbo₀⟩ := back_end J hP hS₂ hρ hG hfb hbA hbB hbne hbS hbo hAL hbout hp₀ ht₀
    hnc₀ hfG₀ ho₀
  have hfe := fwd_end J hP hS₂ hρ hG hff hfA hfF hfne hfS hfo hAL hfout hp₀ ht₀ hnc₀ hfG₀
    ho₀
  refine ⟨hfe, fun e he pw tw pb tb hW hB hWB hoW hoZ hoB hB0 => ?_⟩
  obtain ⟨kA0, kA1⟩ := Corr.key_mem hbA.1 hbA.2.1 hbA.2.2.1
  obtain ⟨kB0, kB1⟩ := Corr.key_mem hB.1 hB.2.1 hB.2.2.1
  have hA0 := off_nonneg kA0 hgn
  have heb : e ≠ fb := by
    rintro rfl
    rcases key_of_two hM (hFs he) hbA hbB hbne hW with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> linarith
  have hef : e ≠ ff := by
    rintro rfl
    rcases key_of_two hM (hFs he) hfA hfF hfne hW with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · linarith
    · rcases hoZ with h | h <;> linarith
  -- non-crossing with `fb`: the stretch attachment of `e` is before the tie
  have hBA : o (pb + tb) < o (pa + 0) := by
    have hle : o (pb + tb) ≤ o (pa + 0) := by
      by_contra hc
      push Not at hc
      have := no_cross_off hM hFs hF.1 hfb he (Ne.symm heb) hbA hbB hbne hB hW hg0 hgn
        (by linarith) hc (by linarith)
      linarith [this.2]
    rcases hle.lt_or_eq with h | h
    · exact h
    · exfalso
      have hk := off_inj hg0 hgn kB0 kB1 kA0 kA1 h
      obtain ⟨rfl, rfl⟩ := sideKey_inj hB.2.1 hB.2.2.1 hbA.2.1 hbA.2.2.1 hk
      rcases tie_third hM hFs hfb hff he hbf hbA hfA hB with h' | h'
      · exact heb h'
      · exact hef h'
  rcases hfe with hz | ⟨hLz, hz⟩
  · have hB0' := lt_of_le_of_ne (off_nonneg kB0 hgn) (Ne.symm hB0)
    have := no_cross_off hM hFs hF.1 hff he (Ne.symm hef) hfF hfA (Ne.symm hfne) hB hW hg0 hgn
      (by rw [hz]; linarith) (by rwa [hz]) hBA
    linarith [this.2]
  · rcases hoZ with h | h
    · linarith
    · have := no_cross_off hM hFs hF.1 hff he (Ne.symm hef) hfA hfF hfne hW hB hg0 hgn
        (by linarith) (by linarith) h
      linarith [this.1]

end

/-! ## Transparent brackets -/

end Top

end Sweep

end

end Chazelle.Core
