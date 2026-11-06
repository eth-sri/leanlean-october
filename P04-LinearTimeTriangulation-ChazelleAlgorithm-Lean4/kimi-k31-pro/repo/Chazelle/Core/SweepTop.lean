module

public import Chazelle.Core.SweepBracketT
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.SimpTactics

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

/-- **`RLabel` from the positions just before a vertex position of the stretch** (offset
`1 ≤ d ≤ rL1 + rL2`): the corresponding positions of the walk of `C₂` are those just before the
position following the counterpart of `d - 1`.  This covers the split vertex (`d = rL1`, case G)
and the end of the stretch (`d = rL1 + rL2`). -/
theorem rlabel_before0 (hP : J.P.Simple) {S₂ : Set (Set Point)}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hS₂f : S₂.Finite) {d : ℕ} (hd1 : 1 ≤ d)
    (hd : d ≤ rL1 J + rL2 J) {G V : Set Point}
    (hW : BeforeFaces (chainModel J.whole)
      ((6 + tpos J.whole J.m₁ + d) % (chainModel J.whole).W.n) 0 G)
    (hW₂ : BeforeFaces (chainModel J.right)
      ((6 + tpos J.right 0 + (dq (rL1 J) (rδ J) (d - 1) + 1)) % (chainModel J.right).W.n) 0 V) :
    RLabel J S₂ G V := by
  have hC := corr_right0 J hP hS₂ hS₂f
  obtain ⟨δ, hδ, -, h1b⟩ := hW
  obtain ⟨δ₂, hδ₂, -, h2b⟩ := hW₂
  have hn0  := hC.n_pos
  have hn₂  := hC.n₂_pos
  set P := (6 + tpos J.whole J.m₁ + d) % (chainModel J.whole).W.n with hPdef
  set P' := (P + (chainModel J.whole).W.n - 1) % (chainModel J.whole).W.n with hP'def
  have hPm : (6 + tpos J.whole J.m₁ + (d - 1)) % (chainModel J.whole).W.n = P' := by
    rw [hP'def, hPdef, mod_pred_mod hn0 _ hd1]
  have hPm₂ : (6 + tpos J.right 0 + dq (rL1 J) (rδ J) (d - 1)) % (chainModel J.right).W.n =
      ((6 + tpos J.right 0 + (dq (rL1 J) (rδ J) (d - 1) + 1)) % (chainModel J.right).W.n +
        (chainModel J.right).W.n - 1) % (chainModel J.right).W.n := by
    rw [mod_pred_mod hn₂ _ (by omega)]
    rfl
  obtain ⟨s, hnc, hs⟩ := ((eventually_not_cut_before hC.hM hC.hF hC.hfin
    (((P' : ℕ) : ℝ) + 1)).and
    (Ioo_mem_nhdsGT (show (0 : ℝ) < min (min δ δ₂) 1 from
      lt_min (lt_min hδ hδ₂) one_pos))).exists
  have hs1 : s < δ := lt_of_lt_of_le hs.2 ((min_le_left _ _).trans (min_le_left _ _))
  have hs2 : s < δ₂ := lt_of_lt_of_le hs.2 ((min_le_left _ _).trans (min_le_right _ _))
  have hs3 : s < 1 := lt_of_lt_of_le hs.2 (min_le_right _ _)
  refine ⟨d - 1, by omega, 1 - s, ⟨by linarith, by linarith [hs.1]⟩, ?_, ?_, ?_⟩
  · rwx [hPm, show ((P' : ℕ) : ℝ) + (1 - s) = ((P' : ℕ) : ℝ) + 1 - s by ring]
  · rw [hPm]; exact h1b rfl s hs.1 hs1
  · rw [hPm₂]; exact h2b rfl s hs.1 hs2

/-- **The label of a faced side.**  If the region `G` is the faced side `ρ` of a chord going in
direction `dir` at a position of the right stretch, its label is the region of `S₂` faced on the
same side of the corresponding position of the walk of `C₂` (just after it if `ρ · dir = -1`,
just before it if `ρ · dir = 1`; at a vertex position, just before the position following the
counterpart of the predecessor). -/
theorem rlabel_of_faced (hP : J.P.Simple) {S₂ : Set (Set Point)}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hS₂f : S₂.Finite) {d : ℕ}
    (hd : d < rL1 J + rL2 J) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) {ρ dir : ℝ} {G : Set Point}
    (hfac : FacedSide (chainModel J.whole)
      ((6 + tpos J.whole J.m₁ + d) % (chainModel J.whole).W.n) t ρ dir G) :
    (ρ * dir = -1 → ∀ V, AfterFaces (chainModel J.right)
      ((6 + tpos J.right 0 + dq (rL1 J) (rδ J) d) % (chainModel J.right).W.n) t V →
        RLabel J S₂ G V) ∧
    (ρ * dir = 1 → ∀ V,
      (0 < t → BeforeFaces (chainModel J.right)
        ((6 + tpos J.right 0 + dq (rL1 J) (rδ J) d) % (chainModel J.right).W.n) t V →
          RLabel J S₂ G V) ∧
      (t = 0 → 1 ≤ d → BeforeFaces (chainModel J.right)
        ((6 + tpos J.right 0 + (dq (rL1 J) (rδ J) (d - 1) + 1)) % (chainModel J.right).W.n) 0 V →
          RLabel J S₂ G V)) := by
  refine ⟨fun h V hV => rlabel_after J hP hS₂ hS₂f hd ht0 ht1 (hfac.1 h) hV,
    fun h V => ⟨fun htp hV => ?_, fun ht hd1 hV => ?_⟩⟩
  · exact rlabel_before J hP hS₂ hS₂f hd ht0 ht1 (fun h0 => absurd h0 htp.ne') (hfac.2 h) hV
  · subst ht
    exact rlabel_before0 J hP hS₂ hS₂f hd1 hd.le (hfac.2 h) hV

/-- **The middle region of a tie leaving the stretch has no label.**  Let two distinct chords of
`F₂⁺` be attached at a vertex position inside the right stretch (not its base), with far
attachments off the stretch, and let `G` be on the same side `ρ` of both.  Then `G` has no
label. -/
theorem tie_unlabelled (hP : J.P.Simple) {Q : Polygon}
    {S₂ : Set (Set Point)} (hS₂ : (chainModel J.right).ChordFamily Q S₂)
    (_hF : (chainModel J.whole).ChordFamily Q (F₂plus J S₂)) {e e' : Set Point}
    (he : e ∈ F₂plus J S₂) (he' : e' ∈ F₂plus J S₂) (hne : e' ≠ e) {d : ℕ}
    (hd0 : d ≠ 0) (hd : d < rL1 J + rL2 J)
    (heA : SideAttach (chainModel J.whole).W e
      ((6 + tpos J.whole J.m₁ + d) % (chainModel J.whole).W.n) 0)
    (heA' : SideAttach (chainModel J.whole).W e'
      ((6 + tpos J.whole J.m₁ + d) % (chainModel J.whole).W.n) 0)
    {pb pb' : ℕ} {tb tb' : ℝ} (hB : SideAttach (chainModel J.whole).W e pb tb)
    (hB' : SideAttach (chainModel J.whole).W e' pb' tb')
    (hBne : sidePt (chainModel J.whole).W pb tb ≠ sidePt (chainModel J.whole).W
      ((6 + tpos J.whole J.m₁ + d) % (chainModel J.whole).W.n) 0)
    (hBne' : sidePt (chainModel J.whole).W pb' tb' ≠ sidePt (chainModel J.whole).W
      ((6 + tpos J.whole J.m₁ + d) % (chainModel J.whole).W.n) 0)
    (hout : ¬ (0 < off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pb + tb) ∧
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pb + tb) <
        ((rL1 J + rL2 J : ℕ) : ℝ)))
    (hout' : ¬ (0 < off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pb' + tb') ∧
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pb' + tb') <
        ((rL1 J + rL2 J : ℕ) : ℝ)))
    {ρ : ℝ} (hρ : ρ = 1 ∨ ρ = -1) {G : Set Point}
    (hG : G ∈ (chainModel J.whole).regions (F₂plus J S₂))
    (hS : SideOf (chainModel J.whole) ρ e G) (hS' : SideOf (chainModel J.whole) ρ e' G) :
    ∀ V, ¬ RLabel J S₂ G V := by
  rintro V ⟨d'', hd'', t'', ht'', hnc, hfG, -⟩
  have hC := corr_right0 J hP hS₂.2.1 hS₂.1
  have hM := hC.hM
  have hFs  := hC.hF
  set W := (chainModel J.whole).W with hWdef
  set g := 6 + tpos J.whole J.m₁ with hgdef
  set A := (g + d) % W.n with hAdef
  have hg0 : (0 : ℝ) ≤ (g : ℝ) := Nat.cast_nonneg _
  have hgn : (g : ℝ) < W.n := by exact_mod_cast hC.hg
  obtain ⟨-, hy, -⟩ := hM.attach_seg (hFs he) heA hB (Ne.symm hBne)
  obtain ⟨-, hy', -⟩ := hM.attach_seg (hFs he') heA' hB' (Ne.symm hBne')
  have h1 : (sidePt W pb tb).1 ≠ (sidePt W A 0).1 :=
    fun h => hBne (Geometry.point_ext h hy.symm)
  have h1' : (sidePt W pb' tb').1 ≠ (sidePt W A 0).1 :=
    fun h => hBne' (Geometry.point_ext h hy'.symm)
  have hopp := tie_opposite hM hFs he he' hne heA heA' hB.2.2.2.1 hB'.2.2.2.1 h1 h1'
  obtain ⟨θ, hθ, hori⟩ := exists_sign hρ (sub_ne_zero.2 (Ne.symm h1))
  have hθρ : θ * ρ * (θ * ρ) = 1 := by
    rcases hθ with rfl | rfl <;> rcases hρ with rfl | rfl <;> norm_num
  have hori' : 0 < -θ * ρ * ((sidePt W A 0).1 - (sidePt W pb' tb').1) := by
    have e1 : -θ * ρ * ((sidePt W A 0).1 - (sidePt W pb' tb').1) =
        θ * ρ * ((sidePt W pb' tb').1 - (sidePt W A 0).1) := by ring
    rw [e1]
    have hprod : 0 < (θ * ρ * ((sidePt W A 0).1 - (sidePt W pb tb).1)) *
        (θ * ρ * ((sidePt W pb' tb').1 - (sidePt W A 0).1)) := by
      have e2 : (θ * ρ * ((sidePt W A 0).1 - (sidePt W pb tb).1)) *
          (θ * ρ * ((sidePt W pb' tb').1 - (sidePt W A 0).1)) =
          (θ * ρ * (θ * ρ)) * (-(((sidePt W pb tb).1 - (sidePt W A 0).1) *
            ((sidePt W pb' tb').1 - (sidePt W A 0).1))) := by ring
      rw [e2, hθρ, one_mul]
      linarith
    exact pos_of_mul_pos_right hprod hori.le
  have hθ' : -θ = 1 ∨ -θ = -1 := by rcases hθ with rfl | rfl <;> norm_num
  have hoA := hC.off_M hd (t := 0) le_rfl zero_lt_one
  have hA0 : 0 < off W.n (g : ℝ) ((A : ℝ) + 0) := by
    rw [hoA]
    have : (1 : ℝ) ≤ d := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hd0
    linarith
  have hAL : off W.n (g : ℝ) ((A : ℝ) + 0) < ((rL1 J + rL2 J : ℕ) : ℝ) := by
    rw [hoA]
    have : (d : ℝ) + 1 ≤ ((rL1 J + rL2 J : ℕ) : ℝ) := by exact_mod_cast hd
    linarith
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
  have ho := hC.off_M hd'' ht''.1.le ht''.2
  have hpos : 0 < off W.n (g : ℝ) ((((g + d'') % W.n : ℕ) : ℝ) + t'') := by
    rw [ho]; have : (0 : ℝ) ≤ d'' := Nat.cast_nonneg _; linarith [ht''.1]
  have hlt : off W.n (g : ℝ) ((((g + d'') % W.n : ℕ) : ℝ) + t'') <
      ((rL1 J + rL2 J : ℕ) : ℝ) := by
    rw [ho]; have : (d'' : ℝ) + 1 ≤ ((rL1 J + rL2 J : ℕ) : ℝ) := by exact_mod_cast hd''
    linarith [ht''.2]
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
    SideAttach (chainModel J.whole).W e
      ((6 + tpos J.whole J.m₁ + d) % (chainModel J.whole).W.n) t ∧
    SideOf (chainModel J.whole) ρ e G ∧ SideOf (chainModel J.right) ρ c V

/-- **A virtual label is the label** whenever the region has one (lemma (E)). -/
theorem label_of_vlabel (hP : J.P.Simple) {Q : Polygon}
    {S₂ : Set (Set Point)} (hS₂ : (chainModel J.right).ChordFamily Q S₂)
    (hF : (chainModel J.whole).ChordFamily Q (F₂plus J S₂)) {G V V' : Set Point}
    (hG : G ∈ (chainModel J.whole).regions (F₂plus J S₂))
    (hV : V ∈ (chainModel J.right).regions S₂) (hV' : V' ∈ (chainModel J.right).regions S₂)
    (hVL : VLabel J S₂ G V) (hL : RLabel J S₂ G V') :
    V' = V ∨ (GapLab J S₂ V' ∧ GapLab J S₂ V) := by
  obtain ⟨e, c, ρ, d, t, he, hc, hec, hρ, hd, ht0, ht1, hsec, heA, hGs, hVs⟩ := hVL
  exact label_side_gen2 J hP hS₂ hF hd ht0 ht1 hsec he hc hec heA hρ hG hV hV' hGs hVs hL

/-- A region on a side of a chord of `S₂` touches it: the chord is an exit chord of the
region. -/
theorem touches_of_sideOf {S₂ : Set (Set Point)} (hS₂ : S₂ ⊆ Merge.augChords J.right)
    {c V : Set Point} (hc : c ∈ S₂) {ρ : ℝ} (hVs : SideOf (chainModel J.right) ρ c V) :
    Chazelle.Chain.TouchesIn (chainModel J.right).D c V := by
  obtain ⟨y, a, b, hH, -, hcdef, -, -⟩ := Merge.augChords_spec (hS₂ hc)
  have hab := hH.lt
  have hz : (((a + b) / 2, y) : Point) ∈ c := by
    rw [hcdef]; exact ⟨rfl, by sil only, by sil only⟩
  have hzD : (((a + b) / 2, y) : Point) ∈ (chainModel J.right).D :=
    hH.open_mem _ (by linarith) (by linarith)
  exact touches_of_side hz hzD (hVs _ hz hzD)

/-- **Detection in an unlabelled region** (the bracket lemma in terms of virtual labels): for a
region without a label with a virtual label `V`, and a non-cut position of the `C₁` part facing
it, the next chord of `F₂⁺` with an attachment inside the right stretch is a chord in a chord of
`S₂` with `V` on the side of the region, or ends at the shared vertex. -/
theorem detect_unlabelled (hP : J.P.Simple) {Q : Polygon}
    {S₂ : Set (Set Point)} (hS₂ : (chainModel J.right).ChordFamily Q S₂)
    (hF : (chainModel J.whole).ChordFamily Q (F₂plus J S₂)) {G V : Set Point}
    (hG : G ∈ (chainModel J.whole).regions (F₂plus J S₂))
    (hV : V ∈ (chainModel J.right).regions S₂) (hU : ∀ V', ¬ RLabel J S₂ G V')
    (hVL : VLabel J S₂ G V) {p₀ : ℕ} {t₀ : ℝ} (hp₀ : p₀ < (chainModel J.whole).W.n)
    (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) (hnc₀ : ¬ (chainModel J.whole).IsCut (F₂plus J S₂) (p₀ + t₀))
    (hfG₀ : (chainModel J.whole).Faces p₀ t₀ G)
    (ho₀ : ((rL1 J + rL2 J : ℕ) : ℝ) <
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (p₀ + t₀)) :
    ∃ ρ : ℝ, (ρ = 1 ∨ ρ = -1) ∧ BracketConcl2 J S₂ ρ V
      (off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (p₀ + t₀)) := by
  obtain ⟨e, c, ρ, d, t, he, hc, hec, hρ, hd, ht0, ht1, hsec, heA, hGs, hVs⟩ := hVL
  exact ⟨ρ, hρ, bracket2 J hP hS₂ hF hρ hG hV hU he hc hec hd ht0 ht1 hsec heA hGs hVs hp₀ ht₀
    hnc₀ hfG₀ ho₀⟩

/-- **The bracket of a tie leaving the stretch** (the two top chords at the split vertex in
case G): for a tie at a position inside the right stretch whose two chords have their far
attachments off the stretch, with `G` on the same side of both (`fb` oriented by `-1`, `ff` by
`1`), and a non-cut position of the `C₁` part facing `G`: the far attachment of `ff` is after
that position (or at offset `0`), and no chord of `F₂⁺` with an attachment inside the stretch
(not at offset `0`) is attached between them. -/
theorem bracket_tie (hP : J.P.Simple) {Q : Polygon}
    {S₂ : Set (Set Point)} (hS₂ : (chainModel J.right).ChordFamily Q S₂)
    (hF : (chainModel J.whole).ChordFamily Q (F₂plus J S₂)) {ρ : ℝ} (hρ : ρ = 1 ∨ ρ = -1)
    {G : Set Point} (hG : G ∈ (chainModel J.whole).regions (F₂plus J S₂))
    {fb ff : Set Point} (hfb : fb ∈ F₂plus J S₂) (hff : ff ∈ F₂plus J S₂) (hbf : fb ≠ ff)
    {pa : ℕ}
    (hAL : off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pa + 0) <
      ((rL1 J + rL2 J : ℕ) : ℝ))
    (hbA : SideAttach (chainModel J.whole).W fb pa 0)
    (hfA : SideAttach (chainModel J.whole).W ff pa 0) {pbb pff : ℕ} {tbb tff : ℝ}
    (hbB : SideAttach (chainModel J.whole).W fb pbb tbb)
    (hfF : SideAttach (chainModel J.whole).W ff pff tff)
    (hbne : sidePt (chainModel J.whole).W pa 0 ≠ sidePt (chainModel J.whole).W pbb tbb)
    (hfne : sidePt (chainModel J.whole).W pa 0 ≠ sidePt (chainModel J.whole).W pff tff)
    (hbS : SideOf (chainModel J.whole) ρ fb G) (hfS : SideOf (chainModel J.whole) ρ ff G)
    (hbo : 0 < -1 * ρ * ((sidePt (chainModel J.whole).W pa 0).1 -
      (sidePt (chainModel J.whole).W pbb tbb).1))
    (hfo : 0 < 1 * ρ * ((sidePt (chainModel J.whole).W pa 0).1 -
      (sidePt (chainModel J.whole).W pff tff).1))
    (hbout : ¬ (0 < off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pbb + tbb) ∧
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pbb + tbb) <
        ((rL1 J + rL2 J : ℕ) : ℝ)))
    (hfout : ¬ (0 < off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pff + tff) ∧
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pff + tff) <
        ((rL1 J + rL2 J : ℕ) : ℝ)))
    {p₀ : ℕ} {t₀ : ℝ} (hp₀ : p₀ < (chainModel J.whole).W.n) (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1)
    (hnc₀ : ¬ (chainModel J.whole).IsCut (F₂plus J S₂) (p₀ + t₀))
    (hfG₀ : (chainModel J.whole).Faces p₀ t₀ G)
    (ho₀ : ((rL1 J + rL2 J : ℕ) : ℝ) <
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (p₀ + t₀)) :
    (off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pff + tff) = 0 ∨
      (((rL1 J + rL2 J : ℕ) : ℝ) ≤
          off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pff + tff) ∧
        off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (p₀ + t₀) <
          off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pff + tff))) ∧
    ∀ e ∈ F₂plus J S₂, ∀ (pw : ℕ) (tw : ℝ) (pb : ℕ) (tb : ℝ),
      SideAttach (chainModel J.whole).W e pw tw → SideAttach (chainModel J.whole).W e pb tb →
      sidePt (chainModel J.whole).W pw tw ≠ sidePt (chainModel J.whole).W pb tb →
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (p₀ + t₀) <
        off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pw + tw) →
      (off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pff + tff) = 0 ∨
        off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pw + tw) <
          off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pff + tff)) →
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pb + tb) <
        ((rL1 J + rL2 J : ℕ) : ℝ) →
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pb + tb) ≠ 0 → False := by
  have hC := corr_right0 J hP hS₂.2.1 hS₂.1
  have hM := hC.hM
  have hFs  := hC.hF
  have hg0 : (0 : ℝ) ≤ ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) := Nat.cast_nonneg _
  have hgn : ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) < (chainModel J.whole).W.n := by
    exact_mod_cast hC.hg
  set o := off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) with hodef
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
  · have hB0' : 0 < o (pb + tb) := lt_of_le_of_ne (off_nonneg kB0 hgn) (Ne.symm hB0)
    have := no_cross_off hM hFs hF.1 hff he (Ne.symm hef) hfF hfA (Ne.symm hfne) hB hW hg0 hgn
      (by rwli [hz]) (by rwx [hz]) hBA
    linarith [this.2]
  · rcases hoZ with h | h
    · linarith
    · have := no_cross_off hM hFs hF.1 hff he (Ne.symm hef) hfA hfF hfne hW hB hg0 hgn
        (by linarith) (by linarith) h
      linarith [this.1]

/-! ## Transparent brackets -/

end Top

end Sweep

end

end Chazelle.Core
