module

public import Chazelle.Golf

public import Chazelle.Core.SweepMachine7

/-!
# The sweep (WP-D), part 24: the abstract machine, the next event and its detection

* `StopChord`: the chords the RAM precomputes as stops (design §9.2): the shared chords and the
  chords seen from an endpoint of a chord of `S₂` off `C₂` (a box-wall endpoint).
* `stretch_end`: a chord of `F₂⁺` that is not a stop chord has an attachment on the open right
  stretch.
* `next_event_origin` (**completeness of the detection**): from a valid label `λ` of the region
  faced at a non-cut position of the `C₁` part, the next cut key that carries no stop chord
  carries a chord seen from an endpoint (on `C₂`, not the shared vertex) of an exit chord of `λ`,
  or from the top of `C₂` — the RAM's shot origins.
* `top_of_genuine`: a genuine hit of the shot from the top of `C₂` in the model of `C₁` is the
  first hit in `C` (the top chord).
* `cut_of_genuine` (**soundness of the detection**): a genuine hit of a shot from an endpoint of a
  chord of `S₂` (before its far end), arriving at a position of the left stretch, is a cut of
  `F₂⁺` at the corresponding position of `C`, at the offset `L + d + t`.
-/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sideInArc sidePt sideLeft sideCross freeIn regionsIn)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd hseg)
open Chazelle.Geometry (lerp point_ext)
open Chazelle.Merge (FreeAt)
open WalkEmbed

namespace Sweep

section Machine

variable (J : Merge.Junction)

/-- **The stop chords** (precomputed by the RAM, design §9.2): the shared chords, and the chords
seen from an endpoint of a chord of `S₂` that is not on `C₂` (a box-wall endpoint). -/
def StopChord (S₂ : Set (Set Point)) (e : Set Point) : Prop :=
  (∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ FreeAt J.whole J.shared σ ∧ e = Merge.shoot J.whole J.shared σ) ∨
  (∃ c ∈ S₂, ∃ (a : Point) (σ : ℝ), ((σ = 1 ∧ a = Merge.lend c) ∨ (σ = -1 ∧ a = Merge.rend c)) ∧
    a ∉ J.right.set ∧ FreeAt J.whole a σ ∧ e = Merge.shoot J.whole a σ)

/-- The origin of a chord seen from a point off the domain is an end of it, off the domain. -/
theorem origin_mem {a : Point} {σ : ℝ} : a ∈ Merge.shoot J.whole a σ :=
  Geometry.left_mem_segment _ _

/-- An endpoint of a chord of `S₂` is off the domain of `C`. -/
theorem end_not_mem_dom {S₂ : Set (Set Point)} (hS₂ : S₂ ⊆ Merge.augChords J.right)
    {c : Set Point} (hc : c ∈ S₂) :
    Merge.lend c ∉ J.whole.dom ∧ Merge.rend c ∉ J.whole.dom := by
  obtain ⟨y, l, r, hH, hy, -, hl, hr⟩ := Merge.augChords_spec (hS₂ hc)
  Ξ hl, hr
  exact ⟨fun hd => hH.left_not (dom_right J hd hy), fun hd => hH.right_not (dom_right J hd hy)⟩

/-- **A non-stop chord has an attachment on the open right stretch.** -/
theorem stretch_end (hP : J.P.Simple)
    {S₂ : Set (Set Point)} (hS₂ : S₂ ⊆ Merge.augChords J.right)
    (hS₂f : S₂.Finite) {e : Set Point} (he : e ∈ F₂plus J S₂) (hns : ¬ StopChord J S₂ e) :
    ∃ (pB : ℕ) (tB : ℝ), SideAttach (chainModel J.whole).W e pB tB ∧
      0 < off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pB + tB) ∧
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pB + tB) <
        ((rL1 J + rL2 J : ℕ) : ℝ) ∧
      sidePt (chainModel J.whole).W pB tB ∈ J.right.set ∧
      sidePt (chainModel J.whole).W pB tB ≠ J.shared := by
  have hM : WalkAx (chainModel J.whole) := FactsChain.walkAx J.whole hP
  have hA : e ∈ Merge.augChords J.whole := F₂plus_subset J hS₂ he
  have hvD : J.shared ∉ J.whole.dom := fun hd =>
    J.whole.not_mem_set_of_mem_dom hd (J.left_set_subset J.shared_mem_left)
  -- an end of `e` on `C₂` other than the shared vertex gives the attachment
  have key : ∀ x, x ∈ e → x ∈ J.right.set → x ≠ J.shared → ∃ (pB : ℕ) (tB : ℝ),
      SideAttach (chainModel J.whole).W e pB tB ∧
      0 < off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pB + tB) ∧
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pB + tB) <
        ((rL1 J + rL2 J : ℕ) : ℝ) ∧
      sidePt (chainModel J.whole).W pB tB ∈ J.right.set ∧
      sidePt (chainModel J.whole).W pB tB ≠ J.shared := by
    intro x hxe hx hxv
    have hxD : x ∉ J.whole.dom := fun hd =>
      J.whole.not_mem_set_of_mem_dom hd (J.right_set_subset hx)
    obtain ⟨a, b, -, hcab, -, hopen, ⟨⟨pa, ta, hAa, hAa'⟩, -⟩, ⟨⟨pb, tb, hBb, hBb'⟩, -⟩⟩ :=
      hM.ends e hA
    have hxab : x = a ∨ x = b := by
      by_cases hxa : x = a
      · exact Or.inl hxa
      · right
        rw [hcab] at hxe
        exact seg_end hxe hxD hopen hxa
    rcases hxab with rfl | rfl
    · refine ⟨pa, ta, hAa, ?_⟩
      have := off_right_pt J hP hS₂ hS₂f hAa.1 hAa.2.1 hAa.2.2.1 (by rw [hAa']; exact hx)
        (by rw [hAa']; exact hxv)
      exact ⟨this.1, this.2, by rw [hAa']; exact hx, by rw [hAa']; exact hxv⟩
    · refine ⟨pb, tb, hBb, ?_⟩
      have := off_right_pt J hP hS₂ hS₂f hBb.1 hBb.2.1 hBb.2.2.1 (by rw [hBb']; exact hx)
        (by rw [hBb']; exact hxv)
      exact ⟨this.1, this.2, by rw [hBb']; exact hx, by rw [hBb']; exact hxv⟩
  -- a chord through the shared vertex is a shared chord, a stop chord
  have hshared : J.shared ∉ e := by
    intro hv'
    obtain ⟨σ, hσ, hfree, heq⟩ := chord_eq_shoot_of_end J.whole hA hv' hvD
    exact hns (Or.inl ⟨σ, hσ, hfree, heq⟩)
  rcases he with ((⟨c', hc', hfree, rfl⟩ | ⟨c', hc', hfree, rfl⟩) | hsh) | htop
  · have hc'S : c' ∈ S₂ := by simpa using hc'
    by_cases hr : Merge.lend c' ∈ J.right.set
    · exact key _ (origin_mem J) hr (fun h => hshared (h ▸ origin_mem J))
    · exact absurd (Or.inr ⟨c', hc'S, _, 1, Or.inl ⟨rfl, rfl⟩, hr, hfree, rfl⟩) hns
  · have hc'S : c' ∈ S₂ := by simpa using hc'
    by_cases hr : Merge.rend c' ∈ J.right.set
    · exact key _ (origin_mem J) hr (fun h => hshared (h ▸ origin_mem J))
    · exact absurd (Or.inr ⟨c', hc'S, _, -1, Or.inr ⟨rfl, rfl⟩, hr, hfree, rfl⟩) hns
  · obtain ⟨σ, hσ, hfree, rfl⟩ := hsh
    exact absurd (Or.inl ⟨σ, hσ, (Merge.freeAt_vertex _ _ _).2 hfree, rfl⟩) hns
  · obtain ⟨σ, hσ, hfree, rfl⟩ := htop
    have hv' : J.whole.vertex (J.m₁ + J.right.topIdx) = J.right.top := by
      rw [Merge.Junction.whole_vertex_add]; rfl
    have hmem : J.right.top ∈ J.whole.chordSet (J.m₁ + J.right.topIdx) σ := by
      rw [← hv']; exact Geometry.left_mem_segment _ _
    exact key _ hmem J.right.top_mem_set (fun h => hshared (h ▸ hmem))

/-- **Completeness of the detection**: from a valid label `λ` of the region faced at a non-cut
position of the `C₁` part, the next cut key `K` without stop chords carries a chord seen from an
endpoint (on `C₂`, not the shared vertex) of an exit chord of `λ` or of a region at a side of
the slit of `C₂`, or from the top of `C₂`. -/
theorem next_event_origin (hP : J.P.Simple)
    {Q : Polygon} {S₂ : Set (Set Point)}
    (hS₂ : (chainModel J.right).ChordFamily Q S₂)
    (hF : (chainModel J.whole).ChordFamily Q (F₂plus J S₂)) {G L : Set Point}
    (hG : G ∈ (chainModel J.whole).regions (F₂plus J S₂))
    (hL : L ∈ (chainModel J.right).regions S₂) (hvalid : Valid J S₂ G L)
    {p₀ : ℕ} {t₀ : ℝ} (hp₀ : p₀ < (chainModel J.whole).W.n) (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1)
    (hnc₀ : ¬ (chainModel J.whole).IsCut (F₂plus J S₂) (p₀ + t₀))
    (hfG₀ : (chainModel J.whole).Faces p₀ t₀ G)
    (ho₀ : ((rL1 J + rL2 J : ℕ) : ℝ) <
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (p₀ + t₀))
    {pK : ℕ} {tK : ℝ} (hpK : pK < (chainModel J.whole).W.n) (htK0 : 0 ≤ tK) (htK1 : tK < 1)
    (hoK : off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (p₀ + t₀) <
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pK + tK))
    (hgap : ∀ x, (chainModel J.whole).IsCut (F₂plus J S₂) x → 0 ≤ x →
      x < (chainModel J.whole).W.n →
      ¬ (off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (p₀ + t₀) <
          off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) x ∧
        off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) x <
          off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pK + tK)))
    {e : Set Point} (he : e ∈ F₂plus J S₂) (heK : SideAttach (chainModel J.whole).W e pK tK)
    (hstop : ∀ e' ∈ F₂plus J S₂, SideAttach (chainModel J.whole).W e' pK tK →
      ¬ StopChord J S₂ e') :
    ∃ h ∈ F₂plus J S₂, SideAttach (chainModel J.whole).W h pK tK ∧
      ∃ (a : Point) (σ : ℝ), (σ = 1 ∨ σ = -1) ∧ FreeAt J.whole a σ ∧
        h = Merge.shoot J.whole a σ ∧
        ((∃ c ∈ S₂, (∃ V, LabS J S₂ L V ∧ Chazelle.Chain.TouchesIn (chainModel J.right).D c V) ∧
          ((σ = 1 ∧ a = Merge.lend c) ∨ (σ = -1 ∧ a = Merge.rend c)) ∧
          a ∈ J.right.set ∧ a ≠ J.shared) ∨ a = J.right.top) := by
  have hM : WalkAx (chainModel J.whole) := FactsChain.walkAx J.whole hP
  have hFs := hF.2.1
  have hvD : J.shared ∉ J.whole.dom := fun hd =>
    J.whole.not_mem_set_of_mem_dom hd (J.left_set_subset J.shared_mem_left)
  -- the stretch attachment of `e`
  obtain ⟨pB, tB, heB, hB0, hBL, hBr, hBv⟩ :=
    stretch_end J hP hS₂.2.1 hS₂.1 he (hstop e he heK)
  have hLK : ((rL1 J + rL2 J : ℕ) : ℝ) <
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pK + tK) := ⟡
  have heKB : sidePt (chainModel J.whole).W pK tK ≠ sidePt (chainModel J.whole).W pB tB := by
    intro h
    have := off_right_pt J hP hS₂.2.1 hS₂.1 hpK htK0 htK1 (by rw [h]; exact hBr)
      (by rw [h]; exact hBv)
    linarith [this.2]
  have hnobr : ∀ e' ∈ F₂plus J S₂, SideAttach (chainModel J.whole).W e' pK tK →
      ∃ (pb : ℕ) (tb : ℝ), SideAttach (chainModel J.whole).W e' pb tb ∧
        off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pb + tb) <
          ((rL1 J + rL2 J : ℕ) : ℝ) := by
    intro e' he' heK'
    obtain ⟨pb, tb, hb, -, hbL, -⟩ :=
      stretch_end J hP hS₂.2.1 hS₂.1 he' (hstop e' he' heK')
    exact ⟨pb, tb, hb, hbL⟩
  obtain ⟨h, hh, hhK⟩ := next_event_detected J hP hS₂ hF hG hL hvalid hp₀ ht₀ hnc₀ hfG₀ ho₀
    hpK htK0 htK1 hoK hgap he heK heB heKB hB0 hBL hnobr
  have hhF := hh.1
  refine ⟨h, hhF, hhK, ?_⟩
  have hns := hstop h hhF hhK
  rcases cand_cases J hS₂.2.1 hh with ⟨c, hc, htouch, hcase⟩ | ⟨σ, hσ, hfree, rfl⟩ |
      ⟨σ, hσ, hfree, rfl⟩
  · rcases hcase with ⟨hfree, rfl⟩ | ⟨hfree, rfl⟩
    · refine ⟨_, 1, Or.inl rfl, hfree, rfl, Or.inl ⟨c, hc, htouch, Or.inl ⟨rfl, rfl⟩, ?_, ?_⟩⟩
      · by_contra hr
        exact hns (Or.inr ⟨c, hc, _, 1, Or.inl ⟨rfl, rfl⟩, hr, hfree, rfl⟩)
      · intro hlv
        exact hns (Or.inl ⟨1, Or.inl rfl, by rw [← hlv]; exact hfree, Ρ hlv⟩)
    · refine ⟨_, -1, Or.inr rfl, hfree, rfl, Or.inl ⟨c, hc, htouch, Or.inr ⟨rfl, rfl⟩, ?_, ?_⟩⟩
      · by_contra hr
        exact hns (Or.inr ⟨c, hc, _, -1, Or.inr ⟨rfl, rfl⟩, hr, hfree, rfl⟩)
      · intro hlv
        exact hns (Or.inl ⟨-1, Or.inr rfl, by rw [← hlv]; exact hfree, Ρ hlv⟩)
  · exact absurd (Or.inl ⟨σ, hσ, hfree, rfl⟩) hns
  · exact ⟨_, σ, hσ, hfree, rfl, Or.inr rfl⟩

end Machine

end Sweep

end

end Chazelle.Core
