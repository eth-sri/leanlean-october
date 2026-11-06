module

public import Chazelle.Core.SweepEvStopLabSG
public import Chazelle.Core.SweepChainT
public import Chazelle.Core.SweepEvKey

/-!
# The sweep (WP-D), stage 2: the middle of a split tie with a partner ending on `C₂` (Task SG)

Case G: two chords `e ≠ e'` of `F₂⁺` at the split vertex `u` (the top of `C₂`), `e` also attached
on the `C₁` part, `e'` also attached at a point `Y ≠ u` of the open right stretch, and a region
`G` on the same side `ρ` of both.

* `ρ = -1` is impossible (`sg_sep`): the tie at the split vertex descends, so the region above
  `e'` is also above `e`; the points just below and just above an inner point of `e'` lie in one
  region of the family `{e}`, which then lies on both sides of `e`.
* `ρ = 1`: `e'` is an augmented chord of `C₂` (`partner_cases`), the region `V` of `S₂` above it
  is a gap label (`split_copy`, `faced_or_middle` at the copy of `u`), and at `Y` either `G` is
  faced with `V` faced at the counterpart (`RLabel`), or a chord `f'` of a chord `c ∈ S₂` is
  tied with `e'` at `Y` (`local_step2`), giving the virtual label `V` (`VLabel`); `f'` cannot
  pass through `u` (`sg_top_not_mem`).

**`splitGapTask : SplitGapTask`**.
-/

namespace Chazelle.Core

namespace SweepEv

open Set Filter Topology Metric
open Sweep WalkEmbed
open Chazelle.Chain (SideAttach sidePt freeIn regionsIn)

@[expose] public section

/-- **No region lies below two chords whose upper regions agree**: if the region `U` is above both
chords `e` and `e'`, and the region `G` is below both, and the points of `e'` are on a vertical
line off `e`, then the regions of `{e}` on the two sides of `e` would meet. -/
theorem sg_sep {M : Model} (hM : WalkAx M) {F : Set (Set Point)} (hF : F ⊆ M.Adm)
    {e e' : Set Point} (he : e ∈ F) {p : ℕ} {t : ℝ} (heA : SideAttach M.W e p t) {z : Point}
    (hz : z ∈ e') (hzD : z ∈ M.D) (hze : ∀ w ∈ e, w.1 ≠ z.1) {G U : Set Point}
    (hG : G ∈ M.regions F) (hU : U ∈ M.regions F) (hGe : SideOf M (-1) e G)
    (hUe : SideOf M 1 e U) (hGe' : SideOf M (-1) e' G) (hUe' : SideOf M 1 e' U) : False := by
  have hF1 : ({e} : Set (Set Point)) ⊆ M.Adm := singleton_subset_iff.2 (hF he)
  have hfin1 : ({e} : Set (Set Point)).Finite := finite_singleton e
  obtain ⟨R₁, hR₁, hS1⟩ := side_region_exists' hM hF1 hfin1 (mem_singleton e) (Or.inr rfl)
  obtain ⟨R₂, hR₂, hS2⟩ := side_region_exists' hM hF1 hfin1 (mem_singleton e) (Or.inl rfl)
  have hne := side_regions_ne hM hF1 hfin1 (mem_singleton e) heA hR₂ hR₁ hS2 hS1
  have hsub : freeIn M.D F ⊆ freeIn M.D {e} :=
    sdiff_subset_sdiff_right (sUnion_mono (singleton_subset_iff.2 he))
  -- a region of `F` on a side of `e` lies in the region of `{e}` on that side
  have into : ∀ {X R : Set Point} {ρ : ℝ}, X ∈ M.regions F → R ∈ M.regions {e} →
      SideOf M ρ e X → SideOf M ρ e R → X ⊆ R := by
    intro X R ρ hX hR hXs hRs
    obtain ⟨w, hw, hwD⟩ := adm_mem_dom hM (hF he)
    obtain ⟨δ, h1, h2⟩ := ((hXs w hw hwD).and (hRs w hw hwD)).exists
    obtain ⟨x, hx, rfl⟩ := hX
    exact subset_region hR isPreconnected_connectedComponentIn
      ((connectedComponentIn_subset _ _).trans hsub) h1 h2
  have hGR := into hG hR₁ hGe hS1
  have hUR := into hU hR₂ hUe hS2
  -- the vertical segment through `z`
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hM.isOpen z hzD
  obtain ⟨δ, ⟨hGd, hUd⟩, hδr⟩ := (((hGe' z hz hzD).and (hUe' z hz hzD)).and
    (Ioo_mem_nhdsGT hr)).exists
  set S := (fun s : ℝ => ((z.1, z.2 + s) : Point)) '' Icc (-δ) δ
  have hSc : IsPreconnected S :=
    isPreconnected_Icc.image _ (by fun_prop : Continuous fun s : ℝ => ((z.1, z.2 + s) : Point)).continuousOn
  have hSf : S ⊆ freeIn M.D {e} := by
    rintro _ ⟨s, ⟨hs1, hs2⟩, rfl⟩
    refine ⟨hball ?_, ?_⟩
    · rw [Metric.mem_ball, Prod.dist_eq]
      simp only [dist_self, Real.dist_eq, add_sub_cancel_left]
      rw [max_lt_iff]
      exact ⟨hr, by rw [abs_lt]; constructor <;> linarith [hδr.2]⟩
    · rintro ⟨c, hc, hmem⟩
      rw [mem_singleton_iff] at hc
      subst hc
      exact hze _ hmem rfl
  have ha : ((z.1, z.2 + -1 * δ) : Point) ∈ S :=
    ⟨-δ, ⟨le_rfl, by linarith⟩, by simp⟩
  have hb : ((z.1, z.2 + 1 * δ) : Point) ∈ S :=
    ⟨δ, ⟨by linarith, le_rfl⟩, by simp⟩
  have hSR := subset_region hR₁ hSc hSf ha (hGR hGd)
  have hb1 := hSR hb
  have hb2 := hUR hUd
  exact hne ((Chazelle.Chain.regionsIn_eq_component hR₂ hb2).trans (Chazelle.Chain.regionsIn_eq_component hR₁ hb1).symm)

/-- **A chord tied with `e'` at its far end does not pass through the top of `C₂`.** -/
theorem sg_top_not_mem {J : Merge.Junction} (hP : J.P.Simple) {S₂ : Set (Set Point)}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) {e' f' : Set Point} (he' : e' ∈ F₂plus J S₂)
    (hf' : f' ∈ F₂plus J S₂) (hne : f' ≠ e') {Pu q : ℕ} {s : ℝ}
    (hA1 : SideAttach (chainModel J.whole).W e' Pu 0)
    (hpt1 : sidePt (chainModel J.whole).W Pu 0 = J.right.top)
    (hA2 : SideAttach (chainModel J.whole).W e' q s)
    (hne2 : sidePt (chainModel J.whole).W q s ≠ sidePt (chainModel J.whole).W Pu 0)
    (hf'A : SideAttach (chainModel J.whole).W f' q s) (hu : J.right.top ∈ f') : False := by
  have hM : WalkAx (chainModel J.whole) := FactsChain.walkAx J.whole hP
  have huD := hM.trace _ hA1.1 0 le_rfl zero_le_one
  have hYD := hM.trace _ hA2.1 s hA2.2.1 hA2.2.2.1.le
  have hue : sidePt (chainModel J.whole).W Pu 0 ∈ e' := hA1.2.2.2.1
  have hYe : sidePt (chainModel J.whole).W q s ∈ e' := hA2.2.2.2.1
  have hYf : sidePt (chainModel J.whole).W q s ∈ f' := hf'A.2.2.2.1
  rw [hpt1] at hue huD hne2
  set u := J.right.top
  set Y := sidePt (chainModel J.whole).W q s
  have he'A := F₂plus_subset J hS₂ he'
  have hf'Ad := F₂plus_subset J hS₂ hf'
  obtain ⟨y, a, b, hH, -, he'd, -, -⟩ := Merge.augChords_spec he'A
  obtain ⟨y', a', b', -, -, hf'd, -, -⟩ := Merge.augChords_spec hf'Ad
  have hend : ∀ w ∈ e', w ∉ (chainModel J.whole).D → w.1 = a ∨ w.1 = b := by
    intro w hw hwD
    rw [he'd] at hw
    obtain ⟨hwy, hwa, hwb⟩ := hw
    rcases hwa.lt_or_eq with h1 | h1
    · rcases hwb.lt_or_eq with h2 | h2
      · exact absurd (show w ∈ (chainModel J.whole).D by
          rw [show w = (w.1, y) from Prod.ext rfl hwy]; exact hH.open_mem w.1 h1 h2) hwD
      · exact Or.inr h2
    · exact Or.inl h1.symm
  have hu1 := hend u hue huD
  have hY1 := hend Y hYe hYD
  have huy : u.2 = y := by rw [he'd] at hue; exact hue.1
  have hYy : Y.2 = y := by rw [he'd] at hYe; exact hYe.1
  have huY : u.1 ≠ Y.1 := fun h => hne2 (Prod.ext h.symm (hYy.trans huy.symm))
  rw [hf'd] at hu hYf
  obtain ⟨huy', hua', hub'⟩ := hu
  obtain ⟨-, hYa', hYb'⟩ := hYf
  have hsub : e' ⊆ f' := by
    rw [he'd, hf'd]
    rintro w ⟨hwy, hwa, hwb⟩
    refine ⟨hwy.trans (huy.symm.trans huy'), ?_, ?_⟩
    · rcases hu1 with h | h <;> rcases hY1 with h' | h'
      · exact absurd (h.trans h'.symm) huY
      · linarith
      · linarith
      · exact absurd (h.trans h'.symm) huY
    · rcases hu1 with h | h <;> rcases hY1 with h' | h'
      · exact absurd (h.trans h'.symm) huY
      · linarith
      · linarith
      · exact absurd (h.trans h'.symm) huY
  exact hne (augChords_nest he'A hf'Ad hsub).symm

set_option maxHeartbeats 4000000 in
/-- **Task SG: the middle region of a split tie with a partner ending on `C₂`.** -/
theorem splitGapTask : SplitGapTask := by
  intro J Q S₂ hP hS₂ hF hδ e he e' he' hne heA he'A ⟨qe, se, heB, heL⟩
    ⟨q, s, hYA, hYne, hY0, hYL⟩ ρ hρ G hG hGe hGe'
  have hC := corr_right0 J hP hS₂.2.1 hS₂.1
  have hM := hC.hM
  have hM₂ := hC.hM₂
  have hS₂a : S₂ ⊆ Merge.augChords J.right := hS₂.2.1
  have hFs : F₂plus J S₂ ⊆ (chainModel J.whole).Adm := hC.hF
  have hGM : GoodModel (chainModel J.whole) := Or.inl ⟨J.whole, hP, rfl⟩
  have hGM₂ : GoodModel (chainModel J.right) := Or.inl ⟨J.right, hP, rfl⟩
  obtain ⟨hL1, -, hL2, -, hlt⟩ := caseG_consts J hδ
  have hτ' := tpos_lt J.right 0
  have hm2 : J.right.m = J.m₂ := rfl
  have hL1pos : 1 ≤ rL1 J := by omega
  have hd : rL1 J < rL1 J + rL2 J := by omega
  obtain ⟨hpt, -⟩ := split_facts J hδ
  set W := (chainModel J.whole).W
  set W₂ := (chainModel J.right).W
  set Pu := (6 + tpos J.whole J.m₁ + rL1 J) % W.n
  have heA' : SideAttach W e Pu 0 := heA
  have he'A' : SideAttach W e' Pu 0 := he'A
  have hinPu : 0 < off W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ((Pu : ℝ) + 0) ∧
      off W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ((Pu : ℝ) + 0) < ((rL1 J + rL2 J : ℕ) : ℝ) := by
    rw [hC.off_M hd (t := 0) le_rfl zero_lt_one]
    have h1 : (1 : ℝ) ≤ rL1 J := by exact_mod_cast hL1pos
    have h2 : ((rL1 J : ℕ) : ℝ) + 1 ≤ ((rL1 J + rL2 J : ℕ) : ℝ) := by exact_mod_cast hd
    constructor <;> linarith
  have hY0' : 0 < off W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ((q : ℝ) + s) := hY0
  have hYL' : off W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ((q : ℝ) + s) <
      ((rL1 J + rL2 J : ℕ) : ℝ) := hYL
  have hYne' : sidePt W q s ≠ sidePt W Pu 0 := hYne
  -- `e'` is an augmented chord of `C₂`
  have he'R : e' ∈ Merge.augChords J.right := by
    rcases partner_cases J hP hS₂a hS₂.1 he' he'A' hinPu with h | h
    · exact h
    · exact absurd ⟨hY0', hYL'⟩ (h q s hYA hYne')
  rcases hρ with rfl | rfl
  · -- above: a gap label
    have hSx := S₂x_family J hS₂ hF
    have hSs : S₂x J S₂ ⊆ (chainModel J.right).Adm := S₂x_subset J hS₂a
    have hc : e' ∈ S₂x J S₂ := Or.inr ⟨he', he'R⟩
    obtain ⟨U₂, hU₂, hU₂s⟩ := side_region_exists' hM₂ hSs hSx.1 hc (Or.inl rfl)
    obtain ⟨V, hV, hU₂V⟩ := super_region (subset_S₂x J S₂) hU₂
    have hVs : SideOf (chainModel J.right) 1 e' V := sideOf_mono hU₂s hU₂V
    obtain ⟨-, -, hp1, hp2, -, -⟩ := copy_facts J hδ
    have hk₂' : (6 + tpos J.right 0 + (rL1 J + rδ J)) % W₂.n =
        (6 + tpos J.right 0 + rL1 J + rδ J) % W₂.n := by rw [← add_assoc]
    have hgap : GapLab J S₂ V := by
      rcases split_copy J hP hδ (F₂plus_subset J hS₂a he') (hSs hc) subset_rfl he'A' with
        ⟨hcW, hAk⟩ | ⟨hcE, hAk⟩
      · have hdirC : ((-1 : ℝ) = 1 ∧ ∀ z ∈ e',
            (sidePt W₂ ((6 + tpos J.right 0 + rL1 J) % W₂.n) 0).1 ≤ z.1) ∨
            ((-1 : ℝ) = -1 ∧ ∀ z ∈ e',
              z.1 ≤ (sidePt W₂ ((6 + tpos J.right 0 + rL1 J) % W₂.n) 0).1) :=
          Or.inr ⟨rfl, fun z hz => by rw [hp1]; exact hcW z hz⟩
        have hFV := (faced_or_middle hGM₂ hSx hc hAk (Or.inl rfl) hU₂ hU₂s hdirC).1
          (fun c'' hc'' hA'' => oneAt_right J hP (S₂x_subset J hS₂a) hδ (rL1 J) (Or.inl rfl)
            c'' hc'' e' hc hA'' hAk)
        exact ⟨hδ, hV, Or.inl (afterFaces_mono (hFV.1 (by norm_num)) hU₂V)⟩
      · have hdirC : ((1 : ℝ) = 1 ∧ ∀ z ∈ e',
            (sidePt W₂ ((6 + tpos J.right 0 + rL1 J + rδ J) % W₂.n) 0).1 ≤ z.1) ∨
            ((1 : ℝ) = -1 ∧ ∀ z ∈ e',
              z.1 ≤ (sidePt W₂ ((6 + tpos J.right 0 + rL1 J + rδ J) % W₂.n) 0).1) :=
          Or.inl ⟨rfl, fun z hz => by rw [hp2]; exact hcE z hz⟩
        have hFV := (faced_or_middle hGM₂ hSx hc hAk (Or.inl rfl) hU₂ hU₂s hdirC).1
          (fun c'' hc'' hA'' => oneAt_right J hP (S₂x_subset J hS₂a) hδ (rL1 J + rδ J)
            (Or.inr rfl) c'' hc'' e' hc (by rwa [hk₂']) (by rwa [hk₂']))
        exact ⟨hδ, hV, Or.inr (beforeFaces_mono (hFV.2 (by norm_num)) hU₂V)⟩
    refine ⟨V, hgap, ?_⟩
    -- at the far end `Y`
    obtain ⟨dY, hdY, hdY0, hqY⟩ := stretch_decomp J hP hS₂a hS₂.1 hYA.1 hYA.2.1 hYA.2.2.1 hY0'
      hYL'
    have hsecY : s = 0 → dY ≠ 0 ∧ dY ≠ rL1 J := by
      intro hs0
      refine ⟨hdY0 hs0, fun hdr => hYne' ?_⟩
      rw [hqY, hs0, hdr]
    have hYA2 : SideAttach W e' ((6 + tpos J.whole J.m₁ + dY) % W.n) s := by
      rw [← hqY]; exact hYA
    rcases local_step2 J hP hS₂ hF hdY hYA.2.1 hYA.2.2.1 hsecY he' hc subset_rfl hYA2
      (Or.inl rfl) hG hV hGe' hVs with hR | ⟨hs0, f', hf', hfne, hf'A, hf'G, hcase⟩
    · exact Or.inl hR
    · subst hs0
      have hnotu : J.right.top ∉ f' := fun hu =>
        sg_top_not_mem hP hS₂a he' hf' hfne he'A' hpt hYA hYne'
          (by rw [hqY]; exact hf'A) hu
      have hnotv : J.shared ∉ f' := by
        intro hv
        apply hnotu
        obtain ⟨y', a', b', -, -, hf'd, -, -⟩ := Merge.augChords_spec (F₂plus_subset J hS₂a hf')
        have hYf : sidePt W q 0 ∈ f' := by rw [hqY]; exact hf'A.2.2.2.1
        have huy : (sidePt W Pu 0).2 = (sidePt W q 0).2 := by
          obtain ⟨y, a, b, -, -, he'd, -, -⟩ :=
            Merge.augChords_spec (F₂plus_subset J hS₂a he')
          have h1 := he'A'.2.2.2.1
          have h2 := hYA.2.2.2.1
          rw [he'd] at h1 h2
          exact h1.1.trans h2.1.symm
        rw [hf'd] at hv hYf
        have hsh : J.shared = J.right.top := shared_eq_top_of_snd J (by
          rw [← hpt, huy, hYf.1, hv.1])
        rwa [← hsh, hf'd]
      have vlab : ∀ c ∈ S₂, f' ⊆ c → SideOf (chainModel J.right) 1 c V →
          VLabel J S₂ G V := fun c hcS hfc hcV =>
        ⟨f', c, 1, dY, 0, hf', hcS, hfc, Or.inl rfl, hdY, le_rfl, zero_lt_one, hsecY, hf'A,
          hf'G, hcV⟩
      rcases hcase with ⟨c', hc', hfc', hc'V⟩ | ⟨hk, -⟩
      · right
        rcases hc' with hc'S | ⟨hc'F, hc'R⟩
        · exact vlab c' hc'S hfc' hc'V
        · have hfeq : f' = c' :=
            augChords_nest (F₂plus_subset J hS₂a hf') (F₂plus_subset J hS₂a hc'F) hfc'
          subst hfeq
          rcases F₂plus_kind J hS₂a hf' with ⟨c, hcS, hfc⟩ | hv | hu
          · have hcc : f' = c := augChords_nest hc'R (hS₂a hcS) hfc
            subst hcc
            exact vlab f' hcS subset_rfl hc'V
          · exact absurd hv hnotv
          · exact absurd hu hnotu
      · rcases hk with hv | hu
        · exact absurd hv hnotv
        · exact absurd hu hnotu
  · -- below: impossible
    exfalso
    -- the tie at the split vertex descends
    have hwa : (chainModel J.whole).wa Pu = J.right.top := by
      rw [← hpt, Chazelle.Chain.sidePt_zero]; rfl
    have hn₂ := cm_n J.right
    have hwb : ((chainModel J.whole).wb Pu).2 ≤ J.right.top.2 := by
      have e0 := hC.sideNext_eq hd
      have edq : dq (rL1 J) (rδ J) (rL1 J) = rL1 J + rδ J := by
        unfold dq; rw [ite_eq_right (lt_irrefl _)]
      obtain ⟨-, g2, -, -, -, -, -, v7⟩ := gap_walk J hδ
      rw [edq, g2] at e0
      have e7 : Chazelle.Chain.sideNext W₂ 6 = J.right.sideTour J.right.sideBeta 1 := by
        unfold Chazelle.Chain.sideNext; rwa [hn₂, Nat.mod_eq_of_lt (by omega)]
      show (Chazelle.Chain.sideNext W Pu).2 ≤ J.right.top.2
      rw [e0, e7]
      have := sideTour_sub_top_snd J.right J.right.sideBeta 1
      simp only [Prod.snd_sub] at this
      linarith
    obtain ⟨U, hU, hUs⟩ := side_region_exists' hM hFs (F₂plus_finite J hS₂.1) he' (Or.inl rfl)
    obtain ⟨de', hde'⟩ := dirAt_exists hM (hFs he') he'A'
    obtain ⟨-, hhor, hdn, -⟩ :=
      (faced_or_middle hGM hF he' he'A' (Or.inl rfl) hU hUs hde').2 e he hne.symm heA'
    have hdesc : ((chainModel J.whole).wb Pu).2 < ((chainModel J.whole).wa Pu).2 := by
      rw [hwa] at hhor ⊢
      exact lt_of_le_of_ne hwb hhor
    have hUe : SideOf (chainModel J.whole) 1 e U := (hdn hdesc).1 rfl
    -- a point of `e'` in the domain, on a vertical line off `e`
    obtain ⟨z, hz, hzD⟩ := adm_mem_dom hM (hFs he')
    have huD := hM.trace _ he'A'.1 0 le_rfl zero_le_one
    obtain ⟨y, a, b, -, -, he'd, -, -⟩ := Merge.augChords_spec (F₂plus_subset J hS₂a he')
    have hzy : z.2 = (sidePt W Pu 0).2 := by
      have h1 := he'A'.2.2.2.1
      have h2 := hz
      rw [he'd] at h1 h2
      exact h2.1.trans h1.1.symm
    have hzu : z.1 ≠ (sidePt W Pu 0).1 := fun h =>
      huD (show sidePt W Pu 0 ∈ (chainModel J.whole).D by
        rwa [show sidePt W Pu 0 = z from Prod.ext h.symm hzy.symm])
    have hze : ∀ w ∈ e, w.1 ≠ z.1 := by
      rcases hM.tie_pair hFs he he' hne.symm heA' he'A' with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · intro w hw hwz
        have := h1 w hw
        have := h2 z hz
        exact hzu (le_antisymm (by linarith) (by linarith))
      · intro w hw hwz
        have := h1 w hw
        have := h2 z hz
        exact hzu (le_antisymm (by linarith) (by linarith))
    exact sg_sep hM hFs he heA' hz hzD hze hG hU hGe hUe hGe' hUs

end

end SweepEv

end Chazelle.Core
