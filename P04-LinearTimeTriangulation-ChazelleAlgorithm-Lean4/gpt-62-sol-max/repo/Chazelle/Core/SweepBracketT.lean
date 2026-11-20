module

public import Chazelle.Core.SweepBracket
public import Chazelle.Core.SweepChainT2

/-!
# The sweep (WP-D), part 9b: chain brackets without `TopStrict` (F2)

The bracket lemma of `SweepBracket` for a region without a label, with the walk of
`SweepChainT` (the enlarged family `S₂x`, the split step).  The tracked region of `S₂` may switch
to the other side of the slit of `C₂` at the split vertex, so the last chord of the chain lies in
a chord of `S₂` whose side is the region `V` of the start or (with `V`) a gap label
(`ChainKind`), or is a shared chord or a top chord.

* `kind_of_S₂x`: a chord of `F₂⁺` inside a chord of `S₂x` is inside a chord of `S₂`, or is that
  chord, a shared or top chord.
* `chain_gen2`, `bracket_core2`, `bracket2`: as `chain_gen`, `bracket_core`, `bracket`.
-/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sideInArc sidePt sideLeft sideKey_inj)
open Chazelle.Jordan (offset)
open Chazelle.Geometry (lerp)
open WalkEmbed

namespace Sweep

section ChainWalk2

variable (J : Merge.Junction)

section

variable (hP : J.P.Simple) {Q : Polygon}
    {S₂ : Set (Set Point)} (hS₂ : J.rightModel.ChordFamily Q S₂)

include hP hS₂ in
/-- The facts at a tie step: a chord with an attachment in the `C₁` part is not the chord `f`
arriving at the tie, is not attached at the tie unless it is `f'`, and the two attachments of
`f` have distinct offsets. -/
theorem tie_step_facts2
    {f f' : Set Point} {pn : ℕ} {tn : ℝ} {pf : ℕ} (hf : f ∈ F₂plus J S₂)
    (hf' : f' ∈ F₂plus J S₂) (hne : f' ≠ f) (hfA : SideAttach J.wholeModel.W f pn tn)
    (hfF : SideAttach J.wholeModel.W f pf 0)
    (hNF : sidePt J.wholeModel.W pn tn ≠ sidePt J.wholeModel.W pf 0)
    (hA' : SideAttach J.wholeModel.W f' pf 0)
    (hnL : off J.wholeModel.W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pn + tn) <
      ((rL1 J + rL2 J : ℕ) : ℝ))
    (hfL : off J.wholeModel.W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pf + 0) <
      ((rL1 J + rL2 J : ℕ) : ℝ))
    {e : Set Point} (he : e ∈ F₂plus J S₂) (hne' : e ≠ f') {pw : ℕ} {tw : ℝ} {pb : ℕ} {tb : ℝ}
    (hW : SideAttach J.wholeModel.W e pw tw)
    (hB : SideAttach J.wholeModel.W e pb tb)
    (hoW : ((rL1 J + rL2 J : ℕ) : ℝ) <
      off J.wholeModel.W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pw + tw)) :
    e ≠ f ∧
      off J.wholeModel.W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pb + tb) ≠
        off J.wholeModel.W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pf + 0) ∧
      off J.wholeModel.W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pn + tn) ≠
        off J.wholeModel.W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pf + 0) := by
  have hC := corr_right0 J hP hS₂.2.1 hS₂.1
  have hM := hC.hM
  have hFs := hC.hF
  have hg0 : (0 : ℝ) ≤ ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) := Nat.cast_nonneg _
  have hgn : ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) < J.wholeModel.W.n := by
    exact_mod_cast hC.hg
  obtain ⟨n0, n1⟩ := Corr.key_mem hfA.1 hfA.2.1 hfA.2.2.1
  obtain ⟨f0, f1⟩ := Corr.key_mem hfF.1 hfF.2.1 hfF.2.2.1
  obtain ⟨b0, b1⟩ := Corr.key_mem hB.1 hB.2.1 hB.2.2.1
  have hef : e ≠ f := by
    rintro rfl
    rcases key_of_two hM (hFs he) hfA hfF hNF hW with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> linarith
  refine ⟨hef, fun heq => ?_, fun heq => ?_⟩
  · have hk := off_inj hg0 hgn b0 b1 f0 f1 heq
    obtain ⟨rfl, rfl⟩ := sideKey_inj hB.2.1 hB.2.2.1 hfF.2.1 hfF.2.2.1 hk
    rcases tie_third hM hFs hf hf' he (Ne.symm hne) hfF hA' hB with h | h
    · exact hef h
    · exact hne' h
  · exact WalkAx.key_ne_of_pt_ne hfA hfF hNF (off_inj hg0 hgn n0 n1 f0 f1 heq)

include hP hS₂ in
/-- The forward invariant propagates across ties. -/
theorem propag_I2
    (hF : J.wholeModel.ChordFamily Q (F₂plus J S₂)) {lo : ℝ}
    (hlo : ((rL1 J + rL2 J : ℕ) : ℝ) ≤ lo) : Propag J S₂ (PhiI J S₂ lo) := by
  intro f f' pn tn pf pb tb hf hf' hne hfA hfF hNF hA' hB hBne hn0 hnL hf0 hfL hΦ e he hne'
    pw tw pb' tb' hW hB' hWB hoW hoB
  have hC := corr_right0 J hP hS₂.2.1 hS₂.1
  have hg0 : (0 : ℝ) ≤ ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) := Nat.cast_nonneg _
  have hgn : ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) < J.wholeModel.W.n := by
    exact_mod_cast hC.hg
  obtain ⟨hef, hBF, hNFo⟩ := tie_step_facts2 J hP hS₂ hf hf' hne hfA hfF hNF hA' hnL hfL he
    hne' hW hB' (lt_of_le_of_lt hlo hoW)
  have h1 := hΦ e he hef pw tw pb' tb' hW hB' hWB hoW hoB
  rcases lt_or_gt_of_ne hNFo with h | h
  · linarith
  · by_contra hc
    push Not at hc
    have := no_cross_off hC.hM hC.hF hF.1 hf he (Ne.symm hef) hfF hfA (Ne.symm hNF) hB' hW hg0
      hgn h (lt_of_le_of_ne hc (Ne.symm hBF)) h1
    linarith [this.2]

include hP hS₂ in
/-- The backward invariant propagates across ties. -/
theorem propag_K2
    (hF : J.wholeModel.ChordFamily Q (F₂plus J S₂)) (oA : ℝ) :
    Propag J S₂ (PhiK J S₂ oA) := by
  intro f f' pn tn pf pb tb hf hf' hne hfA hfF hNF hA' hB hBne hn0 hnL hf0 hfL hΦ e he hne'
    pw tw pb' tb' hW hB' hWB hoW hoB hle
  have hC := corr_right0 J hP hS₂.2.1 hS₂.1
  have hg0 : (0 : ℝ) ≤ ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) := Nat.cast_nonneg _
  have hgn : ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) < J.wholeModel.W.n := by
    exact_mod_cast hC.hg
  obtain ⟨hef, hBF, hNFo⟩ := tie_step_facts2 J hP hS₂ hf hf' hne hfA hfF hNF hA' hnL hfL he
    hne' hW hB' hoW
  have hlt := lt_of_le_of_ne hle hBF
  rcases lt_or_gt_of_ne hNFo with h | h
  · by_cases hb : off J.wholeModel.W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pb' + tb') ≤
        off J.wholeModel.W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pn + tn)
    · exact hΦ e he hef pw tw pb' tb' hW hB' hWB hoW hoB hb
    · push Not at hb
      exfalso
      have := no_cross_off hC.hM hC.hF hF.1 hf he (Ne.symm hef) hfA hfF hNF hB' hW hg0 hgn h
        hb hlt
      linarith [this.2]
  · exact hΦ e he hef pw tw pb' tb' hW hB' hWB hoW hoB (by linarith)

/-! ## The ends of a chain -/

/-- **The kind of the last chord of a chain**: inside a chord of `S₂` whose side `ρ` is the region
`V` of the start, or (with `V`) a gap label; or a shared chord; or a top chord. -/
def ChainKind (S₂ : Set (Set Point)) (ρ : ℝ) (V h : Set Point) : Prop :=
  (∃ c ∈ S₂, h ⊆ c ∧ ∃ V' ∈ J.rightModel.regions S₂,
      (V' = V ∨ (GapLab J S₂ V ∧ GapLab J S₂ V')) ∧ SideOf J.rightModel ρ c V') ∨
    J.shared ∈ h ∨ J.right.top ∈ h

/-- **A chord of `F₂⁺` inside a chord of `S₂x`** is inside a chord of `S₂` (that chord), or is
the chord itself, a shared or a top chord. -/
theorem kind_of_S₂x (hP : J.P.Simple) {S₂ : Set (Set Point)}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hS₂f : S₂.Finite) {f c : Set Point}
    (hf : f ∈ F₂plus J S₂) (hc : c ∈ S₂x J S₂) (hfc : f ⊆ c) :
    c ∈ S₂ ∨ J.shared ∈ f ∨ J.right.top ∈ f := by
  rcases hc with hc | ⟨hcF, hcA⟩
  · exact Or.inl hc
  have hC := corr_right0 J hP hS₂ hS₂f
  have hfe := hC.nest f hf c hcF hfc
  subst hfe
  rcases F₂plus_kind J hS₂ hf with ⟨c₀, hc₀, hfc₀⟩ | h
  · left
    have := s2_eq_of_sub J (S₂ := Merge.augChords J.right) subset_rfl hcA (hS₂ hc₀)
      (F₂plus_subset J hS₂ hf) subset_rfl hfc₀
    rwa [this]
  · exact Or.inr h

/-- The kind of the last chord from the tracked data. -/
theorem chainKind_of (hP : J.P.Simple) {S₂ : Set (Set Point)}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hS₂f : S₂.Finite) {ρ : ℝ} {V₀ V h : Set Point}
    (hh : h ∈ F₂plus J S₂) (hV : V ∈ J.rightModel.regions S₂)
    (hrel : V = V₀ ∨ (GapLab J S₂ V₀ ∧ GapLab J S₂ V))
    (htr : (∃ c ∈ S₂x J S₂, h ⊆ c ∧ SideOf J.rightModel ρ c V) ∨
      (J.shared ∈ h ∨ J.right.top ∈ h)) :
    ChainKind J S₂ ρ V₀ h := by
  rcases htr with ⟨c, hc, hhc, hVs⟩ | hk
  · rcases kind_of_S₂x J hP hS₂ hS₂f hh hc hhc with hc' | hk
    · exact Or.inl ⟨c, hc', hhc, V, hV, hrel, hVs⟩
    · exact Or.inr hk
  · exact Or.inr hk

/-- **The end of a chain** (without `TopStrict`): as `ChainEnd`, with the kind of the last chord
(`ChainKind`). -/
def ChainEnd2 (S₂ : Set (Set Point)) (ρ θ : ℝ) (G V : Set Point)
    (Φ : Set Point → ℝ → Prop) : Prop :=
  ∃ h ∈ F₂plus J S₂, ∃ (ph : ℕ) (th : ℝ) (pz : ℕ) (tz : ℝ),
    SideAttach J.wholeModel.W h ph th ∧ SideAttach J.wholeModel.W h pz tz ∧
    sidePt J.wholeModel.W ph th ≠ sidePt J.wholeModel.W pz tz ∧
    SideOf J.wholeModel ρ h G ∧
    0 < θ * ρ * ((sidePt J.wholeModel.W ph th).1 -
      (sidePt J.wholeModel.W pz tz).1) ∧
    ChainKind J S₂ ρ V h ∧
    0 < off J.wholeModel.W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (ph + th) ∧
    off J.wholeModel.W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (ph + th) <
      ((rL1 J + rL2 J : ℕ) : ℝ) ∧
    ¬ (0 < off J.wholeModel.W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pz + tz) ∧
      off J.wholeModel.W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pz + tz) <
        ((rL1 J + rL2 J : ℕ) : ℝ)) ∧
    Φ h (off J.wholeModel.W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (ph + th))

include hP hS₂ in
/-- **Walking along a chain of an unlabelled region** without `TopStrict`: as `chain_gen`; the
tracked region `V` of `S₂` is `V₀` or (with `V₀`) a gap label. -/
theorem chain_gen2
    (hF : J.wholeModel.ChordFamily Q (F₂plus J S₂)) {ρ θ : ℝ} (hρ : ρ = 1 ∨ ρ = -1)
    (hθ : θ = 1 ∨ θ = -1) {G V₀ : Set Point}
    (hG : G ∈ J.wholeModel.regions (F₂plus J S₂)) (hU : ∀ V', ¬ RLabel J S₂ G V')
    (Φ : Set Point → ℝ → Prop) (hΦ : Propag J S₂ Φ) :
    ∀ (N : ℕ) (f : Set Point) (pn : ℕ) (tn : ℝ) (pf : ℕ) (tf : ℝ) (V : Set Point),
      V ∈ J.rightModel.regions S₂ → (V = V₀ ∨ (GapLab J S₂ V₀ ∧ GapLab J S₂ V)) →
      (beyond (F₂plus J S₂) (θ * ρ) (sidePt J.wholeModel.W pf tf)).ncard ≤ N →
      f ∈ F₂plus J S₂ → SideAttach J.wholeModel.W f pn tn →
      SideAttach J.wholeModel.W f pf tf →
      sidePt J.wholeModel.W pn tn ≠ sidePt J.wholeModel.W pf tf →
      SideOf J.wholeModel ρ f G →
      0 < θ * ρ * ((sidePt J.wholeModel.W pn tn).1 -
        (sidePt J.wholeModel.W pf tf).1) →
      ((∃ c ∈ S₂x J S₂, f ⊆ c ∧ SideOf J.rightModel ρ c V) ∨
        ((J.shared ∈ f ∨ J.right.top ∈ f) ∧
          ¬ (0 < off J.wholeModel.W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pf + tf) ∧
            off J.wholeModel.W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pf + tf) <
              ((rL1 J + rL2 J : ℕ) : ℝ)))) →
      0 < off J.wholeModel.W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pn + tn) →
      off J.wholeModel.W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pn + tn) <
        ((rL1 J + rL2 J : ℕ) : ℝ) →
      Φ f (off J.wholeModel.W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pn + tn)) →
      ChainEnd2 J S₂ ρ θ G V₀ Φ := by
  have hC := corr_right0 J hP hS₂.2.1 hS₂.1
  have hM := hC.hM
  have hFs : F₂plus J S₂ ⊆ J.wholeModel.Adm := hC.hF
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro f pn tn pf tf V hV hrel hN hf hfA hfF hNF hS hori htrack hn0 hnL hΦf
  set W := J.wholeModel.W with hWdef
  set g := 6 + tpos J.whole J.m₁ with hgdef
  set L := rL1 J + rL2 J with hLdef
  by_cases hin : 0 < off W.n (g : ℝ) (pf + tf) ∧ off W.n (g : ℝ) (pf + tf) < ((L : ℕ) : ℝ)
  swap
  · refine ⟨f, hf, pn, tn, pf, tf, hfA, hfF, hNF, hS, hori, ?_, hn0, hnL, hin, hΦf⟩
    exact chainKind_of J hP hS₂.2.1 hS₂.1 hf hV hrel (htrack.imp_right fun h => h.1)
  -- the far end is in the right stretch
  obtain ⟨c, hc, hfc, hVs⟩ := htrack.resolve_right fun h => h.2 hin
  obtain ⟨hpf, hoF⟩ := hC.decomp hfF.1 hfF.2.1 hfF.2.2.1
  set d' := dOf W.n g pf with hd'def
  have hd' : d' < L := by
    have h := hin.2
    rw [hoF] at h
    have : (d' : ℝ) < ((L : ℕ) : ℝ) := by linarith [hfF.2.1]
    exact_mod_cast this
  have hin1 := hin.1
  rw [hoF] at hin1
  clear_value d'
  subst hpf
  -- the step to a partner at the far end
  have hstep : ∀ (f' V' : Set Point), tf = 0 → f' ∈ F₂plus J S₂ → f' ≠ f →
      SideAttach W f' ((g + d') % W.n) 0 → SideOf J.wholeModel ρ f' G →
      V' ∈ J.rightModel.regions S₂ → (V' = V₀ ∨ (GapLab J S₂ V₀ ∧ GapLab J S₂ V')) →
      ((∃ c' ∈ S₂x J S₂, f' ⊆ c' ∧ SideOf J.rightModel ρ c' V') ∨
        ((J.shared ∈ f' ∨ J.right.top ∈ f') ∧ OffOut J f' ((g + d') % W.n) 0)) →
      ChainEnd2 J S₂ ρ θ G V₀ Φ := by
    intro f' V' htf0 hf' hne hA' hS' hV' hrel' hpart
    subst htf0
    obtain ⟨pb, tb, hB, hBne⟩ := hM.other_attach (hFs hf') hA'
    set Pf := sidePt W ((g + d') % W.n) 0 with hPfdef
    set Pn := sidePt W pn tn with hPndef
    set Bp := sidePt W pb tb with hBpdef
    have hori' := tie_continue (tie_opposite hM hFs hf hf' hne hfF hA' hfA hB hNF hBne) hori
    have hΦ' := hΦ f f' pn tn ((g + d') % W.n) pb tb hf hf' hne hfA hfF hNF hA' hB hBne hn0
      hnL hin.1 hin.2 hΦf
    rcases hpart with ⟨c', hc', hfc', hVs'⟩ | ⟨hk, hoff⟩
    · -- recursion along the partner
      have hlt : (beyond (F₂plus J S₂) (θ * ρ) Bp).ncard <
          (beyond (F₂plus J S₂) (θ * ρ) Pf).ncard := by
        refine Set.ncard_lt_ncard ?_ (hF.1.subset fun h hh => hh.1)
        refine ⟨fun h ⟨hh, z, hz, hz'⟩ => ⟨hh, z, hz, ?_⟩, fun hsub => ?_⟩
        · have e : θ * ρ * (Pf.1 - z.1) = θ * ρ * (Pf.1 - Bp.1) + θ * ρ * (Bp.1 - z.1) := by
            ring
          rw [e]
          exact add_pos hori' hz'
        · obtain ⟨-, z, hz, hz'⟩ := hsub ⟨hf', Bp, hB.2.2.2.1, hori'⟩
          obtain ⟨hseg', -, -, -, -⟩ := hM.attach_seg (hFs hf') hA' hB (Ne.symm hBne)
          rw [hseg'] at hz
          obtain ⟨s, hs0, hs1, rfl⟩ := Geometry.mem_segment_iff_lerp.1 hz
          simp only [Geometry.lerp_fst] at hz'
          
          nlinarith
      exact ih _ (lt_of_lt_of_le hlt hN) f' ((g + d') % W.n) 0 pb tb V' hV' hrel' le_rfl hf'
        hA' hB (Ne.symm hBne) hS' hori' (Or.inl ⟨c', hc', hfc', hVs'⟩) hin.1 hin.2 hΦ'
    · -- the partner leaves the stretch
      exact ⟨f', hf', (g + d') % W.n, 0, pb, tb, hA', hB, Ne.symm hBne, hS', hori',
        Or.inr hk, hin.1, hin.2, hoff pb tb hB hBne, hΦ'⟩
  by_cases hsplit : tf = 0 ∧ d' = rL1 J
  · obtain ⟨htf0, hdL⟩ := hsplit
    subst htf0
    subst hdL
    have hδ : 0 < rδ J := by
      by_contra h0
      have := hC.hδ (by omega)
      omega
    rcases split_step J hP hS₂ hF hδ hf hc hfc hfF hρ hG hV hS hVs with
      hRL | ⟨-, Vg, -, hRLg⟩ | ⟨hgV, f', hf', hne, hA', hS', hpart⟩
    · exact absurd hRL (hU V)
    · exact absurd hRLg (hU Vg)
    · have hgV₀ : GapLab J S₂ V₀ := by
        rcases hrel with rfl | ⟨h, -⟩
        · exact hgV
        · exact h
      rcases hpart with ⟨c', hc', hfc', V', hV', hVs', hgV'⟩ | hoff
      · exact hstep f' V' rfl hf' hne hA' hS' hV' (Or.inr ⟨hgV₀, hgV'⟩)
          (Or.inl ⟨c', hc', hfc', hVs'⟩)
      · exact hstep f' V rfl hf' hne hA' hS' hV hrel (Or.inr hoff)
  · have hsec' : tf = 0 → d' ≠ 0 ∧ d' ≠ rL1 J := by
      intro htf
      refine ⟨fun h => ?_, fun h => hsplit ⟨htf, h⟩⟩
      subst htf
      rw [h] at hin1
      simp at hin1
    rcases local_step2 J hP hS₂ hF hd' hfF.2.1 hfF.2.2.1 hsec' hf hc hfc hfF hρ hG hV hS hVs
      with hRL | ⟨htf0, f', hf', hne, hA', hS', hpart⟩
    · exact absurd hRL (hU V)
    · subst htf0
      exact hstep f' V rfl hf' hne hA' hS' hV hrel hpart

/-- **The conclusion of the bracket lemma** for a non-cut position with offset `o₀` in the `C₁`
part facing a region without a label: a chord `h` of `F₂⁺` (in a chord of `S₂` with `V` on the
side of the region, or ending at the shared vertex) is attached at a key `Z` after `o₀` (or at
offset `0`), and no chord of `F₂⁺` with an attachment inside the right stretch (not at offset
`0`) has an attachment between `o₀` and `Z`. -/
def BracketConcl2 (S₂ : Set (Set Point)) (ρ : ℝ) (V : Set Point) (o₀ : ℝ) : Prop :=
  ∃ h ∈ F₂plus J S₂, ∃ (pz : ℕ) (tz : ℝ), SideAttach J.wholeModel.W h pz tz ∧
    ChainKind J S₂ ρ V h ∧
    (off J.wholeModel.W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pz + tz) = 0 ∨
      (((rL1 J + rL2 J : ℕ) : ℝ) ≤
          off J.wholeModel.W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pz + tz) ∧
        o₀ < off J.wholeModel.W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pz + tz))) ∧
    ∀ e ∈ F₂plus J S₂, ∀ (pw : ℕ) (tw : ℝ) (pb : ℕ) (tb : ℝ),
      SideAttach J.wholeModel.W e pw tw → SideAttach J.wholeModel.W e pb tb →
      sidePt J.wholeModel.W pw tw ≠ sidePt J.wholeModel.W pb tb →
      o₀ < off J.wholeModel.W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pw + tw) →
      (off J.wholeModel.W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pz + tz) = 0 ∨
        off J.wholeModel.W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pw + tw) <
          off J.wholeModel.W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pz + tz)) →
      off J.wholeModel.W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pb + tb) <
        ((rL1 J + rL2 J : ℕ) : ℝ) →
      off J.wholeModel.W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pb + tb) ≠ 0 → False

include hP hS₂ in
/-- **The bracket lemma, from a tie.**  Let `fb`, `ff` be the two chords of `F₂⁺` of a tie at a
position `A` inside the right stretch, with the region `G` (without a label) on their side `ρ`,
`fb` oriented by `-1` and `ff` by `1`, each contained in a chord of `S₂` with `V` on its side `ρ`
(or ending at the shared vertex).  Then for every non-cut position of the `C₁` part facing `G`,
the conclusion `BracketConcl2` holds. -/
theorem bracket_core2
    (hF : J.wholeModel.ChordFamily Q (F₂plus J S₂)) {ρ : ℝ} (hρ : ρ = 1 ∨ ρ = -1)
    {G V : Set Point} (hG : G ∈ J.wholeModel.regions (F₂plus J S₂))
    (hU : ∀ V', ¬ RLabel J S₂ G V')
    {fb ff : Set Point} (hfb : fb ∈ F₂plus J S₂) (hff : ff ∈ F₂plus J S₂) (hbf : fb ≠ ff)
    {pa : ℕ}
    (hA0 : 0 < off J.wholeModel.W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pa + 0))
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
    {Vb Vf : Set Point} (hVb : Vb ∈ J.rightModel.regions S₂)
    (hVf : Vf ∈ J.rightModel.regions S₂)
    (hrel : Vf = V ∨ (GapLab J S₂ V ∧ GapLab J S₂ Vf))
    (hbT : (∃ c ∈ S₂x J S₂, fb ⊆ c ∧ SideOf J.rightModel ρ c Vb) ∨
      ((J.shared ∈ fb ∨ J.right.top ∈ fb) ∧
        ¬ (0 < off J.wholeModel.W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pbb + tbb) ∧
          off J.wholeModel.W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pbb + tbb) <
            ((rL1 J + rL2 J : ℕ) : ℝ))))
    (hfT : (∃ c ∈ S₂x J S₂, ff ⊆ c ∧ SideOf J.rightModel ρ c Vf) ∨
      ((J.shared ∈ ff ∨ J.right.top ∈ ff) ∧
        ¬ (0 < off J.wholeModel.W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pff + tff) ∧
          off J.wholeModel.W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pff + tff) <
            ((rL1 J + rL2 J : ℕ) : ℝ))))
    {p₀ : ℕ} {t₀ : ℝ} (hp₀ : p₀ < J.wholeModel.W.n) (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1)
    (hnc₀ : ¬ J.wholeModel.IsCut (F₂plus J S₂) (p₀ + t₀))
    (hfG₀ : J.wholeModel.Faces p₀ t₀ G)
    (ho₀ : ((rL1 J + rL2 J : ℕ) : ℝ) <
      off J.wholeModel.W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (p₀ + t₀)) :
    BracketConcl2 J S₂ ρ V
      (off J.wholeModel.W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (p₀ + t₀)) := by
  have hC := corr_right0 J hP hS₂.2.1 hS₂.1
  have hM := hC.hM
  have hFs := hC.hF
  have hg0 : (0 : ℝ) ≤ ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) := Nat.cast_nonneg _
  have hgn : ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) < J.wholeModel.W.n := by
    exact_mod_cast hC.hg
  set o := off J.wholeModel.W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) with hodef
  set L : ℝ := ((rL1 J + rL2 J : ℕ) : ℝ) with hLdef
  set o₀ := o (p₀ + t₀) with ho₀def
  set oA := o (pa + 0) with hoAdef
  -- the backward run
  obtain ⟨hb, hhb, pP, tP, pZ, tZ, hPa, hZa, hPZ, hSb, horib, -, hP0, hPL, hZout, hΦb⟩ :=
    chain_gen2 J hP hS₂ hF hρ (Or.inr rfl) hG hU (PhiK J S₂ oA)
      (propag_K2 J hP hS₂ hF oA) _ fb pa 0 pbb tbb Vb hVb (Or.inl rfl) le_rfl hfb hbA hbB hbne
      hbS hbo hbT hA0 hAL (fun _ _ _ _ _ _ _ _ _ _ _ _ hle => hle)
  obtain ⟨hLZb, hZb0⟩ := back_end J hP hS₂ hρ hG hhb hPa hZa hPZ hSb horib hPL hZout hp₀ ht₀
    hnc₀ hfG₀ ho₀
  obtain ⟨kP0, kP1⟩ := Corr.key_mem hPa.1 hPa.2.1 hPa.2.2.1
  obtain ⟨kA0, kA1⟩ := Corr.key_mem hbA.1 hbA.2.1 hbA.2.2.1
  -- the far attachment of `fb` is before `o₀`
  have hfbfar : ∀ (pw : ℕ) (tw : ℝ), SideAttach J.wholeModel.W fb pw tw →
      o₀ < o (pw + tw) → False := by
    intro pw tw hW hoW
    rcases key_of_two hM (hFs hfb) hbA hbB hbne hW with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · linarith
    · have hout : ¬ (0 < o (pw + tw) ∧ o (pw + tw) < L) := fun h => by linarith [h.2]
      have := back_end J hP hS₂ hρ hG hfb hbA hbB hbne hbS hbo hAL hout hp₀ ht₀ hnc₀ hfG₀ ho₀
      linarith [this.2]
  -- the base of the forward run
  have hbase : PhiI J S₂ o₀ ff oA := by
    intro e he hne pw tw pb tb hW hB hWB hoW hoB
    have heb : e ≠ fb := fun h => hfbfar pw tw (h ▸ hW) hoW
    have hehb : e ≠ hb := by
      rintro rfl
      rcases key_of_two hM (hFs he) hPa hZa hPZ hW with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> linarith
    obtain ⟨kB0, kB1⟩ := Corr.key_mem hB.1 hB.2.1 hB.2.2.1
    have hBP : o (pb + tb) ≤ o (pP + tP) := by
      by_contra hc
      push Not at hc
      have := no_cross_off hM hFs hF.1 hhb he (Ne.symm hehb) hPa hZa hPZ hB hW hg0 hgn
        (by linarith) hc (by linarith)
      linarith [this.2]
    have hle := hΦb e he hehb pw tw pb tb hW hB hWB (by linarith) hoB hBP
    rcases hle.lt_or_eq with h | h
    · exact h
    · exfalso
      have hk := off_inj hg0 hgn kB0 kB1 kA0 kA1 h
      obtain ⟨rfl, rfl⟩ := sideKey_inj hB.2.1 hB.2.2.1 hbA.2.1 hbA.2.2.1 hk
      rcases tie_third hM hFs hff hfb he (Ne.symm hbf) hfA hbA hB with h' | h'
      · exact hne h'
      · exact heb h'
  -- the forward run
  obtain ⟨hf, hhf, qP, sP, qZ, sZ, hQa, hZa', hQZ, hSf, horif, hTf, hQ0, hQL, hZout', hΦf⟩ :=
    chain_gen2 J hP hS₂ hF hρ (Or.inl rfl) hG hU (PhiI J S₂ o₀)
      (propag_I2 J hP hS₂ hF ho₀.le) _ ff pa 0 pff tff Vf hVf hrel le_rfl hff hfA hfF hfne hfS
      hfo hfT hA0 hAL hbase
  have hfe := fwd_end J hP hS₂ hρ hG hhf hQa hZa' hQZ hSf horif hQL hZout' hp₀ ht₀ hnc₀ hfG₀
    ho₀
  refine ⟨hf, hhf, qZ, sZ, hZa', hTf, hfe, ?_⟩
  intro e he pw tw pb tb hW hB hWB hoW hoZ hoB hB0
  obtain ⟨kB0, kB1⟩ := Corr.key_mem hB.1 hB.2.1 hB.2.2.1
  have hehf : e ≠ hf := by
    rintro rfl
    rcases key_of_two hM (hFs he) hQa hZa' hQZ hW with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · linarith
    · rcases hoZ with h | h <;> linarith
  have h1 := hΦf e he hehf pw tw pb tb hW hB hWB hoW hoB
  rcases hfe with hz | ⟨hLz, hz⟩
  · have hB0' := lt_of_le_of_ne (off_nonneg kB0 hgn) (Ne.symm hB0)
    have := no_cross_off hM hFs hF.1 hhf he (Ne.symm hehf) hZa' hQa (Ne.symm hQZ) hB hW hg0 hgn
      (by rwa [hz]) (by rwa [hz]) h1
    linarith [this.2]
  · rcases hoZ with h | h
    · linarith
    · have := no_cross_off hM hFs hF.1 hhf he (Ne.symm hehf) hQa hZa' hQZ hW hB hg0 hgn
        (by linarith) (by linarith) h
      linarith [this.1]

include hP hS₂ in
/-- **The bracket lemma.**  Let `G` be a region of `F₂⁺` without a label, on the side `ρ` of a
chord `e ⊆ c ∈ S₂` of `F₂⁺` attached at a position of the right stretch (not the base or the
split vertex), with `V` on the side `ρ` of `c`.  Then for every non-cut position of the `C₁` part
facing `G`, the next chord of `F₂⁺` with an attachment in the right stretch is a chord in a
chord of `S₂` with `V` on the side of `G` (or ends at the shared vertex) — `BracketConcl2`. -/
theorem bracket2
    (hF : J.wholeModel.ChordFamily Q (F₂plus J S₂)) {ρ : ℝ} (hρ : ρ = 1 ∨ ρ = -1)
    {G V : Set Point} (hG : G ∈ J.wholeModel.regions (F₂plus J S₂))
    (hV : V ∈ J.rightModel.regions S₂) (hU : ∀ V', ¬ RLabel J S₂ G V')
    {e c : Set Point} (he : e ∈ F₂plus J S₂) (hc : c ∈ S₂) (hec : e ⊆ c) {d : ℕ}
    (hd : d < rL1 J + rL2 J) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (hsec : t = 0 → d ≠ 0 ∧ d ≠ rL1 J)
    (heA : SideAttach J.wholeModel.W e
      ((6 + tpos J.whole J.m₁ + d) % J.wholeModel.W.n) t)
    (hGs : SideOf J.wholeModel ρ e G) (hVs : SideOf J.rightModel ρ c V)
    {p₀ : ℕ} {t₀ : ℝ} (hp₀ : p₀ < J.wholeModel.W.n) (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1)
    (hnc₀ : ¬ J.wholeModel.IsCut (F₂plus J S₂) (p₀ + t₀))
    (hfG₀ : J.wholeModel.Faces p₀ t₀ G)
    (ho₀ : ((rL1 J + rL2 J : ℕ) : ℝ) <
      off J.wholeModel.W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (p₀ + t₀)) :
    BracketConcl2 J S₂ ρ V
      (off J.wholeModel.W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (p₀ + t₀)) := by
  have hC := corr_right0 J hP hS₂.2.1 hS₂.1
  have hM := hC.hM
  have hFs := hC.hF
  have hcx := subset_S₂x J S₂ hc
  rcases local_step2 J hP hS₂ hF hd ht0 ht1 hsec he hcx hec heA hρ hG hV hGs hVs with
    hRL | ⟨rfl, f', hf', hne, hA', hS', hpart⟩
  · exact absurd hRL (hU V)
  have hd0 := (hsec rfl).1
  set W := J.wholeModel.W with hWdef
  set g := 6 + tpos J.whole J.m₁ with hgdef
  set A := (g + d) % W.n with hAdef
  obtain ⟨pb, tb, hB, hBne⟩ := hM.other_attach (hFs he) heA
  obtain ⟨pb', tb', hB', hBne'⟩ := hM.other_attach (hFs hf') hA'
  obtain ⟨θ, hθ, hori, hori'⟩ := tie_signs hρ (tie_opposite hM hFs he hf' hne heA hA' hB hB' hBne hBne')
  have hA0 := hC.off_M_pos hd le_rfl zero_lt_one fun _ => hd0
  have hAL := hC.off_M_lt hd le_rfl zero_lt_one
  have hTf' : (∃ c ∈ S₂x J S₂, f' ⊆ c ∧ SideOf J.rightModel ρ c V) ∨
      ((J.shared ∈ f' ∨ J.right.top ∈ f') ∧
        ¬ (0 < off W.n (g : ℝ) (pb' + tb') ∧ off W.n (g : ℝ) (pb' + tb') <
          ((rL1 J + rL2 J : ℕ) : ℝ))) := by
    rcases hpart with h | ⟨hk, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨hk, h pb' tb' hB' hBne'⟩
  rcases hθ with rfl | rfl
  · exact bracket_core2 J hP hS₂ hF hρ hG hU hf' he hne hA0 hAL hA' heA hB' hB
      (Ne.symm hBne') (Ne.symm hBne) hS' hGs (by linarith) hori hV hV (Or.inl rfl) hTf'
      (Or.inl ⟨c, hcx, hec, hVs⟩) hp₀ ht₀ hnc₀ hfG₀ ho₀
  · exact bracket_core2 J hP hS₂ hF hρ hG hU he hf' (Ne.symm hne) hA0 hAL heA hA' hB hB'
      (Ne.symm hBne) (Ne.symm hBne') hGs hS' hori (by linarith) hV hV (Or.inl rfl)
      (Or.inl ⟨c, hcx, hec, hVs⟩) hTf' hp₀ ht₀ hnc₀ hfG₀ ho₀

end


end ChainWalk2

end Sweep

end

end Chazelle.Core
