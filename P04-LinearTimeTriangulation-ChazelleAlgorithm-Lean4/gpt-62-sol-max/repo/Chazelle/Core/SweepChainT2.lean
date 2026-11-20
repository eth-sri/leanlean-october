module

public import Chazelle.Core.SweepChainT

/-!
# The sweep (WP-D), part 8c: the walk along a chain without `TopStrict` (F2)

The walk of `SweepChain.half_walk` with the enlarged family `S₂x` of the model of `C₂` and the
split step (`SweepChainT.split_step`): walking along a chain gives a label, a bound, or a pair of
gap labels (`GapPair`: the tracked region is a gap label and so is some label of the region).
Lemma (E) holds in the weakened form of (K3) (`label_side_gen2`).
-/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sideInArc sidePt sideLeft)
open Chazelle.Geometry (lerp)
open WalkEmbed

namespace Sweep

section Walk2

variable (J : Merge.Junction)

/-- **A pair of gap labels**: `V` is a gap label and some label of `G` is a gap label. -/
def GapPair (S₂ : Set (Set Point)) (G V : Set Point) : Prop :=
  GapLab J S₂ V ∧ ∃ Vg, GapLab J S₂ Vg ∧ RLabel J S₂ G Vg

section

variable (hP : J.P.Simple) {Q : Polygon}
    {S₂ : Set (Set Point)} (hS₂ : J.rightModel.ChordFamily Q S₂)
    (hF : J.wholeModel.ChordFamily Q (F₂plus J S₂)) {ρ θ : ℝ} (hρ : ρ = 1 ∨ ρ = -1)
    (hθ : θ = 1 ∨ θ = -1)
include hP hS₂ hF hρ hθ

/-- **Walking along a chain** without `TopStrict`.  As `half_walk`, with the chord of the model
of `C₂` in `S₂x`; the tracked region may switch sides of the slit at the split vertex, and the
walk ends with a label, a bound, or a pair of gap labels. -/
theorem half_walk2 {G : Set Point}
    (hG : G ∈ J.wholeModel.regions (F₂plus J S₂)) :
    ∀ (N d : ℕ) (t : ℝ) (f : Set Point) (pf : ℕ) (tf : ℝ) (V : Set Point),
      V ∈ J.rightModel.regions S₂ →
      (beyond (F₂plus J S₂) (θ * ρ) (sidePt J.wholeModel.W pf tf)).ncard ≤ N →
      d < rL1 J + rL2 J → 0 ≤ t → t < 1 → (t = 0 → d ≠ 0) → f ∈ F₂plus J S₂ →
      SideAttach J.wholeModel.W f
        ((6 + tpos J.whole J.m₁ + d) % J.wholeModel.W.n) t →
      SideAttach J.wholeModel.W f pf tf →
      sidePt J.wholeModel.W ((6 + tpos J.whole J.m₁ + d) % J.wholeModel.W.n) t ≠
        sidePt J.wholeModel.W pf tf →
      SideOf J.wholeModel ρ f G →
      0 < θ * ρ * ((sidePt J.wholeModel.W
        ((6 + tpos J.whole J.m₁ + d) % J.wholeModel.W.n) t).1 -
          (sidePt J.wholeModel.W pf tf).1) →
      (∃ c ∈ S₂x J S₂, f ⊆ c ∧ SideOf J.rightModel ρ c V) →
      RLabel J S₂ G V ∨ Bound J.wholeModel (F₂plus J S₂) G
        ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ((rL1 J + rL2 J : ℕ) : ℝ) θ
        (off J.wholeModel.W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ)
          ((((6 + tpos J.whole J.m₁ + d) % J.wholeModel.W.n : ℕ) : ℝ) + t)) ∨
        GapPair J S₂ G V := by
  have hC := corr_right0 J hP hS₂.2.1 hS₂.1
  have hM := hC.hM
  have hFs : F₂plus J S₂ ⊆ J.wholeModel.Adm := hC.hF
  have hg0 : (0 : ℝ) ≤ ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) := Nat.cast_nonneg _
  have hgn : ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) < J.wholeModel.W.n := by
    exact_mod_cast hC.hg
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro d t f pf tf V hV hN hd ht0 ht1 hd0 hf hfA hfF hNF hS hori htrack
  set W := J.wholeModel.W with hWdef
  set g := 6 + tpos J.whole J.m₁ with hgdef
  set L := rL1 J + rL2 J with hLdef
  have hoN := hC.off_M hd ht0 ht1
  have hN0 := hC.off_M_pos hd ht0 ht1 hd0
  have hNL := hC.off_M_lt hd ht0 ht1
  -- the bound through `f`, given a bound (or nothing) at the far end
  have hthrough : (∀ (p : ℕ) (t' : ℝ), p < W.n → t' ∈ Ioo (0 : ℝ) 1 →
      ¬ J.wholeModel.IsCut (F₂plus J S₂) (p + t') → J.wholeModel.Faces p t' G →
      0 < off W.n (g : ℝ) (p + t') → off W.n (g : ℝ) (p + t') < ((L : ℕ) : ℝ) →
      0 < θ * (off W.n (g : ℝ) (p + t') - off W.n (g : ℝ) (pf + tf)) ∨
        ((L : ℕ) : ℝ) ≤ off W.n (g : ℝ) (pf + tf) ∨ off W.n (g : ℝ) (pf + tf) ≤ 0) →
      Bound J.wholeModel (F₂plus J S₂) G (g : ℝ) ((L : ℕ) : ℝ) θ
        (off W.n (g : ℝ) ((((g + d) % W.n : ℕ) : ℝ) + t)) :=
    fun hpre => chord_bound hM hFs hf hfA hfF hNF hρ hG hS hθ hori hg0 hgn hN0 hNL hpre
  by_cases hin : 0 < off W.n (g : ℝ) (pf + tf) ∧ off W.n (g : ℝ) (pf + tf) < ((L : ℕ) : ℝ)
  swap
  · right; left
    refine hthrough fun _ _ _ _ _ _ _ _ => Or.inr ?_
    by_contra hc
    push Not at hc
    exact hin ⟨hc.2, hc.1⟩
  -- the far end is in the right stretch
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
  obtain ⟨c, hc, hfc, hVs⟩ := htrack
  -- the partner step: from a partner at the far end, a label, a bound or a gap pair there
  have hstep : ∀ (f' : Set Point) (V' : Set Point), tf = 0 → d' ≠ 0 → f' ∈ F₂plus J S₂ →
      f' ≠ f → SideAttach W f' ((g + d') % W.n) 0 → SideOf J.wholeModel ρ f' G →
      V' ∈ J.rightModel.regions S₂ →
      ((∃ c' ∈ S₂x J S₂, f' ⊆ c' ∧ SideOf J.rightModel ρ c' V') ∨
        ((J.shared ∈ f' ∨ J.right.top ∈ f') ∧ OffOut J f' ((g + d') % W.n) 0)) →
      RLabel J S₂ G V' ∨ Bound J.wholeModel (F₂plus J S₂) G (g : ℝ) ((L : ℕ) : ℝ) θ
        (off W.n (g : ℝ) ((((g + d') % W.n : ℕ) : ℝ) + 0)) ∨ GapPair J S₂ G V' := by
    intro f' V' htf0 hd'0 hf' hne hA' hS' hV' hpart
    subst htf0
    obtain ⟨pb, tb, hB, hBne⟩ := hM.other_attach (hFs hf') hA'
    set Pf := sidePt W ((g + d') % W.n) 0 with hPfdef
    set Pn := sidePt W ((g + d) % W.n) t with hPndef
    set Bp := sidePt W pb tb with hBpdef
    have hori' := tie_continue (tie_opposite hM hFs hf hf' hne hfF hA' hfA hB hNF hBne) hori
    rcases hpart with ⟨c', hc', hfc', hVs'⟩ | ⟨-, hoff⟩
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
      exact ih _ (lt_of_lt_of_le hlt hN) d' 0 f' pb tb V' hV' le_rfl hd' le_rfl zero_lt_one
        (fun _ => hd'0) hf' hA' hB (Ne.symm hBne) hS' hori' ⟨c', hc', hfc', hVs'⟩
    · -- the partner leaves the stretch
      right; left
      have hBout := hoff pb tb hB hBne
      refine chord_bound hM hFs hf' hA' hB (Ne.symm hBne) hρ hG hS' hθ hori' hg0 hgn (hC.off_M_pos hd' le_rfl zero_lt_one fun _ => hd'0)
        (hC.off_M_lt hd' le_rfl zero_lt_one)        fun _ _ _ _ _ _ _ _ => Or.inr ?_
      · by_contra hc
        push Not at hc
        exact hBout ⟨hc.2, hc.1⟩
  -- combining a result at the far end
  have hcomb : ∀ V' : Set Point, (V' = V ∨ (GapLab J S₂ V ∧ GapLab J S₂ V')) → tf = 0 →
      (RLabel J S₂ G V' ∨ Bound J.wholeModel (F₂plus J S₂) G (g : ℝ) ((L : ℕ) : ℝ) θ
        (off W.n (g : ℝ) ((((g + d') % W.n : ℕ) : ℝ) + 0)) ∨ GapPair J S₂ G V') →
      RLabel J S₂ G V ∨ Bound J.wholeModel (F₂plus J S₂) G (g : ℝ) ((L : ℕ) : ℝ) θ
        (off W.n (g : ℝ) ((((g + d) % W.n : ℕ) : ℝ) + t)) ∨ GapPair J S₂ G V := by
    intro V' hVV htf0 h
    subst htf0
    rcases h with hRL | hbd | ⟨hg', hgp⟩
    · rcases hVV with rfl | ⟨hgV, hgV'⟩
      · exact Or.inl hRL
      · exact Or.inr (Or.inr ⟨hgV, V', hgV', hRL⟩)
    · right; left
      exact hthrough fun p t' hp ht' hnc hfG h0 hL => Or.inl (hbd p t' hp ht' hnc hfG h0 hL)
    · rcases hVV with rfl | ⟨hgV, -⟩
      · exact Or.inr (Or.inr ⟨hg', hgp⟩)
      · exact Or.inr (Or.inr ⟨hgV, hgp⟩)
  by_cases hsplit : tf = 0 ∧ d' = rL1 J
  · obtain ⟨htf0, hdL⟩ := hsplit
    subst htf0
    subst hdL
    have hδ : 0 < rδ J := by
      by_contra h0
      have := hC.hδ (by omega)
      omega
    have hd'0 : rL1 J ≠ 0 := by
      intro h; rw [h] at hin1; simp at hin1
    rcases split_step J hP hS₂ hF hδ hf hc hfc hfF hρ hG hV hS hVs with
      hRL | hgp | ⟨hgV, f', hf', hne, hA', hS', hpart⟩
    · exact Or.inl hRL
    · exact Or.inr (Or.inr hgp)
    · rcases hpart with ⟨c', hc', hfc', V', hV', hVs', hgV'⟩ | hoff
      · exact hcomb V' (Or.inr ⟨hgV, hgV'⟩) rfl
          (hstep f' V' rfl hd'0 hf' hne hA' hS' hV' (Or.inl ⟨c', hc', hfc', hVs'⟩))
      · exact hcomb V (Or.inl rfl) rfl (hstep f' V rfl hd'0 hf' hne hA' hS' hV (Or.inr hoff))
  · have hsec' : tf = 0 → d' ≠ 0 ∧ d' ≠ rL1 J := by
      intro htf
      refine ⟨fun h => ?_, fun h => hsplit ⟨htf, h⟩⟩
      subst htf
      rw [h] at hin1
      simp at hin1
    rcases local_step2 J hP hS₂ hF hd' hfF.2.1 hfF.2.2.1 hsec' hf hc hfc hfF hρ hG hV hS hVs
      with hRL | ⟨htf0, f', hf', hne, hA', hS', hpart⟩
    · exact Or.inl hRL
    · subst htf0
      exact hcomb V (Or.inl rfl) rfl
        (hstep f' V rfl (hsec' rfl).1 hf' hne hA' hS' hV hpart)

/-- **The bound from one chord of a tie** without `TopStrict` (as `end_bound`). -/
theorem end_bound2 {G V : Set Point}
    (hG : G ∈ J.wholeModel.regions (F₂plus J S₂))
    (hV : V ∈ J.rightModel.regions S₂) {d : ℕ} (hd : d < rL1 J + rL2 J) (hd0 : d ≠ 0)
    {f : Set Point} (hf : f ∈ F₂plus J S₂)
    (hfA : SideAttach J.wholeModel.W f
      ((6 + tpos J.whole J.m₁ + d) % J.wholeModel.W.n) 0)
    {pb : ℕ} {tb : ℝ} (hB : SideAttach J.wholeModel.W f pb tb)
    (hBne : sidePt J.wholeModel.W pb tb ≠ sidePt J.wholeModel.W
      ((6 + tpos J.whole J.m₁ + d) % J.wholeModel.W.n) 0)
    (hS : SideOf J.wholeModel ρ f G)
    (hori : 0 < θ * ρ * ((sidePt J.wholeModel.W
      ((6 + tpos J.whole J.m₁ + d) % J.wholeModel.W.n) 0).1 -
        (sidePt J.wholeModel.W pb tb).1))
    (htr : (∃ c ∈ S₂x J S₂, f ⊆ c ∧ SideOf J.rightModel ρ c V) ∨
      ((J.shared ∈ f ∨ J.right.top ∈ f) ∧
        OffOut J f ((6 + tpos J.whole J.m₁ + d) % J.wholeModel.W.n) 0)) :
    RLabel J S₂ G V ∨ Bound J.wholeModel (F₂plus J S₂) G
      ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ((rL1 J + rL2 J : ℕ) : ℝ) θ
      (off J.wholeModel.W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ)
        ((((6 + tpos J.whole J.m₁ + d) % J.wholeModel.W.n : ℕ) : ℝ) + 0)) ∨
      GapPair J S₂ G V := by
  rcases htr with htr | ⟨-, hoff⟩
  · exact half_walk2 J hP hS₂ hF hρ hθ hG _ d 0 f pb tb V hV le_rfl hd le_rfl zero_lt_one
      (fun _ => hd0) hf hfA hB (Ne.symm hBne) hS hori htr
  right; left
  have hC := corr_right0 J hP hS₂.2.1 hS₂.1
  have hg0 : (0 : ℝ) ≤ ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) := Nat.cast_nonneg _
  have hgn : ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) < J.wholeModel.W.n := by
    exact_mod_cast hC.hg
  have hBout := hoff pb tb hB hBne
  refine chord_bound hC.hM hC.hF hf hfA hB (Ne.symm hBne) hρ hG hS hθ hori hg0 hgn (hC.off_M_pos hd le_rfl zero_lt_one fun _ => hd0)
    (hC.off_M_lt hd le_rfl zero_lt_one)    fun _ _ _ _ _ _ _ _ => Or.inr ?_
  · by_contra hc
    push Not at hc
    exact hBout ⟨hc.2, hc.1⟩

end

/-- A gap pair of `G` and a label of `G` make the (K3) alternative. -/
theorem gapPair_label (hP : J.P.Simple) {S₂ : Set (Set Point)}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hS₂f : S₂.Finite) {G V V' : Set Point}
    (hG : G ∈ J.wholeModel.regions (F₂plus J S₂))
    (hV' : V' ∈ J.rightModel.regions S₂) (hL : RLabel J S₂ G V')
    (hgp : GapPair J S₂ G V) : V' = V ∨ (GapLab J S₂ V' ∧ GapLab J S₂ V) := by
  obtain ⟨hgV, Vg, hgVg, hRLg⟩ := hgp
  right
  refine ⟨?_, hgV⟩
  rcases label_right3 J hP hS₂ hS₂f hG hV' hgVg.2.1 hL hRLg with rfl | ⟨h, -⟩
  · exact hgVg
  · exact h

/-- **Lemma (E) without `TopStrict`** (the weakened form of (K3)): let `e ∈ F₂⁺`, contained in
`c ∈ S₂`, be attached at a position of the right stretch (not the base or the split vertex),
`G` on the side `ρ` of `e` and `V` on the side `ρ` of `c`.  Then every label of `G` is `V`, or
it and `V` are gap labels. -/
theorem label_side_gen2 (hP : J.P.Simple) {Q : Polygon}
    {S₂ : Set (Set Point)} (hS₂ : J.rightModel.ChordFamily Q S₂)
    (hF : J.wholeModel.ChordFamily Q (F₂plus J S₂)) {d : ℕ} (hd : d < rL1 J + rL2 J)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (hsec : t = 0 → d ≠ 0 ∧ d ≠ rL1 J)
    {e c : Set Point} (he : e ∈ F₂plus J S₂) (hc : c ∈ S₂) (hec : e ⊆ c)
    (heA : SideAttach J.wholeModel.W e
      ((6 + tpos J.whole J.m₁ + d) % J.wholeModel.W.n) t)
    {ρ : ℝ} (hρ : ρ = 1 ∨ ρ = -1) {G V V' : Set Point}
    (hG : G ∈ J.wholeModel.regions (F₂plus J S₂))
    (hV : V ∈ J.rightModel.regions S₂) (hV' : V' ∈ J.rightModel.regions S₂)
    (hGs : SideOf J.wholeModel ρ e G) (hVs : SideOf J.rightModel ρ c V)
    (hL : RLabel J S₂ G V') : V' = V ∨ (GapLab J S₂ V' ∧ GapLab J S₂ V) := by
  have hC := corr_right0 J hP hS₂.2.1 hS₂.1
  have hM := hC.hM
  have hFs := hC.hF
  have hcx := subset_S₂x J S₂ hc
  rcases local_step2 J hP hS₂ hF hd ht0 ht1 hsec he hcx hec heA hρ hG hV hGs hVs with
    hRL | ⟨rfl, f', hf', hne, hA', hS', hpart⟩
  · exact label_right3 J hP hS₂.2.1 hS₂.1 hG hV' hV hL hRL
  have hd0 := (hsec rfl).1
  set W := J.wholeModel.W with hWdef
  set A := (6 + tpos J.whole J.m₁ + d) % W.n with hAdef
  obtain ⟨pb, tb, hB, hBne⟩ := hM.other_attach (hFs he) heA
  obtain ⟨pb', tb', hB', hBne'⟩ := hM.other_attach (hFs hf') hA'
  obtain ⟨θ, hθ, hori, hori'⟩ := tie_signs hρ (tie_opposite hM hFs he hf' hne heA hA' hB hB' hBne hBne')
  have hθ' : -θ = 1 ∨ -θ = -1 := by rcases hθ with rfl | rfl <;> norm_num
  rcases end_bound2 J hP hS₂ hF hρ hθ hG hV hd hd0 he heA hB hBne hGs hori
      (Or.inl ⟨c, hcx, hec, hVs⟩) with hRL | hb1 | hgp
  · exact label_right3 J hP hS₂.2.1 hS₂.1 hG hV' hV hL hRL
  · rcases end_bound2 J hP hS₂ hF hρ hθ' hG hV hd hd0 hf' hA' hB' hBne' hS' hori' hpart with
      hRL | hb2 | hgp
    · exact label_right3 J hP hS₂.2.1 hS₂.1 hG hV' hV hL hRL
    · exfalso
      obtain ⟨d'', hd'', t'', ht'', hnc, hfG, -⟩ := hL
      have hpos := hC.off_M_pos hd'' ht''.1.le ht''.2 fun h => (ht''.1.ne' h).elim
      have hlt := hC.off_M_lt hd'' ht''.1.le ht''.2
      have x1 := hb1 _ t'' (Nat.mod_lt _ hC.n_pos) ht'' hnc hfG hpos hlt
      have x2 := hb2 _ t'' (Nat.mod_lt _ hC.n_pos) ht'' hnc hfG hpos hlt
      linarith
    · exact gapPair_label J hP hS₂.2.1 hS₂.1 hG hV' hL hgp
  · exact gapPair_label J hP hS₂.2.1 hS₂.1 hG hV' hL hgp

end Walk2

end Sweep

end

end Chazelle.Core
