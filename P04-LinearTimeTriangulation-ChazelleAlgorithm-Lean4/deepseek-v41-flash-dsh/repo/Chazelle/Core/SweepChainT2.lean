module

public import Chazelle.Golf

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

/-- **Walking along a chain** without `TopStrict`.  As `half_walk`, with the chord of the model
of `C₂` in `S₂x`; the tracked region may switch sides of the slit at the split vertex, and the
walk ends with a label, a bound, or a pair of gap labels. -/
theorem half_walk2 (hP : J.P.Simple) {Q : Polygon}
    {S₂ : Set (Set Point)} (hS₂ : (chainModel J.right).ChordFamily Q S₂)
    (hF : (chainModel J.whole).ChordFamily Q (F₂plus J S₂)) {ρ θ : ℝ} (hρ : ρ = 1 ∨ ρ = -1)
    (hθ : θ = 1 ∨ θ = -1) {G : Set Point}
    (hG : G ∈ (chainModel J.whole).regions (F₂plus J S₂)) :
    ∀ (N d : ℕ) (t : ℝ) (f : Set Point) (pf : ℕ) (tf : ℝ) (V : Set Point),
      V ∈ (chainModel J.right).regions S₂ →
      (beyond (F₂plus J S₂) (θ * ρ) (sidePt (chainModel J.whole).W pf tf)).ncard ≤ N →
      d < rL1 J + rL2 J → 0 ≤ t → t < 1 → (t = 0 → d ≠ 0) → f ∈ F₂plus J S₂ →
      SideAttach (chainModel J.whole).W f
        ((6 + tpos J.whole J.m₁ + d) % (chainModel J.whole).W.n) t →
      SideAttach (chainModel J.whole).W f pf tf →
      sidePt (chainModel J.whole).W ((6 + tpos J.whole J.m₁ + d) % (chainModel J.whole).W.n) t ≠
        sidePt (chainModel J.whole).W pf tf →
      SideOf (chainModel J.whole) ρ f G →
      0 < θ * ρ * ((sidePt (chainModel J.whole).W
        ((6 + tpos J.whole J.m₁ + d) % (chainModel J.whole).W.n) t).1 -
          (sidePt (chainModel J.whole).W pf tf).1) →
      (∃ c ∈ S₂x J S₂, f ⊆ c ∧ SideOf (chainModel J.right) ρ c V) →
      RLabel J S₂ G V ∨ Bound (chainModel J.whole) (F₂plus J S₂) G
        ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ((rL1 J + rL2 J : ℕ) : ℝ) θ
        (off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ)
          ((((6 + tpos J.whole J.m₁ + d) % (chainModel J.whole).W.n : ℕ) : ℝ) + t)) ∨
        GapPair J S₂ G V := by
  have hC := corr_right0 J hP hS₂.2.1 hS₂.1
  have hM := hC.hM
  have hFs := hC.hF
  have hg0 : (0 : ℝ) ≤ ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) := Nat.cast_nonneg _
  have hgn : ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) < (chainModel J.whole).W.n := by
    exact_mod_cast hC.hg
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro d t f pf tf V hV hN hd ht0 ht1 hd0 hf hfA hfF hNF hS hori htrack
  set W := (chainModel J.whole).W with hWdef
  set g := 6 + tpos J.whole J.m₁ with hgdef
  set L := rL1 J + rL2 J with hLdef
  have hoN : off W.n (g : ℝ) ((((g + d) % W.n : ℕ) : ℝ) + t) = d + t := hC.off_M hd ht0 ht1
  have hN0 : 0 < off W.n (g : ℝ) ((((g + d) % W.n : ℕ) : ℝ) + t) := by
    Ξ hoN
    rcases ht0.lt_or_eq with h | h
    · have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      linarith
    · have := hd0 h.symm
      have : (1 : ℝ) ≤ d := by exact_mod_cast Nat.one_le_iff_ne_zero.2 this
      linarith
  have hNL : off W.n (g : ℝ) ((((g + d) % W.n : ℕ) : ℝ) + t) < ((L : ℕ) : ℝ) := by
    Ξ hoN
    have : (d : ℝ) + 1 ≤ ((L : ℕ) : ℝ) := by exact_mod_cast hd
    linarith
  -- the bound through `f`, given a bound (or nothing) at the far end
  have hthrough : (∀ (p : ℕ) (t' : ℝ), p < W.n → t' ∈ Ioo (0 : ℝ) 1 →
      ¬ (chainModel J.whole).IsCut (F₂plus J S₂) (p + t') → (chainModel J.whole).Faces p t' G →
      0 < off W.n (g : ℝ) (p + t') → off W.n (g : ℝ) (p + t') < ((L : ℕ) : ℝ) →
      0 < θ * (off W.n (g : ℝ) (p + t') - off W.n (g : ℝ) (pf + tf)) ∨
        ((L : ℕ) : ℝ) ≤ off W.n (g : ℝ) (pf + tf) ∨ off W.n (g : ℝ) (pf + tf) ≤ 0) →
      Bound (chainModel J.whole) (F₂plus J S₂) G (g : ℝ) ((L : ℕ) : ℝ) θ
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
      f' ≠ f → SideAttach W f' ((g + d') % W.n) 0 → SideOf (chainModel J.whole) ρ f' G →
      V' ∈ (chainModel J.right).regions S₂ →
      ((∃ c' ∈ S₂x J S₂, f' ⊆ c' ∧ SideOf (chainModel J.right) ρ c' V') ∨
        ((J.shared ∈ f' ∨ J.right.top ∈ f') ∧ OffOut J f' ((g + d') % W.n) 0)) →
      RLabel J S₂ G V' ∨ Bound (chainModel J.whole) (F₂plus J S₂) G (g : ℝ) ((L : ℕ) : ℝ) θ
        (off W.n (g : ℝ) ((((g + d') % W.n : ℕ) : ℝ) + 0)) ∨ GapPair J S₂ G V' := by
    intro f' V' htf0 hd'0 hf' hne hA' hS' hV' hpart
    subst htf0
    obtain ⟨pb, tb, hB, hBne⟩ := hM.other_attach (hFs hf') hA'
    set Pf := sidePt W ((g + d') % W.n) 0 with hPfdef
    set Pn := sidePt W ((g + d) % W.n) t with hPndef
    set Bp := sidePt W pb tb with hBpdef
    obtain ⟨-, hyf, -⟩ := hM.attach_seg (hFs hf) hfA hfF hNF
    obtain ⟨-, hyf', -⟩ := hM.attach_seg (hFs hf') hA' hB (Ne.symm hBne)
    have hPn1 : Pn.1 ≠ Pf.1 := fun h => hNF (Geometry.point_ext h hyf)
    have hB1 : Bp.1 ≠ Pf.1 := fun h => hBne (Geometry.point_ext h hyf'.symm)
    have hopp := tie_opposite hM hFs hf hf' hne hfF hA' hfA.2.2.2.1 hB.2.2.2.1 hPn1 hB1
    have hθρ : θ * ρ * θ * ρ = 1 := by
      rcases hθ with rfl | rfl <;> rcases hρ with rfl | rfl <;> norm_num
    have hori' : 0 < θ * ρ * (Pf.1 - Bp.1) := by
      have h1 := hori
      nlinarith [mul_pos h1 h1]
    rcases hpart with ⟨c', hc', hfc', hVs'⟩ | ⟨-, hoff⟩
    · -- recursion along the partner
      have hlt : (beyond (F₂plus J S₂) (θ * ρ) Bp).ncard <
          (beyond (F₂plus J S₂) (θ * ρ) Pf).ncard := by
        refine Set.ncard_lt_ncard ?_ (hF.1.subset fun h hh => hh.1)
        refine ⟨fun h ⟨hh, z, hz, hz'⟩ => ⟨hh, z, hz, ?_⟩, fun hsub => ?_⟩
        · have e : θ * ρ * (Pf.1 - z.1) = θ * ρ * (Pf.1 - Bp.1) + θ * ρ * (Bp.1 - z.1) := by
            ring
          Ξ e
          exact add_pos hori' hz'
        · obtain ⟨-, z, hz, hz'⟩ := hsub ⟨hf', Bp, hB.2.2.2.1, hori'⟩
          obtain ⟨hseg', -, -, -, -⟩ := hM.attach_seg (hFs hf') hA' hB (Ne.symm hBne)
          rw [hseg'] at hz
          obtain ⟨s, hs0, hs1, rfl⟩ := Geometry.mem_segment_iff_lerp.1 hz
          simp only [Geometry.lerp_fst] at hz'
          have : θ * ρ * (Bp.1 - (Pf.1 + s * (Bp.1 - Pf.1))) =
              (1 - s) * (θ * ρ * (Bp.1 - Pf.1)) := ⋆
          nlinarith
      exact ih _ (lt_of_lt_of_le hlt hN) d' 0 f' pb tb V' hV' le_rfl hd' le_rfl zero_lt_one
        (fun _ => hd'0) hf' hA' hB (Ne.symm hBne) hS' hori' ⟨c', hc', hfc', hVs'⟩
    · -- the partner leaves the stretch
      right; left
      have hBout := hoff pb tb hB hBne
      have hoF0 := hC.off_M hd' (t := 0) le_rfl zero_lt_one
      refine chord_bound hM hFs hf' hA' hB (Ne.symm hBne) hρ hG hS' hθ hori' hg0 hgn ?_ ?_
        fun _ _ _ _ _ _ _ _ => Or.inr ?_
      · Ξ hoF0
        have : (1 : ℝ) ≤ d' := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hd'0
        linarith
      · Ξ hoF0
        have : (d' : ℝ) + 1 ≤ ((L : ℕ) : ℝ) := by exact_mod_cast hd'
        linarith
      · by_contra hc
        push Not at hc
        exact hBout ⟨hc.2, hc.1⟩
  -- combining a result at the far end
  have hcomb : ∀ V' : Set Point, (V' = V ∨ (GapLab J S₂ V ∧ GapLab J S₂ V')) → tf = 0 →
      (RLabel J S₂ G V' ∨ Bound (chainModel J.whole) (F₂plus J S₂) G (g : ℝ) ((L : ℕ) : ℝ) θ
        (off W.n (g : ℝ) ((((g + d') % W.n : ℕ) : ℝ) + 0)) ∨ GapPair J S₂ G V') →
      RLabel J S₂ G V ∨ Bound (chainModel J.whole) (F₂plus J S₂) G (g : ℝ) ((L : ℕ) : ℝ) θ
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
      have := hC.hδ (⋄)
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
theorem end_bound2 (hP : J.P.Simple) {Q : Polygon}
    {S₂ : Set (Set Point)} (hS₂ : (chainModel J.right).ChordFamily Q S₂)
    (hF : (chainModel J.whole).ChordFamily Q (F₂plus J S₂)) {ρ θ : ℝ} (hρ : ρ = 1 ∨ ρ = -1)
    (hθ : θ = 1 ∨ θ = -1) {G V : Set Point}
    (hG : G ∈ (chainModel J.whole).regions (F₂plus J S₂))
    (hV : V ∈ (chainModel J.right).regions S₂) {d : ℕ} (hd : d < rL1 J + rL2 J) (hd0 : d ≠ 0)
    {f : Set Point} (hf : f ∈ F₂plus J S₂)
    (hfA : SideAttach (chainModel J.whole).W f
      ((6 + tpos J.whole J.m₁ + d) % (chainModel J.whole).W.n) 0)
    {pb : ℕ} {tb : ℝ} (hB : SideAttach (chainModel J.whole).W f pb tb)
    (hBne : sidePt (chainModel J.whole).W pb tb ≠ sidePt (chainModel J.whole).W
      ((6 + tpos J.whole J.m₁ + d) % (chainModel J.whole).W.n) 0)
    (hS : SideOf (chainModel J.whole) ρ f G)
    (hori : 0 < θ * ρ * ((sidePt (chainModel J.whole).W
      ((6 + tpos J.whole J.m₁ + d) % (chainModel J.whole).W.n) 0).1 -
        (sidePt (chainModel J.whole).W pb tb).1))
    (htr : (∃ c ∈ S₂x J S₂, f ⊆ c ∧ SideOf (chainModel J.right) ρ c V) ∨
      ((J.shared ∈ f ∨ J.right.top ∈ f) ∧
        OffOut J f ((6 + tpos J.whole J.m₁ + d) % (chainModel J.whole).W.n) 0)) :
    RLabel J S₂ G V ∨ Bound (chainModel J.whole) (F₂plus J S₂) G
      ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ((rL1 J + rL2 J : ℕ) : ℝ) θ
      (off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ)
        ((((6 + tpos J.whole J.m₁ + d) % (chainModel J.whole).W.n : ℕ) : ℝ) + 0)) ∨
      GapPair J S₂ G V := by
  rcases htr with htr | ⟨-, hoff⟩
  · exact half_walk2 J hP hS₂ hF hρ hθ hG _ d 0 f pb tb V hV le_rfl hd le_rfl zero_lt_one
      (fun _ => hd0) hf hfA hB (Ne.symm hBne) hS hori htr
  right; left
  have hC := corr_right0 J hP hS₂.2.1 hS₂.1
  have hg0 : (0 : ℝ) ≤ ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) := Nat.cast_nonneg _
  have hgn : ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) < (chainModel J.whole).W.n := by
    exact_mod_cast hC.hg
  have hBout := hoff pb tb hB hBne
  have hoF0 := hC.off_M hd (t := 0) le_rfl zero_lt_one
  refine chord_bound hC.hM hC.hF hf hfA hB (Ne.symm hBne) hρ hG hS hθ hori hg0 hgn ?_ ?_
    fun _ _ _ _ _ _ _ _ => Or.inr ?_
  · Ξ hoF0
    have : (1 : ℝ) ≤ d := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hd0
    linarith
  · Ξ hoF0
    have : (d : ℝ) + 1 ≤ ((rL1 J + rL2 J : ℕ) : ℝ) := by exact_mod_cast hd
    linarith
  · by_contra hc
    push Not at hc
    exact hBout ⟨hc.2, hc.1⟩

/-- A gap pair of `G` and a label of `G` make the (K3) alternative. -/
theorem gapPair_label (hP : J.P.Simple) {S₂ : Set (Set Point)}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hS₂f : S₂.Finite) {G V V' : Set Point}
    (hG : G ∈ (chainModel J.whole).regions (F₂plus J S₂))
    (hV' : V' ∈ (chainModel J.right).regions S₂) (hL : RLabel J S₂ G V')
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
    {S₂ : Set (Set Point)} (hS₂ : (chainModel J.right).ChordFamily Q S₂)
    (hF : (chainModel J.whole).ChordFamily Q (F₂plus J S₂)) {d : ℕ} (hd : d < rL1 J + rL2 J)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (hsec : t = 0 → d ≠ 0 ∧ d ≠ rL1 J)
    {e c : Set Point} (he : e ∈ F₂plus J S₂) (hc : c ∈ S₂) (hec : e ⊆ c)
    (heA : SideAttach (chainModel J.whole).W e
      ((6 + tpos J.whole J.m₁ + d) % (chainModel J.whole).W.n) t)
    {ρ : ℝ} (hρ : ρ = 1 ∨ ρ = -1) {G V V' : Set Point}
    (hG : G ∈ (chainModel J.whole).regions (F₂plus J S₂))
    (hV : V ∈ (chainModel J.right).regions S₂) (hV' : V' ∈ (chainModel J.right).regions S₂)
    (hGs : SideOf (chainModel J.whole) ρ e G) (hVs : SideOf (chainModel J.right) ρ c V)
    (hL : RLabel J S₂ G V') : V' = V ∨ (GapLab J S₂ V' ∧ GapLab J S₂ V) := by
  have hC := corr_right0 J hP hS₂.2.1 hS₂.1
  have hM := hC.hM
  have hFs := hC.hF
  have hcx : c ∈ S₂x J S₂ := subset_S₂x J S₂ hc
  rcases local_step2 J hP hS₂ hF hd ht0 ht1 hsec he hcx hec heA hρ hG hV hGs hVs with
    hRL | ⟨rfl, f', hf', hne, hA', hS', hpart⟩
  · exact label_right3 J hP hS₂.2.1 hS₂.1 hG hV' hV hL hRL
  have hd0 : d ≠ 0 := (hsec rfl).1
  set W := (chainModel J.whole).W with hWdef
  set A := (6 + tpos J.whole J.m₁ + d) % W.n with hAdef
  obtain ⟨pb, tb, hB, hBne⟩ := hM.other_attach (hFs he) heA
  obtain ⟨pb', tb', hB', hBne'⟩ := hM.other_attach (hFs hf') hA'
  obtain ⟨-, hy, -⟩ := hM.attach_seg (hFs he) heA hB (Ne.symm hBne)
  obtain ⟨-, hy', -⟩ := hM.attach_seg (hFs hf') hA' hB' (Ne.symm hBne')
  set Pa := sidePt W A 0 with hPadef
  set Bp := sidePt W pb tb with hBpdef
  set Bq := sidePt W pb' tb' with hBqdef
  have h1 : Bp.1 ≠ Pa.1 := fun h => hBne (Geometry.point_ext h hy.symm)
  have h1' : Bq.1 ≠ Pa.1 := fun h => hBne' (Geometry.point_ext h hy'.symm)
  have hopp := tie_opposite hM hFs he hf' hne heA hA' hB.2.2.2.1 hB'.2.2.2.1 h1 h1'
  obtain ⟨θ, hθ, hori⟩ := exists_sign hρ (sub_ne_zero.2 (Ne.symm h1))
  have hθρ : θ * ρ * (θ * ρ) = 1 := by
    rcases hθ with rfl | rfl <;> rcases hρ with rfl | rfl <;> norm_num
  have hori' : 0 < -θ * ρ * (Pa.1 - Bq.1) := by
    have e1 : -θ * ρ * (Pa.1 - Bq.1) = θ * ρ * (Bq.1 - Pa.1) := ⋆
    Ξ e1
    have hprod : 0 < (θ * ρ * (Pa.1 - Bp.1)) * (θ * ρ * (Bq.1 - Pa.1)) := by
      have e2 : (θ * ρ * (Pa.1 - Bp.1)) * (θ * ρ * (Bq.1 - Pa.1)) =
          (θ * ρ * (θ * ρ)) * (-((Bp.1 - Pa.1) * (Bq.1 - Pa.1))) := ⋆
      Ξ e2, hθρ, one_mul
      linarith
    exact pos_of_mul_pos_right hprod hori.le
  have hθ' : -θ = 1 ∨ -θ = -1 := by rcases hθ with rfl | rfl <;> norm_num
  rcases end_bound2 J hP hS₂ hF hρ hθ hG hV hd hd0 he heA hB hBne hGs hori
      (Or.inl ⟨c, hcx, hec, hVs⟩) with hRL | hb1 | hgp
  · exact label_right3 J hP hS₂.2.1 hS₂.1 hG hV' hV hL hRL
  · rcases end_bound2 J hP hS₂ hF hρ hθ' hG hV hd hd0 hf' hA' hB' hBne' hS' hori' hpart with
      hRL | hb2 | hgp
    · exact label_right3 J hP hS₂.2.1 hS₂.1 hG hV' hV hL hRL
    · exfalso
      obtain ⟨d'', hd'', t'', ht'', hnc, hfG, -⟩ := hL
      have ho := hC.off_M hd'' ht''.1.le ht''.2
      have hpos : 0 < off W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ)
          ((((6 + tpos J.whole J.m₁ + d'') % W.n : ℕ) : ℝ) + t'') := by
        rw [ho]; have : (0 : ℝ) ≤ d'' := Nat.cast_nonneg _; linarith [ht''.1]
      have hlt : off W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ)
          ((((6 + tpos J.whole J.m₁ + d'') % W.n : ℕ) : ℝ) + t'') <
            ((rL1 J + rL2 J : ℕ) : ℝ) := by
        rw [ho]; have : (d'' : ℝ) + 1 ≤ ((rL1 J + rL2 J : ℕ) : ℝ) := by exact_mod_cast hd''
        linarith [ht''.2]
      have x1 := hb1 _ t'' (Nat.mod_lt _ hC.n_pos) ht'' hnc hfG hpos hlt
      have x2 := hb2 _ t'' (Nat.mod_lt _ hC.n_pos) ht'' hnc hfG hpos hlt
      linarith
    · exact gapPair_label J hP hS₂.2.1 hS₂.1 hG hV' hL hgp
  · exact gapPair_label J hP hS₂.2.1 hS₂.1 hG hV' hL hgp

end Walk2

end Sweep

end

end Chazelle.Core
