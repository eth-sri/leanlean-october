module

public import Chazelle.Golf

public import Chazelle.Core.FactsAttach
public import Chazelle.Core.NFLocateMath

/-!
# WP-B, part 2: arc cover (C9) and the side faced after an attachment (C10)

* `arcCover : NFLoc.ArcCoverSpec` (finding C9): every chord family of a good model has an arc,
  and every cut key is the start of an arc.  For `F = ∅` the domain is the only region and the
  pinned arc `(0, 0)` covers the walk; otherwise the gap after a cut key is an arc
  (`WalkAx.attach_face`).
* `UpSideSpec` and `upSide : UpSideSpec` (finding C10): for a chord `c` of an admissible family
  attached at a walk position `A` at which no other chord of the family is attached, the walk
  just after `A` faces the region **below** `c` and just before `A` the region **above** `c`
  when the point of `A` is the **left** (lower-`x`) endpoint of `c`, and the other way round when
  it is the right endpoint.

  For `BuildNF`: with a chord record `r` (left endpoint at `r.lpos`, right endpoint at `r.rpos`),
  the region faced just **before** the left endpoint and just **after** the right endpoint is
  `r.up`; the region faced just **after** the left endpoint and just **before** the right endpoint
  is `r.dn`.

  Why: the walk keeps the domain on its left.  At the left endpoint `a` the chord leaves eastward
  into the left sector of the walk; the side-aware Lemma 2.1 (`Chain.sideArc_split`) says that the
  positions strictly between the attachment at `a` and the attachment at the right endpoint `b`
  have their left sectors in the component `K₁` of `D \ c` lying on the left of `b → a`, i.e.
  *below* the chord (the left normal of a westward segment points down).  Sanity check on a
  counterclockwise square with a chord from the west side to the east side: the walk goes down
  the west side, so just after the chord's left endpoint it is below the chord.  The same holds in
  the chain model (the walk is `sideWalk`, domain on the left, `sideArc_split` is generic).
-/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sideInArc sidePt SideFaces freeIn regionsIn TouchesIn
  sideArc_split)
open Chazelle.Jordan (offset nrm)
open Chazelle.Geometry (lerp point_ext lerp_mem_segment)

/-! ## C9: the arc cover -/

/-- **WP-B (finding C9): the arc cover.**  Every chord family of a good model has an arc, and
every cut key is the start of an arc. -/
theorem arcCover : NFLoc.ArcCoverSpec := by
  intro M Q F hM hF
  have hW := walkAx_of_goodModel hM
  obtain ⟨hfin, hAdm, -⟩ := hF
  have hstart : ∀ y : ℝ, M.IsCut F y → ∃ U ∈ M.regions F, ∃ b : ℝ, M.IsArc F U y b := by
    rintro y ⟨c, hc, p, t, hA, rfl⟩
    obtain ⟨U, -, -, r, hU, -, -, harc, -⟩ := hW.attach_face hAdm hfin hc hA
    exact ⟨U, hU, r, harc⟩
  refine ⟨?_, hstart⟩
  rcases F.eq_empty_or_nonempty with rfl | hne
  · obtain ⟨z, hz⟩ := hW.nonempty
    have hfree : freeIn M.D ∅ = M.D := ⊚ freeIn
    have hall : ∀ U ∈ M.regions (∅ : Set (Set Point)), U = M.D := by
      rintro U ⟨z', hz', rfl⟩
      rw [hfree] at hz' ⊢
      exact hW.preconn.connectedComponentIn hz'
    have hU : connectedComponentIn M.D z ∈ M.regions (∅ : Set (Set Point)) :=
      ⟨z, by rw [hfree]; exact hz, Ρ hfree⟩
    have hnocut : ∀ x, ¬ M.IsCut ∅ x := fun x ⟨c, hc, _⟩ => hc
    obtain ⟨p₀, t₀, hp₀, -, -, -⟩ := hW.exists_faces (empty_subset _) finite_empty hU
    have hn : (0 : ℝ) < M.W.n := by exact_mod_cast (Nat.zero_lt_of_lt hp₀)
    refine ⟨_, hU, 0, 0, le_rfl, hn, le_rfl, hn, Or.inr ⟨rfl, rfl, rfl⟩,
      fun x _ => hnocut x, fun p t hp ht0 ht1 _ => ?_⟩
    obtain ⟨U', hU', hf⟩ :=
      hW.exists_faces_of_not_cut (empty_subset _) finite_empty hp ⟨ht0, ht1⟩ (hnocut _)
    Ξ hall _ hU, ← hall _ hU'
    exact hf
  · obtain ⟨c, hc⟩ := hne
    obtain ⟨-, -, -, -, -, -, ⟨⟨p, t, hA, -⟩, -⟩, -⟩ := hW.ends c (hAdm hc)
    obtain ⟨U, hU, b, harc⟩ := hstart _ ⟨c, hc, p, t, hA, rfl⟩
    exact ⟨U, hU, _, b, harc⟩

/-! ## C10: which side the walk faces after an attachment -/

/-- Rescaling a right-neighbourhood of `0` by a positive factor. -/
theorem eventually_mul_pos {P : ℝ → Prop} (h : ∀ᶠ ε in 𝓝[>] (0 : ℝ), P ε) {w : ℝ} (hw : 0 < w) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ), P (δ * w) := by
  have ht : Tendsto (fun δ : ℝ => δ * w) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    Ξ tendsto_nhdsWithin_iff
    refine ⟨?_, ?_⟩
    · have : Tendsto (fun δ : ℝ => δ * w) (𝓝 (0 : ℝ)) (𝓝 (0 * w)) :=
        (continuous_id.mul continuous_const).tendsto 0
      rw [zero_mul] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with δ hδ
      exact mul_pos hδ hw
  exact ht.eventually h

/-- The offsets of the midpoint of a horizontal segment. -/
theorem offset_mid_ab {a b : Point} (hy : a.2 = b.2) (δ : ℝ) :
    offset a b (1 / 2) δ = ((lerp a b (1 / 2)).1, (lerp a b (1 / 2)).2 + δ * (b.1 - a.1)) := by
  apply point_ext <;> simp [offset, nrm, lerp, hy]

namespace WalkAx

variable {M : Model}

/-- **The side faced after an attachment** (walk-axiom form).  Let `c ∈ F` be attached at `A`
(point `a`) and at `B` (point `b ≠ a`).  If a region `U` faces the walk at a position strictly
between `A` and `B` (inside a walk edge), then `U` does not contain the points just on the left of
`a → b` at the midpoint of `c` (equivalently: those points are on the other side of `c`). -/
theorem not_left_of_after (hM : WalkAx M) {F : Set (Set Point)} (hF : F ⊆ M.Adm)
    {c : Set Point} (hc : c ∈ F) {pa pb : ℕ} {ta tb : ℝ} (hA : SideAttach M.W c pa ta)
    (hB : SideAttach M.W c pb tb) (hAB : sidePt M.W pa ta ≠ sidePt M.W pb tb)
    {U : Set Point} (hU : U ∈ M.regions F) {p : ℕ} (hp : p < M.W.n) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) (hin : sideInArc (pa + ta) (pb + tb) (p + t)) (hf : M.Faces p t U) :
    ¬ ∀ᶠ δ in 𝓝[>] (0 : ℝ), offset (sidePt M.W pa ta) (sidePt M.W pb tb) (1 / 2) δ ∈ U := by
  intro hleft
  have hcA := hF hc
  obtain ⟨hcab, hy, hopen, hEA, hEB⟩ := hM.attach_seg hcA hA hB hAB
  have hA' := hA
  have hB' := hB
  rw [hcab] at hA' hB'
  have hsep := hM.hsep hcA hcab hAB hy hopen
  obtain ⟨K₁, K₂, -, ⟨c₁, hK₁⟩, -, hsec₁, -, hF₁, -⟩ := sideArc_split M.W hM.isOpen hAB hM.nd
    hM.trace hM.clean hopen hA' rfl hB' rfl
    (fun p hp t ht ht1 hne' heq => hEA.2 pa p ta t hA.1 hA.2.1 hA.2.2.1 hp ht ht1
      (fun h => fun h' => hne' h.symm h'.symm) rfl heq)
    (fun p hp t ht ht1 hne' heq => hEB.2 pb p tb t hB.1 hB.2.1 hB.2.2.1 hp ht ht1
      (fun h => fun h' => hne' h.symm h'.symm) rfl heq)
    hsep
  rw [← hcab] at hK₁
  subst hK₁
  have hsub : U ⊆ connectedComponentIn (M.D \ c) c₁ :=
    hM.region_subset_of_sector hc hU hp ht hf (hsec₁ p hp t ht.1.le ht.2 hin)
  obtain ⟨δ, h1, h2, h3⟩ := (hleft.and (hF₁.and hsep)).exists
  rw [← hcab] at h3
  apply h3
  Ξ ← connectedComponentIn_eq (hsub h1), ← connectedComponentIn_eq h2

end WalkAx

/-- **WP-B (finding C10): the side faced after an attachment.** -/
theorem upSide : UpSideSpec := by
  intro M Q F hM hF c hc p t hA hsole
  have hW := walkAx_of_goodModel hM
  have hAdm := hF.2.1
  obtain ⟨U, V, hU, hV, hUV, hcU, hcV, δ, hδ, hfac⟩ := attachFaceNC M Q F hM hF c hc p t hA hsole
  obtain ⟨Up, Dn, hUp, hDn, hUD, hside, htouch⟩ := chordSides M Q F hM hF c hc
  have hU2 := (htouch U hU).1 hcU
  have hV2 := (htouch V hV).1 hcV
  -- the other attachment
  obtain ⟨pb, tb, hB, hBne⟩ := hW.other_attach (hAdm hc) hA
  have hAB : sidePt M.W p t ≠ sidePt M.W pb tb := Ne.symm hBne
  obtain ⟨hcab, hy, hopen, -, -⟩ := hW.attach_seg (hAdm hc) hA hB hAB
  have hkne : (p : ℝ) + t ≠ pb + tb := WalkAx.key_ne_of_pt_ne hA hB hAB
  -- a position just after `A`, facing `U`
  obtain ⟨ε, hε1, hε2, hε3⟩ := ((WalkAx.exists_pos_after hA.2.1 hA.2.2.1).and
    ((WalkAx.eventually_after_start hkne).and (Ioo_mem_nhdsGT hδ))).exists
  have hin : sideInArc (p + t) (pb + tb) (p + (t + ε)) := by rw [← add_assoc]; exact hε2
  have hfU : M.Faces p (t + ε) U := (hfac p (t + ε) hA.1 hε1.1 hε1.2).1
    (Or.inl ⟨by linarith [hε3.1], by linarith [hε3.2]⟩)
  have hnot := hW.not_left_of_after hAdm hc hA hB hAB hU hA.1 hε1 hin hfU
  -- the midpoint of the chord
  set a := sidePt M.W p t with ha
  set b := sidePt M.W pb tb with hb
  have hmid : lerp a b (1 / 2) ∈ c := by
    rw [hcab]; exact lerp_mem_segment _ _ (⊛) (⊛)
  have hmidD : lerp a b (1 / 2) ∈ M.D := hopen _ ⟨⊛, ⊛⟩
  have hsm := hside _ hmid hmidD
  have hbc : b ∈ c := by rw [hcab]; exact Geometry.right_mem_segment _ _
  have hne1 : a.1 ≠ b.1 := fun h => hAB (point_ext h hy)
  have hpt : lerp (M.wa p) (M.wb p) t = a := rfl
  have hBelow : M.BelowOf c Dn := fun z hz hzD => (hside z hz hzD).mono fun _ h => h.2
  have hAbove : M.AboveOf c Up := fun z hz hzD => (hside z hz hzD).mono fun _ h => h.1
  refine ⟨U, V, hU, hV, hUV, ⟨δ, hδ, hfac⟩, fun hleft => ?_, fun hright => ?_⟩
  · -- `a` is the left endpoint: `U` is below
    have hlt : a.1 < b.1 := lt_of_le_of_ne (hpt ▸ hleft b hbc) hne1
    have hUDn : U = Dn := by
      rcases hU2 with h | h
      · exfalso
        apply hnot
        have := eventually_mul_pos (hsm.mono fun _ h => h.1) (sub_pos.2 hlt)
        Ξ h
        refine this.mono fun δ' h' => ?_
        Ξ offset_mid_ab hy
        exact h'
      · exact h
    have hVUp : V = Up := by
      rcases hV2 with h | h
      · exact h
      · exact absurd (hUDn.trans h.symm) hUV
    Ξ hUDn, hVUp
    exact ⟨hBelow, hAbove⟩
  · -- `a` is the right endpoint: `U` is above
    have hlt : b.1 < a.1 := lt_of_le_of_ne (hpt ▸ hright b hbc) (Ne.symm hne1)
    have hUUp : U = Up := by
      rcases hU2 with h | h
      · exact h
      · exfalso
        apply hnot
        have := eventually_mul_pos (hsm.mono fun _ h => h.2) (sub_pos.2 hlt)
        Ξ h
        refine this.mono fun δ' h' => ?_
        Ξ offset_mid_ab hy
        convert h' using 2
        ring
    have hVDn : V = Dn := by
      rcases hV2 with h | h
      · exact absurd (hUUp.trans h.symm) hUV
      · exact h
    Ξ hUUp, hVDn
    exact ⟨hAbove, hBelow⟩

end

end Chazelle.Core
