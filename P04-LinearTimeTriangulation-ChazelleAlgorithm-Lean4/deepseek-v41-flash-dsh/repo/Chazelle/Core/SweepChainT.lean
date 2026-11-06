module

public import Chazelle.Golf

public import Chazelle.Golf

public import Chazelle.Core.SweepChain

/-!
# The sweep (WP-D), part 8b: chains of chords without `TopStrict` (F2)

With ties at the top of `C₂` (other points of `C₂` at the height `h` of its top `u`), two
things change in the walk along a chain of collinear chords (`SweepChain`):

* a chord of `F₂⁺` in a tie may be a top chord of `C` at `u` ending on `C₂`: it is then an
  augmented chord of `C₂` itself, and the walk tracks it through the family
  `S₂x = S₂ ∪ (F₂⁺ ∩ augChords C₂)` of the model of `C₂` (`local_step2`);
* in case G the chain may reach the split vertex (the copy of `u` in the right stretch), where the
  model of `C₂` has its slit: there the tracked region of `S₂` may switch to the region on the
  other side of the slit, and both are the gap labels (`split_step`).

The walk (`half_walk2`, `end_bound2`) concludes a label, a bound, or a pair of gap labels, and
lemma (E) holds in the weakened form of (K3) (`label_side_gen2`).

* `shared_eq_top_of_snd`: the shared vertex at the height of the top is the top (least index).
* `S₂x`, `corr_right0x`: the enlarged family and its correspondence.
* `OffOut`, `partner_cases`: a chord of `F₂⁺` attached in the stretch is an augmented chord of
  `C₂`, or its other end is off the stretch.
-/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sideInArc sidePt sidePrev sideNext sideLeft sideLeftOf sideCcw
  sideCross sideDot freeIn regionsIn)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
open Chazelle.Geometry (lerp)
open WalkEmbed

namespace Sweep

/-! ## Generic helpers -/

section Generic

/-- A property eventually true just after `0` holds on an interval `(0, δ)`. -/
theorem exists_of_eventually_gt {P : ℝ → Prop} (h : ∀ᶠ s in 𝓝[>] (0 : ℝ), P s) :
    ∃ δ > (0 : ℝ), ∀ s, 0 < s → s < δ → P s := by
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 h
  exact ⟨u, hu, fun s h0 h1 => hsub ⟨h0, h1⟩⟩

/-- Keys just before a key inside an open cyclic interval are inside it. -/
theorem sideInArc_eventually_sub {a b x : ℝ} (h : sideInArc a b x) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), sideInArc a b (x - s) := by
  unfold sideInArc at h ⊢
  split_ifs at h ⊢ with hab
  · filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (show (0 : ℝ) < x - a by linarith [h.1])]
      with s hs hs'
    have : (0 : ℝ) < s := hs
    exact ⟨by linarith [hs'.2], by linarith [h.2]⟩
  · rcases h with h | h
    · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < x - a by linarith)] with s hs
      left; linarith [hs.2]
    · filter_upwards [self_mem_nhdsWithin] with s hs
      have : (0 : ℝ) < s := hs
      right; linarith

theorem faces_mono {M : Model} {p : ℕ} {t : ℝ} {U V : Set Point} (h : M.Faces p t U)
    (hUV : U ⊆ V) : M.Faces p t V :=
  h.mono fun _ hx => hUV hx

theorem afterFaces_mono {M : Model} {p : ℕ} {t : ℝ} {U V : Set Point} (h : AfterFaces M p t U)
    (hUV : U ⊆ V) : AfterFaces M p t V := by
  obtain ⟨δ, hδ, h⟩ := h
  exact ⟨δ, hδ, fun s h0 h1 h2 => faces_mono (h s h0 h1 h2) hUV⟩

theorem beforeFaces_mono {M : Model} {p : ℕ} {t : ℝ} {U V : Set Point}
    (h : BeforeFaces M p t U) (hUV : U ⊆ V) : BeforeFaces M p t V := by
  obtain ⟨δ, hδ, h1, h2⟩ := h
  exact ⟨δ, hδ, fun ht s h0 h1' h2' => faces_mono (h1 ht s h0 h1' h2') hUV,
    fun ht s h0 h1' => faces_mono (h2 ht s h0 h1') hUV⟩

theorem facedSide_mono {M : Model} {p : ℕ} {t ρ dir : ℝ} {U V : Set Point}
    (h : FacedSide M p t ρ dir U) (hUV : U ⊆ V) : FacedSide M p t ρ dir V :=
  ⟨fun h' => afterFaces_mono (h.1 h') hUV, fun h' => beforeFaces_mono (h.2 h') hUV⟩

theorem sideOf_mono {M : Model} {ρ : ℝ} {c U V : Set Point} (h : SideOf M ρ c U)
    (hUV : U ⊆ V) : SideOf M ρ c V :=
  fun z hz hzD => (h z hz hzD).mono fun _ hx => hUV hx

/-- An admissible chord has a point in the domain. -/
theorem adm_mem_dom {M : Model} (hM : WalkAx M) {c : Set Point} (hc : c ∈ M.Adm) :
    ∃ z ∈ c, z ∈ M.D := by
  obtain ⟨a, b, -, hcab, -, hopen, -, -⟩ := hM.ends c hc
  refine ⟨lerp a b (1 / 2), ?_, hopen _ ⟨⊛, ⊛⟩⟩
  Ξ hcab
  exact Geometry.lerp_mem_segment _ _ (⊛) (⊛)

/-- Every chord of a finite admissible family has a region on each side. -/
theorem side_region_exists' {M : Model} (hM : WalkAx M) {F : Set (Set Point)} (hF : F ⊆ M.Adm)
    (hfin : F.Finite) {c : Set Point} (hc : c ∈ F) {ρ : ℝ} (hρ : ρ = 1 ∨ ρ = -1) :
    ∃ U ∈ M.regions F, SideOf M ρ c U := by
  obtain ⟨Up, Dn, hUp, hDn, -, hside, -⟩ := chordSides_of_system (hM.sys F hF hfin) hc
  rcases hρ with rfl | rfl
  · exact ⟨Up, hUp, fun z hz hzD => (hside z hz hzD).mono fun δ h => by simpa using h.1⟩
  · exact ⟨Dn, hDn, fun z hz hzD => (hside z hz hzD).mono fun δ h => by
      simpa [sub_eq_add_neg] using h.2⟩

/-- A region of a finer family lies in a region of a coarser one. -/
theorem super_region {M : Model} {F F' : Set (Set Point)} (hFF : F ⊆ F') {U : Set Point}
    (hU : U ∈ M.regions F') : ∃ V ∈ M.regions F, U ⊆ V := by
  obtain ⟨z, hz, rfl⟩ := hU
  have hsub : freeIn M.D F' ⊆ freeIn M.D F :=
    sdiff_subset_sdiff_right (Set.sUnion_mono hFF)
  refine ⟨connectedComponentIn (freeIn M.D F) z, ⟨z, hsub hz, rfl⟩, ?_⟩
  exact (isPreconnected_connectedComponentIn).subset_connectedComponentIn
    (mem_connectedComponentIn hz) ((connectedComponentIn_subset _ _).trans hsub)

/-- **The region of a finer family on a side of a chord** lies in the region of the coarser
family on that side. -/
theorem sub_region_side {M : Model} (hM : WalkAx M) {F F' : Set (Set Point)} (hFF : F ⊆ F')
    (hF' : F' ⊆ M.Adm) (hfin : F'.Finite) {c : Set Point} (hc : c ∈ F') {ρ : ℝ}
    (hρ : ρ = 1 ∨ ρ = -1) {V : Set Point} (hV : V ∈ M.regions F) (hVs : SideOf M ρ c V) :
    ∃ U ∈ M.regions F', U ⊆ V ∧ SideOf M ρ c U := by
  obtain ⟨U, hU, hUs⟩ := side_region_exists' hM hF' hfin hc hρ
  refine ⟨U, hU, ?_, hUs⟩
  obtain ⟨z, hz, hzD⟩ := adm_mem_dom hM (hF' hc)
  obtain ⟨δ, h1, h2⟩ := ((hUs z hz hzD).and (hVs z hz hzD)).exists
  have hsub : freeIn M.D F' ⊆ freeIn M.D F :=
    sdiff_subset_sdiff_right (Set.sUnion_mono hFF)
  obtain ⟨w, -, rfl⟩ := hU
  exact subset_region hV isPreconnected_connectedComponentIn
    ((connectedComponentIn_subset _ _).trans hsub) h1 h2

end Generic

/-! ## The shared vertex at the top height -/

section Basic

variable (J : Merge.Junction)

/-- **The shared vertex at the height of the top of `C₂` is the top** (`topIdx` is the least
index of a topmost vertex, and the shared vertex is vertex `0` of `C₂`). -/
theorem shared_eq_top_of_snd (h : J.right.top.2 ≤ J.shared.2) : J.shared = J.right.top := by
  have h0 : J.right.topIdx = 0 := by
    apply Nat.le_zero.1
    refine J.right.topIdx_min (Nat.zero_le _) fun i hi => ?_
    Ξ J.right_vertex_zero
    exact (J.right.vertex_snd_le_top hi).trans h
  show J.shared = J.right.vertex J.right.topIdx
  Ξ h0, J.right_vertex_zero

/-- **The chords of `F₂⁺` are not above the top of `C₂`.** -/
theorem F₂plus_snd_le {S₂ : Set (Set Point)} (hS₂ : S₂ ⊆ Merge.augChords J.right)
    {f : Set Point} (hf : f ∈ F₂plus J S₂) {z : Point} (hz : z ∈ f) : z.2 ≤ J.right.top.2 := by
  rcases hf with ((⟨c₀, hc₀, -, rfl⟩ | ⟨c₀, hc₀, -, rfl⟩) | ⟨σ, -, -, rfl⟩) | ⟨σ, -, -, rfl⟩
  · have hc₀' : c₀ ∈ S₂ := by simpa using hc₀
    have hz' := J.shoot_lend_subset (Or.inr (hS₂ hc₀')) hz
    obtain ⟨y, a, b, -, hy, rfl, -, -⟩ := Merge.augChords_spec (hS₂ hc₀')
    rw [hz'.1]; exact hy
  · have hc₀' : c₀ ∈ S₂ := by simpa using hc₀
    have hz' := J.shoot_rend_subset (Or.inr (hS₂ hc₀')) hz
    obtain ⟨y, a, b, -, hy, rfl, -, -⟩ := Merge.augChords_spec (hS₂ hc₀')
    rw [hz'.1]; exact hy
  · Ξ' Chain.chordSet_eq_hseg at hz
    Ξ hz.1, Merge.Junction.whole_vertex_m₁
    exact J.right.snd_le_top_of_mem_set J.shared_mem_right
  · Ξ' Chain.chordSet_eq_hseg at hz
    Ξ hz.1, Merge.Junction.whole_vertex_add
    exact J.right.vertex_snd_le_top J.right.topIdx_le

/-- **The kinds of chords of `F₂⁺`**: inside a chord of `S₂`, through the shared vertex, or
through the top of `C₂`. -/
theorem F₂plus_kind {S₂ : Set (Set Point)} (hS₂ : S₂ ⊆ Merge.augChords J.right)
    {f : Set Point} (hf : f ∈ F₂plus J S₂) :
    (∃ c ∈ S₂, f ⊆ c) ∨ J.shared ∈ f ∨ J.right.top ∈ f := by
  rcases hf with ((⟨c₀, hc₀, -, rfl⟩ | ⟨c₀, hc₀, -, rfl⟩) | ⟨σ, -, -, rfl⟩) | ⟨σ, -, -, rfl⟩
  · have hc₀' : c₀ ∈ S₂ := by simpa using hc₀
    exact Or.inl ⟨c₀, hc₀', J.shoot_lend_subset (Or.inr (hS₂ hc₀'))⟩
  · have hc₀' : c₀ ∈ S₂ := by simpa using hc₀
    exact Or.inl ⟨c₀, hc₀', J.shoot_rend_subset (Or.inr (hS₂ hc₀'))⟩
  · right; left
    Ξ ← Merge.Junction.whole_vertex_m₁
    exact Geometry.left_mem_segment _ _
  · right; right
    show J.right.vertex J.right.topIdx ∈ _
    Ξ ← Merge.Junction.whole_vertex_add
    exact Geometry.left_mem_segment _ _

end Basic

/-! ## The enlarged family of `C₂` -/

section Family

variable (J : Merge.Junction)

/-- **The family of `C₂` along the stretch**: `S₂` together with the chords of `F₂⁺` that are
augmented chords of `C₂` (such as a top chord of `C` at the top of `C₂` ending on `C₂`). -/
def S₂x (S₂ : Set (Set Point)) : Set (Set Point) :=
  S₂ ∪ {e | e ∈ F₂plus J S₂ ∧ e ∈ Merge.augChords J.right}

theorem subset_S₂x (S₂ : Set (Set Point)) : S₂ ⊆ S₂x J S₂ := subset_union_left

theorem S₂x_subset {S₂ : Set (Set Point)} (hS₂ : S₂ ⊆ Merge.augChords J.right) :
    S₂x J S₂ ⊆ Merge.augChords J.right := by
  rintro c (hc | ⟨-, hc⟩)
  · exact hS₂ hc
  · exact hc

theorem S₂x_finite {S₂ : Set (Set Point)} (hS₂f : S₂.Finite) : (S₂x J S₂).Finite :=
  hS₂f.union ((F₂plus_finite J hS₂f).subset fun _ h => h.1)

theorem S₂x_family {Q : Polygon} {S₂ : Set (Set Point)}
    (hS₂ : (chainModel J.right).ChordFamily Q S₂)
    (hF : (chainModel J.whole).ChordFamily Q (F₂plus J S₂)) :
    (chainModel J.right).ChordFamily Q (S₂x J S₂) := by
  refine ⟨S₂x_finite J hS₂.1, S₂x_subset J hS₂.2.1, ?_⟩
  rintro c (hc | ⟨hc, -⟩)
  · exact hS₂.2.2 c hc
  · exact hF.2.2 c hc

/-- **The right correspondence with the enlarged family.** -/
theorem corr_right0x (hP : J.P.Simple) {S₂ : Set (Set Point)}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hS₂f : S₂.Finite) :
    Corr0 (chainModel J.whole) (chainModel J.right) (F₂plus J S₂) (S₂x J S₂)
      (6 + tpos J.whole J.m₁) (6 + tpos J.right 0) (rL1 J) (rL2 J) (rδ J) := by
  have hC := corr_right0 J hP hS₂ hS₂f
  refine { hC with hS := S₂x_subset J hS₂, hSfin := S₂x_finite J hS₂f, trans := ?_ }
  rintro c (hc | ⟨hcF, -⟩) q hq hqD hqv
  · exact hC.trans c hc q hq hqD hqv
  · exact ⟨c, hcF, hq, subset_rfl⟩

/-- The other attachments of a chord of `F₂⁺` are off the open right stretch. -/
def OffOut (f : Set Point) (P : ℕ) (t : ℝ) : Prop :=
  ∀ (p' : ℕ) (t' : ℝ), SideAttach (chainModel J.whole).W f p' t' →
    sidePt (chainModel J.whole).W p' t' ≠ sidePt (chainModel J.whole).W P t →
    ¬ (0 < off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (p' + t') ∧
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (p' + t') <
        ((rL1 J + rL2 J : ℕ) : ℝ))

/-- **The points of the stretch are not in the domain of `C₂`.** -/
theorem stretch_not_dom₂ (hP : J.P.Simple) {S₂ : Set (Set Point)}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hS₂f : S₂.Finite) {p : ℕ}
    (hp : p < (chainModel J.whole).W.n) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (hin : 0 < off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (p + t) ∧
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (p + t) <
        ((rL1 J + rL2 J : ℕ) : ℝ)) :
    sidePt (chainModel J.whole).W p t ∉ J.right.dom := by
  have hC := corr_right0 J hP hS₂ hS₂f
  obtain ⟨hpd, hoff⟩ := hC.decomp hp ht0 ht1
  set d := dOf (chainModel J.whole).W.n (6 + tpos J.whole J.m₁) p
  have hd : d < rL1 J + rL2 J := by
    have h := hin.2
    Ξ' hoff at h
    have : (d : ℝ) < ((rL1 J + rL2 J : ℕ) : ℝ) := ⟡
    exact_mod_cast this
  Ξ ← hpd, hC.sidePt_eq hd t
  exact hC.hM₂.trace _ (Nat.mod_lt _ hC.n₂_pos) t ht0 ht1.le

/-- **A chord of `F₂⁺` attached in the right stretch is an augmented chord of `C₂`, or its other
end is off the stretch.** -/
theorem partner_cases (hP : J.P.Simple) {S₂ : Set (Set Point)}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hS₂f : S₂.Finite) {f : Set Point}
    (hf : f ∈ F₂plus J S₂) {p : ℕ} {t : ℝ} (hA : SideAttach (chainModel J.whole).W f p t)
    (hin : 0 < off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (p + t) ∧
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (p + t) <
        ((rL1 J + rL2 J : ℕ) : ℝ)) :
    f ∈ Merge.augChords J.right ∨ OffOut J f p t := by
  by_cases hfA : f ∈ Merge.augChords J.right
  · exact Or.inl hfA
  right
  intro p' t' hB hne hin'
  have hC := corr_right0 J hP hS₂ hS₂f
  have hM := hC.hM
  obtain ⟨y, a, b, hH, -, rfl, -, -⟩ := Merge.augChords_spec (F₂plus_subset J hS₂ hf)
  have hw := stretch_not_dom₂ J hP hS₂ hS₂f hA.1 hA.2.1 hA.2.2.1 hin
  have hw' := stretch_not_dom₂ J hP hS₂ hS₂f hB.1 hB.2.1 hB.2.2.1 hin'
  have hwD := hM.trace _ hA.1 t hA.2.1 hA.2.2.1.le
  have hwD' := hM.trace _ hB.1 t' hB.2.1 hB.2.2.1.le
  have hyh : y ≤ J.right.top.2 := by
    have := F₂plus_snd_le J hS₂ hf hA.2.2.2.1
    rwa [hA.2.2.2.1.1] at this
  -- an end of a point of the chord off the domain
  have hend : ∀ z ∈ Visibility.hseg y a b, z ∉ (chainModel J.whole).D → z.1 = a ∨ z.1 = b := by
    rintro z ⟨hzy, hza, hzb⟩ hzD
    rcases hza.lt_or_eq with h1 | h1
    · rcases hzb.lt_or_eq with h2 | h2
      · exact absurd (show z ∈ (chainModel J.whole).D by
          rw [show z = (z.1, y) from Prod.ext rfl hzy]; exact hH.open_mem z.1 h1 h2) hzD
      · exact Or.inr h2
    · exact Or.inl h1.symm
  have hpt : ∀ z ∈ Visibility.hseg y a b, z.1 = a ∨ z.1 = b → z = (a, y) ∨ z = (b, y) := by
    rintro z ⟨hzy, -, -⟩ (h | h)
    · left; exact Prod.ext h hzy
    · right; exact Prod.ext h hzy
  apply hfA
  refine ⟨y, a, b, ⟨hH.lt, ?_, ?_, fun x h1 h2 => ?_⟩, hyh, rfl⟩
  rotate_right
  · exact dom_right J (hH.open_mem x h1 h2) (by simpa using hyh)
  all_goals
    intro hD
    have e1 := hpt _ hA.2.2.2.1 (hend _ hA.2.2.2.1 hwD)
    have e2 := hpt _ hB.2.2.2.1 (hend _ hB.2.2.2.1 hwD')
    rcases e1 with e1 | e1 <;> rcases e2 with e2 | e2 <;>
      first
      | exact hne (e2.trans e1.symm)
      | (rw [e1] at hw; exact hw hD)
      | (rw [e2] at hw'; exact hw' hD)

end Family

/-! ## Junction facts without `TopStrict` -/

section JunctionFacts2

variable (J : Merge.Junction)

/-- **`RLabel` from the positions just after a position of the right stretch.** -/
theorem rlabel_after2 (hP : J.P.Simple) {S₂ : Set (Set Point)}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hS₂f : S₂.Finite) {d : ℕ} (hd : d < rL1 J + rL2 J)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) {G V : Set Point}
    (hW : AfterFaces (chainModel J.whole)
      ((6 + tpos J.whole J.m₁ + d) % (chainModel J.whole).W.n) t G)
    (hW₂ : AfterFaces (chainModel J.right)
      ((6 + tpos J.right 0 + dq (rL1 J) (rδ J) d) % (chainModel J.right).W.n) t V) :
    RLabel J S₂ G V := by
  have hC := corr_right0 J hP hS₂ hS₂f
  obtain ⟨δ, hδ, h1⟩ := hW
  obtain ⟨δ₂, hδ₂, h2⟩ := hW₂
  obtain ⟨s, hnc, hs⟩ := ((eventually_not_cut_after hC.hM hC.hF hC.hfin
    ((((6 + tpos J.whole J.m₁ + d) % (chainModel J.whole).W.n : ℕ) : ℝ) + t)).and
    (Ioo_mem_nhdsGT (show (0 : ℝ) < min (min δ δ₂) (1 - t) from
      lt_min (lt_min hδ hδ₂) (⟡)))).exists
  have hs1 := lt_of_lt_of_le hs.2 ((min_le_left _ _).trans (min_le_left _ _))
  have hs2 := lt_of_lt_of_le hs.2 ((min_le_left _ _).trans (min_le_right _ _))
  have hs3 : t + s < 1 := by linarith [lt_of_lt_of_le hs.2 (min_le_right _ _)]
  refine ⟨d, hd, t + s, ⟨by linarith [hs.1], hs3⟩, ?_, h1 s hs.1 hs1 hs3, h2 s hs.1 hs2 hs3⟩
  rw [← add_assoc]; exact hnc

/-- **`RLabel` from the positions just before a position of the right stretch.** -/
theorem rlabel_before2 (hP : J.P.Simple) {S₂ : Set (Set Point)}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hS₂f : S₂.Finite) {d : ℕ} (hd : d < rL1 J + rL2 J)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (hsec : t = 0 → d ≠ 0 ∧ d ≠ rL1 J) {G V : Set Point}
    (hW : BeforeFaces (chainModel J.whole)
      ((6 + tpos J.whole J.m₁ + d) % (chainModel J.whole).W.n) t G)
    (hW₂ : BeforeFaces (chainModel J.right)
      ((6 + tpos J.right 0 + dq (rL1 J) (rδ J) d) % (chainModel J.right).W.n) t V) :
    RLabel J S₂ G V := by
  have hC := corr_right0 J hP hS₂ hS₂f
  obtain ⟨δ, hδ, h1a, h1b⟩ := hW
  obtain ⟨δ₂, hδ₂, h2a, h2b⟩ := hW₂
  rcases ht0.lt_or_eq with htpos | ht00
  · obtain ⟨s, hnc, hs⟩ := ((eventually_not_cut_before hC.hM hC.hF hC.hfin
      ((((6 + tpos J.whole J.m₁ + d) % (chainModel J.whole).W.n : ℕ) : ℝ) + t)).and
      (Ioo_mem_nhdsGT (show (0 : ℝ) < min (min δ δ₂) t from
        lt_min (lt_min hδ hδ₂) htpos))).exists
    have hs1 := lt_of_lt_of_le hs.2 ((min_le_left _ _).trans (min_le_left _ _))
    have hs2 := lt_of_lt_of_le hs.2 ((min_le_left _ _).trans (min_le_right _ _))
    have hs3 := lt_of_lt_of_le hs.2 (min_le_right _ _)
    refine ⟨d, hd, t - s, ⟨⟡, by linarith [hs.1]⟩, ?_, h1a htpos s hs.1 hs1 hs3,
      h2a htpos s hs.1 hs2 hs3⟩
    rw [show ((((6 + tpos J.whole J.m₁ + d) % (chainModel J.whole).W.n : ℕ) : ℝ) + (t - s)) =
      (((6 + tpos J.whole J.m₁ + d) % (chainModel J.whole).W.n : ℕ) : ℝ) + t - s by ring]
    exact hnc
  · subst ht00
    obtain ⟨hd0, -⟩ := hsec rfl
    have hn0 := hC.n_pos
    have hn₂ := hC.n₂_pos
    set P := (6 + tpos J.whole J.m₁ + d) % (chainModel J.whole).W.n with hPdef
    set P' := (P + (chainModel J.whole).W.n - 1) % (chainModel J.whole).W.n with hP'def
    have hPm : (6 + tpos J.whole J.m₁ + (d - 1)) % (chainModel J.whole).W.n = P' := by
      Ξ hP'def, hPdef, mod_pred_mod hn0 _ (show 1 ≤ d by omega)
    have hdq0 : 1 ≤ dq (rL1 J) (rδ J) d := by unfold dq; split_ifs <;> omega
    have hdq1 : dq (rL1 J) (rδ J) (d - 1) = dq (rL1 J) (rδ J) d - 1 := by
      have := (hsec rfl).2; unfold dq; split_ifs <;> omega
    have hPm₂ : (6 + tpos J.right 0 + dq (rL1 J) (rδ J) (d - 1)) % (chainModel J.right).W.n =
        ((6 + tpos J.right 0 + dq (rL1 J) (rδ J) d) % (chainModel J.right).W.n +
          (chainModel J.right).W.n - 1) % (chainModel J.right).W.n := by
      Ξ hdq1, mod_pred_mod hn₂ _ hdq0
    obtain ⟨s, hnc, hs⟩ := ((eventually_not_cut_before hC.hM hC.hF hC.hfin
      (((P' : ℕ) : ℝ) + 1)).and
      (Ioo_mem_nhdsGT (show (0 : ℝ) < min (min δ δ₂) 1 from
        lt_min (lt_min hδ hδ₂) one_pos))).exists
    have hs1 := lt_of_lt_of_le hs.2 ((min_le_left _ _).trans (min_le_left _ _))
    have hs2 := lt_of_lt_of_le hs.2 ((min_le_left _ _).trans (min_le_right _ _))
    have hs3 := lt_of_lt_of_le hs.2 (min_le_right _ _)
    refine ⟨d - 1, ⋄, 1 - s, ⟨⟡, by linarith [hs.1]⟩, ?_, ?_, ?_⟩
    · rw [hPm, show ((P' : ℕ) : ℝ) + (1 - s) = ((P' : ℕ) : ℝ) + 1 - s by ring]; exact hnc
    · rw [hPm]; exact h1b rfl s hs.1 hs1
    · rw [hPm₂]; exact h2b rfl s hs.1 hs2

/-- **A chord of `S₂` containing a chord of `F₂⁺` attached at a position of the right stretch is
attached at the corresponding position of the walk of `C₂`.** -/
theorem attach_counterpart2 (hP : J.P.Simple) {S₂ : Set (Set Point)}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hS₂f : S₂.Finite) {d : ℕ} (hd : d < rL1 J + rL2 J)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (hsec : t = 0 → d ≠ 0 ∧ d ≠ rL1 J)
    {f c : Set Point} (hf : f ∈ F₂plus J S₂) (hc : c ∈ Merge.augChords J.right) (hfc : f ⊆ c)
    (hfA : SideAttach (chainModel J.whole).W f
      ((6 + tpos J.whole J.m₁ + d) % (chainModel J.whole).W.n) t) :
    SideAttach (chainModel J.right).W c
      ((6 + tpos J.right 0 + dq (rL1 J) (rδ J) d) % (chainModel J.right).W.n) t := by
  have hC := corr_right0 J hP hS₂ hS₂f
  set w := sidePt (chainModel J.whole).W ((6 + tpos J.whole J.m₁ + d) %
    (chainModel J.whole).W.n) t with hwdef
  have hw₂ := (hC.sidePt_eq hd t).symm
  rw [← hwdef] at hw₂
  have hwD₂ : w ∉ J.right.dom := by
    rw [← hw₂]; exact hC.hM₂.trace _ (Nat.mod_lt _ hC.n₂_pos) t ht0 ht1.le
  obtain ⟨y, a, b, hH, -, hcdef, -, -⟩ := Merge.augChords_spec hc
  obtain ⟨y₁, a₁, b₁, hH₁, -, hfdef⟩ := F₂plus_subset J hS₂ hf
  have hwf := hfA.2.2.2.1
  have hwc := hfc hwf
  obtain ⟨rf, hrf, hlf⟩ := hfA.2.2.2.2
  have hsecEq := hC.sideLeft_eq hd hsec
  have hab₁ := hH₁.lt
  refine ⟨Nat.mod_lt _ hC.n₂_pos, ht0, ht1, by rw [hw₂]; exact hwc, min rf (b₁ - a₁),
    lt_min hrf (by linarith), fun x hx hxne hxd => ?_⟩
  rw [hw₂] at hxne hxd
  rw [← hsecEq]
  refine hlf x ?_ hxne (lt_of_lt_of_le hxd (min_le_left _ _))
  have hxd' := lt_of_lt_of_le hxd (min_le_right _ _)
  have hx1 : |x.1 - w.1| < b₁ - a₁ := by
    have := (le_max_left _ _).trans_lt (show max (dist x.1 w.1) (dist x.2 w.2) < b₁ - a₁ by
      rw [← Prod.dist_eq]; exact hxd')
    rwa [Real.dist_eq] at this
  rw [hfdef] at hwf hfc ⊢
  rw [hcdef] at hwc hfc hx
  obtain ⟨hwy₁, hwa₁, hwb₁⟩ := hwf
  obtain ⟨hwy, hwa, hwb⟩ := hwc
  obtain ⟨hxy, hxa, hxb⟩ := hx
  obtain ⟨hy1, ha1, -⟩ : ((a₁, y₁) : Point) ∈ Visibility.hseg y a b := hfc ⟨rfl, le_rfl, hab₁.le⟩
  obtain ⟨-, -, hb1⟩ : ((b₁, y₁) : Point) ∈ Visibility.hseg y a b := hfc ⟨rfl, hab₁.le, le_rfl⟩
  simp only at hy1 ha1 hb1
  -- `w` is an endpoint of `c`
  have hwend : w.1 = a ∨ w.1 = b := by
    rcases hwa.lt_or_eq with h1 | h1
    · rcases hwb.lt_or_eq with h2 | h2
      · exact absurd (show w ∈ J.right.dom by
          rw [show w = (w.1, y) from Prod.ext rfl hwy]; exact hH.open_mem w.1 h1 h2) hwD₂
      · exact Or.inr h2
    · exact Or.inl h1.symm
  refine ⟨by rw [hxy, ← hy1], ?_, ?_⟩ <;> rcases hwend with h | h <;>
    rw [abs_lt] at hx1 <;> linarith [hx1.1, hx1.2]

/-- **No tie at the top of `C₂`** on the right stretch: two chords of `F₂⁺` are never attached at
one position of the right stretch whose point is the top of `C₂` (the corresponding position of
the walk of `C₂` is next to the slit). -/
theorem no_tie_at_top2 (hP : J.P.Simple) {S₂ : Set (Set Point)}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hS₂f : S₂.Finite) {d : ℕ} (hd : d < rL1 J + rL2 J)
    (hsec : d ≠ 0 ∧ d ≠ rL1 J) {e e' : Set Point} (he : e ∈ F₂plus J S₂)
    (he' : e' ∈ F₂plus J S₂) (hne : e ≠ e')
    (hA : SideAttach (chainModel J.whole).W e
      ((6 + tpos J.whole J.m₁ + d) % (chainModel J.whole).W.n) 0)
    (hA' : SideAttach (chainModel J.whole).W e'
      ((6 + tpos J.whole J.m₁ + d) % (chainModel J.whole).W.n) 0)
    (htop : sidePt (chainModel J.whole).W
      ((6 + tpos J.whole J.m₁ + d) % (chainModel J.whole).W.n) 0 = J.right.top) : False := by
  have hC := corr_right0 J hP hS₂ hS₂f
  have hM := hC.hM
  have hF := hC.hF
  set W := (chainModel J.whole).W with hWdef
  set W₂ := (chainModel J.right).W with hW₂def
  set P := (6 + tpos J.whole J.m₁ + d) % W.n with hPdef
  set P₂ := (6 + tpos J.right 0 + dq (rL1 J) (rδ J) d) % W₂.n with hP₂def
  have hsec' : (0 : ℝ) = 0 → d ≠ 0 ∧ d ≠ rL1 J := fun _ => hsec
  -- east and west chords
  obtain ⟨ce, cw, hce, hcw, hAe, hAw, hE, hW⟩ : ∃ ce cw, ce ∈ F₂plus J S₂ ∧ cw ∈ F₂plus J S₂ ∧
      SideAttach W ce P 0 ∧ SideAttach W cw P 0 ∧ (∀ z ∈ ce, (sidePt W P 0).1 ≤ z.1) ∧
      (∀ z ∈ cw, z.1 ≤ (sidePt W P 0).1) := by
    rcases hM.tie_pair hF he he' hne hA hA' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨e, e', he, he', hA, hA', h1, h2⟩
    · exact ⟨e', e, he', he, hA', hA, h2, h1⟩
  obtain ⟨-, s₁, s₂, hs₁, hs₂, hsE, hsW⟩ := hM.tie_setup (hF hce) (hF hcw) hAe hAw hE hW
  obtain ⟨-, hhor, -⟩ := hM.tie_shape hF hce hcw hAe hAw hE hW
  have hv : (chainModel J.whole).wa P = J.right.top := by
    rw [← htop, Chazelle.Chain.sidePt_zero]; rfl
  have hv₂ : W₂.vtx P₂ = J.right.top := by
    have := hC.sidePt_eq hd 0
    Ξ' Chazelle.Chain.sidePt_zero, Chazelle.Chain.sidePt_zero at this
    Ξ ← this, ← htop, Chazelle.Chain.sidePt_zero
  have hnext : (chainModel J.whole).wb P = W₂.vtx ((P₂ + 1) % W₂.n) := hC.sideNext_eq hd
  have hprev : W.vtx ((P + W.n - 1) % W.n) = W₂.vtx ((P₂ + W₂.n - 1) % W₂.n) := by
    have := hC.sidePrev_eq hd (t := 0) hsec'
    unfold sidePrev at this
    rwa [ite_eq_left rfl, ite_eq_left rfl] at this
  -- the position of the walk of `C₂` at its top is a tour vertex
  have hP₂n : P₂ < W₂.n := Nat.mod_lt _ hC.n₂_pos
  obtain ⟨-, i, hi, hP₂i, -⟩ := pos_eq_vertex J.right hP J.right.sideBeta hP₂n le_rfl
    zero_lt_one J.right.topIdx_le (by rw [Chazelle.Chain.sidePt_zero]; exact hv₂)
  have hn₂ : W₂.n = 2 * J.right.m + 7 := cm_n J.right
  have hm1 := J.right.one_le
  rcases lt_or_gt_of_ne hhor with hdown | hup
  · -- the leaving edge goes down: the upward direction is in the sector
    have hB2 : ((chainModel J.whole).wb P - (chainModel J.whole).wa P).2 < 0 := by
      simp only [Prod.snd_sub]; linarith
    obtain ⟨-, hX⟩ := Tie.ccw_down hs₂ hB2 hsW
    have hup : ∀ ε > (0 : ℝ), sideLeft W₂ P₂ 0 ((J.right.top.1, J.right.top.2 + ε) : Point) := by
      intro ε hε
      Ξ ← hC.sideLeft_eq hd hsec', Chazelle.Chain.sideLeft_zero
      unfold Chazelle.Chain.sideLeftOf
      have key := hX (((J.right.top.1, J.right.top.2 + ε) : Point) - (chainModel J.whole).wa P)
        (Or.inr (Or.inl (by rw [hv]; simp only [Prod.snd_sub]; linarith)))
      Ξ' hv at key
      have hvP : (chainModel J.whole).W.vtx
          ((6 + tpos J.whole J.m₁ + d) % (chainModel J.whole).W.n) = J.right.top := hv
      Ξ hvP
      exact key
    obtain ⟨r, hr, hsf⟩ := sector_free hC.hM₂ hC.hS hC.hSfin hP₂n le_rfl zero_lt_one
    Ξ' Chazelle.Chain.sidePt_zero, hv₂ at hsf
    have hR := J.right.top_snd_lt_radius
    set ε := min (r / 2) ((J.right.radius - J.right.top.2) / 2) with hε
    have hε0 : 0 < ε := lt_min (⟡) (⟡)
    have hxD := (hsf _ (by
      Ξ mem_ball, Prod.dist_eq
      ϴ Real.dist_eq, sub_self, abs_zero, add_sub_cancel_left, abs_of_pos hε0
      Ξ max_eq_right hε0.le
      exact lt_of_le_of_lt (min_le_left _ _) (⟡)) (hup ε hε0)).1
    apply hxD.2
    right
    show _ ∈ Chazelle.segment _ _
    Ξ Geometry.mem_segment_iff_lerp
    refine ⟨ε / (J.right.radius - J.right.top.2), ⟢, ?_, ?_⟩
    · rw [div_le_one (⟡)]; linarith [min_le_right (r / 2) ((J.right.radius - J.right.top.2) / 2)]
    · apply Geometry.point_ext
      · Θ Geometry.lerp, Chain.slitTop
      · ϴ Geometry.lerp_snd, Chain.slitTop
        Ξ div_mul_cancel₀ _ (⟡)
  · -- the leaving edge goes up: both neighbours would be above the top
    have hB2 : 0 < ((chainModel J.whole).wb P - (chainModel J.whole).wa P).2 := by
      simp only [Prod.snd_sub]; linarith
    obtain ⟨hA2, -⟩ := Tie.ccw_up hs₁ hB2 hsE
    Ξ' hnext, hv at hB2
    Ξ' hprev, show (chainModel J.whole).wa P = W.vtx P from rfl at hA2
    have hvP : W.vtx P = J.right.top := hv
    Ξ' hvP at hA2
    ϴ' Prod.snd_sub at hB2 hA2
    Ξ' hP₂i at hB2 hA2
    rcases lt_or_eq_of_le hi with hi' | hi'
    · have e1 : (i + 6 + 1) % W₂.n = (i + 1) + 6 := by
        rw [hn₂, show i + 6 + 1 = (i + 1) + 6 by ring]; exact Nat.mod_eq_of_lt (⋄)
      Ξ' e1, hW₂def, cm_W, J.right.sideWalk_vtx_tour _ (⋄) at hB2
      have := J.right.vertex_snd_le_top (J.right.sideIdx_le J.right.sideBeta (i + 1))
      unfold Chain.sideTour at hB2
      linarith
    · have e1 : (i + 6 + W₂.n - 1) % W₂.n = (i - 1) + 6 := by
        rw [hn₂, show i + 6 + (2 * J.right.m + 7) - 1 = (i - 1 + 6) + (2 * J.right.m + 7) by
          omega, Nat.add_mod_right, Nat.mod_eq_of_lt (⋄)]
      Ξ' e1, hW₂def, cm_W, J.right.sideWalk_vtx_tour _ (⋄) at hA2
      have := J.right.vertex_snd_le_top (J.right.sideIdx_le J.right.sideBeta (i - 1))
      unfold Chain.sideTour at hA2
      linarith

/-- **`RLabel` from the positions just before a vertex position of the stretch** (offset
`1 ≤ d ≤ rL1 + rL2`): the corresponding positions of the walk of `C₂` are those just before the
position following the counterpart of `d - 1`.  This covers the split vertex (`d = rL1`, case G)
and the end of the stretch (`d = rL1 + rL2`). -/
theorem rlabel_before0_2 (hP : J.P.Simple) {S₂ : Set (Set Point)}
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
  have hn0 := hC.n_pos
  have hn₂ := hC.n₂_pos
  set P := (6 + tpos J.whole J.m₁ + d) % (chainModel J.whole).W.n with hPdef
  set P' := (P + (chainModel J.whole).W.n - 1) % (chainModel J.whole).W.n with hP'def
  have hPm : (6 + tpos J.whole J.m₁ + (d - 1)) % (chainModel J.whole).W.n = P' := by
    Ξ hP'def, hPdef, mod_pred_mod hn0 _ hd1
  have hPm₂ : (6 + tpos J.right 0 + dq (rL1 J) (rδ J) (d - 1)) % (chainModel J.right).W.n =
      ((6 + tpos J.right 0 + (dq (rL1 J) (rδ J) (d - 1) + 1)) % (chainModel J.right).W.n +
        (chainModel J.right).W.n - 1) % (chainModel J.right).W.n := by
    Ξ mod_pred_mod hn₂ _ (⋄)
    rfl
  obtain ⟨s, hnc, hs⟩ := ((eventually_not_cut_before hC.hM hC.hF hC.hfin
    (((P' : ℕ) : ℝ) + 1)).and
    (Ioo_mem_nhdsGT (show (0 : ℝ) < min (min δ δ₂) 1 from
      lt_min (lt_min hδ hδ₂) one_pos))).exists
  have hs1 := lt_of_lt_of_le hs.2 ((min_le_left _ _).trans (min_le_left _ _))
  have hs2 := lt_of_lt_of_le hs.2 ((min_le_left _ _).trans (min_le_right _ _))
  have hs3 := lt_of_lt_of_le hs.2 (min_le_right _ _)
  refine ⟨d - 1, ⋄, 1 - s, ⟨⟡, by linarith [hs.1]⟩, ?_, ?_, ?_⟩
  · rw [hPm, show ((P' : ℕ) : ℝ) + (1 - s) = ((P' : ℕ) : ℝ) + 1 - s by ring]; exact hnc
  · rw [hPm]; exact h1b rfl s hs.1 hs1
  · rw [hPm₂]; exact h2b rfl s hs.1 hs2

end JunctionFacts2

/-! ## The local step with the enlarged family -/

section Local2

variable (J : Merge.Junction)

/-- **The local step without `TopStrict`.**  As `local_step`, with the chord `c ⊇ f` of the
model of `C₂` taken in the enlarged family `S₂x`; the partner at a tie is inside a chord of
`S₂x` with `V` on its side `ρ`, or its other end is off the stretch. -/
theorem local_step2 (hP : J.P.Simple) {Q : Polygon}
    {S₂ : Set (Set Point)} (hS₂ : (chainModel J.right).ChordFamily Q S₂)
    (hF : (chainModel J.whole).ChordFamily Q (F₂plus J S₂)) {d : ℕ} (hd : d < rL1 J + rL2 J)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (hsec : t = 0 → d ≠ 0 ∧ d ≠ rL1 J)
    {f c : Set Point} (hf : f ∈ F₂plus J S₂) (hc : c ∈ S₂x J S₂) (hfc : f ⊆ c)
    (hfA : SideAttach (chainModel J.whole).W f
      ((6 + tpos J.whole J.m₁ + d) % (chainModel J.whole).W.n) t)
    {ρ : ℝ} (hρ : ρ = 1 ∨ ρ = -1) {G V : Set Point}
    (hG : G ∈ (chainModel J.whole).regions (F₂plus J S₂))
    (hV : V ∈ (chainModel J.right).regions S₂) (hGs : SideOf (chainModel J.whole) ρ f G)
    (hVs : SideOf (chainModel J.right) ρ c V) :
    RLabel J S₂ G V ∨ (t = 0 ∧ ∃ f' ∈ F₂plus J S₂, f' ≠ f ∧
      SideAttach (chainModel J.whole).W f' ((6 + tpos J.whole J.m₁ + d) %
        (chainModel J.whole).W.n) 0 ∧ SideOf (chainModel J.whole) ρ f' G ∧
      ((∃ c' ∈ S₂x J S₂, f' ⊆ c' ∧ SideOf (chainModel J.right) ρ c' V) ∨
        ((J.shared ∈ f' ∨ J.right.top ∈ f') ∧
          OffOut J f' ((6 + tpos J.whole J.m₁ + d) % (chainModel J.whole).W.n) 0))) := by
  have hC := corr_right0 J hP hS₂.2.1 hS₂.1
  have hCx := corr_right0x J hP hS₂.2.1 hS₂.1
  have hSx := S₂x_family J hS₂ hF
  have hM := hC.hM
  have hM₂ := hC.hM₂
  have hFs := hC.hF
  have hSs := hCx.hS
  obtain ⟨U, hU, hUV, hUs⟩ := sub_region_side hM₂ (subset_S₂x J S₂) hSs hSx.1 hc hρ hV hVs
  set W := (chainModel J.whole).W with hWdef
  set W₂ := (chainModel J.right).W with hW₂def
  set P := (6 + tpos J.whole J.m₁ + d) % W.n with hPdef
  set P₂ := (6 + tpos J.right 0 + dq (rL1 J) (rδ J) d) % W₂.n with hP₂def
  have hcA : SideAttach W₂ c P₂ t :=
    attach_counterpart2 J hP hS₂.2.1 hS₂.1 hd ht0 ht1 hsec hf (S₂x_subset J hS₂.2.1 hc) hfc hfA
  have hw₂ : sidePt W₂ P₂ t = sidePt W P t := (hC.sidePt_eq hd t).symm
  have hGM : GoodModel (chainModel J.whole) := Or.inl ⟨J.whole, hP, rfl⟩
  have hGM₂ : GoodModel (chainModel J.right) := Or.inl ⟨J.right, hP, rfl⟩
  -- the common direction of `f` and `c`
  obtain ⟨dir, hdirF, hdirC⟩ : ∃ dir : ℝ,
      ((dir = 1 ∧ ∀ z ∈ f, (sidePt W P t).1 ≤ z.1) ∨ (dir = -1 ∧ ∀ z ∈ f, z.1 ≤ (sidePt W P t).1)) ∧
      ((dir = 1 ∧ ∀ z ∈ c, (sidePt W₂ P₂ t).1 ≤ z.1) ∨
        (dir = -1 ∧ ∀ z ∈ c, z.1 ≤ (sidePt W₂ P₂ t).1)) := by
    Ξ hw₂
    rcases hM₂.attach_dir (hSs hc) hcA with h | h <;> Ξ' hw₂ at h
    · exact ⟨1, Or.inl ⟨rfl, fun z hz => h z (hfc hz)⟩, Or.inl ⟨rfl, h⟩⟩
    · exact ⟨-1, Or.inr ⟨rfl, fun z hz => h z (hfc hz)⟩, Or.inr ⟨rfl, h⟩⟩
  obtain ⟨FW1, FW2⟩ := faced_or_middle hGM hF hf hfA hρ hG hGs hdirF
  obtain ⟨FV1, FV2⟩ := faced_or_middle hGM₂ hSx hc hcA hρ hU hUs hdirC
  -- facing on the same side gives the label
  have hRL : FacedSide (chainModel J.whole) P t ρ dir G →
      FacedSide (chainModel J.right) P₂ t ρ dir U → RLabel J S₂ G V := by
    intro h1 h2
    have h2' := facedSide_mono h2 hUV
    have hρd : ρ * dir = -1 ∨ ρ * dir = 1 := by
      rcases hρ with rfl | rfl <;> rcases hdirF with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> norm_num
    rcases hρd with h | h
    · exact rlabel_after2 J hP hS₂.2.1 hS₂.1 hd ht0 ht1 (h1.1 h) (h2'.1 h)
    · exact rlabel_before2 J hP hS₂.2.1 hS₂.1 hd ht0 ht1 hsec (h1.2 h) (h2'.2 h)
  by_cases htie : ∃ f' ∈ F₂plus J S₂, f' ≠ f ∧ SideAttach W f' P t
  swap
  · -- no tie
    push Not at htie
    have huW : ∀ e' ∈ F₂plus J S₂, SideAttach W e' P t → e' = f := by
      intro e' he' hA'
      by_contra hne
      exact htie e' he' hne hA'
    have huW₂ : ∀ c' ∈ S₂x J S₂, SideAttach W₂ c' P₂ t → c' = c := by
      intro c' hc' hA'
      obtain ⟨e'', he'', hec'', -, hA''⟩ := hCx.transfer hd ht0 ht1 hsec hc' hA'
      have := huW e'' he'' hA''
      subst this
      exact s2_eq_of_sub J (S₂x_subset J hS₂.2.1) hc' hc (F₂plus_subset J hS₂.2.1 he'') hec''
        hfc
    exact Or.inl (hRL (FW1 huW) (FV1 huW₂))
  -- a tie
  obtain ⟨f', hf', hne, hA'⟩ := htie
  obtain ⟨ht00, hhor, hdn, hup⟩ := FW2 f' hf' hne hA'
  subst ht00
  have hsec0 := hsec rfl
  have hwa : (chainModel J.right).wa P₂ = (chainModel J.whole).wa P := by
    have := hC.sidePt_eq hd 0
    Ξ' Chazelle.Chain.sidePt_zero, Chazelle.Chain.sidePt_zero at this
    exact this.symm
  have hwb : (chainModel J.right).wb P₂ = (chainModel J.whole).wb P := (hC.sideNext_eq hd).symm
  -- the faced case in `W₂`
  have hfaced₂ : ((chainModel J.whole).wb P).2 < ((chainModel J.whole).wa P).2 → ρ = -1 →
      FacedSide (chainModel J.right) P₂ 0 ρ dir U := by
    intro hdown hρ1
    by_cases htie₂ : ∃ c'' ∈ S₂x J S₂, c'' ≠ c ∧ SideAttach W₂ c'' P₂ 0
    · obtain ⟨c'', hc'', hne'', hA''⟩ := htie₂
      obtain ⟨-, -, h1, -⟩ := FV2 c'' hc'' hne'' hA''
      exact (h1 (by rw [hwa, hwb]; exact hdown)).2 hρ1
    · push Not at htie₂
      exact FV1 fun c'' hc'' hA'' => by_contra fun h => htie₂ c'' hc'' h hA''
  have hfaced₂' : ((chainModel J.whole).wa P).2 < ((chainModel J.whole).wb P).2 → ρ = 1 →
      FacedSide (chainModel J.right) P₂ 0 ρ dir U := by
    intro hupd hρ1
    by_cases htie₂ : ∃ c'' ∈ S₂x J S₂, c'' ≠ c ∧ SideAttach W₂ c'' P₂ 0
    · obtain ⟨c'', hc'', hne'', hA''⟩ := htie₂
      obtain ⟨-, -, -, h1⟩ := FV2 c'' hc'' hne'' hA''
      exact (h1 (by rw [hwa, hwb]; exact hupd)).2 hρ1
    · push Not at htie₂
      exact FV1 fun c'' hc'' hA'' => by_contra fun h => htie₂ c'' hc'' h hA''
  -- the middle case in `W₂`, for a partner inside a chord of `S₂x`
  have hmid₂ : ∀ c' ∈ S₂x J S₂, f' ⊆ c' →
      (((chainModel J.whole).wb P).2 < ((chainModel J.whole).wa P).2 → ρ = 1 →
        SideOf (chainModel J.right) ρ c' V) ∧
      (((chainModel J.whole).wa P).2 < ((chainModel J.whole).wb P).2 → ρ = -1 →
        SideOf (chainModel J.right) ρ c' V) := by
    intro c' hc' hfc'
    have hc'A : SideAttach W₂ c' P₂ 0 :=
      attach_counterpart2 J hP hS₂.2.1 hS₂.1 hd le_rfl zero_lt_one hsec hf'
        (S₂x_subset J hS₂.2.1 hc') hfc' hA'
    have hc'c : c' ≠ c := by
      rintro rfl
      rcases hdirC with ⟨-, hc1⟩ | ⟨-, hc1⟩ <;> Ξ' hw₂ at hc1
      · exact hne (hM.attach_east_unique hFs hf' hf hA' hfA (fun z hz => hc1 z (hfc' hz))
          (fun z hz => hc1 z (hfc hz)))
      · exact hne (hM.attach_west_unique hFs hf' hf hA' hfA (fun z hz => hc1 z (hfc' hz))
          (fun z hz => hc1 z (hfc hz)))
    obtain ⟨-, -, h1, h2⟩ := FV2 c' hc' hc'c hc'A
    exact ⟨fun hd' hρ1 => sideOf_mono ((h1 (by rw [hwa, hwb]; exact hd')).1 hρ1) hUV,
      fun hu' hρ1 => sideOf_mono ((h2 (by rw [hwa, hwb]; exact hu')).1 hρ1) hUV⟩
  -- the partner: an augmented chord of `C₂`, or its other end is off the stretch
  have hpartner : (∃ c' ∈ S₂x J S₂, f' ⊆ c') ∨
      ((J.shared ∈ f' ∨ J.right.top ∈ f') ∧ OffOut J f' P 0) := by
    have hin : 0 < off W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (P + 0) ∧
        off W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (P + 0) < ((rL1 J + rL2 J : ℕ) : ℝ) := by
      have e := hC.off_M hd (t := 0) le_rfl zero_lt_one
      Ξ e
      have h1 : (1 : ℝ) ≤ d := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hsec0.1
      have h2 : (d : ℝ) < ((rL1 J + rL2 J : ℕ) : ℝ) := by exact_mod_cast hd
      constructor <;> linarith
    rcases F₂plus_kind J hS₂.2.1 hf' with ⟨c₀, hc₀, hfc₀⟩ | hkind
    · exact Or.inl ⟨c₀, subset_S₂x J S₂ hc₀, hfc₀⟩
    rcases partner_cases J hP hS₂.2.1 hS₂.1 hf' hA' hin with h | h
    · exact Or.inl ⟨f', Or.inr ⟨hf', h⟩, subset_rfl⟩
    · exact Or.inr ⟨hkind, h⟩
  rcases lt_or_gt_of_ne hhor with hdown | hupd
  · rcases hρ with rfl | rfl
    · refine Or.inr ⟨rfl, f', hf', hne, hA', (hdn hdown).1 rfl, ?_⟩
      rcases hpartner with ⟨c', hc', hfc'⟩ | hsh
      · exact Or.inl ⟨c', hc', hfc', (hmid₂ c' hc' hfc').1 hdown rfl⟩
      · exact Or.inr hsh
    · exact Or.inl (hRL ((hdn hdown).2 rfl) (hfaced₂ hdown rfl))
  · rcases hρ with rfl | rfl
    · exact Or.inl (hRL ((hup hupd).2 rfl) (hfaced₂' hupd rfl))
    · refine Or.inr ⟨rfl, f', hf', hne, hA', (hup hupd).1 rfl, ?_⟩
      rcases hpartner with ⟨c', hc', hfc'⟩ | hsh
      · exact Or.inl ⟨c', hc', hfc', (hmid₂ c' hc' hfc').2 hupd rfl⟩
      · exact Or.inr hsh

end Local2

/-! ## Horizontal directions at the split vertex -/

section SplitGeo

/-- **A west direction of a corner below the horizontal** lies in the corner from the upward
slit (converse of `ccw_lower_left`). -/
theorem ccw_corner_west {a x : ℝ} {A B : Point} (ha : 0 < a) (hA : A.2 ≤ 0) (hB : B.2 ≤ 0)
    (h : sideCcw B ((x, 0) : Point) A) (hx : x < 0) :
    sideCcw ((0, a) : Point) ((x, 0) : Point) A := by
  obtain ⟨b1, b2⟩ := B
  obtain ⟨a1, a2⟩ := A
  simp only at hA hB
  ϴ' sideCcw, sideCross, sideDot at h ⊢
  have hxa : 0 < -(a * x) := ⊞
  rcases lt_trichotomy a1 0 with h1 | h1 | h1
  · rcases hA.lt_or_eq with h2 | h2
    · left
      exact ⟨⊞, ⊞, ⊞⟩
    · exfalso
      subst h2
      rcases h with ⟨h3, h4, h5⟩ | ⟨h3, h4 | h4⟩ | ⟨h3, h4, h5⟩ | ⟨h3, h4, h5 | h5⟩
      · nlinarith
      · have hb : b2 < 0 := ⊞
        nlinarith
      · nlinarith
      · have hb : b2 = 0 := by
          have : b2 * a1 = 0 := ⟡
          rcases mul_eq_zero.1 this with h | h
          · exact h
          · linarith
        subst hb; nlinarith
      · have hb : b2 = 0 := by
          have : b2 * a1 = 0 := ⟡
          rcases mul_eq_zero.1 this with h | h
          · exact h
          · linarith
        subst hb; exact h5 (⋆)
      · have hb : b2 = 0 := by
          have : b2 * a1 = 0 := ⟡
          rcases mul_eq_zero.1 this with h | h
          · exact h
          · linarith
        subst hb
        have : b1 < 0 := ⊞
        nlinarith
  · subst h1
    rcases hA.lt_or_eq with h2 | h2
    · right; right; left
      exact ⟨⋆, ⊞, ⊞⟩
    · exfalso
      subst h2
      rcases h with ⟨h3, -, -⟩ | ⟨h3, -⟩ | ⟨-, h4, -⟩ | ⟨-, h4, -⟩ <;> nlinarith
  · right; left
    exact ⟨⊞, Or.inl (⊞)⟩

/-- **An east direction of a corner below the horizontal** lies in the corner to the upward
slit (converse of `ccw_lower_right`). -/
theorem ccw_corner_east {a x : ℝ} {A B : Point} (ha : 0 < a) (hA : A.2 ≤ 0) (hB : B.2 ≤ 0)
    (h : sideCcw B ((x, 0) : Point) A) (hx : 0 < x) :
    sideCcw B ((x, 0) : Point) ((0, a) : Point) := by
  obtain ⟨b1, b2⟩ := B
  obtain ⟨a1, a2⟩ := A
  simp only at hA hB
  ϴ' sideCcw, sideCross, sideDot at h ⊢
  have hxa : 0 < x * a := ⊞
  rcases lt_trichotomy b1 0 with h1 | h1 | h1
  · right; left
    exact ⟨⊞, Or.inr (⊞)⟩
  · subst h1
    rcases hB.lt_or_eq with h2 | h2
    · right; right; left
      exact ⟨⋆, ⊞, ⊞⟩
    · exfalso
      subst h2
      rcases h with ⟨h3, -, -⟩ | ⟨h3, -⟩ | ⟨-, h4, -⟩ | ⟨-, h4, -⟩ <;> nlinarith
  · rcases hB.lt_or_eq with h2 | h2
    · left
      exact ⟨⊞, ⊞, ⊞⟩
    · exfalso
      subst h2
      rcases h with ⟨h3, h4, h5⟩ | ⟨h3, h4 | h4⟩ | ⟨h3, h4, h5⟩ | ⟨h3, h4, h5 | h5⟩
      · nlinarith
      · nlinarith
      · nlinarith
      · nlinarith
      · exact h5 (⋆)
      · nlinarith

/-- **An admissible chord through a point off the domain** is a horizontal segment from it. -/
theorem seg_of_end {M : Model} (hM : WalkAx M) {c : Set Point} (hc : c ∈ M.Adm) {u : Point}
    (hu : u ∈ c) (huD : u ∉ M.D) : ∃ w, w ≠ u ∧ w.2 = u.2 ∧ c = Chazelle.segment u w := by
  obtain ⟨a, b, hab, heq, hy, hopen, -, -⟩ := hM.ends c hc
  have hue' := hu
  Ξ' heq at hue'
  obtain ⟨s, hs0, hs1, hs⟩ := Geometry.mem_segment_iff_lerp.1 hue'
  rcases hs0.lt_or_eq with hs0 | hs0
  · rcases hs1.lt_or_eq with hs1 | hs1
    · exact absurd (hs ▸ hopen s ⟨hs0, hs1⟩) huD
    · Ξ' hs1, Geometry.lerp_one at hs
      exact ⟨a, fun h => hab (h.trans hs), by rw [hs]; exact hy, by
        rw [heq, hs, Geometry.segment_comm]⟩
  · Ξ' ← hs0, Geometry.lerp_zero at hs
    exact ⟨b, fun h => hab (hs.symm.trans h.symm), by rw [hs]; exact hy.symm, Ρ heq, hs⟩

/-- The direction of a horizontal segment attached at a vertex position lies in its left
sector. -/
theorem sideLeft_of_attach_seg {W : Polygon} {c : Set Point} {p : ℕ} {u w : Point}
    (hpu : sidePt W p 0 = u) (hA : SideAttach W c p 0) (hcw : c = Chazelle.segment u w)
    {σ T : ℝ} (hσ : σ = 1 ∨ σ = -1) (hT : 0 < T)
    (hray : ∀ s, 0 ≤ s → s ≤ T → rayPt u σ s ∈ Chazelle.segment u w) :
    sideLeft W p 0 (rayPt u σ 1) := by
  obtain ⟨-, -, -, -, r, hr, hl⟩ := hA
  set ε := min (r / 2) T with hε
  have hε0 : 0 < ε := lt_min (⟡) hT
  have hz := hl (rayPt u σ ε) (by rw [hcw]; exact hray ε hε0.le (min_le_right _ _))
    (by
      rw [hpu]; intro h
      have := congrArg Prod.fst h; ϴ' rayPt at this
      rcases hσ with rfl | rfl <;> linarith)
    (by
      Ξ hpu, dist_rayPt _ hσ hε0.le
      exact lt_of_le_of_lt (min_le_left _ _) (⟡))
  Ξ' ← hpu at hz ⊢
  exact (FuseMath.sideLeft_rayPt hε0).1 hz

/-- A horizontal segment from the point of a vertex position, with its direction in the left
sector, is attached there. -/
theorem attach_of_sideLeft_seg {W : Polygon} {c : Set Point} {p : ℕ} (hp : p < W.n)
    {u w : Point} (hpu : sidePt W p 0 = u) {σ T : ℝ} (hsl : sideLeft W p 0 (rayPt u σ 1))
    (hcw : c = Chazelle.segment u w)
    (hseg : ∀ z ∈ Chazelle.segment u w, ∃ s, 0 ≤ s ∧ s ≤ T ∧ z = rayPt u σ s) :
    SideAttach W c p 0 := by
  refine ⟨hp, le_rfl, zero_lt_one, by rw [hpu, hcw]; exact Geometry.left_mem_segment _ _, 1,
    one_pos, fun z hz hzu _ => ?_⟩
  Ξ' hcw at hz
  obtain ⟨s, hs0, -, rfl⟩ := hseg z hz
  have hs : 0 < s := by
    rcases hs0.lt_or_eq with h | h
    · exact h
    · exfalso; apply hzu; rw [← h, hpu]; apply Geometry.point_ext <;> Θ rayPt
  Ξ' ← hpu at hsl ⊢
  exact (FuseMath.sideLeft_rayPt hs).2 hsl

/-- Two horizontal segments from `u` sharing a point other than `u` have the same direction. -/
theorem ray_dir_eq {u : Point} {σ σ' T T' : ℝ} (hσ : σ = 1 ∨ σ = -1) (hσ' : σ' = 1 ∨ σ' = -1)
    (hT : 0 < T) (hmem : ∃ s, 0 ≤ s ∧ s ≤ T' ∧ rayPt u σ T = rayPt u σ' s) : σ = σ' := by
  obtain ⟨s, hs0, -, h⟩ := hmem
  have h1 := congrArg Prod.fst h
  ϴ' rayPt at h1
  rcases hσ with rfl | rfl <;> rcases hσ' with rfl | rfl
  · rfl
  · exfalso; nlinarith
  · exfalso; nlinarith
  · rfl

end SplitGeo

/-! ## The split vertex of the right stretch (case G) -/

section Split

/-- **The regions around a vertex position that is not a cut**: one region is faced just before
and just after it. -/
theorem faces_around_vertex {M : Model} (hGM : GoodModel M) {Q : Polygon} {F : Set (Set Point)}
    (hFam : M.ChordFamily Q F) {p : ℕ} (hp : p < M.W.n) (hp0 : 0 < p)
    (hcut : ¬ M.IsCut F (p : ℝ)) :
    ∃ X ∈ M.regions F, AfterFaces M p 0 X ∧ BeforeFaces M p 0 X := by
  have hpos : (0 : ℝ) < p := by exact_mod_cast hp0
  obtain ⟨X, hX, l, r, harc, hin⟩ := WalkEmbed.exists_arc_around hGM hFam hpos hcut
  have hfac := harc.2.2.2.2.2.2
  obtain ⟨δ₁, hδ₁, h1⟩ := exists_of_eventually_gt (sideInArc_eventually_add hin)
  obtain ⟨δ₂, hδ₂, h2⟩ := exists_of_eventually_gt (sideInArc_eventually_sub hin)
  refine ⟨X, hX, ⟨δ₁, hδ₁, fun s h0 h1' h2' => ?_⟩,
    ⟨min δ₂ 1, lt_min hδ₂ one_pos, fun h => absurd h (lt_irrefl 0), fun _ s h0 h1' => ?_⟩⟩
  · Ξ' zero_add at h2' ⊢
    exact hfac p s hp h0 h2' (h1 s h0 h1')
  · have hs1 : s < 1 := lt_of_lt_of_le h1' (min_le_right _ _)
    have hsδ := lt_of_lt_of_le h1' (min_le_left _ _)
    Ξ prev_mod hp hp0
    refine hfac (p - 1) (1 - s) (⋄) (⟡) (⟡) ?_
    have : ((p - 1 : ℕ) : ℝ) + (1 - s) = (p : ℝ) - s := by
      rw [Nat.cast_sub hp0]; push_cast; ring
    rw [this]; exact h2 s h0 hsδ

variable (J : Merge.Junction)

/-- The two copies of the top of `C₂` next to the slit, in the walk of `C₂` (case G). -/
theorem copy_facts (hδ : 0 < rδ J) :
    (6 + tpos J.right 0 + rL1 J) % (chainModel J.right).W.n = 2 * J.right.m + 6 ∧
    (6 + tpos J.right 0 + rL1 J + rδ J) % (chainModel J.right).W.n = 6 ∧
    sidePt (chainModel J.right).W ((6 + tpos J.right 0 + rL1 J) % (chainModel J.right).W.n) 0 =
      J.right.top ∧
    sidePt (chainModel J.right).W
      ((6 + tpos J.right 0 + rL1 J + rδ J) % (chainModel J.right).W.n) 0 = J.right.top ∧
    (∀ x, sideLeft (chainModel J.right).W
        ((6 + tpos J.right 0 + rL1 J) % (chainModel J.right).W.n) 0 x ↔
      sideLeftOf (J.right.sideTour J.right.sideBeta (2 * J.right.m - 1)) J.right.top
        J.right.slitTop x) ∧
    (∀ x, sideLeft (chainModel J.right).W
        ((6 + tpos J.right 0 + rL1 J + rδ J) % (chainModel J.right).W.n) 0 x ↔
      sideLeftOf J.right.slitTop J.right.top (J.right.sideTour J.right.sideBeta 1) x) := by
  obtain ⟨g1, g2, v26, v0, v25, v6, v5, v7⟩ := gap_walk J hδ
  have hn₂ := cm_n J.right
  have hm := J.right.one_le
  have g2' : (6 + tpos J.right 0 + rL1 J + rδ J) % (chainModel J.right).W.n = 6 := by
    rw [add_assoc]; exact g2
  refine ⟨g1, g2', by rw [g1, Chazelle.Chain.sidePt_zero, v26],
    by rw [g2', Chazelle.Chain.sidePt_zero, v6], fun x => ?_, fun x => ?_⟩
  · rw [g1, Chazelle.Chain.sideLeft_zero]
    have e1 : (2 * J.right.m + 6 + 1) % (chainModel J.right).W.n = 0 := by
      rw [hn₂, show 2 * J.right.m + 6 + 1 = 2 * J.right.m + 7 by ring, Nat.mod_self]
    have e2 : (2 * J.right.m + 6 + (chainModel J.right).W.n - 1) % (chainModel J.right).W.n =
        2 * J.right.m + 5 := by
      rw [hn₂, show 2 * J.right.m + 6 + (2 * J.right.m + 7) - 1 = (2 * J.right.m + 5) +
        (2 * J.right.m + 7) by omega, Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
    rw [e1, e2, v0, v25, v26]
  · rw [g2', Chazelle.Chain.sideLeft_zero]
    have e1 : (6 + 1) % (chainModel J.right).W.n = 7 := by
      rw [hn₂]; exact Nat.mod_eq_of_lt (by omega)
    have e2 : (6 + (chainModel J.right).W.n - 1) % (chainModel J.right).W.n = 5 := by
      rw [hn₂, show 6 + (2 * J.right.m + 7) - 1 = 5 + (2 * J.right.m + 7) by omega,
        Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
    rw [e1, e2, v7, v5, v6]

/-- **The direction of a chord at a copy of the split vertex**: a chord of `C₂` attached at the
copy before the slit goes west, at the copy after it east. -/
theorem copy_dir (hP : J.P.Simple) (hδ : 0 < rδ J) {c : Set Point}
    (hc : c ∈ Merge.augChords J.right) :
    (SideAttach (chainModel J.right).W c
        ((6 + tpos J.right 0 + rL1 J) % (chainModel J.right).W.n) 0 →
      ∀ z ∈ c, z.1 ≤ J.right.top.1) ∧
    (SideAttach (chainModel J.right).W c
        ((6 + tpos J.right 0 + rL1 J + rδ J) % (chainModel J.right).W.n) 0 →
      ∀ z ∈ c, J.right.top.1 ≤ z.1) := by
  have hM₂ := walkAx_chainModel (C := J.right) hP
  obtain ⟨-, -, hp1, hp2, hs1, hs2⟩ := copy_facts J hδ
  have hRt := J.right.top_snd_lt_radius
  have hA0 := sideTour_sub_top_snd J.right J.right.sideBeta (2 * J.right.m - 1)
  have hB0 := sideTour_sub_top_snd J.right J.right.sideBeta 1
  have shape : ∀ P : ℕ, sidePt (chainModel J.right).W P 0 = J.right.top →
      SideAttach (chainModel J.right).W c P 0 → ∃ σ T : ℝ, (σ = 1 ∨ σ = -1) ∧ 0 < T ∧
        sideLeft (chainModel J.right).W P 0 (rayPt J.right.top σ 1) ∧
        ∀ z ∈ c, ∃ s, 0 ≤ s ∧ s ≤ T ∧ z = rayPt J.right.top σ s := by
    intro P hpu hA
    have hu : J.right.top ∈ c := hpu ▸ hA.2.2.2.1
    have huD : J.right.top ∉ (chainModel J.right).D := by
      rw [← hpu]; exact hM₂.trace _ hA.1 0 le_rfl zero_le_one
    obtain ⟨w, hwu, hwy, hcw⟩ := seg_of_end hM₂ hc hu huD
    obtain ⟨σ, T, hσ, hT, hray, hseg⟩ := seg_ray hwu hwy
    exact ⟨σ, T, hσ, hT, sideLeft_of_attach_seg hpu hA hcw hσ hT hray,
      fun z hz => hseg z (hcw ▸ hz)⟩
  constructor
  · intro hA
    obtain ⟨σ, T, hσ, -, hsl, hseg⟩ := shape _ hp1 hA
    Ξ' hs1 at hsl
    unfold sideLeftOf at hsl
    Ξ' rayPt_sub_self, slitTop_sub_top at hsl
    have hneg := ccw_up_left (⟡) hA0 hsl
    intro z hz
    obtain ⟨s, hs0, -, rfl⟩ := hseg z hz
    ϴ rayPt
    nlinarith
  · intro hA
    obtain ⟨σ, T, hσ, -, hsl, hseg⟩ := shape _ hp2 hA
    Ξ' hs2 at hsl
    unfold sideLeftOf at hsl
    Ξ' rayPt_sub_self, slitTop_sub_top at hsl
    have hpos := ccw_up_right (⟡) hB0 hsl
    intro z hz
    obtain ⟨s, hs0, -, rfl⟩ := hseg z hz
    ϴ rayPt
    nlinarith

/-- **The copy of a chord at the split vertex**: a chord of `C` attached at the split vertex of
the right stretch, inside an augmented chord `c` of `C₂`, goes west and `c` is attached at the
copy before the slit, or it goes east and `c` is attached at the copy after the slit. -/
theorem split_copy (hP : J.P.Simple) (hδ : 0 < rδ J) {f c : Set Point}
    (hf : f ∈ Merge.augChords J.whole) (hc : c ∈ Merge.augChords J.right) (hfc : f ⊆ c)
    (hfA : SideAttach (chainModel J.whole).W f
      ((6 + tpos J.whole J.m₁ + rL1 J) % (chainModel J.whole).W.n) 0) :
    ((∀ z ∈ c, z.1 ≤ J.right.top.1) ∧ SideAttach (chainModel J.right).W c
        ((6 + tpos J.right 0 + rL1 J) % (chainModel J.right).W.n) 0) ∨
      ((∀ z ∈ c, J.right.top.1 ≤ z.1) ∧ SideAttach (chainModel J.right).W c
        ((6 + tpos J.right 0 + rL1 J + rδ J) % (chainModel J.right).W.n) 0) := by
  have hM := walkAx_chainModel (C := J.whole) hP
  have hM₂ := walkAx_chainModel (C := J.right) hP
  obtain ⟨hpt, hsec⟩ := split_facts J hδ
  obtain ⟨-, -, hp1, hp2, hs1, hs2⟩ := copy_facts J hδ
  have hRt := J.right.top_snd_lt_radius
  have hA0 := sideTour_sub_top_snd J.right J.right.sideBeta (2 * J.right.m - 1)
  have hB0 := sideTour_sub_top_snd J.right J.right.sideBeta 1
  have hn₂ : 0 < (chainModel J.right).W.n := by rw [cm_n]; omega
  set u := J.right.top with hu_def
  have huf : u ∈ f := hpt ▸ hfA.2.2.2.1
  have huD : u ∉ (chainModel J.whole).D := by
    rw [← hpt]; exact hM.trace _ hfA.1 0 le_rfl zero_le_one
  obtain ⟨w, hwu, hwy, hfw⟩ := seg_of_end hM hf huf huD
  obtain ⟨σ, T, hσ, hT, hray, -⟩ := seg_ray hwu hwy
  have hslM := sideLeft_of_attach_seg hpt hfA hfw hσ hT hray
  Ξ' hsec at hslM
  unfold sideLeftOf at hslM
  Ξ' rayPt_sub_self at hslM
  -- the shape of `c`
  have huD₂ : u ∉ (chainModel J.right).D := fun h =>
    J.right.not_mem_set_of_mem_dom h J.right.top_mem_set
  obtain ⟨w', hwu', hwy', hcw⟩ := seg_of_end hM₂ hc (hfc huf) huD₂
  obtain ⟨σ', T', hσ', -, -, hseg'⟩ := seg_ray hwu' hwy'
  have hσσ : σ = σ' := by
    refine ray_dir_eq (u := u) (T' := T') hσ hσ' hT ?_
    have : rayPt u σ T ∈ Chazelle.segment u w' := by
      rw [← hcw]; exact hfc (hfw ▸ hray T hT.le le_rfl)
    obtain ⟨s, hs0, hs1', he⟩ := hseg' _ this
    exact ⟨s, hs0, hs1', he⟩
  subst hσσ
  rcases hσ with rfl | rfl
  · right
    refine ⟨fun z hz => ?_, attach_of_sideLeft_seg (Nat.mod_lt _ hn₂) hp2 ?_ hcw hseg'⟩
    · obtain ⟨s, hs0, -, rfl⟩ := hseg' z (hcw ▸ hz)
      simp only [rayPt]; linarith
    · Ξ hs2
      unfold sideLeftOf
      Ξ rayPt_sub_self, slitTop_sub_top
      exact ccw_corner_east (⟡) hA0 hB0 hslM one_pos
  · left
    refine ⟨fun z hz => ?_, attach_of_sideLeft_seg (Nat.mod_lt _ hn₂) hp1 ?_ hcw hseg'⟩
    · obtain ⟨s, hs0, -, rfl⟩ := hseg' z (hcw ▸ hz)
      simp only [rayPt]; linarith
    · Ξ hs1
      unfold sideLeftOf
      Ξ rayPt_sub_self, slitTop_sub_top
      exact ccw_corner_west (⟡) hA0 hB0 hslM (⊛)

end Split

/-! ## The split step -/

section SplitStep

variable (J : Merge.Junction)

/-- **No chord of `S₂` at the other copy of the split vertex** when a single chord of `F₂⁺` is
attached at the split vertex of the right stretch (case G): its piece at the top of `C₂` would be
attached there too. -/
theorem other_copy_not_cut (hP : J.P.Simple) {S₂ : Set (Set Point)}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hS₂f : S₂.Finite) (hδ : 0 < rδ J) {f c : Set Point}
    (hf : f ∈ F₂plus J S₂) (hc : c ∈ Merge.augChords J.right) (hfc : f ⊆ c)
    (hfA : SideAttach (chainModel J.whole).W f
      ((6 + tpos J.whole J.m₁ + rL1 J) % (chainModel J.whole).W.n) 0)
    (huniq : ∀ e' ∈ F₂plus J S₂, SideAttach (chainModel J.whole).W e'
      ((6 + tpos J.whole J.m₁ + rL1 J) % (chainModel J.whole).W.n) 0 → e' = f) :
    ((∀ z ∈ c, z.1 ≤ J.right.top.1) → ¬ (chainModel J.right).IsCut S₂
      (((6 + tpos J.right 0 + rL1 J + rδ J) % (chainModel J.right).W.n : ℕ) : ℝ)) ∧
    ((∀ z ∈ c, J.right.top.1 ≤ z.1) → ¬ (chainModel J.right).IsCut S₂
      (((6 + tpos J.right 0 + rL1 J) % (chainModel J.right).W.n : ℕ) : ℝ)) := by
  have hC := corr_right0 J hP hS₂ hS₂f
  have hM₂ := hC.hM₂
  obtain ⟨hpt, -⟩ := split_facts J hδ
  obtain ⟨-, -, hp1, hp2, -, -⟩ := copy_facts J hδ
  obtain ⟨hL1, -, -, -, -⟩ := caseG_consts J hδ
  have hτ' := tpos_lt J.right 0
  have hn₂ := cm_n J.right
  have huD₂ : J.right.top ∉ (chainModel J.right).D := fun h =>
    J.right.not_mem_set_of_mem_dom h J.right.top_mem_set
  have hunV : J.right.top ≠ (chainModel J.right).W.vtx (6 + tpos J.right 0) := by
    Ξ ← hp1
    have hoff := off_key (t := 0) hC.hg' (show rL1 J < (chainModel J.right).W.n by omega) le_rfl
      zero_lt_one
    have h1 : (1 : ℝ) ≤ rL1 J := by exact_mod_cast (show 1 ≤ rL1 J by omega)
    have hL := hC.hfull hδ
    have h2 : (rL1 J : ℝ) + 1 ≤ ((rL1 J + rδ J + rL2 J : ℕ) : ℝ) := by
      exact_mod_cast (show rL1 J + 1 ≤ rL1 J + rδ J + rL2 J by omega)
    refine hC.noV _ (Nat.mod_lt _ hC.n₂_pos) 0 le_rfl zero_lt_one ?_ ?_
    · rw [hoff]; linarith
    · rw [hoff]; push_cast at h2 ⊢; linarith
  -- a chord of `S₂` at a copy of the split vertex is `c`
  have hsame : ∀ k : ℕ, (k = rL1 J ∨ k = rL1 J + rδ J) → ∀ c'' ∈ S₂,
      SideAttach (chainModel J.right).W c'' ((6 + tpos J.right 0 + k) %
        (chainModel J.right).W.n) 0 →
      sidePt (chainModel J.right).W ((6 + tpos J.right 0 + k) % (chainModel J.right).W.n) 0 =
        J.right.top → c'' = c := by
    intro k hk c'' hc'' hA'' hpk
    have hu'' := hpk ▸ hA''.2.2.2.1
    obtain ⟨e'', he'', hue'', hec''⟩ := hC.trans c'' hc'' _ hu'' huD₂ hunV
    have heA := splitAttach_right J hP hS₂ hδ k hk c'' hc'' hA'' e'' he'' hec''
      (by rw [hpt]; exact hue'')
    have := huniq e'' he'' heA
    subst this
    exact s2_eq_of_sub J (S₂ := Merge.augChords J.right) subset_rfl (hS₂ hc'') hc
      (F₂plus_subset J hS₂ he'') hec'' hfc
  -- `c` does not go both ways
  have hboth : (∀ z ∈ c, z.1 ≤ J.right.top.1) → (∀ z ∈ c, J.right.top.1 ≤ z.1) → False := by
    intro hW hE
    have hu := hfc (hpt ▸ hfA.2.2.2.1)
    obtain ⟨w, hwu, hwy, hcw⟩ := seg_of_end hM₂ hc hu huD₂
    have hw : w ∈ c := by rw [hcw]; exact Geometry.right_mem_segment _ _
    exact hwu (Geometry.point_ext (le_antisymm (hW w hw) (hE w hw)) hwy)
  constructor
  · rintro hW ⟨c'', hc'', p, t, hA'', hkey⟩
    obtain ⟨hp, ht⟩ := Chazelle.Chain.sideKey_inj le_rfl zero_lt_one hA''.2.1 hA''.2.2.1
      (show (((6 + tpos J.right 0 + rL1 J + rδ J) % (chainModel J.right).W.n : ℕ) : ℝ) + 0 =
        p + t by rw [add_zero]; exact hkey)
    subst hp; subst ht
    have hA2 : SideAttach (chainModel J.right).W c''
        ((6 + tpos J.right 0 + (rL1 J + rδ J)) % (chainModel J.right).W.n) 0 := by
      rw [← add_assoc]; exact hA''
    have hcc := hsame _ (Or.inr rfl) c'' hc'' hA2 (by rw [← add_assoc]; exact hp2)
    subst hcc
    exact hboth hW ((copy_dir J hP hδ hc).2 hA'')
  · rintro hE ⟨c'', hc'', p, t, hA'', hkey⟩
    obtain ⟨hp, ht⟩ := Chazelle.Chain.sideKey_inj le_rfl zero_lt_one hA''.2.1 hA''.2.2.1
      (show (((6 + tpos J.right 0 + rL1 J) % (chainModel J.right).W.n : ℕ) : ℝ) + 0 =
        p + t by rw [add_zero]; exact hkey)
    subst hp; subst ht
    have hcc := hsame _ (Or.inl rfl) c'' hc'' hA'' hp1
    subst hcc
    exact hboth ((copy_dir J hP hδ hc).1 hA'') hE

end SplitStep

section SplitStep2

variable (J : Merge.Junction)

/-- **The split step** (case G).  Let `f ∈ F₂⁺`, inside a chord `c` of `S₂x`, be attached at the
split vertex of the right stretch, with `G` on its side `ρ` and `V` on the side `ρ` of `c`.
Then `V` is a label of `G`; or `V` is a gap label and `G` has a gap label; or `V` is a gap label
and the split vertex is a tie whose other chord `f'` (with `G` on its side `ρ` too) lies in a
chord of `S₂x` whose side `ρ` is a gap label, or has its other end off the stretch. -/
theorem split_step (hP : J.P.Simple) {Q : Polygon} {S₂ : Set (Set Point)}
    (hS₂ : (chainModel J.right).ChordFamily Q S₂)
    (hF : (chainModel J.whole).ChordFamily Q (F₂plus J S₂)) (hδ : 0 < rδ J)
    {f c : Set Point} (hf : f ∈ F₂plus J S₂) (hc : c ∈ S₂x J S₂) (hfc : f ⊆ c)
    (hfA : SideAttach (chainModel J.whole).W f
      ((6 + tpos J.whole J.m₁ + rL1 J) % (chainModel J.whole).W.n) 0)
    {ρ : ℝ} (hρ : ρ = 1 ∨ ρ = -1) {G V : Set Point}
    (hG : G ∈ (chainModel J.whole).regions (F₂plus J S₂))
    (hV : V ∈ (chainModel J.right).regions S₂) (hGs : SideOf (chainModel J.whole) ρ f G)
    (hVs : SideOf (chainModel J.right) ρ c V) :
    RLabel J S₂ G V ∨ (GapLab J S₂ V ∧ ∃ Vg, GapLab J S₂ Vg ∧ RLabel J S₂ G Vg) ∨
      (GapLab J S₂ V ∧ ∃ f' ∈ F₂plus J S₂, f' ≠ f ∧ SideAttach (chainModel J.whole).W f'
        ((6 + tpos J.whole J.m₁ + rL1 J) % (chainModel J.whole).W.n) 0 ∧
        SideOf (chainModel J.whole) ρ f' G ∧
        ((∃ c' ∈ S₂x J S₂, f' ⊆ c' ∧ ∃ V' ∈ (chainModel J.right).regions S₂,
            SideOf (chainModel J.right) ρ c' V' ∧ GapLab J S₂ V') ∨
          ((J.shared ∈ f' ∨ J.right.top ∈ f') ∧
            OffOut J f' ((6 + tpos J.whole J.m₁ + rL1 J) % (chainModel J.whole).W.n) 0))) := by
  have hC := corr_right0 J hP hS₂.2.1 hS₂.1
  have hSx := S₂x_family J hS₂ hF
  have hM := hC.hM
  have hM₂ := hC.hM₂
  have hFs := hC.hF
  have hSs : S₂x J S₂ ⊆ (chainModel J.right).Adm := S₂x_subset J hS₂.2.1
  have hGM : GoodModel (chainModel J.whole) := Or.inl ⟨J.whole, hP, rfl⟩
  have hGM₂ : GoodModel (chainModel J.right) := Or.inl ⟨J.right, hP, rfl⟩
  obtain ⟨hL1, -, hL2, -, hlt⟩ := caseG_consts J hδ
  have hτ' := tpos_lt J.right 0
  have hm2 : J.right.m = J.m₂ := rfl
  have hL1pos : 1 ≤ rL1 J := ⋄
  have hd : rL1 J < rL1 J + rL2 J := ⋄
  obtain ⟨hpt, -⟩ := split_facts J hδ
  obtain ⟨hk1, hk2, hp1, hp2, -, -⟩ := copy_facts J hδ
  have hn₂ := cm_n J.right
  set W := (chainModel J.whole).W with hWdef
  set W₂ := (chainModel J.right).W with hW₂def
  set Pu := (6 + tpos J.whole J.m₁ + rL1 J) % W.n with hPudef
  set k₁ := (6 + tpos J.right 0 + rL1 J) % W₂.n with hk₁def
  set k₂ := (6 + tpos J.right 0 + rL1 J + rδ J) % W₂.n with hk₂def
  set u := J.right.top with hudef
  have hk₂' : (6 + tpos J.right 0 + (rL1 J + rδ J)) % W₂.n = k₂ := Ρ ← add_assoc
  have hk1n : k₁ < W₂.n := Nat.mod_lt _ hC.n₂_pos
  have hk2n : k₂ < W₂.n := Nat.mod_lt _ hC.n₂_pos
  -- the region of `S₂x` on the side `ρ` of `c`
  obtain ⟨U, hU, hUV, hUs⟩ := sub_region_side hM₂ (subset_S₂x J S₂) hSs hSx.1 hc hρ hV hVs
  -- labels from the positions around the split vertex
  have hRLa : ∀ X, AfterFaces (chainModel J.whole) Pu 0 G →
      AfterFaces (chainModel J.right) k₂ 0 X → RLabel J S₂ G X := by
    intro X h1 h2
    refine rlabel_after2 J hP hS₂.2.1 hS₂.1 hd le_rfl zero_lt_one h1 ?_
    have e : 6 + tpos J.right 0 + dq (rL1 J) (rδ J) (rL1 J) =
        6 + tpos J.right 0 + rL1 J + rδ J := by
      unfold dq; rw [ite_eq_right (lt_irrefl _)]; ring
    rw [e]; exact h2
  have hRLb : ∀ X, BeforeFaces (chainModel J.whole) Pu 0 G →
      BeforeFaces (chainModel J.right) k₁ 0 X → RLabel J S₂ G X := by
    intro X h1 h2
    refine rlabel_before0_2 J hP hS₂.2.1 hS₂.1 hL1pos hd.le h1 ?_
    have e : 6 + tpos J.right 0 + (dq (rL1 J) (rδ J) (rL1 J - 1) + 1) =
        6 + tpos J.right 0 + rL1 J := by
      unfold dq; rw [ite_eq_left (⋄)]; omega
    rw [e]; exact h2
  -- the leaving edge at the split vertex is not above it
  have hwa : (chainModel J.whole).wa Pu = u := by
    rw [← hpt, Chazelle.Chain.sidePt_zero]; rfl
  have hwb : ((chainModel J.whole).wb Pu).2 ≤ u.2 := by
    have e := hC.sideNext_eq hd
    have edq : dq (rL1 J) (rδ J) (rL1 J) = rL1 J + rδ J := by
      unfold dq; Ξ ite_eq_right (lt_irrefl _)
    obtain ⟨-, g2, -, -, -, -, -, v7⟩ := gap_walk J hδ
    Ξ' edq, g2 at e
    have e7 : sideNext W₂ 6 = J.right.sideTour J.right.sideBeta 1 := by
      unfold Chazelle.Chain.sideNext; rw [hn₂, Nat.mod_eq_of_lt (⋄)]; exact v7
    show (sideNext W Pu).2 ≤ u.2
    Ξ e, e7
    have := sideTour_sub_top_snd J.right J.right.sideBeta 1
    ϴ' Prod.snd_sub at this
    linarith
  have hinPu : 0 < off W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ((Pu : ℝ) + 0) ∧
      off W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ((Pu : ℝ) + 0) < ((rL1 J + rL2 J : ℕ) : ℝ) := by
    Ξ hC.off_M hd (t := 0) le_rfl zero_lt_one
    have h1 : (1 : ℝ) ≤ rL1 J := by exact_mod_cast hL1pos
    have h2 : ((rL1 J : ℕ) : ℝ) + 1 ≤ ((rL1 J + rL2 J : ℕ) : ℝ) := by exact_mod_cast hd
    constructor <;> linarith
  have hdw : ∀ f' ∈ F₂plus J S₂, f' ≠ f → SideAttach W f' Pu 0 →
      ((chainModel J.whole).wb Pu).2 ≠ ((chainModel J.whole).wa Pu).2 →
      ((chainModel J.whole).wb Pu).2 < ((chainModel J.whole).wa Pu).2 := by
    intro f' _ _ _ hhor
    Ξ' hwa at hhor ⊢
    exact lt_of_le_of_ne hwb hhor
  have hpart : ∀ f' ∈ F₂plus J S₂, SideAttach W f' Pu 0 → (∃ c' ∈ S₂x J S₂, f' ⊆ c') ∨
      ((J.shared ∈ f' ∨ J.right.top ∈ f') ∧ OffOut J f' Pu 0) := by
    intro f' hf' hA'
    rcases F₂plus_kind J hS₂.2.1 hf' with ⟨c₀, hc₀, hfc₀⟩ | hkind
    · exact Or.inl ⟨c₀, subset_S₂x J S₂ hc₀, hfc₀⟩
    rcases partner_cases J hP hS₂.2.1 hS₂.1 hf' hA' hinPu with h | h
    · exact Or.inl ⟨f', Or.inr ⟨hf', h⟩, subset_rfl⟩
    · exact Or.inr ⟨hkind, h⟩
  rcases split_copy J hP hδ (F₂plus_subset J hS₂.2.1 hf) (hSs hc) hfc hfA with
    ⟨hcW, hAk⟩ | ⟨hcE, hAk⟩
  · -- `c` goes west, attached at the copy before the slit
    have hdirF : ((-1 : ℝ) = 1 ∧ ∀ z ∈ f, (sidePt W Pu 0).1 ≤ z.1) ∨
        ((-1 : ℝ) = -1 ∧ ∀ z ∈ f, z.1 ≤ (sidePt W Pu 0).1) :=
      Or.inr ⟨rfl, fun z hz => by rw [hpt]; exact hcW z (hfc hz)⟩
    have hdirC : ((-1 : ℝ) = 1 ∧ ∀ z ∈ c, (sidePt W₂ k₁ 0).1 ≤ z.1) ∨
        ((-1 : ℝ) = -1 ∧ ∀ z ∈ c, z.1 ≤ (sidePt W₂ k₁ 0).1) :=
      Or.inr ⟨rfl, fun z hz => by rw [hp1]; exact hcW z hz⟩
    obtain ⟨FW1, FW2⟩ := faced_or_middle hGM hF hf hfA hρ hG hGs hdirF
    have hFV := (faced_or_middle hGM₂ hSx hc hAk hρ hU hUs hdirC).1 (fun c'' hc'' hA'' =>
      oneAt_right J hP (S₂x_subset J hS₂.2.1) hδ (rL1 J) (Or.inl rfl) c'' hc'' c hc hA'' hAk)
    rcases hρ with rfl | rfl
    · -- above `c`: the west side of the slit
      have hgapV : GapLab J S₂ V :=
        ⟨hδ, hV, Or.inl (afterFaces_mono (hFV.1 (⊛)) hUV)⟩
      right
      by_cases htie : ∃ f' ∈ F₂plus J S₂, f' ≠ f ∧ SideAttach W f' Pu 0
      · obtain ⟨f', hf', hne, hA'⟩ := htie
        obtain ⟨-, hhor, hdn, -⟩ := FW2 f' hf' hne hA'
        refine Or.inr ⟨hgapV, f', hf', hne, hA', (hdn (hdw f' hf' hne hA' hhor)).1 rfl, ?_⟩
        rcases hpart f' hf' hA' with ⟨c', hc'x, hfc'⟩ | hoff
        · left
          rcases split_copy J hP hδ (F₂plus_subset J hS₂.2.1 hf') (hSs hc'x) hfc' hA' with
            ⟨hW', -⟩ | ⟨hE', hAk'⟩
          · exact absurd (hM.attach_west_unique hFs hf' hf hA' hfA
              (fun z hz => by rw [hpt]; exact hW' z (hfc' hz))
              (fun z hz => by rw [hpt]; exact hcW z (hfc hz))) hne
          · obtain ⟨U', hU', hU's⟩ := side_region_exists' hM₂ hSs hSx.1 hc'x (Or.inl rfl)
            obtain ⟨V', hV', hU'V'⟩ := super_region (subset_S₂x J S₂) hU'
            have hdirC' : ((1 : ℝ) = 1 ∧ ∀ z ∈ c', (sidePt W₂ k₂ 0).1 ≤ z.1) ∨
                ((1 : ℝ) = -1 ∧ ∀ z ∈ c', z.1 ≤ (sidePt W₂ k₂ 0).1) :=
              Or.inl ⟨rfl, fun z hz => by rw [hp2]; exact hE' z hz⟩
            have hFV' := (faced_or_middle hGM₂ hSx hc'x hAk' (Or.inl rfl) hU' hU's hdirC').1
              (fun c'' hc'' hA'' => oneAt_right J hP (S₂x_subset J hS₂.2.1) hδ (rL1 J + rδ J)
                (Or.inr rfl) c'' hc'' c' hc'x (by rw [hk₂']; exact hA'')
                (by rw [hk₂']; exact hAk'))
            exact ⟨c', hc'x, hfc', V', hV', sideOf_mono hU's hU'V', hδ, hV',
              Or.inr (beforeFaces_mono (hFV'.2 (⊛)) hU'V')⟩
        · exact Or.inr hoff
      · push Not at htie
        have huniq : ∀ e' ∈ F₂plus J S₂, SideAttach W e' Pu 0 → e' = f :=
          fun e' he' hA' => by_contra fun h => htie e' he' h hA'
        have hGa := (FW1 huniq).1 (⊛)
        have hnc := (other_copy_not_cut J hP hS₂.2.1 hS₂.1 hδ hf (hSs hc) hfc hfA huniq).1 hcW
        obtain ⟨X, hX, hXa, hXb⟩ := faces_around_vertex hGM₂ hS₂ hk2n (by rw [hk2]; norm_num)
          hnc
        exact Or.inl ⟨hgapV, X, ⟨hδ, hX, Or.inr hXb⟩, hRLa X hGa hXa⟩
    · -- below `c`: faced before the split vertex in both walks
      left
      have hGb : BeforeFaces (chainModel J.whole) Pu 0 G := by
        by_cases htie : ∃ f' ∈ F₂plus J S₂, f' ≠ f ∧ SideAttach W f' Pu 0
        · obtain ⟨f', hf', hne, hA'⟩ := htie
          obtain ⟨-, hhor, hdn, -⟩ := FW2 f' hf' hne hA'
          exact ((hdn (hdw f' hf' hne hA' hhor)).2 rfl).2 (⊛)
        · push Not at htie
          exact (FW1 fun e' he' hA' => by_contra fun h => htie e' he' h hA').2 (⊛)
      exact hRLb V hGb (beforeFaces_mono (hFV.2 (⊛)) hUV)
  · -- `c` goes east, attached at the copy after the slit
    have hdirF : ((1 : ℝ) = 1 ∧ ∀ z ∈ f, (sidePt W Pu 0).1 ≤ z.1) ∨
        ((1 : ℝ) = -1 ∧ ∀ z ∈ f, z.1 ≤ (sidePt W Pu 0).1) :=
      Or.inl ⟨rfl, fun z hz => by rw [hpt]; exact hcE z (hfc hz)⟩
    have hdirC : ((1 : ℝ) = 1 ∧ ∀ z ∈ c, (sidePt W₂ k₂ 0).1 ≤ z.1) ∨
        ((1 : ℝ) = -1 ∧ ∀ z ∈ c, z.1 ≤ (sidePt W₂ k₂ 0).1) :=
      Or.inl ⟨rfl, fun z hz => by rw [hp2]; exact hcE z hz⟩
    obtain ⟨FW1, FW2⟩ := faced_or_middle hGM hF hf hfA hρ hG hGs hdirF
    have hFV := (faced_or_middle hGM₂ hSx hc hAk hρ hU hUs hdirC).1 (fun c'' hc'' hA'' =>
      oneAt_right J hP (S₂x_subset J hS₂.2.1) hδ (rL1 J + rδ J) (Or.inr rfl) c'' hc'' c hc
        (by rw [hk₂']; exact hA'') (by rw [hk₂']; exact hAk))
    rcases hρ with rfl | rfl
    · -- above `c`: the east side of the slit
      have hgapV : GapLab J S₂ V :=
        ⟨hδ, hV, Or.inr (beforeFaces_mono (hFV.2 (⊛)) hUV)⟩
      right
      by_cases htie : ∃ f' ∈ F₂plus J S₂, f' ≠ f ∧ SideAttach W f' Pu 0
      · obtain ⟨f', hf', hne, hA'⟩ := htie
        obtain ⟨-, hhor, hdn, -⟩ := FW2 f' hf' hne hA'
        refine Or.inr ⟨hgapV, f', hf', hne, hA', (hdn (hdw f' hf' hne hA' hhor)).1 rfl, ?_⟩
        rcases hpart f' hf' hA' with ⟨c', hc'x, hfc'⟩ | hoff
        · left
          rcases split_copy J hP hδ (F₂plus_subset J hS₂.2.1 hf') (hSs hc'x) hfc' hA' with
            ⟨hW', hAk'⟩ | ⟨hE', -⟩
          · obtain ⟨U', hU', hU's⟩ := side_region_exists' hM₂ hSs hSx.1 hc'x (Or.inl rfl)
            obtain ⟨V', hV', hU'V'⟩ := super_region (subset_S₂x J S₂) hU'
            have hdirC' : ((-1 : ℝ) = 1 ∧ ∀ z ∈ c', (sidePt W₂ k₁ 0).1 ≤ z.1) ∨
                ((-1 : ℝ) = -1 ∧ ∀ z ∈ c', z.1 ≤ (sidePt W₂ k₁ 0).1) :=
              Or.inr ⟨rfl, fun z hz => by rw [hp1]; exact hW' z hz⟩
            have hFV' := (faced_or_middle hGM₂ hSx hc'x hAk' (Or.inl rfl) hU' hU's hdirC').1
              (fun c'' hc'' hA'' => oneAt_right J hP (S₂x_subset J hS₂.2.1) hδ (rL1 J)
                (Or.inl rfl) c'' hc'' c' hc'x hA'' hAk')
            exact ⟨c', hc'x, hfc', V', hV', sideOf_mono hU's hU'V', hδ, hV',
              Or.inl (afterFaces_mono (hFV'.1 (⊛)) hU'V')⟩
          · exact absurd (hM.attach_east_unique hFs hf' hf hA' hfA
              (fun z hz => by rw [hpt]; exact hE' z (hfc' hz))
              (fun z hz => by rw [hpt]; exact hcE z (hfc hz))) hne
        · exact Or.inr hoff
      · push Not at htie
        have huniq : ∀ e' ∈ F₂plus J S₂, SideAttach W e' Pu 0 → e' = f :=
          fun e' he' hA' => by_contra fun h => htie e' he' h hA'
        have hGb := (FW1 huniq).2 (⊛)
        have hnc := (other_copy_not_cut J hP hS₂.2.1 hS₂.1 hδ hf (hSs hc) hfc hfA huniq).2 hcE
        obtain ⟨X, hX, hXa, hXb⟩ := faces_around_vertex hGM₂ hS₂ hk1n (by rw [hk1]; omega)
          hnc
        exact Or.inl ⟨hgapV, X, ⟨hδ, hX, Or.inl hXa⟩, hRLb X hGb hXb⟩
    · -- below `c`: faced after the split vertex in both walks
      left
      have hGa : AfterFaces (chainModel J.whole) Pu 0 G := by
        by_cases htie : ∃ f' ∈ F₂plus J S₂, f' ≠ f ∧ SideAttach W f' Pu 0
        · obtain ⟨f', hf', hne, hA'⟩ := htie
          obtain ⟨-, hhor, hdn, -⟩ := FW2 f' hf' hne hA'
          exact ((hdn (hdw f' hf' hne hA' hhor)).2 rfl).1 (⊛)
        · push Not at htie
          exact (FW1 fun e' he' hA' => by_contra fun h => htie e' he' h hA').1 (⊛)
      exact hRLa V hGa (afterFaces_mono (hFV.1 (⊛)) hUV)

end SplitStep2

end Sweep

end

end Chazelle.Core
