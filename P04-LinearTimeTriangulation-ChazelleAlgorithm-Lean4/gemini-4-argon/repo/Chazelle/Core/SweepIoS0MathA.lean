module

public import Chazelle.Core.SweepIoSpec
public import Chazelle.Core.SweepEvOrigin
public import Chazelle.Core.SweepEvCand3
public import Chazelle.Core.SweepMachine10
public import Chazelle.Core.SweepRamLog
public import Chazelle.Core.SweepWalk

/-!
# The side-0 answer cases (sweep, `Side0MathSpec`), part 1: tools

* `hPoly`, `chordFamily_hPoly`: a polygon carrying the heights of a finite family of augmented
  chords (so that the generic leave lemmas, stated for chord families, apply to `F₂⁺`);
* `left_pt_right_dom`: a point of `C₁` other than the shared vertex, not above the top of `C₂`,
  is in the domain of `C₂`;
* `left_hit_of`, `right_hit_of`: the first hit of `C` is the one of `C₁` unless its point is on
  `C₂` and off `C₁`; it is the one of `C₂` when its point is on `C₂`;
* `after_of_near`, `near_after`, `near_before`: regions faced just after a key, from a non-cut
  position facing it with no cut in between.
-/

namespace Chazelle.Core

namespace S0Math

open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sidePt sideLeft sideInArc)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd hseg)
open Chazelle.Merge (FreeAt)
open WalkEmbed Sweep

@[expose] public section

/-! ## A polygon carrying the heights of a family -/

/-- A polygon whose vertices carry the heights of the chords of a finite family. -/
noncomputable def hPoly (F : Set (Set Point)) (hfin : F.Finite) : Polygon :=
  ⟨hfin.toFinset.toList.map fun c => ((0 : ℝ), (Merge.lend c).2)⟩

theorem chordFamily_hPoly (C : Chain) {F : Set (Set Point)} (hfin : F.Finite)
    (hF : F ⊆ Merge.augChords C) : (chainModel C).ChordFamily (hPoly F hfin) F := by
  refine ⟨hfin, hF, fun c hc => ?_⟩
  have hmem : ((0 : ℝ), (Merge.lend c).2) ∈ (hPoly F hfin).vertices := by
    simp only [hPoly]
    exact List.mem_map.2 ⟨c, by simp [hc], rfl⟩
  obtain ⟨h, hh, he⟩ := List.mem_iff_getElem.1 hmem
  obtain ⟨y, a, b, -, -, hcd, hl, -⟩ := Merge.augChords_spec (hF hc)
  refine ⟨h, hh, a, b, ?_⟩
  have hv : (hPoly F hfin).vtx h = ((0 : ℝ), (Merge.lend c).2) := by
    unfold Polygon.vtx
    rw [List.getD_eq_getElem _ _ hh, he]
  rw [hv, hl, hcd]

/-! ## The query point -/

variable (J : Merge.Junction)

/-- **A point of `C₁` other than the shared vertex, not above the top of `C₂`, is in the domain of
`C₂`.** -/
theorem left_pt_right_dom (hP : J.P.Simple) {z : Point} (hz : z ∈ J.left.set)
    (hzv : z ≠ J.shared) (hz2 : z.2 ≤ J.right.top.2) : z ∈ J.right.dom := by
  by_contra h
  rcases (Merge.not_mem_dom_iff J.right hz2).1 h with hb | hs
  · apply hb
    rw [FuseMath.radius_of_P J (C' := J.right) rfl, ← FuseMath.radius_of_P J (C' := J.left) rfl]
    exact J.left.set_subset_box hz
  · have : z ∈ J.left.set ∩ J.right.set := ⟨hz, hs⟩
    rw [J.left_inter_right hP] at this
    exact hzv this

/-- A point of `C₁` is strictly inside the box of `C`. -/
theorem left_pt_abs {z : Point} (hz : z ∈ J.left.set) : |z.2| < J.whole.radius := by
  rw [← FuseMath.radius_of_P J (C' := J.left) rfl]
  exact (J.left.set_subset_box hz).2

/-- **The first hit of `C₁`**: unless the hit point of `C` is on `C₂` and off `C₁`, the first hit
of `C` is the first hit of `C₁`. -/
theorem left_hit_of {z : Point} (hz₁ : z.2 ≤ J.left.top.2) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hfree : FreeAt J.whole z σ)
    (hc : ¬ (rayPt z σ (J.whole.hitParam z σ) ∈ J.right.set ∧
      rayPt z σ (J.whole.hitParam z σ) ∉ J.left.set)) :
    J.left.hitParam z σ = J.whole.hitParam z σ := by
  have hz' : z.2 ≤ J.whole.top.2 := hz₁.trans J.left_top_le
  obtain ⟨hT, hwD, hdom⟩ := Merge.hit_of_freeAt J.whole hz' hσ hfree
  set T := J.whole.hitParam z σ
  have hy : ∀ t, (rayPt z σ t).2 = z.2 := fun t => rfl
  have hfree₁ : Merge.FreeAt J.left z σ := by
    filter_upwards [hfree] with t ht
    exact dom_left J ht (by rwa [hy])
  obtain ⟨hT₁, hw₁D, hdom₁⟩ := Merge.hit_of_freeAt J.left hz₁ hσ hfree₁
  have hwD₁ : rayPt z σ T ∉ J.left.dom := by
    intro hmem
    rcases (Merge.not_mem_dom_iff J.whole (p := rayPt z σ T) (by rwa [hy])).1 hwD
      with h | h
    · apply h
      rw [← FuseMath.radius_of_P J (C' := J.left) rfl]
      exact J.left.dom_subset_box hmem
    · rw [J.whole_set] at h
      rcases h with h | h
      · exact J.left.not_mem_set_of_mem_dom hmem h
      · exact hc ⟨h, fun h' => J.left.not_mem_set_of_mem_dom hmem h'⟩
  rcases lt_trichotomy (J.left.hitParam z σ) T with h | h | h
  · exact absurd (dom_left J (hdom _ hT₁ h) (by rwa [hy])) hw₁D
  · exact h
  · exact absurd (hdom₁ T hT h) hwD₁

/-- **The first hit of `C₂`**: if the hit point of `C` is on `C₂` (and the query is not above the
top of `C₂`), the first hit of `C` is the first hit of `C₂`. -/
theorem right_hit_of {z : Point} (hz₂ : z.2 ≤ J.right.top.2) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hfree : FreeAt J.whole z σ) (hw : rayPt z σ (J.whole.hitParam z σ) ∈ J.right.set) :
    J.right.hitParam z σ = J.whole.hitParam z σ := by
  have hz' : z.2 ≤ J.whole.top.2 := hz₂.trans J.right_top_le
  obtain ⟨hT, -, hdom⟩ := Merge.hit_of_freeAt J.whole hz' hσ hfree
  set T := J.whole.hitParam z σ
  have hy : ∀ t, (rayPt z σ t).2 = z.2 := fun t => rfl
  have hfree₂ : Merge.FreeAt J.right z σ := by
    filter_upwards [hfree] with t ht
    exact dom_right J ht (by rwa [hy])
  obtain ⟨hT₂, hw₂D, hdom₂⟩ := Merge.hit_of_freeAt J.right hz₂ hσ hfree₂
  rcases lt_trichotomy (J.right.hitParam z σ) T with h | h | h
  · exact absurd (dom_right J (hdom _ hT₂ h) (by rwa [hy])) hw₂D
  · exact h
  · exact absurd hw (J.right.not_mem_set_of_mem_dom (hdom₂ T hT h))

/-! ## Regions faced near a key -/

section Gen

variable {M : Model}

/-- **The region faced just after a key**: a non-cut position inside a walk edge, after the key
with no cut in between, faces the region faced just after the key. -/
theorem after_of_near (hM : WalkAx M) {F : Set (Set Point)} (hF : F ⊆ M.Adm) (hfin : F.Finite)
    {g : ℕ} (hg : g < M.W.n) {U : Set Point} (hU : U ∈ M.regions F) {pa : ℕ} {ta : ℝ}
    (hpa : pa < M.W.n) (hta : 0 ≤ ta) {q : ℕ} {u : ℝ} (hq : q < M.W.n)
    (hu : u ∈ Ioo (0 : ℝ) 1) (hqc : ¬ M.IsCut F (q + u)) (hqf : M.Faces q u U)
    (hlt : off M.W.n g (pa + ta) < off M.W.n g (q + u))
    (hgap : ∀ x, M.IsCut F x → 0 ≤ x → x < M.W.n →
      ¬ (off M.W.n g (pa + ta) < off M.W.n g x ∧ off M.W.n g x < off M.W.n g (q + u))) :
    AfterFaces M pa ta U := by
  have hg0 : (0 : ℝ) ≤ (g : ℝ) := Nat.cast_nonneg _
  have hgn : (g : ℝ) < M.W.n := by exact_mod_cast hg
  obtain ⟨δ₁, hδ₁, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1
    (eventually_not_cut_after hM hF hfin ((pa : ℝ) + ta))
  have hδ₁' : (0 : ℝ) < δ₁ := hδ₁
  set D := off M.W.n g ((q : ℝ) + u) - off M.W.n g ((pa : ℝ) + ta)
  have hD0 : 0 < D := by linarith
  refine ⟨min δ₁ D, lt_min hδ₁' hD0, fun s hs0 hs1 hs2 => ?_⟩
  have hsD : s < D := lt_of_lt_of_le hs1 (min_le_right _ _)
  have hsδ : s < δ₁ := lt_of_lt_of_le hs1 (min_le_left _ _)
  have hnc : ¬ M.IsCut F ((pa : ℝ) + (ta + s)) := by
    have := hsub ⟨hs0, hsδ⟩
    rw [Set.mem_ofPred_eq] at this
    rwa [← add_assoc]
  have hts : ta + s ∈ Ioo (0 : ℝ) 1 := ⟨by linarith, hs2⟩
  obtain ⟨U', hU', hf'⟩ := hM.exists_faces_of_not_cut hF hfin hpa hts hnc
  have hoff : off M.W.n g ((pa : ℝ) + (ta + s)) = off M.W.n g ((pa : ℝ) + ta) + s :=
    off_add_small hg hpa hta hs0.le hs2
  have heq := same_region_of_gap hM hF hfin hg0 hgn hU' hU hpa hq hts hu hnc hqc hf' hqf
    (by rw [hoff]; linarith) (fun x hx hx0 hxn ⟨h1, h2⟩ => hgap x hx hx0 hxn ⟨by linarith, h2⟩)
  rwa [← heq]

/-- **A region faced just after a position** is faced at a non-cut position of the same edge, at an
offset just after it. -/
theorem near_after (hM : WalkAx M) {F : Set (Set Point)} (hF : F ⊆ M.Adm) (hfin : F.Finite)
    {g : ℕ} (hg : g < M.W.n) {p : ℕ} (hp : p < M.W.n) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    {U : Set Point} (hW : AfterFaces M p t U) {ε : ℝ} (hε : 0 < ε) :
    ∃ s, 0 < s ∧ s < ε ∧ t + s ∈ Ioo (0 : ℝ) 1 ∧ ¬ M.IsCut F ((p : ℝ) + (t + s)) ∧
      M.Faces p (t + s) U ∧
      off M.W.n g ((p : ℝ) + (t + s)) = off M.W.n g ((p : ℝ) + t) + s := by
  obtain ⟨s, hs0, hsε, hs1, hnc, hf⟩ := faces_near_after hM hF hfin ht0 ht1 hW hε
  exact ⟨s, hs0, hsε, ⟨by linarith, hs1⟩, hnc, hf, off_add_small hg hp ht0 hs0.le hs1⟩

end Gen

end

end S0Math

end Chazelle.Core
