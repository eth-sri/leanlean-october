module

public import Chazelle.Core.SweepMachine5
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.SimpTactics

/-!
# The sweep (WP-D), part 22: the abstract machine, candidate chords and their shot origins

* `chord_eq_shoot_of_end`: an admissible chord of `C` is the chord seen from either of its ends.
* `cand_cases`: a candidate chord of the label `λ` (`Cand`) is seen from an endpoint of an exit
  chord of `λ` (the RAM's shot origins), or is a shared chord (seen from the shared vertex; the RAM
  precomputes them), or is seen from the top of `C₂` (the RAM always shoots from it).
* `detect_hit`: a chord seen from a point `a` (not above the top of `C₁`), attached at a position
  of the left stretch of `C`, is a genuine hit of the shot from `a` in the model of `C₁`, arriving at
  the corresponding position (`genuine_of_attach`, stated for the RAM's origins).
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

/-- **An admissible chord is the chord seen from either end.** -/
theorem chord_eq_shoot_of_end (C : Chain) {h : Set Point} (hh : h ∈ Merge.augChords C)
    {w : Point} (hw : w ∈ h) (hwD : w ∉ C.dom) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ FreeAt C w σ ∧ h = Merge.shoot C w σ := by
  obtain ⟨y, l, r, hH, hy, rfl, -, -⟩ := Merge.augChords_spec hh
  have hlr := hH.lt
  obtain ⟨hwy, hwl, hwr⟩ := hw
  have hw' : w = ((w.1, y) : Point) := Prod.ext rfl hwy
  have hend : w.1 = l ∨ w.1 = r := by
    rcases hwl.lt_or_eq with h1 | h1
    · rcases hwr.lt_or_eq with h2 | h2
      · exact absurd (by rw [hw']; exact hH.open_mem _ h1 h2) hwD
      · exact Or.inr h2
    · exact Or.inl h1.symm
  have hwy' : w.2 ≤ C.top.2 := by rwx [hwy]
  rcases hend with hl | hr
  · -- from the left end, to the right
    have hfree : FreeAt C w 1 := by
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < r - l by linarith)] with s hs
      rw [show rayPt w 1 s = ((w.1 + s, y) : Point) from
        point_ext (by simp [rayPt]) (by simp [rayPt, hwy])]
      exact hH.open_mem _ (by linarith [hs.1]) (by linarith [hs.2])
    obtain ⟨hT, hTD, hTdom⟩ := Merge.hit_of_freeAt C hwy' (Or.inl rfl) hfree
    have hTeq : C.hitParam w 1 = r - l := by
      rcases lt_trichotomy (C.hitParam w 1) (r - l) with h | h | h
      · exfalso; apply hTD
        rw [show rayPt w 1 (C.hitParam w 1) = ((w.1 + C.hitParam w 1, y) : Point) from
          point_ext (by simp [rayPt]) (by simp [rayPt, hwy])]
        exact hH.open_mem _ (by linarith) (by linarith)
      · exact h
      · exfalso
        have := hTdom (r - l) (by linarith) h
        rw [show rayPt w 1 (r - l) = ((r, y) : Point) from
          point_ext (by sil [rayPt]) (by simp [rayPt, hwy])] at this
        exact hH.right_not this
    refine ⟨1, Or.inl rfl, hfree, ?_⟩
    unfold Merge.shoot
    rw [hTeq]
    ext z
    rw [Geometry.mem_segment_iff_lerp]
    constructor
    · rintro ⟨hzy, hzl, hzr⟩
      refine ⟨(z.1 - l) / (r - l), div_nonneg (by linarith) (by linarith),
        (div_le_one (by linarith)).2 (by linarith), ?_⟩
      apply point_ext
      · simp only [Geometry.lerp_fst, rayPt_fst, hl]
        rw [show l + 1 * (r - l) - l = r - l by ring, div_mul_cancel₀ _ (by linarith : r - l ≠ 0)]
        ring
      · simp [lerp, rayPt, hzy, hwy]
    · rintro ⟨u, hu0, hu1, rfl⟩
      refine ⟨by simp [lerp, rayPt, hwy], ?_, ?_⟩ <;> simp [lerp, rayPt, hl] <;> nlinarith
  · -- from the right end, to the left
    have hfree : FreeAt C w (-1) := by
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < r - l by linarith)] with s hs
      rw [show rayPt w (-1) s = ((w.1 - s, y) : Point) from
        point_ext (by sir [rayPt]) (by simp [rayPt, hwy])]
      exact hH.open_mem _ (by linarith [hs.2]) (by linarith [hs.1])
    obtain ⟨hT, hTD, hTdom⟩ := Merge.hit_of_freeAt C hwy' (Or.inr rfl) hfree
    have hTeq : C.hitParam w (-1) = r - l := by
      rcases lt_trichotomy (C.hitParam w (-1)) (r - l) with h | h | h
      · exfalso; apply hTD
        rw [show rayPt w (-1) (C.hitParam w (-1)) = ((w.1 - C.hitParam w (-1), y) : Point) from
          point_ext (by sir [rayPt]) (by simp [rayPt, hwy])]
        exact hH.open_mem _ (by linarith) (by linarith)
      · exact h
      · exfalso
        have := hTdom (r - l) (by linarith) h
        rw [show rayPt w (-1) (r - l) = ((l, y) : Point) from
          point_ext (by sil [rayPt]) (by simp [rayPt, hwy])] at this
        exact hH.left_not this
    refine ⟨-1, Or.inr rfl, hfree, ?_⟩
    unfold Merge.shoot
    rw [hTeq]
    ext z
    rw [Geometry.mem_segment_iff_lerp]
    constructor
    · rintro ⟨hzy, hzl, hzr⟩
      refine ⟨(r - z.1) / (r - l), div_nonneg (by linarith) (by linarith),
        (div_le_one (by linarith)).2 (by linarith), ?_⟩
      apply point_ext
      · simp only [Geometry.lerp_fst, rayPt_fst, hr]
        rw [show r + -1 * (r - l) - r = -(r - l) by ring, mul_neg,
          div_mul_cancel₀ _ (by linarith : r - l ≠ 0)]
        ring
      · simp [lerp, rayPt, hzy, hwy]
    · rintro ⟨u, hu0, hu1, rfl⟩
      refine ⟨by simp [lerp, rayPt, hwy], ?_, ?_⟩ <;> simp [lerp, rayPt, hr] <;> nlinarith

section Machine

variable (J : Merge.Junction)

/-- **The shot origins of the candidate chords**: a candidate chord of `λ` is seen from an
endpoint of an exit chord of `λ` or of a region at a side of the slit of `C₂` along it, or from the shared vertex, or from the top of `C₂`. -/
theorem cand_cases {S₂ : Set (Set Point)} (hS₂ : S₂ ⊆ Merge.augChords J.right) {L : Set Point}
    {h : Set Point} (hh : h ∈ Cand J S₂ L) :
    (∃ c ∈ S₂, (∃ V, LabS J S₂ L V ∧ Chazelle.Chain.TouchesIn (chainModel J.right).D c V) ∧
      ((FreeAt J.whole (Merge.lend c) 1 ∧ h = Merge.shoot J.whole (Merge.lend c) 1) ∨
        (FreeAt J.whole (Merge.rend c) (-1) ∧ h = Merge.shoot J.whole (Merge.rend c) (-1)))) ∨
    (∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ FreeAt J.whole J.shared σ ∧ h = Merge.shoot J.whole J.shared σ) ∨
    (∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ FreeAt J.whole J.right.top σ ∧
      h = Merge.shoot J.whole J.right.top σ) := by
  obtain ⟨hF, hc⟩ := hh
  have hA  := F₂plus_subset J hS₂ hF
  have hvD : J.shared ∉ J.whole.dom := fun hd =>
    J.whole.not_mem_set_of_mem_dom hd (J.left_set_subset J.shared_mem_left)
  have htD : J.right.top ∉ J.whole.dom := fun hd =>
    J.whole.not_mem_set_of_mem_dom hd (J.right_set_subset J.right.top_mem_set)
  rcases hc with ⟨c, hcS, hhc, htouch⟩ | hv | ht
  · rcases hF with ((⟨c', hc', hfree, rfl⟩ | ⟨c', hc', hfree, rfl⟩) | hsh) | htop
    · have hc'S : c' ∈ S₂ := by simpa using hc'
      have := s2_eq_of_sub J hS₂ hcS hc'S hA hhc (by
        obtain ⟨y, l, r, hH, hy, hceq, hl, -⟩ := Merge.augChords_spec (hS₂ hc'S)
        rw [hl, hceq]
        exact Merge.shoot_subset_pos J.whole hH.lt (fun hd => hH.right_not
          (dom_right J hd hy)))
      subst this
      exact Or.inl ⟨c, hcS, htouch, Or.inl ⟨hfree, rfl⟩⟩
    · have hc'S : c' ∈ S₂ := by simpa using hc'
      have := s2_eq_of_sub J hS₂ hcS hc'S hA hhc (by
        obtain ⟨y, l, r, hH, hy, hceq, -, hr⟩ := Merge.augChords_spec (hS₂ hc'S)
        rw [hr, hceq]
        exact Merge.shoot_subset_neg J.whole hH.lt (fun hd => hH.left_not
          (dom_right J hd hy)))
      subst this
      exact Or.inl ⟨c, hcS, htouch, Or.inr ⟨hfree, rfl⟩⟩
    · obtain ⟨σ, hσ, hfree, rfl⟩ := hsh
      exact Or.inr (Or.inl ⟨σ, hσ, (Merge.freeAt_vertex _ _ _).2 hfree, rfl⟩)
    · obtain ⟨σ, hσ, hfree, rfl⟩ := htop
      have hv : J.whole.vertex (J.m₁ + J.right.topIdx) = J.right.top := by
        rwr [Merge.Junction.whole_vertex_add]
      refine Or.inr (Or.inr ⟨σ, hσ, ?_, ?_⟩)
      · rw [← hv]; exact (Merge.freeAt_vertex _ _ _).2 hfree
      · rwr [← hv]
  · obtain ⟨σ, hσ, hfree, heq⟩ := chord_eq_shoot_of_end J.whole hA hv hvD
    exact Or.inr (Or.inl ⟨σ, hσ, hfree, heq⟩)
  · obtain ⟨σ, hσ, hfree, heq⟩ := chord_eq_shoot_of_end J.whole hA ht htD
    exact Or.inr (Or.inr ⟨σ, hσ, hfree, heq⟩)

end Machine

end Sweep

end

end Chazelle.Core
