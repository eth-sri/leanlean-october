module

public import Chazelle.Core.RestoreValid

/-!
# WP-E, Lemma 3.2 part 8: the validity checks accept the good chords

The search accepts a candidate walk vertex `(p, 0)` and direction `σ` only if one of the checks
of `RestoreValid` passes.  For completeness, the checks must accept the vertex chords of the full
map that split the region well.

* `cut_dichotomy`: at a walk vertex with a chord `c` attached that avoids the ray, the ray is
  strictly counterclockwise from the next walk edge or strictly clockwise from the previous one
  (the dichotomy inside `Sweep.hit_mem_arcSet`).
* `ray_not_mem_of_chord`: the ray along an admissible chord `e ∉ S` meets no chord of `S` in the
  domain.
* `valid_complete`: if the admissible chord `e ∉ S` leaves the walk vertex `(p, 0)` in direction
  `σ` (in its left sector) and its open part lies in the region `R` of `S`, then either the key `p`
  is inside an arc of `R`, or an arc of `R` begins at `p` and `σ` is strictly counterclockwise
  from the next edge, or an arc of `R` ends at `p` and `σ` is strictly clockwise from the previous
  edge; and no chord of `S` contains ray points near the vertex.
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sideInArc sidePt sideLeft sideLeftOf sideCcw sideCross sideDot
  freeIn regionsIn TouchesIn sideLeft_zero sideCcw_smul sideKey_inj)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
open Chazelle.Geometry (point_ext lerp_fst lerp_snd)
open Chazelle.Jordan (offset SectorSide)
open Sweep

variable {M : Model}

/-- **The dichotomy at a cut vertex.** -/
theorem cut_dichotomy (hM : WalkAx M) {c : Set Point} (hc : c ∈ M.Adm) {p : ℕ} (hp : p < M.W.n)
    (hA : SideAttach M.W c p 0) {τ : ℝ} (hτ : τ = 1 ∨ τ = -1)
    (hsec : sideLeft M.W p 0 (rayPt (sidePt M.W p 0) τ 1))
    (hav : ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt (sidePt M.W p 0) τ s ∉ c) :
    0 < sideCross (M.W.vtx ((p + 1) % M.W.n) - M.W.vtx p) ((τ, 0) : Point) ∨
      0 < sideCross ((τ, 0) : Point) (M.W.vtx ((p + M.W.n - 1) % M.W.n) - M.W.vtx p) := by
  have hne := hM.nd p hp
  obtain ⟨d, hd, -, hcD, -⟩ := attached_opposite hM hc hA hτ hav
  have hn0 : 0 < M.W.n := by omega
  have hwv : sidePt M.W p 0 = M.W.vtx p := Chazelle.Chain.sidePt_zero _ _
  set v := M.W.vtx p with hv
  set a := M.W.vtx ((p + M.W.n - 1) % M.W.n) with ha
  set b := M.W.vtx ((p + 1) % M.W.n) with hb
  have hsecv : ∀ x, sideLeft M.W p 0 x ↔ sideCcw (b - v) (x - v) (a - v) :=
    fun x => sideLeft_zero _ _ _
  have hττ : τ * τ = 1 := by rcases hτ with rfl | rfl <;> norm_num
  have hdp : sideCcw (b - v) ((τ, 0) : Point) (a - v) := by
    have := (hsecv _).1 hsec
    rwa [hwv, rayPt_sub, one_smul] at this
  have hBdm : ¬ (sideCross (b - v) ((-τ, 0) : Point) = 0 ∧
      0 < sideDot (b - v) ((-τ, 0) : Point)) := by
    rintro ⟨h1, h2⟩
    simp only [sideCross, sideDot, Prod.fst_sub, Prod.snd_sub] at h1 h2
    have hb2 : b.2 = v.2 := by
      have h1' : (b.2 - v.2) * τ = 0 := by linarith
      rcases mul_eq_zero.1 h1' with h | h
      · linarith
      · rcases hτ with rfl | rfl <;> norm_num at h
    set k := -(τ * (b.1 - v.1)) with hk
    have hk0 : 0 < k := by rw [hk]; nlinarith
    set s := min d k / 2 with hs
    have hmin : 0 < min d k := lt_min hd hk0
    have hs0 : 0 < s := by rw [hs]; linarith
    have hsd : s < d := by rw [hs]; linarith [min_le_left d k]
    have hsk : s ≤ k := by rw [hs]; linarith [min_le_right d k]
    have hmem : rayPt v (-τ) s ∈ M.D := by rw [← hwv]; exact hcD s hs0 hsd
    apply hM.trace p hp (s / k) (div_nonneg hs0.le hk0.le) ((div_le_one hk0).2 hsk)
    have e : sidePt M.W p (s / k) = rayPt v (-τ) s := by
      unfold sidePt
      apply point_ext
      · simp only [lerp_fst, rayPt_fst]
        have h3 : s / k * (b.1 - v.1) = -τ * s := by
          rw [div_mul_eq_mul_div, div_eq_iff hk0.ne', hk]
          linear_combination (-(s * (b.1 - v.1))) * hττ
        rw [← h3]
      · simp only [lerp_snd, rayPt_snd]
        rw [show (M.W.vtx ((p + 1) % M.W.n)).2 = b.2 from rfl, hb2]; ring
    rw [e]; exact hmem
  rcases hdp with ⟨-, h2, -⟩ | ⟨-, h2⟩ | ⟨-, -, h3⟩ | ⟨h1, h2, h3⟩
  · exact Or.inl h2
  · exact h2
  · exact Or.inl h3
  · rcases lt_trichotomy (sideCross (b - v) ((τ, 0) : Point)) 0 with h4 | h4 | h4
    · exact Or.inr (cross_dir_aux h1 h2 h4)
    · exfalso; apply hBdm
      rcases h3 with h3 | h3
      · exact absurd h4 h3
      · rw [sideCross_neg_dir, sideDot_neg_dir, h4]
        exact ⟨by ring, by linarith⟩
    · exact Or.inl h4

/-- The ray along an admissible chord `e ∉ S` from its end meets no chord of `S` in the domain
(two distinct chords of a chord system meet only off the domain). -/
theorem ray_not_mem_of_chord (hM : WalkAx M) {S : Set (Set Point)} (hS : S ⊆ M.Adm)
    (hfin : S.Finite) {e : Set Point} (he : e ∈ M.Adm) (heS : e ∉ S) {z : Point} {σ T : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hT : 0 < T) (heq : e = chordOf z σ T)
    (hdom : ∀ t, 0 < t → t < T → rayPt z σ t ∈ M.D) {c : Set Point} (hc : c ∈ S) :
    ∀ t, 0 < t → t < T → rayPt z σ t ∉ c := by
  intro t ht htT hmem
  have hsys := hM.sys (insert e S) (insert_subset he hS) (hfin.insert e)
  have hce : c ≠ e := fun h => heS (h ▸ hc)
  have he' : rayPt z σ t ∈ e := by
    rw [heq]; exact (mem_chordOf hσ hT.le).2 ⟨t, ht.le, htT.le, rfl⟩
  exact hsys.inter_subset_compl (mem_insert_of_mem e hc) (mem_insert e S) hce ⟨hmem, he'⟩
    (hdom t ht htT)

/-- **The validity checks accept a good chord.** -/
theorem valid_complete (hGM : GoodModel M) {Q : Polygon} {S : Set (Set Point)}
    (hFam : M.ChordFamily Q S) (hne : S.Nonempty) {R : Set Point} (hR : R ∈ M.regions S)
    {e : Set Point} (he : e ∈ M.Adm) (heS : e ∉ S) (heR : e ∩ M.D ⊆ R) {p : ℕ}
    (hp : p < M.W.n) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hsec : sideLeft M.W p 0 (rayPt (sidePt M.W p 0) σ 1)) {T : ℝ} (hT : 0 < T)
    (heq : e = chordOf (sidePt M.W p 0) σ T)
    (hdom : ∀ t, 0 < t → t < T → rayPt (sidePt M.W p 0) σ t ∈ M.D) :
    (∀ c ∈ S, ∀ t, 0 < t → t < T → rayPt (sidePt M.W p 0) σ t ∉ c) ∧
    ((∃ a b, M.IsArc S R a b ∧ sideInArc a b ((p : ℝ) + 0)) ∨
      (∃ b, M.IsArc S R ((p : ℝ) + 0) b ∧
        0 < sideCross (M.W.vtx ((p + 1) % M.W.n) - M.W.vtx p) ((σ, 0) : Point)) ∨
      (∃ a, M.IsArc S R a ((p : ℝ) + 0) ∧
        0 < sideCross ((σ, 0) : Point) (M.W.vtx ((p + M.W.n - 1) % M.W.n) - M.W.vtx p))) := by
  have hM := walkAx_of_goodModel hGM
  have hS := hFam.2.1
  have hfin := hFam.1
  have hnot : ∀ c ∈ S, ∀ t, 0 < t → t < T → rayPt (sidePt M.W p 0) σ t ∉ c :=
    fun c hc => ray_not_mem_of_chord hM hS hfin he heS hσ hT heq hdom hc
  refine ⟨hnot, ?_⟩
  -- the ray points are in `R`
  have hrayR : ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt (sidePt M.W p 0) σ s ∈ R := by
    filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT hT] with s hs hsT
    have hs0 : (0 : ℝ) < s := hs
    refine heR ⟨?_, hdom s hs0 hsT.2⟩
    rw [heq]; exact (mem_chordOf hσ hT.le).2 ⟨s, hs0.le, hsT.2.le, rfl⟩
  have same : ∀ X ∈ M.regions S, (∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt (sidePt M.W p 0) σ s ∈ X) →
      X = R := by
    intro X hX hev
    obtain ⟨s, h1, h2⟩ := (hev.and hrayR).exists
    rcases Chazelle.Chain.regionsIn_eq_or_disjoint hX hR with h | h
    · exact h
    · exact absurd (Set.disjoint_left.1 h h1) (not_not.2 h2)
  have hav : ∀ c ∈ S, ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt (sidePt M.W p 0) σ s ∉ c := by
    intro c hc
    filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT hT] with s hs hsT
    exact hnot c hc s hs hsT.2
  by_cases hcut : M.IsCut S ((p : ℝ) + 0)
  · obtain ⟨c, hc, hA⟩ := attach_of_cut hM hcut
    obtain ⟨U, V, l, r, hU, hV, -, harcU, harcV, -⟩ := hM.attach_face hS hfin hc hA
    rcases cut_dichotomy hM (hS hc) hp hA hσ hsec (hav c hc) with h | h
    · have hin := ray_mem_region_after hGM hFam hU hp harcU hc hA hσ hsec
        (fun c' hc' _ => hav c' hc') h
      have := same U hU hin
      subst this
      exact Or.inr (Or.inl ⟨r, harcU, h⟩)
    · have hin := ray_mem_region_before' hGM hFam hV hp harcV hc hA hσ hsec
        (fun c' hc' _ => hav c' hc') h
      have := same V hV hin
      subst this
      exact Or.inr (Or.inr ⟨l, harcV, h⟩)
  · obtain ⟨X, hX, l, r, harc, hin⟩ := hM.arc_around hS hfin hne hcut
    have hev := ray_mem_region_of_arc hGM hFam hX hp le_rfl one_pos harc hin hσ hsec
    have := same X hX hev
    subst this
    exact Or.inl ⟨l, r, harc, hin⟩

end

end Restore

end Chazelle.Core
