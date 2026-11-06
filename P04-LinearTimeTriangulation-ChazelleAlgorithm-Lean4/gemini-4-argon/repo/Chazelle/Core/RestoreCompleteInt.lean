module

public import Chazelle.Core.RestoreComplete

/-!
# WP-E, Lemma 3.2 part 8b: the validity check accepts good chords from inside a walk edge

The companion of `valid_complete` for a candidate position inside a walk edge (parameter in
`(0, 1)`): if the admissible chord `e ∉ S` leaves the point in direction `σ` (into the left side
of the edge) and its open part lies in the region `R` of `S`, then the key of the position is
strictly inside an arc of `R`.  The key is not a cut: a chord of `S` attached there runs in the
direction `-σ` (it avoids the ray, `attached_opposite`), and the two horizontal directions cannot
both point into the open left side of the edge (`interior_sides`).
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sideInArc sidePt sideLeft sideKey_inj)
open Chazelle.Visibility (rayPt)
open Sweep

variable {M : Model}

/-- Inside a walk edge, the two horizontal directions do not both point into the left side. -/
theorem interior_sides (hM : WalkAx M) {p : ℕ} (hp : p < M.W.n) {t : ℝ} (ht0 : 0 < t)
    (ht1 : t < 1) {σ s : ℝ}
    (h1 : sideLeft M.W p t (rayPt (sidePt M.W p t) σ s))
    (h2 : sideLeft M.W p t (rayPt (sidePt M.W p t) (-σ) s)) : False := by
  have hne := hM.nd p hp
  rw [Chazelle.Chain.sideLeft_edge hne ⟨ht0, ht1⟩] at h1 h2
  unfold sidePt at h1 h2
  simp only [det, Visibility.rayPt, Geometry.lerp_fst, Geometry.lerp_snd] at h1 h2
  nlinarith

/-- **The validity check accepts a good chord from inside a walk edge.** -/
theorem valid_complete_int (hGM : GoodModel M) {Q : Polygon} {S : Set (Set Point)}
    (hFam : M.ChordFamily Q S) (hne : S.Nonempty) {R : Set Point} (hR : R ∈ M.regions S)
    {e : Set Point} (he : e ∈ M.Adm) (heS : e ∉ S) (heR : e ∩ M.D ⊆ R) {p : ℕ}
    (hp : p < M.W.n) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hsec : sideLeft M.W p t (rayPt (sidePt M.W p t) σ 1)) {T : ℝ} (hT : 0 < T)
    (heq : e = chordOf (sidePt M.W p t) σ T)
    (hdom : ∀ s, 0 < s → s < T → rayPt (sidePt M.W p t) σ s ∈ M.D) :
    ∃ a b, M.IsArc S R a b ∧ sideInArc a b ((p : ℝ) + t) := by
  have hM := walkAx_of_goodModel hGM
  have hS := hFam.2.1
  have hfin := hFam.1
  set w := sidePt M.W p t
  have hnot : ∀ c ∈ S, ∀ s, 0 < s → s < T → rayPt w σ s ∉ c :=
    fun c hc => ray_not_mem_of_chord hM hS hfin he heS hσ hT heq hdom hc
  have hav : ∀ c ∈ S, ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt w σ s ∉ c := by
    intro c hc
    filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT hT] with s hs hsT
    exact hnot c hc s hs hsT.2
  have hrayR : ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt w σ s ∈ R := by
    filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT hT] with s hs hsT
    have hs0 : (0 : ℝ) < s := hs
    refine heR ⟨?_, hdom s hs0 hsT.2⟩
    rw [heq]; exact (mem_chordOf hσ hT.le).2 ⟨s, hs0.le, hsT.2.le, rfl⟩
  by_cases hcut : M.IsCut S ((p : ℝ) + t)
  · exfalso
    obtain ⟨c, hc, p', t', hA', hkey⟩ := hcut
    obtain ⟨hpp, htt⟩ := sideKey_inj ht0.le ht1 hA'.2.1 hA'.2.2.1 hkey
    rw [← hpp, ← htt] at hA'
    obtain ⟨d, hd, -, -, hcd⟩ := attached_opposite hM (hS hc) hA' hσ (hav c hc)
    obtain ⟨r, hr, hloc⟩ := hA'.2.2.2.2
    set s := min d r / 2 with hs
    have hmin : 0 < min d r := lt_min hd hr
    have hs0 : 0 < s := by rw [hs]; linarith
    have hsd : s < d := by rw [hs]; linarith [min_le_left d r]
    have hsr : s < r := by rw [hs]; linarith [min_le_right d r]
    have hσ' : -σ = 1 ∨ -σ = -1 := by rcases hσ with rfl | rfl <;> norm_num
    have hxc := hcd s hs0 hsd
    have hxne : rayPt w (-σ) s ≠ w := by
      intro h
      have := congrArg Prod.fst h
      simp only [Visibility.rayPt] at this
      rcases hσ with rfl | rfl <;> linarith
    have h2 := hloc _ hxc hxne (by rwa [dist_rayPt _ hσ' hs0.le])
    have h1 := (sideLeft_rayPt_iff _ p t σ one_pos hs0).1 hsec
    exact interior_sides hM hp ht0 ht1 h1 h2
  · obtain ⟨X, hX, l, r, harc, hin⟩ := hM.arc_around hS hfin hne hcut
    have hev := ray_mem_region_of_arc hGM hFam hX hp ht0.le ht1 harc hin hσ hsec
    obtain ⟨s, h1, h2⟩ := (hev.and hrayR).exists
    rcases Chazelle.Chain.regionsIn_eq_or_disjoint hX hR with h | h
    · subst h; exact ⟨l, r, harc, hin⟩
    · exact absurd (Set.disjoint_left.1 h h1) (not_not.2 h2)

end

end Restore

end Chazelle.Core
