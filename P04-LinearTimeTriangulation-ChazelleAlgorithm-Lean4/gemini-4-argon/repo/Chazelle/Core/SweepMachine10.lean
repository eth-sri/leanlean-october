module

public import Chazelle.Core.SweepMachine9

/-!
# The sweep (WP-D), part 26: the abstract machine, the region of a query ray

A query ray leaves its walk position into the left sector.  When it does not run along a chord of
the family, it starts in a region `U`, which is the region faced just after the position (non-cut
key, or cut walk vertex turning counterclockwise from the next walk edge) or just before it (cut
walk vertex turning clockwise from the previous edge) — so the machine's label for that region
answers the query (`answer_of_label_gen`).

* `afterFaces_of_arc`, `beforeFaces_of_arc_end`: arcs face their region just after a key inside
  or at their start, and just before their end.
* `leave_region`: the region of the ray and the side on which it is faced.
-/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sideInArc sidePt sideLeft sideCross freeIn regionsIn)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
open WalkEmbed

namespace Sweep

variable {M : Model}

/-- **An arc faces its region just after a key inside it** (or at its start). -/
theorem afterFaces_of_arc {F : Set (Set Point)} {U : Set Point} {l r : ℝ}
    (harc : M.IsArc F U l r) {p : ℕ} (hp : p < M.W.n) {t : ℝ} (ht0 : 0 ≤ t)
    (hin : ∀ᶠ s in 𝓝[>] (0 : ℝ), sideInArc l r ((p : ℝ) + t + s)) : AfterFaces M p t U := by
  obtain ⟨δ, hδ, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hin
  refine ⟨δ, hδ, fun s hs0 hs1 hs2 => ?_⟩
  have := hsub ⟨hs0, hs1⟩
  exact harc.2.2.2.2.2.2 p (t + s) hp (by linarith) hs2 (by rw [← add_assoc]; exact this)

/-- **An arc faces its region just before its end at a walk vertex.** -/
theorem beforeFaces_of_arc_end {F : Set (Set Point)} {U : Set Point} {l : ℝ} {p : ℕ}
    (hp : p < M.W.n) (hp1 : 1 ≤ p) (harc : M.IsArc F U l (p + 0)) (hlr : l ≠ (p : ℝ) + 0) :
    BeforeFaces M p 0 U := by
  obtain ⟨δ, hδ, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 (sideInArc_before_end hlr)
  have hδ' : (0 : ℝ) < δ := hδ
  refine ⟨min δ 1, lt_min hδ' one_pos, fun h => absurd h (lt_irrefl 0), fun _ s hs0 hs1 => ?_⟩
  have hs1' : s < δ := lt_of_lt_of_le hs1 (min_le_left _ _)
  have hs2 : s < 1 := lt_of_lt_of_le hs1 (min_le_right _ _)
  have := hsub ⟨hs0, hs1'⟩
  rw [prev_mod hp hp1]
  refine harc.2.2.2.2.2.2 (p - 1) (1 - s) (by omega) (by linarith) (by linarith) ?_
  have hc : ((p - 1 : ℕ) : ℝ) + (1 - s) = (p : ℝ) + 0 - s := by
    rw [Nat.cast_sub hp1]; push_cast; ring
  rw [hc]; exact this

section ChainModel

variable (C : Chain)

/-- **The region of a query ray off the chords**: the ray from the point of the position `(p, t)`
into its left sector, along no chord of the family, starts in a region `U`, faced just after the
position (a non-cut key, or a cut vertex turning counterclockwise from the next walk edge) or just
before it (a cut vertex turning clockwise from the previous walk edge). -/
theorem leave_region (hP : C.P.Simple) {Q : Polygon} {F : Set (Set Point)}
    (hFam : (chainModel C).ChordFamily Q F) {z : Point} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) {p : ℕ}
    {t : ℝ} (hp : p < (chainModel C).W.n) (ht : 0 ≤ t) (ht1 : t < 1)
    (hpt : sidePt (chainModel C).W p t = z) (hsec : sideLeft (chainModel C).W p t (rayPt z σ 1))
    (hzR : |z.2| < C.radius)
    (hno : ∀ e ∈ F, ¬ ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt z σ s ∈ e) :
    ∃ U ∈ (chainModel C).regions F, (∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt z σ s ∈ U) ∧
      ((¬ (chainModel C).IsCut F (p + t) ∧ AfterFaces (chainModel C) p t U) ∨
        (t = 0 ∧ 0 < sideCross ((chainModel C).W.vtx ((p + 1) % (chainModel C).W.n) -
            (chainModel C).W.vtx p) ((σ, 0) : Point) ∧ AfterFaces (chainModel C) p t U) ∨
        (t = 0 ∧ 0 < sideCross ((σ, 0) : Point) ((chainModel C).W.vtx
            ((p + (chainModel C).W.n - 1) % (chainModel C).W.n) - (chainModel C).W.vtx p) ∧
          BeforeFaces (chainModel C) p t U)) := by
  have hM : WalkAx (chainModel C) := FactsChain.walkAx C hP
  have hGM : GoodModel (chainModel C) := Or.inl ⟨C, hP, rfl⟩
  have hF : F ⊆ (chainModel C).Adm := hFam.2.1
  have hfin : F.Finite := hFam.1
  have hsec' : sideLeft (chainModel C).W p t (rayPt (sidePt (chainModel C).W p t) σ 1) := by
    rw [hpt]; exact hsec
  by_cases hcut : (chainModel C).IsCut F (p + t)
  · rcases leave_cases C hP hFam hσ hp ht ht1 hpt hsec hzR with ⟨e, he, -, hev⟩ | hnc |
        ⟨rfl, hp1, hnot, hcr⟩
    · exact absurd hev (hno e he)
    · exact absurd hcut hnc
    · obtain ⟨c, hc, p', t', hAc, hkey⟩ := hcut
      obtain ⟨rfl, rfl⟩ := Chazelle.Chain.sideKey_inj hAc.2.1 hAc.2.2.1 le_rfl one_pos hkey.symm
      obtain ⟨U, V, l, r, hU, hV, -, harcU, harcV, -⟩ := hM.attach_face hF hfin hc hAc
      have hne : F.Nonempty := ⟨c, hc⟩
      have hnot' : ∀ c ∈ F, SideAttach (chainModel C).W c p' 0 →
          ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt (sidePt (chainModel C).W p' 0) σ s ∉ c := by
        intro c hc hA; rw [hpt]; exact hnot c hc hA
      rcases hcr with hcr | hcr
      · have hray := ray_mem_region_after hGM hFam hU hp harcU hc hAc hσ hsec' hnot' hcr
        rw [hpt] at hray
        refine ⟨U, hU, hray, Or.inr (Or.inl ⟨rfl, hcr, ?_⟩)⟩
        exact afterFaces_of_arc harcU hp le_rfl
          (WalkAx.eventually_after_start (WalkAx.arc_cuts hne harcU).2.2)
      · have hray := ray_mem_region_before hGM hFam hV hp hp1 harcV hc hAc hσ hsec' hnot' hcr
        rw [hpt] at hray
        exact ⟨V, hV, hray, Or.inr (Or.inr ⟨rfl, hcr,
          beforeFaces_of_arc_end hp hp1 harcV (WalkAx.arc_cuts hne harcV).2.2⟩)⟩
  · -- a non-cut key: the arc around it
    have hnc := hcut
    have hkey : (0 : ℝ) < p + t := by
      by_contra hle
      push Not at hle
      have hp0 : p = 0 := by
        have : (p : ℝ) ≤ 0 := by linarith
        exact_mod_cast le_antisymm (by exact_mod_cast this) (Nat.zero_le p)
      have ht0 : t = 0 := by
        have : (0 : ℝ) ≤ p := Nat.cast_nonneg p
        linarith
      subst hp0 ht0
      have h0 : sidePt (chainModel C).W 0 0 = C.slitTop := by
        rw [Chazelle.Chain.sidePt_zero]; rfl
      have := congrArg Prod.snd (hpt.symm.trans h0)
      simp only [Chain.slitTop] at this
      rw [this] at hzR
      have hR := C.radius_pos
      rw [abs_of_pos hR] at hzR
      exact lt_irrefl _ hzR
    obtain ⟨U, hU, l, r, harc, hin⟩ := exists_arc_around hGM hFam hkey hnc
    have hray := ray_mem_region_of_arc hGM hFam hU hp ht ht1 harc hin hσ hsec'
    rw [hpt] at hray
    exact ⟨U, hU, hray, Or.inl ⟨hnc, afterFaces_of_arc harc hp ht (sideInArc_eventually_add hin)⟩⟩

end ChainModel

end Sweep

end

end Chazelle.Core
