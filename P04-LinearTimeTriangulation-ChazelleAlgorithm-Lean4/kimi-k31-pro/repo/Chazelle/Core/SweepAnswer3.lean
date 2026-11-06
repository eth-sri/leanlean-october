module

public import Chazelle.Core.SweepAnswer2
public import Chazelle.Rwx
public import Chazelle.RewriteTactics

/-!
# The sweep (WP-D), part 16: rays leaving a walk position; the box-gap queries (gap S5)

A query of `SweepSpec` is a walk position of the model of its own chain whose direction points
into the left sector.  Its ray leaves the position

* along a chord of the family attached there (`leave_cases`, first case; then its first hit in
  that chain is the far end of the chord, `genuine_along_chord`), or
* into the region of the arc around a non-cut key (`ray_mem_region_of_arc`), or
* at a cut walk vertex (chords avoiding the ray, `p ≥ 1`) into the region of the arc beginning
  or ending there, by the turning condition (`ray_mem_region_after`, `ray_mem_region_before`);
  a cut inside a walk edge forces the first case.

**Box-gap queries (S5).**  When the top of `C` lies on `C₂`, the box block of the model of `C₁`
is not part of the left stretch of `C`, and the sweep never passes its queries.  Such a query
point `z` (on a vertical box wall or the bottom of the box, below both tops) is a walk position of
both chain models (the boxes coincide, `FuseMath.radius_of_P`), so it is answered by a double
identification: `leave_cases` in each model gives a genuine first hit per chain (a region shot or
a chord end), and `whole_of_genuine` combines them (`answer_two_positions`).  Computing the
position of `z` in the model of `C₂` from its position in the model of `C₁` is a RAM primitive
(box edge indices depend on the slit abscissa and the orientation bit).
-/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sideInArc sidePt sideLeft sideCross freeIn regionsIn)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
open Chazelle.Geometry (point_ext)
open Chazelle.Merge (FreeAt)

namespace Sweep

section ChainModel

variable (C : Chain)

/-- **The cases at a cut walk vertex** for a ray arriving (equivalently, its reverse leaving)
off the chords: the chords attached there avoid the ray, and one of the two turning conditions
holds (`vertex_cases_of_genuine` without the genuine hypothesis, given `1 ≤ p`). -/
theorem vertex_cases (hP : C.P.Simple) {Q : Polygon} {F : Set (Set Point)}
    (hFam : (chainModel C).ChordFamily Q F) {w : Point} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    {p : ℕ} (hA : Arrival (chainModel C).W w σ p 0) (hp1 : 1 ≤ p)
    (hcut : (chainModel C).IsCut F ((p : ℝ) + 0))
    (hno : ∀ e ∈ F, ¬ ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt w (-σ) s ∈ e) :
    (∀ c ∈ F, SideAttach (chainModel C).W c p 0 →
      ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt w (-σ) s ∉ c) ∧
      (0 < sideCross ((chainModel C).W.vtx ((p + 1) % (chainModel C).W.n) -
          (chainModel C).W.vtx p) ((-σ, 0) : Point) ∨
        0 < sideCross ((-σ, 0) : Point) ((chainModel C).W.vtx
          ((p + (chainModel C).W.n - 1) % (chainModel C).W.n) - (chainModel C).W.vtx p)) := by
  have hM  := FactsChain.walkAx C hP
  have hF  := hFam.2.1
  have hfin  := hFam.1
  have hnσ : -σ = 1 ∨ -σ = -1 := by rcases hσ with rfl | rfl <;> norm_num
  obtain ⟨hp, -, -, hpt, hsec⟩ := hA
  have hnot : ∀ c ∈ F, ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt w (-σ) s ∉ c := by
    intro c hc
    rcases ray_chord_dichotomy C (hF hc) w hnσ with h | h
    · exact absurd h (hno c hc)
    · exact h
  refine ⟨fun c hc _ => hnot c hc, ?_⟩
  -- the arriving ray reversed lies in a region
  obtain ⟨r₀, hr₀, hsf⟩ := sector_free hM hF hfin hp le_rfl one_pos
  have hsec' : ∀ s > 0, sideLeft (chainModel C).W p 0 (rayPt w (-σ) s) := by
    intro s hs
    have h1 : sideLeft (chainModel C).W p 0 (rayPt (sidePt (chainModel C).W p 0) (-σ) 1) := by
      rwx [hpt]
    have := (sideLeft_rayPt_iff _ p 0 (-σ) one_pos hs).1 h1
    rwa [hpt] at this
  have hall  := (hfin.eventually_all).2 hnot
  obtain ⟨δ, hδ, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1
    (hall.and (Ioo_mem_nhdsGT hr₀))
  have hδ0 : (0 : ℝ) < δ := hδ
  have hfree : ∀ s ∈ Ioo (0 : ℝ) δ, rayPt w (-σ) s ∈ freeIn C.dom F := by
    intro s hs
    obtain ⟨hc, hs'⟩ := hsub hs
    have hball : rayPt w (-σ) s ∈ ball (sidePt (chainModel C).W p 0) r₀ := by
      rw [hpt, mem_ball, dist_rayPt _ hnσ hs.1.le]; exact hs'.2
    refine ⟨(hsf _ hball (hsec' s hs.1)).1, ?_⟩
    rintro ⟨c, hcF, hxc⟩
    exact hc c hcF hxc
  set z := rayPt w (-σ) (δ / 2) with hz
  have hzfree : z ∈ freeIn C.dom F := hfree _ ⟨by linarith, by linarith⟩
  set U := connectedComponentIn (freeIn C.dom F) z with hU
  have hUreg  := Chazelle.Chain.mem_regionsIn hzfree
  have hconn : IsPreconnected ((fun s => rayPt w (-σ) s) '' Ioo (0 : ℝ) δ) :=
    isPreconnected_Ioo.image _ (by unfold rayPt; fun_prop)
  have hsubU : (fun s => rayPt w (-σ) s) '' Ioo (0 : ℝ) δ ⊆ U :=
    hconn.subset_connectedComponentIn ⟨δ / 2, ⟨by linarith, by linarith⟩, rfl⟩
      (by rintro _ ⟨s, hs, rfl⟩; exact hfree s hs)
  have happ : ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt (sidePt (chainModel C).W p 0) (-σ) s ∈ U := by
    filter_upwards [Ioo_mem_nhdsGT hδ0] with s hs
    rw [hpt]; exact hsubU ⟨s, hs, rfl⟩
  have hsecv : ∀ s > 0, sideLeft (chainModel C).W p 0
      (rayPt (sidePt (chainModel C).W p 0) (-σ) s) := by
    intro s hs; rw [hpt]; exact hsec' s hs
  exact ((approach_vertex hM hF hfin hUreg hp hp1 hnσ hsecv happ).2 hcut).1

/-- **A query ray is free in its own chain**: a ray leaving a walk position into its left sector
starts in the domain. -/
theorem freeAt_of_leave (hP : C.P.Simple) {z : Point} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) {p : ℕ}
    {t : ℝ} (hp : p < (chainModel C).W.n) (ht : 0 ≤ t) (ht1 : t < 1)
    (hpt : sidePt (chainModel C).W p t = z) (hsec : sideLeft (chainModel C).W p t (rayPt z σ 1)) :
    FreeAt C z σ := by
  have hM  := FactsChain.walkAx C hP
  obtain ⟨r, hr, hsf⟩ := sector_free hM (F := ∅) (empty_subset _) finite_empty hp ht ht1
  filter_upwards [Ioo_mem_nhdsGT hr] with s hs
  have hsec' : sideLeft (chainModel C).W p t (rayPt (sidePt (chainModel C).W p t) σ s) := by
    rw [hpt]
    have h1 : sideLeft (chainModel C).W p t (rayPt (sidePt (chainModel C).W p t) σ 1) := by
      rwx [hpt]
    have := (sideLeft_rayPt_iff _ p t σ one_pos hs.1).1 h1
    rwa [hpt] at this
  have hball : rayPt (sidePt (chainModel C).W p t) σ s ∈ ball (sidePt (chainModel C).W p t) r := by
    rw [mem_ball, dist_rayPt _ hσ hs.1.le]; exact hs.2
  have := (hsf _ hball hsec').1
  rwa [hpt] at this

/-- **The cases of a ray leaving a walk position** (a query in its own chain): along a chord of
the family attached there; or the key is not a cut (then `ray_mem_region_of_arc` applies to the
arc around it); or a cut walk vertex `p ≥ 1` whose chords avoid the ray, with one of the two
turning conditions (then `ray_mem_region_after` / `ray_mem_region_before` apply). -/
theorem leave_cases (hP : C.P.Simple) {Q : Polygon} {F : Set (Set Point)}
    (hFam : (chainModel C).ChordFamily Q F) {z : Point} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) {p : ℕ}
    {t : ℝ} (hp : p < (chainModel C).W.n) (ht : 0 ≤ t) (ht1 : t < 1)
    (hpt : sidePt (chainModel C).W p t = z) (hsec : sideLeft (chainModel C).W p t (rayPt z σ 1))
    (hzR : |z.2| < C.radius) :
    (∃ e ∈ F, SideAttach (chainModel C).W e p t ∧ ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt z σ s ∈ e) ∨
      ¬ (chainModel C).IsCut F (p + t) ∨
      (t = 0 ∧ 1 ≤ p ∧ (∀ c ∈ F, SideAttach (chainModel C).W c p 0 →
          ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt z σ s ∉ c) ∧
        (0 < sideCross ((chainModel C).W.vtx ((p + 1) % (chainModel C).W.n) -
            (chainModel C).W.vtx p) ((σ, 0) : Point) ∨
          0 < sideCross ((σ, 0) : Point) ((chainModel C).W.vtx
            ((p + (chainModel C).W.n - 1) % (chainModel C).W.n) - (chainModel C).W.vtx p))) := by
  have hM  := FactsChain.walkAx C hP
  have hF  := hFam.2.1
  have hnσ : -σ = 1 ∨ -σ = -1 := by rcases hσ with rfl | rfl <;> norm_num
  have hA : Arrival (chainModel C).W z (-σ) p t := ⟨hp, ht, ht1, hpt, by rwx [neg_neg]⟩
  have hsec' : ∀ s > 0, sideLeft (chainModel C).W p t (rayPt z σ s) := by
    intro s hs
    have h1 : sideLeft (chainModel C).W p t (rayPt (sidePt (chainModel C).W p t) σ 1) := by
      rwx [hpt]
    have := (sideLeft_rayPt_iff _ p t σ one_pos hs).1 h1
    rwa [hpt] at this
  have hzD : z ∉ C.dom := by rw [← hpt]; exact hM.trace p hp t ht ht1.le
  by_cases hch : ∃ e ∈ F, ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt z σ s ∈ e
  · left
    obtain ⟨e, he, hev⟩ := hch
    refine ⟨e, he, ?_, hev⟩
    have heA  := hF he
    obtain ⟨y, l, r, hH, -, rfl, -, -⟩ := Merge.augChords_spec heA
    have hlr := hH.lt
    obtain ⟨s₁, hs₁, hs₁0⟩ := (hev.and self_mem_nhdsWithin).exists
    have hzy : z.2 = y := by simpa [rayPt] using hs₁.1
    have hzpt : ∀ x : ℝ, x = z.1 → ((x, y) : Point) = z := fun x hx => Prod.ext hx hzy.symm
    refine ⟨hp, ht, ht1, ?_, 1, one_pos, fun x hx hxz _ => ?_⟩
    · rw [hpt]
      rcases hσ with rfl | rfl
      · have hzl : l ≤ z.1 := by
          by_contra h
          push Not at h
          obtain ⟨s, hs, hs'⟩ := (hev.and (Ioo_mem_nhdsGT (show (0 : ℝ) < l - z.1 by linarith))).exists
          have := hs.2.1; simp [rayPt] at this; linarith [hs'.2]
        have hzr : z.1 ≤ r := by
          have := hs₁.2.2; simp [rayPt] at this; have : (0 : ℝ) < s₁ := hs₁0; linarith
        exact ⟨hzy, hzl, hzr⟩
      · have hzr : z.1 ≤ r := by
          by_contra h
          push Not at h
          obtain ⟨s, hs, hs'⟩ := (hev.and (Ioo_mem_nhdsGT (show (0 : ℝ) < z.1 - r by linarith))).exists
          have := hs.2.2; simp [rayPt] at this; linarith [hs'.2]
        have hzl : l ≤ z.1 := by
          have := hs₁.2.1; simp [rayPt] at this; have : (0 : ℝ) < s₁ := hs₁0; linarith
        exact ⟨hzy, hzl, hzr⟩
    · rw [hpt] at hxz
      obtain ⟨hxy, hxl, hxr⟩ := hx
      rcases hσ with rfl | rfl
      · -- σ = 1: `z` is the left end
        have hzl : z.1 = l := by
          have h1 : l ≤ z.1 := by
            by_contra h
            push Not at h
            obtain ⟨s, hs, hs'⟩ :=
              (hev.and (Ioo_mem_nhdsGT (show (0 : ℝ) < l - z.1 by linarith))).exists
            have := hs.2.1; simp [rayPt] at this; linarith [hs'.2]
          have h2 : z.1 < r := by
            have := hs₁.2.2; simp [rayPt] at this; have : (0 : ℝ) < s₁ := hs₁0; linarith
          rcases h1.lt_or_eq with h | h
          · exact absurd (by rw [← hzpt z.1 rfl]; exact hH.open_mem _ h h2) hzD
          · exact h.symm
        have hxl' : l < x.1 := by
          rcases hxl.lt_or_eq with h | h
          · exact h
          · exfalso; apply hxz; exact Prod.ext (by rw [← h, hzl]) (by rw [hxy, hzy])
        have e : x = rayPt z 1 (x.1 - l) := point_ext (by simp [rayPt, hzl]) (by simp [rayPt, hxy, hzy])
        rw [e]; exact hsec' _ (by linarith)
      · -- σ = -1: `z` is the right end
        have hzr : z.1 = r := by
          have h1 : z.1 ≤ r := by
            by_contra h
            push Not at h
            obtain ⟨s, hs, hs'⟩ :=
              (hev.and (Ioo_mem_nhdsGT (show (0 : ℝ) < z.1 - r by linarith))).exists
            have := hs.2.2; simp [rayPt] at this; linarith [hs'.2]
          have h2 : l < z.1 := by
            have := hs₁.2.1; simp [rayPt] at this; have : (0 : ℝ) < s₁ := hs₁0; linarith
          rcases h1.lt_or_eq with h | h
          · exact absurd (by rw [← hzpt z.1 rfl]; exact hH.open_mem _ h2 h) hzD
          · exact h
        have hxr' : x.1 < r := by
          rcases hxr.lt_or_eq with h | h
          · exact h
          · exfalso; apply hxz; exact Prod.ext (by rw [h, hzr]) (by rw [hxy, hzy])
        have e : x = rayPt z (-1) (r - x.1) :=
          point_ext (by simp [rayPt, hzr]) (by simp [rayPt, hxy, hzy])
        rw [e]; exact hsec' _ (by linarith)
  · right
    have hch' : ∀ e ∈ F, ¬ ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt z σ s ∈ e :=
      fun e he h => hch ⟨e, he, h⟩
    have hno : ∀ e ∈ F, ¬ ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt z (-(-σ)) s ∈ e := by
      intro e he; rw [neg_neg]; exact hch' e he
    by_cases hcut : (chainModel C).IsCut F (p + t)
    · right
      rcases ht.lt_or_eq with ht0 | ht0
      · exact absurd hcut (not_cut_of_edge C hP hFam hnσ hA ht0 hno)
      · subst ht0
        have hp1 : 1 ≤ p := by
          by_contra h0
          have hp0 : p = 0 := by omega
          subst hp0
          have h0 : sidePt (chainModel C).W 0 0 = C.slitTop := by
            rwr [Chazelle.Chain.sidePt_zero]
          have := congrArg Prod.snd (hpt.symm.trans h0)
          simp [Chain.slitTop] at this
          rw [this] at hzR
          have hR := C.radius_pos
          rw [abs_of_pos hR] at hzR
          exact lt_irrefl _ hzR
        obtain ⟨h1, h2⟩ := vertex_cases C hP hFam hnσ hA hp1 hcut hno
        refine ⟨rfl, hp1, fun c hc hAc => by simpa using h1 c hc hAc, ?_⟩
        simpa using h2
    · exact Or.inl hcut

end ChainModel

section Junction

variable (J : Merge.Junction)

end Junction

end Sweep

end

end Chazelle.Core
