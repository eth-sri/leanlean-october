module

public import Chazelle.Core.SweepLocal

/-!
# WP-E, Lemma 3.2 part 2: local shooting in any good model

The search of Lemma 3.2 shoots horizontal rays from points of the walk of a good model `M` (a
chain model or the interior model of `Q`) into a region `R` of a chord family, and must know
that the first hit of the ray on the (sub)arcs of `R` is the first point where the ray leaves the
domain.  The sweep (`Sweep.local_shoot`) proves this for chain models; here it is proved for any
good model, from the walk axioms.

* `exit_exists`: a ray that starts in the domain and reaches a point outside has a first exit.
* `chordOf`, `mem_chordOf`, `attach_start`, `attach_end`: the segment from the origin to the exit
  and its attachments.
* `local_exit`: **local shooting** — the exit point lies on an arc of the region, and the segment
  is an admissible chord inside the region.
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sideInArc sidePt sidePrev sideNext sideLeft sideLeftOf sideCcw
  sideCross sideDot freeIn regionsIn sideLeft_edge sideLeft_zero sideLeft_not_self sideKey_inj
  sideCcw_smul IsHChordIn)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
open Chazelle.Geometry (lerp lerp_fst lerp_snd point_ext)
open Chazelle.Jordan (offset SectorSide)
open Sweep


/-! ## Rays in a good model -/

section Ray

variable {M : Model}

/-- A horizontal chord of the domain of a good model is admissible (for a chain model, if it is
not above the top of the chain). -/
theorem hchord_adm (hGM : GoodModel M) {y a b : ℝ} (h : IsHChordIn M.D y a b)
    (htop : ∀ C : Chain, M = chainModel C → y ≤ C.top.2) : Visibility.hseg y a b ∈ M.Adm := by
  rcases hGM with ⟨C, -, rfl⟩ | ⟨Q, -, rfl⟩
  · exact ⟨y, a, b, h, htop C rfl, rfl⟩
  · exact ⟨y, a, b, h, rfl⟩

/-- **The first exit of a ray**: a ray starting in an open set `D` and reaching a point outside
leaves `D` at a first parameter `T`. -/
theorem exit_exists {D : Set Point} (hD : IsOpen D) {z : Point} {σ : ℝ}
    (hini : ∀ᶠ t in 𝓝[>] (0 : ℝ), rayPt z σ t ∈ D) {t₁ : ℝ} (ht₁ : 0 < t₁)
    (hout : rayPt z σ t₁ ∉ D) :
    ∃ T, 0 < T ∧ T ≤ t₁ ∧ rayPt z σ T ∉ D ∧ ∀ t, 0 < t → t < T → rayPt z σ t ∈ D := by
  set S := {t : ℝ | 0 < t ∧ rayPt z σ t ∉ D} with hS
  have hne : S.Nonempty := ⟨t₁, ht₁, hout⟩
  have hbdd : BddBelow S := ⟨0, fun t ht => ht.1.le⟩
  obtain ⟨ε, hε, hεD⟩ := Metric.eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 hini)
  have hTε : ε ≤ sInf S := by
    refine le_csInf hne fun t ht => ?_
    by_contra h
    push Not at h
    exact ht.2 (hεD (by rwa [Real.dist_eq, sub_zero, abs_of_pos ht.1]) ht.1)
  have hTt := csInf_le hbdd ⟨ht₁, hout⟩
  have hbelow : ∀ t, 0 < t → t < sInf S → rayPt z σ t ∈ D := fun t ht htT => by
    by_contra h
    exact absurd (csInf_le hbdd ⟨ht, h⟩) (not_le.2 htT)
  refine ⟨sInf S, by linarith, hTt, fun hTD => ?_, hbelow⟩
  have hc := Chazelle.Visibility.continuous_rayPt z σ
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 (hD.preimage hc) (sInf S) hTD
  obtain ⟨s, hsS, hs⟩ := exists_lt_of_csInf_lt hne (show sInf S < sInf S + δ by linarith)
  have hTs := csInf_le hbdd hsS
  exact hsS.2 (hball (by rw [mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith))

/-- The horizontal segment from `z` to the point of the ray in direction `σ` at parameter `T`. -/
noncomputable def chordOf (z : Point) (σ T : ℝ) : Set Point :=
  Visibility.hseg z.2 (min z.1 (z.1 + σ * T)) (max z.1 (z.1 + σ * T))

/-- The points of `chordOf z σ T` are the ray points up to `T`. -/
theorem mem_chordOf {z : Point} {σ T : ℝ} (hσ : σ = 1 ∨ σ = -1) (hT : 0 ≤ T) {x : Point} :
    x ∈ chordOf z σ T ↔ ∃ s, 0 ≤ s ∧ s ≤ T ∧ x = rayPt z σ s := by
  unfold chordOf Visibility.hseg
  simp only [mem_ofPred_eq]
  rcases hσ with rfl | rfl
  · rw [min_eq_left (by linarith), max_eq_right (by linarith)]
    constructor
    · rintro ⟨hy, h1, h2⟩
      exact ⟨x.1 - z.1, by linarith, by linarith, point_ext (by simp) (by simp [hy])⟩
    simp_all
  · rw [min_eq_right (by linarith), max_eq_left (by linarith)]
    constructor
    · rintro ⟨hy, h1, h2⟩
      exact ⟨z.1 - x.1, by linarith, by linarith, point_ext (by simp) (by simp [hy])⟩
    · rintro ⟨s, hs0, hsT, rfl⟩
      simp only [rayPt_fst, rayPt_snd]
      exact ⟨trivial, by linarith, by linarith⟩

theorem rayPt_zero' (z : Point) (σ : ℝ) : rayPt z σ 0 = z := point_ext (by simp) (by simp)

/-- The ray back from the point at parameter `T`. -/
theorem rayPt_back (z : Point) (σ T s : ℝ) : rayPt (rayPt z σ T) (-σ) s = rayPt z σ (T - s) :=
  point_ext (by simp; ring) (by simp)

section

variable {W : Polygon} {p : ℕ} {t : ℝ} (hp : p < W.n) (ht0 : 0 ≤ t) (ht1 : t < 1)
include hp ht0 ht1

/-- **The chord is attached at its origin** when the ray leaves the origin's position into its
left sector. -/
theorem attach_start
    {σ T : ℝ} (hσ : σ = 1 ∨ σ = -1) (hT : 0 < T)
    (hsec : sideLeft W p t (rayPt (sidePt W p t) σ 1)) :
    SideAttach W (chordOf (sidePt W p t) σ T) p t := by
  refine ⟨hp, ht0, ht1, (mem_chordOf hσ hT.le).2 ⟨0, le_rfl, hT.le, (rayPt_zero' _ _).symm⟩,
    1, one_pos, fun x hx hxz _ => ?_⟩
  obtain ⟨s, hs0, -, rfl⟩ := (mem_chordOf hσ hT.le).1 hx
  have hs : 0 < s := by
    rcases hs0.lt_or_eq with h | h
    · exact h
    · subst h; exact absurd (rayPt_zero' _ _) hxz
  exact (sideLeft_rayPt_iff W p t σ one_pos hs).1 hsec

/-- **The chord is attached at its far end** when the ray back from it enters the left sector of
the far end's position. -/
theorem attach_end
    {z : Point} {σ T : ℝ} (hσ : σ = 1 ∨ σ = -1) (hT : 0 < T)
    (hw : sidePt W p t = rayPt z σ T) (hsec : sideLeft W p t (rayPt (sidePt W p t) (-σ) 1)) :
    SideAttach W (chordOf z σ T) p t := by
  refine ⟨hp, ht0, ht1, by rw [hw]; exact (mem_chordOf hσ hT.le).2 ⟨T, hT.le, le_rfl, rfl⟩,
    1, one_pos, fun x hx hxz _ => ?_⟩
  obtain ⟨s, -, hsT, rfl⟩ := (mem_chordOf hσ hT.le).1 hx
  have hs : s < T := by
    rcases hsT.lt_or_eq with h | h
    · exact h
    · subst h; exact absurd hw.symm hxz
  have e : rayPt z σ s = rayPt (sidePt W p t) (-σ) (T - s) := by simp [hw, rayPt_back]
  rw [e]
  exact (sideLeft_rayPt_iff W p t (-σ) one_pos (by linarith)).1 hsec

end

/-- A point of the chord off the domain is one of its ends, when its open part is in the
domain. -/
theorem chordOf_end {D : Set Point} {z : Point} {σ T : ℝ} (hσ : σ = 1 ∨ σ = -1) (hT : 0 ≤ T)
    (hdom : ∀ t, 0 < t → t < T → rayPt z σ t ∈ D) {x : Point} (hx : x ∈ chordOf z σ T)
    (hxD : x ∉ D) : x = z ∨ x = rayPt z σ T := by
  obtain ⟨s, hs0, hsT, rfl⟩ := (mem_chordOf hσ hT).1 hx
  rcases hs0.lt_or_eq with h0 | h0
  · rcases hsT.lt_or_eq with h1 | h1
    · exact absurd (hdom s h0 h1) hxD
    · right; rw [h1]
  simp [← h0]

/-- **Local shooting in a good model.**  Let the ray from the point `z` off the domain start in
the region `U` of a chord family and reach a point off the domain at parameter `t₁`.  Then it
leaves the domain first at some `T ≤ t₁`; the open stretch before `T` is in `U`; the segment
`chordOf z σ T` is an admissible chord (for a chain model, if `z` is not above the top); it is
attached at a walk position of its far end; and the far end lies on an arc of `U`. -/
theorem local_exit (hGM : GoodModel M) {Q : Polygon} {F : Set (Set Point)}
    (hFam : M.ChordFamily Q F) {U : Set Point} (hU : U ∈ M.regions F) {z : Point} {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hzD : z ∉ M.D) (hini : ∀ᶠ t in 𝓝[>] (0 : ℝ), rayPt z σ t ∈ U)
    {t₁ : ℝ} (ht₁ : 0 < t₁) (hout : rayPt z σ t₁ ∉ M.D)
    (htop : ∀ C : Chain, M = chainModel C → z.2 ≤ C.top.2) :
    ∃ T, 0 < T ∧ T ≤ t₁ ∧ rayPt z σ T ∉ M.D ∧ (∀ t, 0 < t → t < T → rayPt z σ t ∈ U) ∧
      chordOf z σ T ∈ M.Adm ∧
      (∃ p t, SideAttach M.W (chordOf z σ T) p t ∧ sidePt M.W p t = rayPt z σ T) ∧
      ∃ a b, M.IsArc F U a b ∧ rayPt z σ T ∈ M.arcSet a b := by
  have hM := walkAx_of_goodModel hGM
  have hUfree := Chazelle.Chain.regionsIn_subset hU
  have hiniD := hini.mono fun t h => (hUfree h).1
  obtain ⟨T, hT, hTt, hTD, hdom⟩ := exit_exists hM.isOpen hiniD ht₁ hout
  have hray := ray_open_subset (fun _ => adm_hchord hGM) hFam.2.1 hU hσ hT hdom hini
  -- the segment is a horizontal chord of the domain
  have hH : IsHChordIn M.D z.2 (min z.1 (z.1 + σ * T)) (max z.1 (z.1 + σ * T)) := by
    rcases hσ with rfl | rfl
    · rw [min_eq_left (by linarith), max_eq_right (by linarith)]
      refine ⟨by linarith, by simpa using hzD, by simpa [rayPt] using hTD, fun x h1 h2 => ?_⟩
      have := hdom (x - z.1) (by linarith) (by linarith)
      simpa [rayPt] using this
    · rw [min_eq_right (by linarith), max_eq_left (by linarith)]
      refine ⟨by linarith, by simpa [rayPt] using hTD, by simpa using hzD, fun x h1 h2 => ?_⟩
      have := hdom (z.1 - x) (by linarith) (by linarith)
      simpa [rayPt] using this
  have hadm := hchord_adm hGM hH htop
  -- a walk position at the far end
  obtain ⟨a, b, hab, -, -, -, ⟨⟨pa, ta, hAa, hpa⟩, -⟩, ⟨⟨pb, tb, hAb, hpb⟩, -⟩⟩ := hM.ends _ hadm
  have hend : ∃ p t, SideAttach M.W (chordOf z σ T) p t ∧ sidePt M.W p t = rayPt z σ T := by
    have ca := chordOf_end hσ hT.le hdom hAa.2.2.2.1 (hM.trace pa hAa.1 ta hAa.2.1 hAa.2.2.1.le)
    have cb := chordOf_end hσ hT.le hdom hAb.2.2.2.1 (hM.trace pb hAb.1 tb hAb.2.1 hAb.2.2.1.le)
    rw [hpa] at ca
    rw [hpb] at cb
    rcases ca with ca | ca
    · rcases cb with cb | cb
      · exact absurd (ca.trans cb.symm) hab
      · exact ⟨pb, tb, hAb, hpb.trans cb⟩
    · exact ⟨pa, ta, hAa, hpa.trans ca⟩
  obtain ⟨p, t, hA, hpt⟩ := hend
  refine ⟨T, hT, hTt, hTD, hray, hadm, ⟨p, t, hA, hpt⟩, ?_⟩
  -- the far end lies on an arc of `U`
  have hnσ : -σ = 1 ∨ -σ = -1 := by rcases hσ with rfl | rfl <;> norm_num
  obtain ⟨r, hr, hcl⟩ := hA.2.2.2.2
  set s₀ := min T r / 2 with hs₀
  have hmin := lt_min hT hr
  have hs₀0 : 0 < s₀ := by rw [hs₀]; linarith
  have hs₀T : s₀ < T := by rw [hs₀]; linarith [min_le_left T r]
  have hs₀r : s₀ < r := by rw [hs₀]; linarith [min_le_right T r]
  have hx₀ : sideLeft M.W p t (rayPt (sidePt M.W p t) (-σ) s₀) := by
    rw [hpt, rayPt_back]
    refine hcl _ ((mem_chordOf hσ hT.le).2 ⟨T - s₀, by linarith, by linarith, rfl⟩) ?_ ?_
    · intro h
      rw [hpt] at h
      have := congrArg Prod.fst h
      simp only [rayPt_fst] at this
      rcases hσ with rfl | rfl <;> linarith
    · rwa [hpt, ← rayPt_back, dist_rayPt _ hnσ hs₀0.le]
  have hsec : ∀ s > 0, sideLeft M.W p t (rayPt (sidePt M.W p t) (-σ) s) := fun s hs =>
    (sideLeft_rayPt_iff M.W p t (-σ) hs₀0 hs).1 hx₀
  have happ : ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt (sidePt M.W p t) (-σ) s ∈ U := by
    filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT hT] with s hs hsT
    have hs0 : (0 : ℝ) < s := hs
    rw [hpt, rayPt_back]
    exact hray _ (by linarith [hsT.2]) (by linarith)
  obtain ⟨a', b', harc, hmem⟩ :=
    hit_mem_arcSet hGM hFam hU hA.1 hA.2.1 hA.2.2.1 hnσ hsec happ
  rw [hpt] at hmem
  exact ⟨a', b', harc, hmem⟩

end Ray

end

end Restore

end Chazelle.Core
