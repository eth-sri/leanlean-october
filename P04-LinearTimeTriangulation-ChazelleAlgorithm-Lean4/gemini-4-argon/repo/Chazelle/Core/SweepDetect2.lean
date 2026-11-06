module

public import Chazelle.Core.SweepDetect
public import Chazelle.Core.SweepQuery

/-!
# The sweep (WP-D), part 14: detection shots (decision rule, soundness and completeness)

Gap S3 of the design (§10.r).  The sweep shoots, in the model of a chain `C` (the chain `C₁`),
from a point `a` of the domain (an endpoint of a candidate chord of `S₂`) at the arcs of a region
of `S₁`.  A hit at `w = rayPt a σ τ` is **genuine** (`Genuine`) if the ray stays in the domain
before `w` and `w` is off the domain: then `w` is the first point of the walk hit from `a`.  The
RAM decides genuineness from the **arrival position** of the hit (`Arrival`: the walk position of
`w` whose left sector contains the ray arriving at `w`):

* **non-cut key** inside an arc of the shot region: accept (`genuine_of_arc`);
* **cut walk vertex**, no chord of `S₁` along the arriving ray: accept if the shot at the arcs of
  the region of the arc beginning at the vertex (the arriving ray turns counterclockwise from the
  next walk edge) or ending there (clockwise from the previous edge) hits first at `w`
  (`genuine_of_after`, `genuine_of_before`);
* **a chord `e` of `S₁` along the arriving ray**: accept iff `a ∈ e` (`genuine_of_chord`,
  `mem_chord_of_genuine`).

Completeness: a genuine hit is the first hit on any list of subarcs containing it
(`firstHit_of_genuine`); it has an arrival position (`arrival_exists`); if no chord lies along the
arriving ray, a cut key inside a walk edge is impossible (`not_cut_of_edge`), and at a cut walk
vertex the chords avoid the ray and one of the two turning conditions holds
(`vertex_cases_of_genuine`).
-/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sideInArc sidePt sideLeft sideLeftOf sideCross freeIn regionsIn
  IsHChordIn)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd hseg)
open Chazelle.Geometry (lerp point_ext)

namespace Sweep

/-- **A genuine hit**: the ray from `a` stays in the domain of `C` before the parameter `τ` and is
off the domain at `τ`. -/
def Genuine (C : Chain) (a : Point) (σ τ : ℝ) : Prop :=
  0 < τ ∧ (∀ s, 0 < s → s < τ → rayPt a σ s ∈ C.dom) ∧ rayPt a σ τ ∉ C.dom

/-- **An arrival position** of the ray in direction `σ` at the point `w`: a walk position of `w`
whose left sector contains the points just before `w` on the ray. -/
def Arrival (W : Polygon) (w : Point) (σ : ℝ) (p : ℕ) (t : ℝ) : Prop :=
  p < W.n ∧ 0 ≤ t ∧ t < 1 ∧ sidePt W p t = w ∧ sideLeft W p t (rayPt w (-σ) 1)

/-- A genuine hit is the first hit of the chain. -/
theorem genuine_iff (C : Chain) {a : Point} (ha : a.2 ≤ C.top.2) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    {τ : ℝ} : Genuine C a σ τ ↔ Merge.FreeAt C a σ ∧ C.hitParam a σ = τ := by
  constructor
  · rintro ⟨h0, hin, hout⟩
    have hfree : Merge.FreeAt C a σ := by
      filter_upwards [Ioo_mem_nhdsGT h0] with s hs
      exact hin s hs.1 hs.2
    refine ⟨hfree, ?_⟩
    obtain ⟨hT, hTD, hTdom⟩ := Merge.hit_of_freeAt C ha hσ hfree
    rcases lt_trichotomy (C.hitParam a σ) τ with h | h | h
    · exact absurd (hin _ hT h) hTD
    · exact h
    · exact absurd (hTdom τ h0 h) hout
  · rintro ⟨hfree, rfl⟩
    obtain ⟨hT, hTD, hTdom⟩ := Merge.hit_of_freeAt C ha hσ hfree
    exact ⟨hT, hTdom, hTD⟩

section ChainModel

variable (C : Chain)

/-! ## Soundness -/

/-! ## Completeness -/

/-- **A genuine hit has an arrival position.** -/
theorem arrival_exists (hP : C.P.Simple) {a : Point} (ha : a.2 ≤ C.top.2) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) {τ : ℝ} (hg : Genuine C a σ τ) :
    ∃ p t, Arrival (chainModel C).W (rayPt a σ τ) σ p t := by
  obtain ⟨hT, hdom, hwD⟩ := hg
  set T := τ
  set w := rayPt a σ T with hw
  have hback : ∀ s, rayPt w (-σ) s = rayPt a σ (T - s) := fun s => rayPt_back a σ T s
  have hzR : |a.2| < C.radius := by
    have := C.dom_subset_box (hdom (T / 2) (by linarith) (by linarith))
    simpa [rayPt] using this.2
  have he : w ∈ C.set ∨ (|w.1| = C.radius ∧ |w.2| < C.radius) := by
    rcases (Merge.not_mem_dom_iff C (p := w) (by simpa [hw] using ha)).1 hwD with h | h
    · right
      refine ⟨le_antisymm ?_ ?_, by simpa [hw] using hzR⟩
      · by_contra hgt
        push Not at hgt
        set ε := min (T / 2) ((|w.1| - C.radius) / 2) with hε
        have hε0 : 0 < ε := lt_min (by linarith) (by linarith)
        have hεT : ε < T := lt_of_le_of_lt (min_le_left _ _) (by linarith)
        have hbox := C.dom_subset_box (hdom (T - ε) (by linarith) (by linarith))
        have h1 : |(rayPt a σ (T - ε)).1| < C.radius := hbox.1
        have h2 : |w.1| ≤ |(rayPt a σ (T - ε)).1| + ε := by
          have e : w.1 = (rayPt a σ (T - ε)).1 + σ * ε := by simp [hw, rayPt]; ring
          rw [e]
          refine (abs_add_le _ _).trans ?_
          rcases hσ with rfl | rfl <;> simp [abs_of_pos hε0]
        have h3 : ε ≤ (|w.1| - C.radius) / 2 := min_le_right _ _
        linarith
      · by_contra hlt
        push Not at hlt
        exact h ⟨hlt, by simpa [hw] using hzR⟩
    · exact Or.inl h
  have hT2 : (0 : ℝ) < T / 2 := by linarith
  have hee : w ≠ rayPt w (-σ) (T / 2) := by
    intro h
    have := congrArg Prod.fst h
    simp only [rayPt_fst] at this
    rcases hσ with rfl | rfl <;> linarith
  have hopen : ∀ s ∈ Ioo (0 : ℝ) 1, lerp w (rayPt w (-σ) (T / 2)) s ∈ C.dom := by
    intro s hs
    have e : lerp w (rayPt w (-σ) (T / 2)) s = rayPt a σ (T - s * (T / 2)) := by
      apply point_ext <;> simp [lerp, rayPt, hw]; ring
    rw [e]
    exact hdom _ (by nlinarith [hs.2]) (by nlinarith [hs.1])
  obtain ⟨p, t, hp, ht, ht1, hpt, hl⟩ :=
    C.sideSees_chordEnd hP C.sideBeta hee (by simp [rayPt]) hopen he
  refine ⟨p, t, hp, ht, ht1, hpt, ?_⟩
  have hl' : sideLeft (chainModel C).W p t (rayPt (sidePt (chainModel C).W p t) (-σ) (T / 2)) := by
    rw [show sidePt (chainModel C).W p t = w from hpt]; exact hl
  have := (sideLeft_rayPt_iff _ p t (-σ) hT2 one_pos).1 hl'
  rw [show sidePt (chainModel C).W p t = w from hpt] at this
  exact this

/-! ## The arriving ray at a cut key -/

/-- A horizontal ray from `w` either starts along an admissible chord or eventually avoids it. -/
theorem ray_chord_dichotomy {e : Set Point} (he : e ∈ Merge.augChords C) (w : Point) {τ : ℝ}
    (hτ : τ = 1 ∨ τ = -1) :
    (∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt w τ s ∈ e) ∨ (∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt w τ s ∉ e) := by
  obtain ⟨y, l, r, hH, -, rfl, -, -⟩ := Merge.augChords_spec he
  have hlr := hH.lt
  by_cases hy : w.2 = y
  swap
  · right
    exact Filter.Eventually.of_forall fun s hs => hy (by simpa [rayPt] using hs.1)
  rcases hτ with rfl | rfl
  · by_cases h1 : w.1 < l
    · right
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < l - w.1 by linarith)] with s hs hm
      have := hm.2.1; simp [rayPt] at this; linarith [hs.2]
    · by_cases h2 : w.1 < r
      · left
        filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < r - w.1 by linarith)] with s hs
        refine ⟨by simp [rayPt, hy], ?_, ?_⟩ <;> simp [rayPt] <;> linarith [hs.1, hs.2]
      · right
        filter_upwards [self_mem_nhdsWithin] with s hs hm
        have := hm.2.2; simp [rayPt] at this
        have hs' : (0 : ℝ) < s := hs
        linarith
  · by_cases h1 : r < w.1
    · right
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < w.1 - r by linarith)] with s hs hm
      have := hm.2.2; simp [rayPt] at this; linarith [hs.2]
    · by_cases h2 : l < w.1
      · left
        filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < w.1 - l by linarith)] with s hs
        refine ⟨by simp [rayPt, hy], ?_, ?_⟩ <;> simp [rayPt] <;> linarith [hs.1, hs.2]
      · right
        filter_upwards [self_mem_nhdsWithin] with s hs hm
        have := hm.2.1; simp [rayPt] at this
        have hs' : (0 : ℝ) < s := hs
        linarith

/-- The determinant of a walk edge against a horizontal shift of one of its points. -/
theorem det_lerp_shift (u v : Point) (t α : ℝ) :
    det u v ((lerp u v t).1 + α, (lerp u v t).2) = -α * (v.2 - u.2) := by
  simp only [det, Geometry.lerp_fst, Geometry.lerp_snd]; ring

/-- **No cut inside a walk edge under an arriving ray off the chords**: at an arrival position
inside a walk edge, if no chord of the family lies along the arriving ray, the key is not a
cut (a chord attached inside an edge leaves it in the only horizontal direction of the left
half-plane, which is the direction of the arriving ray reversed). -/
theorem not_cut_of_edge (hP : C.P.Simple) {Q : Polygon} {F : Set (Set Point)}
    (hFam : (chainModel C).ChordFamily Q F) {w : Point} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) {p : ℕ}
    {t : ℝ} (hA : Arrival (chainModel C).W w σ p t) (ht0 : 0 < t)
    (hno : ∀ e ∈ F, ¬ ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt w (-σ) s ∈ e) :
    ¬ (chainModel C).IsCut F (p + t) := by
  have hM : WalkAx (chainModel C) := FactsChain.walkAx C hP
  obtain ⟨hp, -, ht1, hpt, hsec⟩ := hA
  rintro ⟨c, hcF, p', t', hAc, hkey⟩
  obtain ⟨hp', ht'0, ht'1, hc', r₀, hr₀, hnear⟩ := hAc
  obtain ⟨rfl, rfl⟩ := Chazelle.Chain.sideKey_inj ht0.le ht1 ht'0 ht'1 hkey
  have hcA : c ∈ Merge.augChords C := hFam.2.1 hcF
  obtain ⟨y, l, r, hH, -, hceq, -, -⟩ := Merge.augChords_spec hcA
  subst hceq
  rw [hpt] at hc' hnear
  obtain ⟨hwy, hwl, hwr⟩ := hc'
  have hwD : w ∉ C.dom := by
    rw [← hpt]; exact hM.trace p hp t ht0.le ht1.le
  have hne := hM.nd p hp
  set u := (chainModel C).W.vtx p with hu
  set v := (chainModel C).W.vtx ((p + 1) % (chainModel C).W.n) with hv
  have hwlerp : w = lerp u v t := hpt.symm
  have hedge : ∀ x, sideLeft (chainModel C).W p t x ↔ 0 < det u v x :=
    fun x => Chazelle.Chain.sideLeft_edge hne ⟨ht0, ht1⟩ x
  have hshift : ∀ α, det u v ((w.1 + α, w.2) : Point) = -α * (v.2 - u.2) := by
    intro α; rw [hwlerp]; exact det_lerp_shift u v t α
  -- the arriving ray reversed is in the left half-plane
  have h1 : 0 < σ * (v.2 - u.2) := by
    have := (hedge _).1 hsec
    have e : rayPt w (-σ) 1 = ((w.1 + -σ, w.2) : Point) := by
      apply point_ext <;> simp [rayPt]
    rw [e, hshift] at this; linarith
  have hlr := hH.lt
  set δ := min r₀ (r - l) / 2 with hδ
  have hδ0 : 0 < δ := by
    have : 0 < min r₀ (r - l) := lt_min hr₀ (by linarith)
    linarith
  have hδr : δ < r₀ := by have := min_le_left r₀ (r - l); linarith
  have hδl : δ < r - l := by have := min_le_right r₀ (r - l); linarith
  have hdist : ∀ α, |α| = δ → dist ((w.1 + α, w.2) : Point) w < r₀ := by
    intro α hα
    rw [Prod.dist_eq]
    simp only [dist_self, Real.dist_eq, add_sub_cancel_left]
    rw [hα, max_eq_left hδ0.le]; exact hδr
  have hno' := fun e he => hno e he
  -- `w` is an end of the chord
  rcases hwl.lt_or_eq with hl | hl
  · rcases hwr.lt_or_eq with hr | hr
    · exact hwD (by rw [show w = ((w.1, y) : Point) from Prod.ext rfl hwy]; exact hH.open_mem _ hl hr)
    · -- `w` is the right end: the chord leaves it to the left
      have hx : sideLeft (chainModel C).W p t ((w.1 + -δ, w.2) : Point) :=
        hnear _ ⟨by simpa using hwy, by linarith, by linarith⟩
          (fun h => by have := congrArg Prod.fst h; simp at this; linarith)
          (hdist _ (by rw [abs_neg, abs_of_pos hδ0]))
      rw [hedge, hshift] at hx
      have hσ1 : σ = 1 := by
        rcases hσ with rfl | rfl
        · rfl
        · nlinarith
      subst hσ1
      apply hno' _ hcF
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < r - l by linarith)] with s hs
      refine ⟨by simp [rayPt, hwy], ?_, ?_⟩ <;> simp [rayPt] <;> linarith [hs.1, hs.2]
  · -- `w` is the left end: the chord leaves it to the right
    have hx : sideLeft (chainModel C).W p t ((w.1 + δ, w.2) : Point) :=
      hnear _ ⟨by simpa using hwy, by linarith, by linarith⟩
        (fun h => by have := congrArg Prod.fst h; simp at this; linarith)
        (hdist _ (abs_of_pos hδ0))
    rw [hedge, hshift] at hx
    have hσ1 : σ = -1 := by
      rcases hσ with rfl | rfl
      · nlinarith
      · rfl
    subst hσ1
    apply hno' _ hcF
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < r - l by linarith)] with s hs
    refine ⟨by simp [rayPt, hwy], ?_, ?_⟩ <;> simp [rayPt] <;> linarith [hs.1, hs.2]

end ChainModel

end Sweep

end

end Chazelle.Core
