module

public import Chazelle.Core.SweepEvMap3
public import Chazelle.Core.SweepEvStep

/-!
# The sweep (WP-D), stage 3: soundness of a candidate (mathematics)

A candidate of the event loop is the hit `w = rayPt a σ τ` in the model of `C₁` of the ray from
an end `a` of a chord `c ∈ S₂` (on `C₂`, not the shared vertex), along `c`.  If the hit is
genuine for `C₁` and strictly before the far end of `c`, the chord of `C` seen from `a` ends at
`w`, and its attachment there is the image (`mEdge`) of the arrival position of `w` in `M₁`.

* `right_hit_end`: the chord of `C₂` seen from an end of `c ∈ augChords C₂` is `c`;
* `whole_free_end`: the direction along `c` is free for `C`;
* `whole_hit_lt`, `whole_hit_right`: the first hit of `C` is the earlier of those of `C₁`, `C₂`;
* `cand_sound`: the attachment of the chord of `C` at the candidate.
-/

namespace Chazelle.Core

@[expose] public section

open Set
open Chazelle.Chain (SideAttach sidePt)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
open Chazelle.Geometry (lerp point_ext)
open Chazelle.Merge (FreeAt)
open WalkEmbed

namespace Sweep

variable {J : Merge.Junction}

/-- **The chord of `C₂` seen from an end** of an augmented chord `c`, along `c`: the direction is
free and the first hit is the far end (at distance the length of `c`). -/
theorem right_hit_end {c : Set Point} (hc : c ∈ Merge.augChords J.right) {a : Point} {σ : ℝ}
    (ha : (σ = 1 ∧ a = Merge.lend c) ∨ (σ = -1 ∧ a = Merge.rend c)) :
    FreeAt J.right a σ ∧ a.2 ≤ J.right.top.2 ∧
      0 < (Merge.rend c).1 - (Merge.lend c).1 ∧
      J.right.hitParam a σ = (Merge.rend c).1 - (Merge.lend c).1 ∧
      (Merge.lend c).2 = a.2 ∧ (Merge.rend c).2 = a.2 := by
  obtain ⟨y, l, r, hH, hy, -, hl, hr⟩ := Merge.augChords_spec hc
  rw [hl, hr]
  have hlr := hH.lt
  rcases ha with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [hl]
    refine ⟨Merge.freeAt_of_isHChordIn_left _ hH, hy, by simp only; linarith, ?_, rfl, rfl⟩
    refine J.right.hitParam_eq_of_first _ 1 (by simp only; linarith) ?_ fun s hs1 hs2 => ?_
    · have : rayPt ((l, y) : Point) 1 (r - l) = ((r, y) : Point) := by
        simp only [rayPt, one_mul, add_sub_cancel]
      simp only
      rw [this]; exact hH.right_not
    · have e : rayPt ((l, y) : Point) 1 s = ((l + s, y) : Point) := by simp [rayPt]
      rw [e]
      exact hH.open_mem _ (by linarith) (by simp only at hs2; linarith)
  · rw [hr]
    refine ⟨Merge.freeAt_of_isHChordIn_right _ hH, hy, by simp only; linarith, ?_, rfl, rfl⟩
    refine J.right.hitParam_eq_of_first _ (-1) (by simp only; linarith) ?_ fun s hs1 hs2 => ?_
    · have : rayPt ((r, y) : Point) (-1) (r - l) = ((l, y) : Point) := by
        simp only [rayPt, neg_one_mul, neg_sub, add_sub_cancel]
      simp only
      rw [this]; exact hH.left_not
    · have e : rayPt ((r, y) : Point) (-1) s = ((r - s, y) : Point) := by
        simp [rayPt, sub_eq_add_neg]
      rw [e]
      exact hH.open_mem _ (by simp only at hs2; linarith) (by linarith)

/-- A point of `C₂` other than the shared vertex is off `C₁`. -/
theorem not_mem_left_of_right (hP : J.P.Simple) {a : Point} (ha : a ∈ J.right.set)
    (hv : a ≠ J.shared) : a ∉ J.left.set := fun h => hv (by
  have : a ∈ J.left.set ∩ J.right.set := ⟨h, ha⟩
  rw [Merge.Junction.left_inter_right J hP] at this
  exact this)

/-- **The direction along a chord of `C₂` from an end on `C₂`** (not the shared vertex) is free for
`C`. -/
theorem whole_free_end (hP : J.P.Simple) {a : Point} (ha : a ∈ J.right.set) (hv : a ≠ J.shared)
    {σ : ℝ} (hfree : FreeAt J.right a σ) : FreeAt J.whole a σ := by
  have haw : a.2 ≤ J.whole.top.2 :=
    J.whole.snd_le_top_of_mem_set (J.right_set_subset ha)
  have ha₂ : a.2 ≤ J.right.top.2 := J.right.snd_le_top_of_mem_set ha
  rw [freeAt_whole_iff J haw]
  have hR₂ : J.right.radius = J.whole.radius := rfl
  have hR₁ : J.left.radius = J.whole.radius := rfl
  have hleft : ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0), rayPt a σ t ∉ J.left.set := by
    by_cases h₁ : a.2 ≤ J.left.top.2
    · have haD : a ∈ J.left.dom := by
        by_contra hn
        rcases (Merge.not_mem_dom_iff J.left h₁).1 hn with hb | hs
        · rw [hR₁, ← hR₂] at hb; exact hb (J.right.set_subset_box ha)
        · exact not_mem_left_of_right hP ha hv hs
      filter_upwards [Merge.freeAt_of_mem_dom J.left haD σ] with t ht
      intro hs
      exact J.left.not_mem_set_of_mem_dom ht hs
    · push Not at h₁
      exact Filter.Eventually.of_forall fun t hs => by
        have := J.left.snd_le_top_of_mem_set hs
        rw [rayPt_snd] at this
        linarith
  filter_upwards [hfree, hleft] with t ht hl
  have h2 : (rayPt a σ t).2 ≤ J.right.top.2 := by rw [rayPt_snd]; exact ha₂
  have hnd := (Merge.not_mem_dom_iff J.right h2)
  refine ⟨?_, hl, fun hs => hnd.2 (Or.inr hs) ht⟩
  by_contra hb
  rw [← hR₂] at hb
  exact hnd.2 (Or.inl hb) ht

/-- **The first hit of `C`** when the genuine hit of `C₁` comes strictly before that of `C₂`. -/
theorem whole_hit_lt {a : Point} (ha₁ : a.2 ≤ J.left.top.2) (ha₂ : a.2 ≤ J.right.top.2) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) {τ : ℝ} (hg : Genuine J.left a σ τ)
    (hlt : τ < J.right.hitParam a σ) : J.whole.hitParam a σ = τ := by
  have haw : a.2 ≤ J.whole.top.2 := le_trans ha₁ J.left_top_le
  rw [whole_hitParam_eq_min J haw hσ, left_hitParam_eq J ha₁, right_hitParam_eq J ha₂]
  rw [((genuine_iff J.left ha₁ hσ).1 hg).2]
  exact min_eq_left hlt.le

/-- **The first hit of `C`** when that of `C₂` is not later than that of `C₁` (or `a` is above
the top of `C₁`). -/
theorem whole_hit_right {a : Point} (ha₂ : a.2 ≤ J.right.top.2) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (h : a.2 ≤ J.left.top.2 → J.right.hitParam a σ ≤ J.left.hitParam a σ)
    (hbox : J.right.hitParam a σ ≤ Merge.rayHit J.whole.radius ∅ a σ) :
    J.whole.hitParam a σ = J.right.hitParam a σ := by
  have haw : a.2 ≤ J.whole.top.2 := le_trans ha₂ J.right_top_le
  rw [whole_hitParam_eq_min J haw hσ, right_hitParam_eq J ha₂]
  apply min_eq_right
  by_cases h₁ : a.2 ≤ J.left.top.2
  · rw [left_hitParam_eq J h₁]; exact h h₁
  · push Not at h₁
    rw [rayHit_eq_empty_of_above J.left h₁]
    exact hbox

/-- **The chord seen from an end of a chord of `S₂`** belongs to `F₂⁺`. -/
theorem shoot_end_mem {S₂ : Set (Set Point)} {c : Set Point} (hc : c ∈ S₂) {a : Point} {σ : ℝ}
    (ha : (σ = 1 ∧ a = Merge.lend c) ∨ (σ = -1 ∧ a = Merge.rend c)) (hfree : FreeAt J.whole a σ) :
    Merge.shoot J.whole a σ ∈ F₂plus J S₂ := by
  rcases ha with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl (Or.inl (Or.inl ⟨c, by simp [hc], hfree, rfl⟩))
  · exact Or.inl (Or.inl (Or.inr ⟨c, by simp [hc], hfree, rfl⟩))

theorem lerp_rayPt (a : Point) (σ τ s : ℝ) : lerp a (rayPt a σ τ) s = rayPt a σ (s * τ) := by
  apply point_ext
  · simp only [Geometry.lerp_fst, rayPt_fst]; ring
  · simp only [Geometry.lerp_snd, rayPt_snd]; ring

/-- **Soundness of a candidate.**  The hit `rayPt a σ τ` of `C₁`, genuine and strictly before the
far end of `c`, arriving at the `b₁`-offset `d` of the walk of `C₁` (a valid offset): the chord of
`C` seen from `a` belongs to `F₂⁺`, ends there, and is attached at `(mEdge d, t)`, on the `C₁`
part. -/
theorem cand_sound (hP : J.P.Simple) {S₂ : Set (Set Point)} (hS₂ : S₂ ⊆ Merge.augChords J.right)
    (hS₂f : S₂.Finite) {c : Set Point} (hc : c ∈ S₂) {a : Point} {σ : ℝ}
    (ha : (σ = 1 ∧ a = Merge.lend c) ∨ (σ = -1 ∧ a = Merge.rend c)) (haR : a ∈ J.right.set)
    (hv : a ≠ J.shared) (ha₁ : a.2 ≤ J.left.top.2) {τ : ℝ} (hg : Genuine J.left a σ τ)
    (hlt : τ < (Merge.rend c).1 - (Merge.lend c).1) {d : ℕ} {t : ℝ}
    (hMV : d < E₁ J ∧ ¬ (0 < lδ J ∧ lL1 J < d ∧ d < lL1 J + lδ J) ∧
      ¬ (0 < lδ J ∧ d = lL1 J ∧ t ≠ 0))
    (hA : Arrival (chainModel J.left).W (rayPt a σ τ) σ ((b₁ J + d) % (chainModel J.left).W.n) t) :
    FreeAt J.whole a σ ∧ J.whole.hitParam a σ = τ ∧ Merge.shoot J.whole a σ ∈ F₂plus J S₂ ∧
      SideAttach (chainModel J.whole).W (Merge.shoot J.whole a σ) (mEdge J d) t ∧
      sidePt (chainModel J.whole).W (mEdge J d) t = rayPt a σ τ ∧
      oW J ((mEdge J d : ℝ) + t) = (Lst J : ℝ) + ψ J d + t := by
  have hσ : σ = 1 ∨ σ = -1 := by rcases ha with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]
  obtain ⟨hfr, ha₂, hlen, hR, -, -⟩ := right_hit_end (hS₂ hc) ha
  have hfree := whole_free_end hP haR hv hfr
  have hτ : 0 < τ := hg.1
  have hhit : J.whole.hitParam a σ = τ := whole_hit_lt ha₁ ha₂ hσ hg (by rw [hR]; exact hlt)
  -- the hit point is in the open chord `c`, hence not the shared vertex
  have hwD : rayPt a σ τ ∈ J.right.dom := by
    obtain ⟨-, -, hdom⟩ := Merge.hit_of_freeAt J.right ha₂ hσ hfr
    exact hdom τ hτ (by rw [hR]; exact hlt)
  have hwv : rayPt a σ τ ≠ J.shared := fun h =>
    J.right.not_mem_set_of_mem_dom hwD (by rw [h]; exact J.shared_mem_right)
  have hMV' : MValid J d t := ⟨hMV.1, hMV.2.1, hMV.2.2, fun ht => by
    have hpt : sidePt (chainModel J.left).W ((b₁ J + d) % (chainModel J.left).W.n) t =
        rayPt a σ τ := hA.2.2.2.1
    rw [ht] at hpt; rw [hpt]; exact hwv⟩
  obtain ⟨hS, hO⟩ := map_sound hP hσ hτ hhit hMV' hA
  have hM : WalkAx (chainModel J.whole) := FactsChain.walkAx J.whole hP
  have hpt : sidePt (chainModel J.whole).W (mEdge J d) t = rayPt a σ τ := by
    have hmem : sidePt (chainModel J.whole).W (mEdge J d) t ∈
        Chazelle.segment a (rayPt a σ τ) := by
      have := hS.2.2.2.1
      unfold Merge.shoot at this; rwa [hhit] at this
    have hnd : sidePt (chainModel J.whole).W (mEdge J d) t ∉ J.whole.dom :=
      hM.trace _ hS.1 t hS.2.1 hS.2.2.1.le
    refine seg_end hmem hnd (fun s hs => ?_) (fun h => ?_)
    · rw [lerp_rayPt]
      obtain ⟨-, -, hdom⟩ := Merge.hit_of_freeAt J.whole
        (le_trans ha₂ J.right_top_le) hσ hfree
      exact hdom _ (mul_pos hs.1 hτ) (by rw [hhit]; nlinarith [hs.2])
    · have := off_right_pt J hP hS₂ hS₂f hS.1 hS.2.1 hS.2.2.1 (by rw [h]; exact haR)
        (by rw [h]; exact hv)
      have h2 : oW J ((mEdge J d : ℝ) + t) < Lst J := by
        unfold oW gW; exact_mod_cast this.2
      rw [hO] at h2
      have : (0 : ℝ) ≤ ψ J d := Nat.cast_nonneg _
      linarith [hS.2.1]
  exact ⟨hfree, hhit, shoot_end_mem hc ha hfree, hS, hpt, hO⟩

end Sweep

end

end Chazelle.Core
