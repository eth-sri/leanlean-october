module

public import Chazelle.Core.ShootCutShCmp
public import Chazelle.Core.ShootCutShPiece

/-!
# WP-G, part 42: the answer on one segment, as the machine decides it

`edgeSel` is the decision tree of the machine on a segment `[U, V]` of a walk edge (the heights
of `U`, `V`, `z`, the side of the ray of the candidates), and `edge_cand` its correctness: the
selected point (`1`: `U`, `2`: `V`, `3`: the point `X` of the segment at the height of `z`, `0`:
none) is the first hit.  `mid_pos`: on a walk edge, the position at the height of `z` strictly
between the heights of the ends is a point of the segment.
-/

namespace Chazelle.Core

@[expose] public section

open Set
open Chazelle.Geometry (lerp lerp_fst lerp_snd)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)

namespace ShootCut

open Classical in
/-- **The decision tree of the machine** on a segment. -/
noncomputable def edgeSel (eUV zU zV aU aV nearU mid aX : Prop) : ℕ :=
  if eUV then (if zU then (if aU then (if nearU then 1 else 2) else 0) else 0)
  else if zU then (if aU then 1 else 0)
  else if zV then (if aV then 2 else 0)
  else if mid then (if aX then 3 else 0) else 0

/-- The abscissa of the selected point. -/
def selX (U V X : Point) : ℕ → ℝ
  | 1 => U.1
  | 2 => V.1
  | 3 => X.1
  | _ => 0

/-- **Correctness of the decision tree.** -/
theorem edge_cand {U V z X : Point} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (hzS : z ∉ seg U V)
    (hX : (U.2 < z.2 ∧ z.2 < V.2) ∨ (V.2 < z.2 ∧ z.2 < U.2) → X ∈ seg U V ∧ X.2 = z.2) :
    let sel := edgeSel (U.2 = V.2) (z.2 = U.2) (z.2 = V.2) (0 < σ * (U.1 - z.1))
      (0 < σ * (V.1 - z.1)) (σ * U.1 ≤ σ * V.1)
      ((U.2 < z.2 ∧ z.2 < V.2) ∨ (V.2 < z.2 ∧ z.2 < U.2)) (0 < σ * (X.1 - z.1))
    Cand (seg U V) z σ (if sel = 0 then 0 else 1) (selX U V X sel) := by
  intro sel
  classical
  have e0 : ∀ f : ℕ, ∀ x : ℝ, Cand (seg U V) z σ 0 x → Cand (seg U V) z σ 0 (selX U V X f) :=
    fun _ _ h => ⟨fun h' => absurd h' (by norm_num), h.2⟩
  by_cases hUV : U.2 = V.2
  · by_cases hzU : z.2 = U.2
    · have hc := seg_on hσ hUV hzU hzS
      by_cases hA : 0 < σ * (U.1 - z.1)
      · by_cases hn : σ * U.1 ≤ σ * V.1
        · have : sel = 1 := by show edgeSel _ _ _ _ _ _ _ _ = _; unfold edgeSel; simp only [hUV, hzU, hA, hn, ↓reduceIte]
          rw [this]; simp only [one_ne_zero, ↓reduceIte, selX]
          simpa [hA, hn] using hc
        · have : sel = 2 := by show edgeSel _ _ _ _ _ _ _ _ = _; unfold edgeSel; simp only [hUV, hzU, hA, hn, ↓reduceIte]
          rw [this]; simp only [OfNat.ofNat_ne_zero, ↓reduceIte, selX]
          simpa [hA, hn] using hc
      · have : sel = 0 := by show edgeSel _ _ _ _ _ _ _ _ = _; unfold edgeSel; simp only [hUV, hzU, hA, ↓reduceIte]
        rw [this]; simp only [↓reduceIte]
        exact e0 0 _ (by simpa [hA] using hc)
    · have : sel = 0 := by show edgeSel _ _ _ _ _ _ _ _ = _; unfold edgeSel; rw [ite_eq_left hUV, ite_eq_right hzU]
      rw [this]; simp only [↓reduceIte]
      exact e0 0 0 (seg_off hUV hzU 0)
  -- ends at different heights
  by_cases hzU : z.2 = U.2
  · have hc := seg_at hσ hUV (U_mem_seg U V) hzU.symm
    by_cases hA : 0 < σ * (U.1 - z.1)
    · have : sel = 1 := by show edgeSel _ _ _ _ _ _ _ _ = _; unfold edgeSel; simp only [hUV, hzU, hA, ↓reduceIte]
      rw [this]; simpa [selX, hA] using hc
    · have : sel = 0 := by show edgeSel _ _ _ _ _ _ _ _ = _; unfold edgeSel; simp only [hUV, hzU, hA, ↓reduceIte]
      rw [this]; simp only [↓reduceIte]; exact e0 0 _ (by simpa [hA] using hc)
  by_cases hzV : z.2 = V.2
  · have hc := seg_at hσ hUV (V_mem_seg U V) hzV.symm
    by_cases hA : 0 < σ * (V.1 - z.1)
    · have : sel = 2 := by show edgeSel _ _ _ _ _ _ _ _ = _; unfold edgeSel; rw [ite_eq_right hUV, ite_eq_right hzU, ite_eq_left hzV, ite_eq_left hA]
      rw [this]; simpa [selX, hA] using hc
    · have : sel = 0 := by show edgeSel _ _ _ _ _ _ _ _ = _; unfold edgeSel; rw [ite_eq_right hUV, ite_eq_right hzU, ite_eq_left hzV, ite_eq_right hA]
      rw [this]; simp only [↓reduceIte]; exact e0 0 _ (by simpa [hA] using hc)
  by_cases hmid : (U.2 < z.2 ∧ z.2 < V.2) ∨ (V.2 < z.2 ∧ z.2 < U.2)
  · obtain ⟨hXS, hXy⟩ := hX hmid
    have hc := seg_at hσ hUV hXS hXy
    by_cases hA : 0 < σ * (X.1 - z.1)
    · have : sel = 3 := by show edgeSel _ _ _ _ _ _ _ _ = _; unfold edgeSel; simp only [hUV, hzU, hzV, hmid, hA, ↓reduceIte]
      rw [this]; simpa [selX, hA] using hc
    · have : sel = 0 := by show edgeSel _ _ _ _ _ _ _ _ = _; unfold edgeSel; simp only [hUV, hzU, hzV, hmid, hA, ↓reduceIte]
      rw [this]; simp only [↓reduceIte]; exact e0 0 _ (by simpa [hA] using hc)
  · have : sel = 0 := by show edgeSel _ _ _ _ _ _ _ _ = _; unfold edgeSel; simp only [hUV, hzU, hzV, hmid, ↓reduceIte]
    rw [this]; simp only [↓reduceIte]
    refine e0 0 0 (seg_out ?_ 0)
    rintro ⟨h1, h2⟩
    apply hmid
    rcases le_total U.2 V.2 with h | h
    · rw [min_eq_left h] at h1; rw [max_eq_right h] at h2
      exact Or.inl ⟨lt_of_le_of_ne h1 (Ne.symm hzU), lt_of_le_of_ne h2 hzV⟩
    · rw [min_eq_right h] at h1; rw [max_eq_left h] at h2
      exact Or.inr ⟨lt_of_le_of_ne h1 (Ne.symm hzV), lt_of_le_of_ne h2 hzU⟩

/-- **The position at the height of `z` inside a sub-segment of a walk edge.** -/
theorem mid_pos (M : Model) (Q : Polygon) {p h : ℕ} {α β : ℝ} (hα : 0 ≤ α) (hαβ : α ≤ β)
    (hβ : β ≤ 1)
    (hmid : ((lerp (M.wa p) (M.wb p) α).2 < (Q.vtx h).2 ∧
        (Q.vtx h).2 < (lerp (M.wa p) (M.wb p) β).2) ∨
      ((lerp (M.wa p) (M.wb p) β).2 < (Q.vtx h).2 ∧
        (Q.vtx h).2 < (lerp (M.wa p) (M.wb p) α).2)) :
    M.pos Q ⟨p, h + 1⟩ ∈ seg (lerp (M.wa p) (M.wb p) α) (lerp (M.wa p) (M.wb p) β) ∧
      (M.pos Q ⟨p, h + 1⟩).2 = (Q.vtx h).2 ∧ 0 < M.param Q ⟨p, h + 1⟩ ∧
      M.param Q ⟨p, h + 1⟩ < 1 := by
  set a := M.wa p
  set b := M.wb p
  have hne : a.2 ≠ b.2 := by
    intro he
    simp only [lerp_snd] at hmid
    rw [he] at hmid
    rcases hmid with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
  have hd : b.2 - a.2 ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
  have hpar : M.param Q ⟨p, h + 1⟩ = ((Q.vtx h).2 - a.2) / (b.2 - a.2) := by
    show (if (M.wa p).2 = (M.wb p).2 then 0 else _) = _
    rw [ite_eq_right hne]
  set t := M.param Q ⟨p, h + 1⟩
  have hpos : M.pos Q ⟨p, h + 1⟩ = lerp a b t := rfl
  have hty : a.2 + t * (b.2 - a.2) = (Q.vtx h).2 := by rw [hpar]; field_simp; ring
  -- `t` strictly between `α` and `β`
  simp only [lerp_snd] at hmid
  have hαt : α < t ∧ t < β := by
    rcases lt_or_gt_of_ne hd with hs | hs
    · rcases hmid with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exfalso; rw [← hty] at h1 h2; nlinarith
      · rw [← hty] at h1 h2
        constructor <;> nlinarith
    · rcases hmid with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [← hty] at h1 h2
        constructor <;> nlinarith
      · exfalso; rw [← hty] at h1 h2; nlinarith
  refine ⟨?_, by rw [hpos, lerp_snd, hty], by linarith [hαt.1], by linarith [hαt.2]⟩
  rw [hpos, ← subSeg_eq_seg M p hαβ]
  exact ⟨t, hαt.1.le, hαt.2.le, rfl⟩

end ShootCut

end

end Chazelle.Core
