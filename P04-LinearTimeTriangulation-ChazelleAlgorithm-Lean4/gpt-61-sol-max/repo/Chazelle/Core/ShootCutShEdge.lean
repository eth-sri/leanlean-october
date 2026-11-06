module

public meta import Chazelle.Arithmetic

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
        · have : sel = 1 := by show edgeSel _ _ _ _ _ _ _ _ = _; simp_all [edgeSel, reduceIte] <;> omega_nf
          rw [this]; simp only [one_ne_zero, ↓reduceIte, selX]
          simp_all
        · have : sel = 2 := by show edgeSel _ _ _ _ _ _ _ _ = _; unfold edgeSel; ram_grind
          rw [this]; simp only [OfNat.ofNat_ne_zero, ↓reduceIte, selX]
          simp_all +arith
      · have : sel = 0 := by show edgeSel _ _ _ _ _ _ _ _ = _; unfold edgeSel; ram_grind
        grind
    · have : sel = 0 := by aesop (add simp [edgeSel]) (add safe (by omega))
      rw [this]; simp only [↓reduceIte]
      exact e0 0 0 (seg_off hUV hzU 0)
  -- ends at different heights
  by_cases hzU : z.2 = U.2
  · have hc := seg_at hσ hUV (U_mem_seg U V) hzU.symm
    by_cases hA : 0 < σ * (U.1 - z.1)
    · have : sel = 1 := by aesop (add simp [edgeSel, reduceIte]) (add safe (by omega))
      core_grind
    · have : sel = 0 := by show edgeSel _ _ _ _ _ _ _ _ = _; simp_all [edgeSel, reduceIte] <;> omega_nf
      grind
  by_cases hzV : z.2 = V.2
  · have hc := seg_at hσ hUV (V_mem_seg U V) hzV.symm
    by_cases hA : 0 < σ * (V.1 - z.1)
    · core_grind [edgeSel]
    · have : sel = 0 := by grind [edgeSel]
      grind
  by_cases hmid : (U.2 < z.2 ∧ z.2 < V.2) ∨ (V.2 < z.2 ∧ z.2 < U.2)
  · obtain ⟨hXS, hXy⟩ := hX hmid
    have hc := seg_at hσ hUV hXS hXy
    by_cases hA : 0 < σ * (X.1 - z.1)
    · have : sel = 3 := by aesop (add simp [edgeSel, reduceIte]) (add safe (by omega))
      simp_all [selX] <;> omega_nf
    · have : sel = 0 := by show edgeSel _ _ _ _ _ _ _ _ = _; simp_all [edgeSel, reduceIte] <;> omega_nf
      grind
  · have : sel = 0 := by show edgeSel _ _ _ _ _ _ _ _ = _; unfold edgeSel; ram_grind
    rw [this]; simp only [↓reduceIte]
    refine e0 0 0 (seg_out ?_ 0)
    ram_grind

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
    grind [lerp_snd]
  have hd : b.2 - a.2 ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
  have hpar : M.param Q ⟨p, h + 1⟩ = ((Q.vtx h).2 - a.2) / (b.2 - a.2) := by
    show (if (M.wa p).2 = (M.wb p).2 then 0 else _) = _
    grind
  set t := M.param Q ⟨p, h + 1⟩
  have hpos : M.pos Q ⟨p, h + 1⟩ = lerp a b t := rfl
  have hty : a.2 + t * (b.2 - a.2) = (Q.vtx h).2 := by simp_all
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
  refine ⟨?_, by simp_all, by linarith, by linarith⟩
  rw [hpos, ← subSeg_eq_seg M p hαβ]
  exact ⟨t, hαt.1.le, hαt.2.le, rfl⟩

end ShootCut

end

end Chazelle.Core
