module

public import Chazelle.Core.DownPhaseHostDom
public import Chazelle.Core.DownPhaseTourA

/-!
# WP-M (X, part 11): local geometry shared by two walks

Two walks passing the same point along the same line in the same direction have the same left
sectors, the same attachments and (up to a positive scaling of the offset) the same faced sets:
* `sideLeftOf_scale`: corners with positively scaled arms have the same left sector;
* `det_lerp_pair`: the left half-plane of a sub-segment is that of the segment;
* `attach_of_sector`: attachment transfers between positions with the same point and sector;
* `offset_lerp_pair`, `faces_of_offset`: facing transfers when the offsets agree up to a positive
  scaling.
-/

namespace Chazelle.Core

namespace ExtG

@[expose] public section

open Set Filter Topology
open Chazelle.Chain (SideAttach sidePt sideLeft sideLeftOf)
open Chazelle.Geometry (lerp)
open Chazelle.Jordan (offset nrm offset_fst offset_snd)

/-- **Corners with positively scaled arms have the same left sector.** -/
theorem sideLeftOf_scale {a a' v b b' x : Point} {l m : ℝ} (hl : 0 < l) (hm : 0 < m)
    (ha : a' - v = l • (a - v)) (hb : b' - v = m • (b - v)) :
    sideLeftOf a' v b' x ↔ sideLeftOf a v b x := by
  unfold sideLeftOf
  rw [ha, hb]
  have := BoxT.sideCcw_smul hm one_pos hl (b - v) (x - v) (a - v)
  rwa [one_smul] at this

/-- The left half-plane of a sub-segment is that of the segment. -/
theorem det_lerp_pair (A B y : Point) (τ₀ τ₁ : ℝ) :
    Chazelle.det (lerp A B τ₀) (lerp A B τ₁) y = (τ₁ - τ₀) * Chazelle.det A B y := by
  unfold Chazelle.det lerp; simp only; ring

/-- The arms of a sub-segment are positive multiples of the arms of the segment. -/
theorem lerp_sub_lerp (A B : Point) (τ₀ τ₁ : ℝ) :
    lerp A B τ₁ - lerp A B τ₀ = (τ₁ - τ₀) • (B - A) := by
  apply Prod.ext <;> simp [lerp] <;> ring

/-- **Attachment transfers** between positions with the same point and the same sector. -/
theorem attach_of_sector {W W' : Polygon} {c : Set Point} {p p' : ℕ} {t t' : ℝ}
    (hpt : sidePt W' p' t' = sidePt W p t)
    (hsec : ∀ y, sideLeft W p t y → sideLeft W' p' t' y) (hp' : p' < W'.n) (ht0 : 0 ≤ t')
    (ht1 : t' < 1) (h : SideAttach W c p t) : SideAttach W' c p' t' := by
  obtain ⟨-, -, -, hmem, r, hr, hnear⟩ := h
  refine ⟨hp', ht0, ht1, hpt ▸ hmem, r, hr, fun y hy hne hd => hsec y (hnear y hy ?_ ?_)⟩
  · rwa [← hpt]
  · rwa [← hpt]

/-- The offsets of a sub-segment. -/
theorem offset_lerp_pair (A B : Point) (τ₀ τ₁ s δ : ℝ) :
    offset (lerp A B τ₀) (lerp A B τ₁) s δ = offset A B (τ₀ + s * (τ₁ - τ₀)) (δ * (τ₁ - τ₀)) := by
  apply Prod.ext <;> simp only [offset_fst, offset_snd, Chazelle.Geometry.lerp_fst,
    Chazelle.Geometry.lerp_snd] <;> ring

/-- **Facing transfers** when the offsets agree up to a positive scaling. -/
theorem faces_of_offset {M₁ M₂ : Model} {p₁ p₂ : ℕ} {t₁ t₂ c : ℝ} (hc : 0 < c)
    (hoff : ∀ δ, offset (M₁.wa p₁) (M₁.wb p₁) t₁ δ = offset (M₂.wa p₂) (M₂.wb p₂) t₂ (δ * c))
    {U V : Set Point} (hVU : V ⊆ U) (hV : M₂.Faces p₂ t₂ V) : M₁.Faces p₁ t₁ U := by
  have h := (Loc.tendsto_mul_const_nhdsGT hc).eventually hV
  filter_upwards [h] with δ hδ
  rw [hoff]; exact hVU hδ

end

end ExtG

end Chazelle.Core
