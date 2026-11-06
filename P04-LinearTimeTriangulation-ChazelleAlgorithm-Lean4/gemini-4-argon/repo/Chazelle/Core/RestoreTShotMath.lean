module

public import Chazelle.Core.RestoreShoot
public import Chazelle.Core.RestoreHoles
public import Chazelle.Core.RestoreTNear
public import Chazelle.Core.ShotListTop

/-!
# WP-E, the candidate test: the shot is the first exit

The shot of the candidate test returns the first hit of the ray on a set `A` between the arc
points outside the holes (`loSet`) and all arc points (`hiSet`).  When the ray starts in the
region `U` and the arc array lists every arc of `U`:

* `exit_lo`: the ray leaves the domain first at a point of `loSet` (local shooting, and the
  holes are near the origin, so they never contain the exit point: `no_common_edge`);
* `firstHit_exit`: the first hit on `A` is that exit;
* `not_noHit`: if the ray leaves the domain at all, the shot hits.
* `arrival_of_attach`: a position at which the chord is attached at its far end is an arrival
  position of the ray; `attach_far_simple`: on a simple walk the proper position of the far end is
  that position.
* `param_code`, `pos_code`: a position at the height of the vertex `h` of `Q` has the parameter
  and point of the position with the same edge and height code `h + 1` (the encoding of chord
  records).
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Set Filter Topology
open Chazelle.Chain (sidePt SideAttach sideLeft)
open Chazelle.Visibility (rayPt)
open ShotList

variable {M : Model}

/-- **The arc points are off the domain.** -/
theorem hiSet_off (hGM : GoodModel M) (Q : Polygon) (m : ℕ → ℕ) (B K : ℕ) :
    hiSet M Q m B K ⊆ (M.D)ᶜ := by
  intro x hx
  simp only [hiSet, mem_iUnion] at hx
  obtain ⟨j, -, p, t, hp, h0, h1, -, rfl⟩ := hx
  exact (walkAx_of_goodModel hGM).trace p hp t h0 h1

/-- **The exit point is an arc point outside the holes.** -/
theorem exit_lo (hGM : GoodModel M) {Q : Polygon} {F : Set (Set Point)}
    (hFam : M.ChordFamily Q F) {U : Set Point} (hU : U ∈ M.regions F) {z : Point} {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hzD : z ∉ M.D) (hini : ∀ᶠ t in 𝓝[>] (0 : ℝ), rayPt z σ t ∈ U)
    (htop : ∀ C : Chain, M = chainModel C → z.2 ≤ C.top.2) {m : ℕ → ℕ} {B K : ℕ}
    {hs : List (WPos × WPos)}
    (harr : ∀ a b, M.IsArc F U a b →
      ∃ j < K, M.key Q (ShotList.arcAt m B j).1 = a ∧ M.key Q (ShotList.arcAt m B j).2 = b)
    (hnear : Near M Q hs z) {t₁ : ℝ} (ht₁ : 0 < t₁) (hout : rayPt z σ t₁ ∉ M.D) :
    ∃ T, 0 < T ∧ T ≤ t₁ ∧ rayPt z σ T ∉ M.D ∧ (∀ t, 0 < t → t < T → rayPt z σ t ∈ U) ∧
      chordOf z σ T ∈ M.Adm ∧
      (∃ p t, SideAttach M.W (chordOf z σ T) p t ∧ sidePt M.W p t = rayPt z σ T) ∧
      rayPt z σ T ∈ loSet M Q m B K hs := by
  obtain ⟨T, hT, hTt, hTD, hdomU, hadm, hatt, a, b, harc, hmem⟩ :=
    local_exit hGM hFam hU hσ hzD hini ht₁ hout htop
  refine ⟨T, hT, hTt, hTD, hdomU, hadm, hatt, ?_⟩
  obtain ⟨p, τ, hp, h0, h1, hk, hx⟩ := hmem
  obtain ⟨j, hj, hja, hjb⟩ := harr a b harc
  refine ⟨p, τ, hp, h0, h1, ⟨j, hj, by rwa [hja, hjb]⟩, fun g hg hin => ?_, hx⟩
  obtain ⟨p', hp', ⟨s₁, a1, a2, e1⟩, s₂, b1, b2, e2⟩ := hnear g hg p τ hp h0 h1 hin
  have hUfree : U ⊆ Chazelle.Chain.freeIn M.D F := Chazelle.Chain.regionsIn_subset hU
  have hdom : ∀ t, 0 < t → t < T → rayPt z σ t ∈ M.D := fun t h1 h2 => (hUfree (hdomU t h1 h2)).1
  exact no_common_edge (walkAx_of_goodModel hGM) hσ hT hdom hp' a1 a2 b1 b2 e1
    (by rw [e2]; exact hx.symm)

/-- **The first hit of the shot is the first exit of the ray.** -/
theorem firstHit_exit (hGM : GoodModel M) {Q : Polygon} {F : Set (Set Point)}
    (hFam : M.ChordFamily Q F) {U : Set Point} (hU : U ∈ M.regions F) {z : Point} {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hzD : z ∉ M.D) (hini : ∀ᶠ t in 𝓝[>] (0 : ℝ), rayPt z σ t ∈ U)
    (htop : ∀ C : Chain, M = chainModel C → z.2 ≤ C.top.2) {m : ℕ → ℕ} {B K : ℕ}
    {hs : List (WPos × WPos)}
    (harr : ∀ a b, M.IsArc F U a b →
      ∃ j < K, M.key Q (ShotList.arcAt m B j).1 = a ∧ M.key Q (ShotList.arcAt m B j).2 = b)
    (hnear : Near M Q hs z) {A : Set Point} (hlo : loSet M Q m B K hs ⊆ A)
    (hhi : A ⊆ hiSet M Q m B K) {t : ℝ} (hfh : FirstHit A z σ t) :
    rayPt z σ t ∉ M.D ∧ (∀ s, 0 < s → s < t → rayPt z σ s ∈ U) ∧ chordOf z σ t ∈ M.Adm ∧
      (∃ p t', SideAttach M.W (chordOf z σ t) p t' ∧ sidePt M.W p t' = rayPt z σ t) := by
  have hout : rayPt z σ t ∉ M.D := hiSet_off hGM Q m B K (hhi hfh.2.1)
  obtain ⟨T, hT, hTt, hTD, hdomU, hadm, hatt, hlo'⟩ :=
    exit_lo hGM hFam hU hσ hzD hini htop harr hnear hfh.1 hout
  have hTe : T = t := by
    rcases hTt.lt_or_eq with h | h
    · exact absurd (hlo hlo') (hfh.2.2 T hT h)
    · exact h
  subst hTe
  exact ⟨hTD, hdomU, hadm, hatt⟩

/-- **The shot hits** when the ray leaves the domain. -/
theorem not_noHit (hGM : GoodModel M) {Q : Polygon} {F : Set (Set Point)}
    (hFam : M.ChordFamily Q F) {U : Set Point} (hU : U ∈ M.regions F) {z : Point} {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hzD : z ∉ M.D) (hini : ∀ᶠ t in 𝓝[>] (0 : ℝ), rayPt z σ t ∈ U)
    (htop : ∀ C : Chain, M = chainModel C → z.2 ≤ C.top.2) {m : ℕ → ℕ} {B K : ℕ}
    {hs : List (WPos × WPos)}
    (harr : ∀ a b, M.IsArc F U a b →
      ∃ j < K, M.key Q (ShotList.arcAt m B j).1 = a ∧ M.key Q (ShotList.arcAt m B j).2 = b)
    (hnear : Near M Q hs z) {A : Set Point} (hlo : loSet M Q m B K hs ⊆ A) {t₁ : ℝ}
    (ht₁ : 0 < t₁) (hout : rayPt z σ t₁ ∉ M.D) : ¬ NoHit A z σ := by
  intro hno
  obtain ⟨T, hT, -, -, -, -, -, hlo'⟩ := exit_lo hGM hFam hU hσ hzD hini htop harr hnear ht₁ hout
  exact hno T hT (hlo hlo')


/-! ## The far end -/

/-- **An attachment at the far end is an arrival position** of the ray. -/
theorem arrival_of_attach {W : Polygon} {z : Point} {σ T : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hT : 0 < T) {p : ℕ} {t : ℝ} (hA : SideAttach W (chordOf z σ T) p t)
    (hw : sidePt W p t = rayPt z σ T) : Sweep.Arrival W (rayPt z σ T) σ p t := by
  obtain ⟨hp, h0, h1, -, r, hr, hsec⟩ := hA
  refine ⟨hp, h0, h1, hw, ?_⟩
  have hσ' : -σ = 1 ∨ -σ = -1 := by rcases hσ with rfl | rfl <;> norm_num
  set s := min (r / 2) (T / 2)
  have hs : 0 < s := lt_min (half_pos hr) (half_pos hT)
  have hsr : s ≤ r / 2 := min_le_left _ _
  have hsT : s ≤ T / 2 := min_le_right _ _
  have hmem : rayPt (rayPt z σ T) (-σ) s ∈ chordOf z σ T := by
    rw [rayPt_back]; exact (mem_chordOf hσ hT.le).2 ⟨T - s, by linarith, by linarith, rfl⟩
  have hd : dist (rayPt (rayPt z σ T) (-σ) s) (rayPt z σ T) = s := Sweep.dist_rayPt _ hσ' hs.le
  have hne : rayPt (rayPt z σ T) (-σ) s ≠ sidePt W p t := by
    rw [hw]; intro h; rw [h, dist_self] at hd; linarith
  have hsl := hsec _ hmem hne (by rw [hw, hd]; linarith)
  rw [← hw] at hsl ⊢
  exact (Sweep.sideLeft_rayPt_iff W p t (-σ) one_pos hs).2 hsl

/-- **On a simple walk**, the chord is attached at the proper position of its far end. -/
theorem attach_far_simple {W : Polygon} (hW : W.Simple) {d : Set Point} {w : Point} {p p' : ℕ}
    {t t' : ℝ} (hA : SideAttach W d p t) (hw : sidePt W p t = w) (hp' : p' < W.n) (h0 : 0 ≤ t')
    (h1 : t' < 1) (hw' : sidePt W p' t' = w) : SideAttach W d p' t' := by
  obtain ⟨rfl, rfl⟩ := FactsInterior.pos_unique hW hA.1 hp' hA.2.1 hA.2.2.1 h0 h1 (hw.trans hw'.symm)
  exact hA

/-! ## The height code of a chord record -/

/-- **The parameter of a position from the height vertex.** -/
theorem param_code (M : Model) (Q : Polygon) {y : WPos} {h : ℕ}
    (hy : (M.pos Q y).2 = (Q.vtx h).2) : M.param Q ⟨y.edge, h + 1⟩ = M.param Q y := by
  have hy' : (M.wa y.edge).2 + M.param Q y * ((M.wb y.edge).2 - (M.wa y.edge).2) = (Q.vtx h).2 := by
    rw [← hy]; unfold Model.pos; simp [Geometry.lerp]
  show (if (M.wa y.edge).2 = (M.wb y.edge).2 then 0
    else ((Q.vtx h).2 - (M.wa y.edge).2) / ((M.wb y.edge).2 - (M.wa y.edge).2)) = M.param Q y
  split_ifs with hz
  · obtain ⟨e, g⟩ := y
    cases g with
    | zero => rfl
    | succ g =>
      show 0 = (if (M.wa e).2 = (M.wb e).2 then 0 else _)
      rw [ite_eq_left hz]
  · rw [div_eq_iff (sub_ne_zero.2 (Ne.symm hz))]
    linarith

/-- **The point of a position from the height vertex.** -/
theorem pos_code (M : Model) (Q : Polygon) {y : WPos} {h : ℕ}
    (hy : (M.pos Q y).2 = (Q.vtx h).2) : M.pos Q ⟨y.edge, h + 1⟩ = M.pos Q y := by
  unfold Model.pos
  rw [param_code M Q hy]

end

end Restore

end Chazelle.Core
