module

public import Chazelle.Core.RestoreNodeEnd

/-!
# WP-E, the search: the arrival offset of an end test

The test at the end `E` of a node chord (in the open stretch) in the direction of the other end
`O` arrives at the far position `F`.  Its offset `α' = off n g kF` from the stretch start is
nonnegative, and when it is in the open stretch it is the offset of `O` (`Stretch.arrive`).
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Set
open Chazelle.Chain (sidePt SideAttach sideLeft sideInArc)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
open Chazelle.Geometry (lerp)
open WalkEmbed (off off_nonneg off_key off_key' dOf dOf_lt add_dOf)

variable {M : Model} {Cα : Chain} {g g' L : ℕ}

/-- **The arrival offset** of the test at an end of a node chord. -/
theorem arrival_off (hS : Stretch M Cα g g' L) (hGα : WalkAx (chainModel Cα)) {c : Set Point}
    (hc : c ∈ (chainModel Cα).Adm) {pO : ℕ} {tO : ℝ}
    (hO : SideAttach (chainModel Cα).W c pO tO)
    {a : Point} (haC : a ∈ Cα.set) {σ L₀ : ℝ} (hσ : σ = 1 ∨ σ = -1) (hL₀ : 0 < L₀)
    (hceq : c = Chazelle.segment a (rayPt a σ L₀))
    (hoO : rayPt a σ L₀ = sidePt (chainModel Cα).W pO tO)
    (hkopen : ∀ s ∈ Ioo (0 : ℝ) 1, lerp a (rayPt a σ L₀) s ∈ Cα.dom)
    (hsetD : ∀ x ∈ Cα.set, x ∉ M.D) {T : ℝ} (hT : 0 < T)
    (hdom : ∀ s, 0 < s → s < T → rayPt a σ s ∈ M.D) {pF : ℕ} {tF : ℝ}
    (hfar : sidePt M.W pF tF = rayPt a σ T) (hFA : SideAttach M.W (chordOf a σ T) pF tF) :
    0 ≤ off M.W.n g (pF + tF) ∧
      (0 < off M.W.n g (pF + tF) → off M.W.n g (pF + tF) < L →
        off M.W.n g (pF + tF) = off (chainModel Cα).W.n g' (pO + tO)) := by
  have hg : (g : ℝ) < M.W.n := by exact_mod_cast hS.hg
  have hFA' := hFA
  obtain ⟨hpF, htF0, htF1, -⟩ := hFA'
  have hk0 : (0 : ℝ) ≤ pF + tF := by positivity
  refine ⟨off_nonneg hk0 hg, fun h0 hL => ?_⟩
  set d := dOf M.W.n g pF
  have he : off M.W.n g (pF + tF) = d + tF := off_key' hS.hg hpF htF0 htF1
  rw [he] at h0 hL ⊢
  have hdL : d < L := by
    have : (d : ℝ) < L := by linarith
    exact_mod_cast this
  have hdt : tF = 0 → 1 ≤ d := fun h => by
    rw [h, add_zero] at h0
    have : (0 : ℝ) < d := h0
    exact_mod_cast this
  have hpF' : pF = (g + d) % M.W.n := (add_dOf hS.hg hpF).symm
  rw [hpF'] at hfar
  obtain ⟨hpO, htO⟩ := hS.arrive hGα hc hO haC hσ hL₀ hceq hoO hkopen hsetD hT hdom hdL htF0
    htF1 hdt hfar (by rwa [← hpF'])
  have hg' : g' < (chainModel Cα).W.n := by rw [Stretch.nα]; have := hS.hgL; omega
  have hdα : d < (chainModel Cα).W.n := by rw [Stretch.nα]; have := hS.hgL; omega
  rw [hpO, htO, ← hS.mod' hdL.le, off_key hg' hdα htF0 htF1]

end

end Restore

end Chazelle.Core
