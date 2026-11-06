module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.DownPhaseBoxTransfer

/-!
# WP-M (B3′, part 8): dropping the wall-to-wall chords

Finding M6 (option 1): before the box transport, the chords of a chain normal form with both
ends on the side walls of the box (walk edges `1` and `3`) are dropped (`dropWalls`).

* The remaining chord list is still valid (`chordTriplesOK_dropWalls`).
* Every remaining chord has an end on a walk edge other than a side wall; such an end lies on the
  chain, or at the top vertex (on the slit, since augmented chords are not above the top), so its
  height is in the fixed band of the box stretch of any twin chain (`inBand_dropWalls`).
-/

namespace Chazelle.Core

namespace BoxT

@[expose] public section

open Set List Chazelle.Chain Chazelle.Visibility BuildNF
open BuildRegions (crec famOf)

/-- A chord triple is **wall-to-wall**: both ends on the side walls (walk edges `1`, `3`) of the
box. -/
def WallRec (x : ℕ × ℕ × ℕ) : Prop := (x.2.1 = 1 ∨ x.2.1 = 3) ∧ (x.2.2 = 1 ∨ x.2.2 = 3)

instance (x : ℕ × ℕ × ℕ) : Decidable (WallRec x) := by unfold WallRec; infer_instance

/-- The chord list without its wall-to-wall chords. -/
def dropWalls (L : List (ℕ × ℕ × ℕ)) : List (ℕ × ℕ × ℕ) := L.filter fun x => !decide (WallRec x)

theorem mem_dropWalls {L : List (ℕ × ℕ × ℕ)} {x : ℕ × ℕ × ℕ} :
    x ∈ dropWalls L ↔ x ∈ L ∧ ¬ WallRec x := by
  simp [dropWalls]

section
variable {M : Model} {Q : Polygon}
/-- A sublist of a valid chord list is valid. -/
theorem chordTriplesOK_sublist {L L' : List (ℕ × ℕ × ℕ)}
    (hs : L' <+ L) (hL : ChordTriplesOK M Q L) : ChordTriplesOK M Q L' := by
  obtain ⟨⟨hfin, hadm, hht⟩, hnd, hatt, hh⟩ := hL
  have sub : {c | ∃ x ∈ L', c = (recOf x).toSet M Q} ⊆ {c | ∃ x ∈ L, c = (recOf x).toSet M Q} := by
    ram_grind
  exact ⟨⟨hfin.subset sub, sub.trans hadm, fun c hc => hht c (sub hc)⟩,
    hnd.sublist (hs.map _), fun x hx => hatt x (hs.subset hx), fun x hx => hh x (hs.subset hx)⟩

theorem chordTriplesOK_dropWalls {L : List (ℕ × ℕ × ℕ)}
    (hL : ChordTriplesOK M Q L) : ChordTriplesOK M Q (dropWalls L) :=
  chordTriplesOK_sublist filter_sublist hL


end

variable {C C' : Chain}

namespace Twin

variable (h : Twin C C')
include h

/-- **Heights at walk points off the side walls.**  A point of a walk edge other than a side wall
at a height `y` of the open box not above the top is in the fixed band. -/
theorem band_of_edge {e : ℕ} (he : e < (C.sideWalk C.sideBeta).n) (h1 : e ≠ 1) (h3 : e ≠ 3)
    {t : ℝ} (ht : 0 ≤ t ∧ t < 1) {y : ℝ} (hpy : (sidePt (C.sideWalk C.sideBeta) e t).2 = y)
    (hyt : y ≤ C.top.2) (hyR : |y| < C.radius) : |y| ≤ bnd C C' - 1 / 2 := by
  have hn : (C.sideWalk C.sideBeta).n = 2 * C.m + 7 := C.sideWalk_n _
  have htop := h.abs_le_of_mem C.top_mem_set
  have hbR : bnd C C' < C.radius := bnd_lt
  have htR : C.top.2 < C.radius := by grind
  have hR := abs_lt.1 hyR
  unfold sidePt at hpy
  rw [Geometry.lerp_snd] at hpy
  rcases Nat.lt_or_ge e 6 with h6 | h6
  · have hmod : (e + 1) % (C.sideWalk C.sideBeta).n = e + 1 := by
      rw [hn]; exact Nat.mod_eq_of_lt (by omega)
    rw [hmod] at hpy
    interval_cases e
    · rw [C.sideWalk_vtx_zero, C.sideWalk_vtx_one] at hpy
      grind [Chain.slitTop]
    · omega
    · rw [C.sideWalk_vtx_two, C.sideWalk_vtx_three] at hpy
      linarith
    · omega
    · rw [C.sideWalk_vtx_four, C.sideWalk_vtx_five] at hpy
      grind [Chain.slitTop]
    · rw [C.sideWalk_vtx_five, C.sideWalk_vtx_six] at hpy
      simp only [Chain.slitTop] at hpy
      nlinarith
  · rcases Nat.lt_or_ge e (2 * C.m + 6) with h' | h'
    · have hmod : (e + 1) % (C.sideWalk C.sideBeta).n = e + 1 := by
        simp_all +arith
      rw [hmod] at hpy
      have hu := h.abs_le_of_mem (tour_mem C h6 (by omega))
      have hv := h.abs_le_of_mem (tour_mem C (by omega : 6 ≤ e + 1) (by omega))
      have hb := abs_lerp_le hu hv ht.1 ht.2.le
      simp_all
    · have he' : e = 2 * C.m + 6 := by omega
      subst he'
      rw [C.sideWalk_vtx_wrap, walk_last] at hpy
      simp only [Chain.slitTop] at hpy
      have hy : y = C.top.2 := by nlinarith
      simp_all

section
variable {Q : Polygon} {L : List (ℕ × ℕ × ℕ)} (hL : ChordTriplesOK (chainModel C) Q L)
include hL
/-- The height of a chord of a valid chord list of a chain, at an end off the side walls, is in
the fixed band. -/
theorem band_of_end
    {x : ℕ × ℕ × ℕ} (hx : x ∈ L) {w : WPos} (hw : w = (recOf x).lpos ∨ w = (recOf x).rpos)
    (h1 : w.edge ≠ 1) (h3 : w.edge ≠ 3) : |(Q.vtx x.1).2| ≤ bnd C C' - 1 / 2 := by
  obtain ⟨hl, hr⟩ := hL.2.2.1 x hx
  have hA : SideAttach (C.sideWalk C.sideBeta) ((recOf x).toSet (chainModel C) Q) w.edge
      ((chainModel C).param Q w) := by aesop
  obtain ⟨hp, ht0, ht1, hmem, -⟩ := hA
  obtain ⟨y', a, b, hh, hyt, e⟩ := hL.1.2.1 ⟨x, hx, rfl⟩
  have hmem' := hmem
  rw [e] at hmem'
  have hy1 : (sidePt (C.sideWalk C.sideBeta) w.edge ((chainModel C).param Q w)).2 =
      (Q.vtx x.1).2 := hmem.1
  have hy2 : (sidePt (C.sideWalk C.sideBeta) w.edge ((chainModel C).param Q w)).2 = y' := hmem'.1
  have hyy : (Q.vtx x.1).2 = y' := hy1.symm.trans hy2
  have hR : |y'| < C.radius := by
    have hm := hh.open_mem ((a + b) / 2) (by linarith [hh.lt]) (by linarith [hh.lt])
    exact (C.dom_subset_box hm).2
  rw [hyy]
  exact h.band_of_edge hp h1 h3 ⟨ht0, ht1⟩ hy2 hyt hR

/-- **The chords off the side walls are in the band.** -/
theorem inBand_dropWalls : InBand C C' Q (dropWalls L) := by
  intro x hx
  obtain ⟨hx, hw⟩ := mem_dropWalls.1 hx
  have hb : bnd C C' - 1 / 2 < bnd C C' := by linarith
  unfold WallRec at hw
  by_cases hl : x.2.1 = 1 ∨ x.2.1 = 3
  · have hr : ¬ (x.2.2 = 1 ∨ x.2.2 = 3) := fun hr => hw ⟨hl, hr⟩
    rw [not_or] at hr
    exact lt_of_le_of_lt (h.band_of_end hL hx (Or.inr rfl) hr.1 hr.2) hb
  · rw [not_or] at hl
    exact lt_of_le_of_lt (h.band_of_end hL hx (Or.inl rfl) hl.1 hl.2) hb


end

end Twin

end

end BoxT

end Chazelle.Core
