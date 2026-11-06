module

public import Chazelle.Golf

public import Chazelle.Core.DownPhaseHostData

/-!
# WP-M (X, part 15): every exit chord of a region is a chord edge of its host polygon

For a region `U` of a submap `F` (walk-axiom model) with at least two host keys, every exit chord
`c` of `U` (a chord of `F` touching `U`) joins two *consecutive* host keys of `U`
(`exit_chordGap`): the chord splits the walk into two sides, the region lies on one of them
(`host_side`), so no host key lies strictly inside the other side, and the two attachment keys of
`c` are consecutive.  In particular the chord is the segment between the two host points.
-/

namespace Chazelle.Core

namespace DownHost

@[expose] public section

open Set
open Chazelle.Chain (SideAttach sideInArc sidePt TouchesIn)

variable {M : Model} {F : Set (Set Point)} {U : Set Point}

/-- Two attachment keys `A ≠ B` of `U` with no host key strictly between them (cyclically) are
consecutive host keys. -/
theorem consecutive_of_empty (hM : WalkAx M) (hF : F ⊆ M.Adm) (hfin : F.Finite)
    (h2 : 2 ≤ nk M F U) {a b : ℝ} (ha : a ∈ hostKeys M F U) (hb : b ∈ hostKeys M F U)
    (hab : a ≠ b) (hnone : ∀ x ∈ hostKeys M F U, ¬ sideInArc a b x) :
    ∃ i, i < nk M F U ∧ hk M F U i = a ∧ hk M F U ((i + 1) % nk M F U) = b := by
  obtain ⟨i, hi, rfl⟩ := exists_hk hM hF hfin ha
  have hsi : (i + 1) % nk M F U < nk M F U := Nat.mod_lt _ (⋄)
  refine ⟨i, hi, rfl, ?_⟩
  exact cyc_first (hk_succ_ne hM hF hfin h2 hi) hab (hnone _ (hk_mem hM hF hfin hsi))
    (hk_gap hM hF hfin h2 hi hb)

/-- **Every exit chord joins two consecutive host keys**: a chord gap witnessed by the chord,
which is the segment between the two host points. -/
theorem exit_chordGap (hM : WalkAx M) (hF : F ⊆ M.Adm) (hfin : F.Finite)
    (hU : U ∈ M.regions F) (h2 : 2 ≤ nk M F U) {c : Set Point} (hc : c ∈ F)
    (ht : TouchesIn M.D c U) :
    ∃ i, i < nk M F U ∧ ∃ (p p' : ℕ) (t t' : ℝ), SideAttach M.W c p t ∧
      SideAttach M.W c p' t' ∧ hk M F U i = p + t ∧ hk M F U ((i + 1) % nk M F U) = p' + t' ∧
      sidePt M.W p t ≠ sidePt M.W p' t' ∧
      c = Chazelle.segment (sidePt M.W p t) (sidePt M.W p' t') := by
  obtain ⟨a, b, hab, -, -, -, ⟨⟨pa, ta, hA, hAa⟩, -⟩, ⟨⟨pb, tb, hB, hBb⟩, -⟩⟩ := hM.ends c (hF hc)
  have hAB : sidePt M.W pa ta ≠ sidePt M.W pb tb := by rw [hAa, hBb]; exact hab
  have hcA : (pa : ℝ) + ta ∈ hostKeys M F U := Or.inl ⟨c, hc, ht, pa, ta, hA, rfl⟩
  have hcB : (pb : ℝ) + tb ∈ hostKeys M F U := Or.inl ⟨c, hc, ht, pb, tb, hB, rfl⟩
  have hkne := WalkAx.key_ne_of_pt_ne hA hB hAB
  obtain ⟨K₁, K₂, hK12, ⟨k₁, rfl⟩, ⟨k₂, rfl⟩, hK₁, hK₂⟩ := hM.split (hF hc) hA hB hAB
  obtain ⟨u, hu⟩ := Chazelle.Chain.regionsIn_nonempty hU
  by_cases h1 : ∀ x ∈ hostKeys M F U, ¬ sideInArc ((pa : ℝ) + ta) (pb + tb) x
  · obtain ⟨i, hi, e1, e2⟩ := consecutive_of_empty hM hF hfin h2 hcA hcB hkne h1
    exact ⟨i, hi, pa, pb, ta, tb, hA, hB, e1, e2, hAB, (hM.attach_seg (hF hc) hA hB hAB).1⟩
  · push Not at h1
    obtain ⟨x, hx, hxin⟩ := h1
    have hU₁ := host_side hM hF hfin hU hc hA hB hAB hK₁ hx hxin
    have h1' : ∀ y ∈ hostKeys M F U, ¬ sideInArc ((pb : ℝ) + tb) (pa + ta) y := by
      intro y hy hyin
      have hU₂ := host_side hM hF hfin hU hc hB hA (Ne.symm hAB) hK₂ hy hyin
      apply hK12
      Ξ connectedComponentIn_eq (hU₁ hu), connectedComponentIn_eq (hU₂ hu)
    obtain ⟨i, hi, e1, e2⟩ := consecutive_of_empty hM hF hfin h2 hcB hcA (Ne.symm hkne) h1'
    exact ⟨i, hi, pb, pa, tb, ta, hB, hA, e1, e2, Ne.symm hAB,
      (hM.attach_seg (hF hc) hB hA (Ne.symm hAB)).1⟩

end

end DownHost

end Chazelle.Core
