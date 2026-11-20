module

public import Chazelle.Core.FactsTie

/-!
# WP-C (BuildNF): walk-axiom facts for the region identification

Facts used to identify the regions of a submap with the labels of the stack pass
(`Chazelle.Core.NFBuildStack`):

* `WalkAx.separates_iff`: a chord separates two keys that are not its attachment keys iff exactly
  one of them lies in the arc from one attachment to the other;
* `WalkAx.not_touches_of_split`: a region faced strictly inside one arc of a chord `j` does not
  touch a chord `i ≠ j` attached strictly inside the other arc of `j`.
-/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sideInArc sidePt sideLeft ChordSystem freeIn regionsIn TouchesIn
  sideKey_inj sideLeft_edge sideInArc_swap)
open Chazelle.Jordan (offset convex_det_pos)
open Chazelle.Geometry (lerp point_ext lerp_mem_segment)

namespace WalkAx

variable {M : Model}

/-- **Separation by a chord in terms of one arc.** -/
theorem separates_iff (hM : WalkAx M) {c : Set Point} (hc : c ∈ M.Adm) {pa pb : ℕ} {ta tb : ℝ}
    (hA : SideAttach M.W c pa ta) (hB : SideAttach M.W c pb tb)
    (hAB : sidePt M.W pa ta ≠ sidePt M.W pb tb) {x x' : ℝ} (hxa : x ≠ pa + ta)
    (hxb : x ≠ pb + tb) (hx'a : x' ≠ pa + ta) (hx'b : x' ≠ pb + tb) :
    M.Separates c x x' ↔
      (sideInArc (pa + ta) (pb + tb) x ↔ ¬ sideInArc (pa + ta) (pb + tb) x') := by
  constructor
  · rintro ⟨pa', pb', ta', tb', hA', hB', hAB', hiff⟩
    obtain ⟨e, -, -, -, -, -, hoth⟩ := hM.attach_other_end hc hA
    have hBe := hoth pb tb hB (Ne.symm hAB)
    -- every attachment of `c` is `A` or `B`
    have hcase : ∀ (q : ℕ) (τ : ℝ), SideAttach M.W c q τ →
        (q = pa ∧ τ = ta) ∨ (q = pb ∧ τ = tb) := by
      intro q τ hQ
      by_cases h : sidePt M.W q τ = sidePt M.W pa ta
      · exact Or.inl (hM.attach_unique hc hQ hA h)
      · exact Or.inr (hM.attach_unique hc hQ hB (by rw [hoth q τ hQ h, hBe]))
    have hkab := key_ne_of_pt_ne hA hB hAB
    rcases hcase pa' ta' hA' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hcase pb' tb' hB' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hAB'
    · exact hiff
    · rw [sideInArc_swap (Ne.symm hkab) hxb hxa, sideInArc_swap (Ne.symm hkab) hx'b hx'a] at hiff
      tauto
    · exact absurd rfl hAB'
  · intro h
    exact ⟨pa, pb, ta, tb, hA, hB, hAB, h⟩

/-- **A region inside one arc of a chord does not touch a chord attached inside the other arc.** -/
theorem not_touches_of_split (hM : WalkAx M) {F : Set (Set Point)} (hF : F ⊆ M.Adm)
    (hfin : F.Finite) {i j : Set Point} (hi : i ∈ F) (hj : j ∈ F) (hij : i ≠ j) {pa pb : ℕ}
    {ta tb : ℝ} (hA : SideAttach M.W j pa ta) (hB : SideAttach M.W j pb tb)
    (hAB : sidePt M.W pa ta ≠ sidePt M.W pb tb) {U : Set Point} (hU : U ∈ M.regions F) {p : ℕ}
    (hp : p < M.W.n) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (hin : sideInArc (pa + ta) (pb + tb) (p + t))
    (hf : M.Faces p t U) {pc : ℕ} {tc : ℝ} (hC : SideAttach M.W i pc tc)
    (hout : sideInArc (pb + tb) (pa + ta) (pc + tc)) : ¬ TouchesIn M.D i U := by
  rintro ⟨z, ⟨hzi, hzD⟩, hzU⟩
  have hsys := hM.sys F hF hfin
  obtain ⟨K₁, K₂, hne, ⟨k₁, rfl⟩, ⟨k₂, rfl⟩, hK₁, hK₂⟩ := hM.split (hF hj) hA hB hAB
  have hUK := hM.region_subset_of_sector hj hU hp ht hf (hK₁ p hp t ht.1.le ht.2 hin)
  -- a point of `i ∩ D` in `K₂`, near its attachment `C`
  obtain ⟨r, hr, hsecr⟩ := hK₂ pc hC.1 tc hC.2.1 hC.2.2.1 hout
  obtain ⟨e, hev, -, hie, hopen, -⟩ := hM.attach_other_end (hF hi) hC
  obtain ⟨s, hs0, hs1, hdist, hleft⟩ := exists_left_on_chord hC hie hev hr
  set x := lerp (sidePt M.W pc tc) e s
  have hxi : x ∈ i ∩ M.D := ⟨by rw [hie]; exact lerp_mem_segment _ _ hs0.le hs1.le,
    hopen s ⟨hs0, hs1⟩⟩
  have hxK := hsecr _ (by rw [mem_ball]; exact hdist) hleft
  have hsub : i ∩ M.D ⊆ M.D \ j := fun y hy =>
    ⟨hy.2, fun hyj => hsys.inter_subset_compl hi hj hij ⟨hy.1, hyj⟩ hy.2⟩
  have hcon := (hsys.chord_inter_nonempty_isPreconnected hi).2.subset_connectedComponentIn
    hxi hsub
  have hzK : z ∈ connectedComponentIn (M.D \ j) k₂ := by
    rw [connectedComponentIn_eq hxK]; exact hcon ⟨hzi, hzD⟩
  have hopenK : IsOpen (connectedComponentIn (M.D \ j) k₂) :=
    (hM.isOpen.sdiff (hsys.isClosed_chord hj)).connectedComponentIn
  obtain ⟨u, huK, huU⟩ := mem_closure_iff.1 hzU _ hopenK hzK
  apply hne
  rw [connectedComponentIn_eq (hUK huU), connectedComponentIn_eq huK]

end WalkAx

end

end Chazelle.Core
