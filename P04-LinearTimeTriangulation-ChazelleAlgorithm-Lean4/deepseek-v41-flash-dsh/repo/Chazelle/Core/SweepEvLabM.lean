module

public import Chazelle.Golf

public import Chazelle.Core.SweepEvCand3
public import Chazelle.Core.SweepMachine17
public import Chazelle.Core.SweepMachine9

/-!
# The sweep (WP-D), stage 3: the labels of a found chord (mathematics)

`evSideLab_fused`: the chord of `C` seen from a valid origin `a` (an end of the chord `k` of `N₂`,
on `C₂`, not the shared vertex, not the top of `C₂`) along the chord has the side labels
`{up k, dn k}` (`EvSideLab`), by `sideLabel_sub`.
-/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology
open Chazelle.Chain (SideAttach sidePt)
open Chazelle.Visibility (rayPt)
open Chazelle.Merge (FreeAt)
open WalkEmbed

namespace Sweep

variable {J : Merge.Junction}

/-- **The regions above and below a chord record** are on its sides. -/
theorem sideOf_rec {M : Model} {Q : Polygon} {N : NF} (hN : IsNF M Q N) {k : ℕ}
    (hk : k < N.nChords) :
    SideOf M 1 ((N.chord k).toSet M Q) (regOf M Q N (N.chord k).up) ∧
      SideOf M (-1) ((N.chord k).toSet M Q) (regOf M Q N (N.chord k).dn) := by
  obtain ⟨-, hsides, -⟩ := regOf_spec hN
  obtain ⟨-, -, h⟩ := hsides k hk
  refine ⟨fun z hz hzD => ?_, fun z hz hzD => ?_⟩
  · obtain ⟨ε₀, hε₀, hε⟩ := h z hz hzD
    filter_upwards [Ioo_mem_nhdsGT hε₀] with δ hδ
    simpa using (hε δ hδ.1 hδ.2).1
  · obtain ⟨ε₀, hε₀, hε⟩ := h z hz hzD
    filter_upwards [Ioo_mem_nhdsGT hε₀] with δ hδ
    simpa [sub_eq_add_neg] using (hε δ hδ.1 hδ.2).2

/-- **The side labels of a found chord.** -/
theorem evSideLab_fused (hP : J.P.Simple) {Q : Polygon} {N : NF}
    (hN : IsNF (chainModel J.right) Q N)
    (hF : (chainModel J.whole).ChordFamily Q (F₂plus J (N.F (chainModel J.right) Q)))
    {k : ℕ} (hk : k < N.nChords) {a : Point} {σ : ℝ}
    (ha : (σ = 1 ∧ a = Merge.lend ((N.chord k).toSet (chainModel J.right) Q)) ∨
      (σ = -1 ∧ a = Merge.rend ((N.chord k).toSet (chainModel J.right) Q)))
    (haR : a ∈ J.right.set) (hav : a ≠ J.shared) (hat : a ≠ J.right.top)
    (hfree : FreeAt J.whole a σ) :
    EvSideLab J (N.F (chainModel J.right) Q)
      (labSet J Q N 2 (N.chord k).up (N.chord k).dn 0 0) (Merge.shoot J.whole a σ) := by
  set S₂ := N.F (chainModel J.right) Q with hS₂d
  set ch := (N.chord k).toSet (chainModel J.right) Q with hch
  have hS₂ : (chainModel J.right).ChordFamily Q S₂ := hN.1
  have hS₂a : S₂ ⊆ Merge.augChords J.right := hS₂.2.1
  have hS₂f : S₂.Finite := hS₂.1
  have hchm : ch ∈ S₂ := by
    refine ⟨N.chord k, ?_, rfl⟩
    unfold NF.chord
    Ξ NFLoc.getD_of_lt _ hk
    exact List.getElem_mem _
  have hf : Merge.shoot J.whole a σ ∈ F₂plus J S₂ := shoot_end_mem hchm ha hfree
  have hfc : Merge.shoot J.whole a σ ⊆ ch := shoot_sub_end hS₂a hchm ha
  have hM : WalkAx (chainModel J.whole) := FactsChain.walkAx J.whole hP
  have hadm := F₂plus_subset J hS₂a hf
  have haD : a ∉ J.whole.dom := fun hd =>
    J.whole.not_mem_set_of_mem_dom hd (J.right_set_subset haR)
  obtain ⟨pB, tB, hB, hpt⟩ := endpoint_attach hM hadm (origin_mem J) haD
  have hoff := off_right_pt J hP hS₂a hS₂f hB.1 hB.2.1 hB.2.2.1 (by rw [hpt]; exact haR)
    (by rw [hpt]; exact hav)
  have hns : tB = 0 → sidePt (chainModel J.whole).W pB tB ≠ J.right.top := fun _ => by
    rw [hpt]; exact hat
  obtain ⟨hup, hdn⟩ := sideOf_rec hN hk
  obtain ⟨hreg, -⟩ := regOf_spec hN
  obtain ⟨hup', hdn', -⟩ := (regOf_spec hN).2.1 k hk
  intro G hG ρ hρ hS
  rcases hρ with rfl | rfl
  · refine ⟨regOf (chainModel J.right) Q N (N.chord k).up, Or.inl ⟨(N.chord k).up,
      Or.inl ⟨⊛, rfl⟩, rfl⟩, hreg.1 _ hup', ?_⟩
    exact sideLabel_sub J hP hS₂ hF hchm hf hfc hB hoff.1 hoff.2 hns (Or.inl rfl) (hreg.1 _ hup')
      hup G hG hS
  · refine ⟨regOf (chainModel J.right) Q N (N.chord k).dn, Or.inl ⟨(N.chord k).dn,
      Or.inr (Or.inl ⟨⊛, rfl⟩), rfl⟩, hreg.1 _ hdn', ?_⟩
    exact sideLabel_sub J hP hS₂ hF hchm hf hfc hB hoff.1 hoff.2 hns (Or.inr rfl) (hreg.1 _ hdn')
      hdn G hG hS

end Sweep

end

end Chazelle.Core
