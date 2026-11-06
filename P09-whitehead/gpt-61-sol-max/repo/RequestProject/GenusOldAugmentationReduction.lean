import Mathlib.Tactic

import RequestProject.GenusSurfaceCharacters

/-! Reduction of capped-cover augmentation to actual old spine faces. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

theorem exists_oldFaceChain_of_caps_zero (c : (cappedSpineCx q).F →₀ ℤ)
    (hc : ∀ x : Fin q × Bool, c (.inr x) = 0) :
    ∃ d : (markedSpineCx q).F →₀ ℤ, Finsupp.mapDomain Sum.inl d = c := by
  refine ⟨c.comapDomain Sum.inl Sum.inl_injective.injOn, ?_⟩
  apply Finsupp.mapDomain_comapDomain _ Sum.inl_injective
  intro f hf
  obtain f | x := f
  · exact ⟨f, rfl⟩
  · exact False.elim ((Finsupp.mem_support_iff.mp hf) (hc x))

theorem controlledAugmentedChain2_old (d : (markedSpineCx q).F →₀ ℤ) :
    controlledAugmentedChain2 q (Finsupp.mapDomain Sum.inl d) =
      chain2 (markedSpineToFullCube q) d := by
  induction d using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => classical simp_all [Finsupp.mapDomain_add, map_add]
  | single f n =>
      rw  [Finsupp.mapDomain_single, controlledAugmentedChain2,
        Finsupp.linearCombination_single]
      change n • Finsupp.single ((markedSpineToFullCube q).onF f) 1 =
        Finsupp.mapDomain (markedSpineToFullCube q).onF (Finsupp.single f n)
      simp

variable (c : (cappedTreeCover q).F →₀ ℤ)
variable (hc : Comb.bdry2 (cappedTreeCover q) c = 0)
include hc in
/-- Every actual capped-cover cycle augments entirely into old spine faces, whose
full-cube image is an actual ordinary three-boundary. -/
theorem cappedCoverCycle_old_augmentation 
     :
    ∃ d : (markedSpineCx q).F →₀ ℤ,
      Finsupp.mapDomain Sum.inl d = Finsupp.mapDomain Prod.snd c ∧
      ∃ y : OrdTet (QCube (cmpRel (GenusVertex q))) →₀ ℤ,
        ordBoundary3 y = chain2 (markedSpineToFullCube q) d := by
  obtain ⟨d, hd⟩ := exists_oldFaceChain_of_caps_zero q (Finsupp.mapDomain Prod.snd c)
    (cappedCoverCycle_cap_augmentation_zero q c hc)
  obtain ⟨y, hy⟩ := controlledAugmentedCycle_boundary3 q c hc
  refine ⟨d, hd, y, ?_⟩
  rw  [← hd, controlledAugmentedChain2_old] at hy
  exact hy

include hc in
theorem cappedCoverCycle_old_augmentation_cycle 
     :
    ∃ d : (markedSpineCx q).F →₀ ℤ,
      Finsupp.mapDomain Sum.inl d = Finsupp.mapDomain Prod.snd c ∧
      Comb.bdry2 (markedSpineCx q) d = 0 ∧
      ∃ y : OrdTet (QCube (cmpRel (GenusVertex q))) →₀ ℤ,
        ordBoundary3 y = chain2 (markedSpineToFullCube q) d := by
  obtain ⟨d, hd, y, hy⟩ := cappedCoverCycle_old_augmentation q c hc
  have hp : Comb.bdry2 (cappedSpineCx q) (Finsupp.mapDomain Prod.snd c) = 0 := by
    let f : Hom (cappedTreeCover q) (cappedSpineCx q) :=
      SpanningTree.treeCoverProj (cappedSpineTree q) (relSub (cappedSpinePresentation q)) _
    change Comb.bdry2 (cappedSpineCx q) (chain2 f c) = 0
    rw  [bdry2_chain2, hc, map_zero]
  rw  [← hd] at hp
  change Comb.bdry2 (cappedSpineCx q) (chain2 (cappedSpineIncl q) d) = 0 at hp
  rw  [bdry2_chain2] at hp
  have hzero : Comb.bdry2 (markedSpineCx q) d = 0 := by
    aesop (add simp [chain1, cappedSpineIncl])
  exact ⟨d, hd, hzero, y, hy⟩

end FiniteChains.Davis.Genus
