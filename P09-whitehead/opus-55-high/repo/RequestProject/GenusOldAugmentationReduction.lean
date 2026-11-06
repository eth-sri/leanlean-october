import RequestProject.GenusSurfaceCharacters
import RequestProject.Tac


/-! Reduction of capped-cover augmentation to actual old spine faces. -/
bwd

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

theorem exists_oldFaceChain_of_caps_zero (c : (cappedSpineCx q).F →₀ ℤ)
    (hc : ∀ x, c (.inr x) = 0) :
    ∃ d : (markedSpineCx q).F →₀ ℤ, Finsupp.mapDomain Sum.inl d = c := by
  refine ⟨c.comapDomain Sum.inl Sum.inl_injective.injOn, ?_⟩
  apply Finsupp.mapDomain_comapDomain _ Sum.inl_injective
  intro f hf
  obtain f | x := f
  · simp
  · exact False.elim ((Finsupp.mem_support_iff.mp hf) (hc x))

theorem controlledAugmentedChain2_old (d : (markedSpineCx q).F →₀ ℤ) :
    controlledAugmentedChain2 q (Finsupp.mapDomain Sum.inl d) =
      chain2 (markedSpineToFullCube q) d := by
  lin_ind d with c d hc hd => simp [Finsupp.mapDomain_add, map_add, hc, hd]
  | f n =>
      rwd [Finsupp.mapDomain_single, controlledAugmentedChain2,
        Finsupp.linearCombination_single]
      change n • Finsupp.single ((markedSpineToFullCube q).onF f) 1 =
        Finsupp.mapDomain (markedSpineToFullCube q).onF (Finsupp.single f n)
      simp

/-- Every actual capped-cover cycle augments entirely into old spine faces, whose
full-cube image is an actual ordinary three-boundary. -/
theorem cappedCoverCycle_old_augmentation c
    (hc : Comb.bdry2 (cappedTreeCover q) c = 0) :
    ∃ d : (markedSpineCx q).F →₀ ℤ,
      Finsupp.mapDomain Sum.inl d = Finsupp.mapDomain Prod.snd c ∧
      ∃ y,
        ordBoundary3 y = chain2 (markedSpineToFullCube q) d := by
  obtain ⟨d, hd⟩ := exists_oldFaceChain_of_caps_zero q _
    (cappedCoverCycle_cap_augmentation_zero q c hc)
  cases' controlledAugmentedCycle_boundary3 q c hc with y hy
  refine ⟨d, hd, y, ?_⟩
  rwd [← hd, controlledAugmentedChain2_old] at hy
  exact hy

theorem cappedCoverCycle_old_augmentation_cycle c
    (hc : Comb.bdry2 (cappedTreeCover q) c = 0) :
    ∃ d : (markedSpineCx q).F →₀ ℤ,
      Finsupp.mapDomain Sum.inl d = Finsupp.mapDomain Prod.snd c ∧
      Comb.bdry2 (markedSpineCx q) d = 0 ∧
      ∃ y,
        ordBoundary3 y = chain2 (markedSpineToFullCube q) d := by
  obtain ⟨d, hd, y, hy⟩ := cappedCoverCycle_old_augmentation q c hc
  have hp : Comb.bdry2 _ (Finsupp.mapDomain Prod.snd c) = 0 := by
    let f : Hom (cappedTreeCover q) (cappedSpineCx q) :=
      SpanningTree.treeCoverProj _ _ _
    change Comb.bdry2 _ (chain2 f c) = 0
    rwd [bdry2_chain2, hc, map_zero]
  rwd [← hd] at hp
  change Comb.bdry2 _ (chain2 (cappedSpineIncl q) d) = 0 at hp
  rwd [bdry2_chain2] at hp
  have hzero : Comb.bdry2 _ d = 0 := by
    convert hp using 1 <;>
      simp only [chain1, cappedSpineIncl, Finsupp.lmapDomain_apply, Finsupp.mapDomain_id]
  tauto
