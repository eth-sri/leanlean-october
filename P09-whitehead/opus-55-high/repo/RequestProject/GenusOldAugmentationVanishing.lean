import RequestProject.GenusSpineCycleFaithfulness
import RequestProject.GenusOldCoordinateVanishing
import RequestProject.Tac


/-! Actual old-spine and total capped-cover augmentation vanishing, with all dependencies proved. -/
bwd

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

/-- The actual normalized full-cube comparison reflects zero on marked-spine cycles,
by the retained-cell retraction and faithful ordinary triangle coordinates. -/
theorem markedSpine_cycle_zero_of_normalized_full_image d
    (hd : Comb.bdry2 (markedSpineCx q) d = 0)
    (hz : normalizeOrdChain2 (chain2 (markedSpineToFullCube q) d) = 0) : d = 0 := by
  let c := chain2 (componentIncl _ _) d
  have hcycle : Comb.bdry2 _ c = 0 := by
    rwd [bdry2_chain2, hd, map_zero]
  have he : normalizedStrictChain2 _
      (genusSpineCellToFullCube_monotone q) c =
      normalizeOrdChain2 (chain2 (markedSpineToFullCube q) d) := by
    change normalizeOrdChain2 (Finsupp.mapDomain
        (orderCxMap _ (genusSpineCellToFullCube_monotone q)).onF
        (Finsupp.mapDomain (strictOrderIncl _).onF
          (Finsupp.mapDomain (componentIncl _ _).onF d))) =
      normalizeOrdChain2 (Finsupp.mapDomain (markedSpineToFullCube q).onF d)
    rwd [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
    rfl
  have hc := genusSpine_cycle_zero_of_normalized_full_image q c hcycle (he.trans hz)
  apply Finsupp.mapDomain_injective
    (componentIncl_injective_onF (X := genusSpineCx q) _)
  tauto

/-- Every actual capped-cover cycle has zero old-spine augmentation. -/
theorem cappedCoverCycle_old_augmentation_zero
    c (hc : Comb.bdry2 (cappedTreeCover q) c = 0) :
    ∃ d : (markedSpineCx q).F →₀ ℤ,
      Finsupp.mapDomain Sum.inl d = Finsupp.mapDomain Prod.snd c ∧ d = 0 := by
  obtain ⟨d, hd, hcycle, hz⟩ := cappedCoverCycle_old_normalized_image_zero q c hc
  exact ⟨d, hd, markedSpine_cycle_zero_of_normalized_full_image q d hcycle hz⟩

/-- The complete augmentation of every actual capped-cover two-cycle is zero. This
includes all old spine faces as well as the previously proved cap coefficients. -/
theorem cappedCoverCycle_total_augmentation_zero
    c (hc : Comb.bdry2 (cappedTreeCover q) c = 0) :
    Finsupp.mapDomain Prod.snd c = 0 := by
  obtain ⟨d, hd, rfl⟩ := cappedCoverCycle_old_augmentation_zero q c hc
  simp_all
