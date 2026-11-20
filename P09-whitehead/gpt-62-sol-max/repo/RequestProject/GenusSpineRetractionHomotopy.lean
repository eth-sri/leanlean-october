module

public import RequestProject.GenusSpineRetraction
public import RequestProject.TruncatedCubePi1
public import RequestProject.OrderTwoMapPrism

@[expose] public section

/-! The actual retained-cube retraction fixes spine two-cycles after normalization. -/

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

/-- On the actual two-dimensional surviving spine, the retained-cube retraction fixes
normalized two-cycles exactly because there are no nondegenerate three-flags. -/
theorem genusSpine_normalized_retraction_cycle (c : (orderCx (GenusSpineCell q)).F →₀ ℤ)
    (hc : Comb.bdry2 (orderCx (GenusSpineCell q)) c = 0) :
    normalizeOrdChain2
      (chain2 (orderCxMap (genusSpineRetraction q) (genusSpineRetraction_monotone q)) c) =
      normalizeOrdChain2 c := by
  let g := genusSpineRetraction q
  let y := ordMapPrism2 id g monotone_id (genusSpineRetraction_monotone q) (genusSpine_le_retraction q) c
  have hy : ordBoundary3 y = chain2 (orderCxMap g (genusSpineRetraction_monotone q)) c - c := by
    change ordBoundary3 y = _ - _
    rw [ordMapPrism_cycle id g monotone_id _ _ c hc]
    change _ - Finsupp.mapDomain id c = _
    rw [Finsupp.mapDomain_id] <;> rfl
  haveI := strictOrdTet_isEmpty_of_rank _ (genusSpineCellDimension_strictMono q)
    (genusSpineCell_dimension_le_two q)
  have h := congrArg normalizeOrdChain2 hy
  erw [normalizeOrdBoundary3_eq_zero, map_sub] at h
  exact sub_eq_zero.mp h.symm

end FiniteChains.Davis.Genus
