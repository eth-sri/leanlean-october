import RequestProject.OrderNormalizationNaturality
import RequestProject.Tac


bwd

namespace FiniteChains.Comb
universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]

/-- For an actual strict map, the normalized map is its genuine strict cellular chain map. -/
theorem normalizedStrictChain2_eq_strict (f : P → Q) hf
    c :
    normalizedStrictChain2 f hf.monotone c = chain2 (strictOrderCxMap f hf) c := by
  classical
  lin_ind c with c d hc hd => simp [map_add, hc, hd]
  | t n =>
    have h01 := hf t.2.1
    have h12 := hf t.2.2
    change normalizeOrdChain2 (Finsupp.mapDomain (orderCxMap f hf.monotone).onF
      (Finsupp.mapDomain (strictOrderIncl P).onF (Finsupp.single t n))) =
      Finsupp.mapDomain (strictOrderCxMap f hf).onF (Finsupp.single t n)
    simp [normalizeOrdTriangle, orderCxMap, strictOrderIncl, strictOrderCxMap, h01, h12]


/-- Actual strict maps commute with genuine normalization of arbitrary finite weak chains. -/
theorem normalizeOrdChain2_strict_map (f : P → Q) hf
    (c : OrdTri P →₀ ℤ) :
    normalizeOrdChain2 (chain2 (orderCxMap f hf.monotone) c) =
      chain2 (strictOrderCxMap f hf) (normalizeOrdChain2 c) := by
  rw [normalizeOrdChain2_map, normalizedStrictChain2_eq_strict]
