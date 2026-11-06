import RequestProject.OrderNerveSmallHomotopyAll


namespace FiniteChains.Comb
open CategoryTheory TopologicalSingular SingularSubdivision
variable {P : Type} [PartialOrder P]

/-- Every positive-degree singular cycle has a homogeneous order-chain representative. -/
theorem orderNerveRealization_cycle_nerveRepresentative n
    c (hc : boundary n c = 0) :
    ∃ z, z ∈ Nerve.Inc P ∧ Nerve.lengthProjection (n + 2) z = z ∧
      Nerve.bdry z = 0 ∧ ∃ b : Chain (orderNerveRealization P) (n + 2),
        boundary (n + 1) b = c - orderNerveGradedRealize P (n + 1) z := by
  obtain ⟨d, hd, hz, a, ha⟩ := orderNerveRealization_exists_small_cycle P n c hc
  let d' : smallChains (orderNerveRealizationOpenStar P) (n + 1) := by tauto
  have hd' : smallBoundary _ n d' = 0 := Subtype.ext hz
  cases' orderSmallSingularApproximation_homologous n d' hd' with b hb
  refine ⟨orderSmallToNerve P _ d', orderSmallToNerve_mem_inc _ _,
    orderSmallToNerve_length _ _, ?_, b - a, ?_⟩
  · rw [orderSmallToNerve_boundary, hd', map_zero]
  aesop
