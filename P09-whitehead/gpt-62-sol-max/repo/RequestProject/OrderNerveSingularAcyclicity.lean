module

public import RequestProject.OrderNerveSmallHomotopyAll

@[expose] public section

namespace FiniteChains.Comb
open CategoryTheory TopologicalSingular SingularSubdivision
variable {P : Type} [PartialOrder P]

/-- Every positive-degree singular cycle has a homogeneous order-chain representative. -/
theorem orderNerveRealization_cycle_nerveRepresentative (n : ℕ)
    (c : Chain (orderNerveRealization P) (n + 1)) (hc : boundary n c = 0) :
    ∃ z : Nerve.Ch P, z ∈ Nerve.Inc P ∧ Nerve.lengthProjection (n + 2) z = z ∧
      Nerve.bdry z = 0 ∧ ∃ b : Chain (orderNerveRealization P) (n + 2),
        boundary (n + 1) b = c - orderNerveGradedRealize P (n + 1) z := by
  obtain ⟨d, hd, hz, a, ha⟩ := orderNerveRealization_exists_small_cycle P n c hc
  let d' : smallChains (orderNerveRealizationOpenStar P) (n + 1) := ⟨d, hd⟩
  have hd' : smallBoundary (orderNerveRealizationOpenStar P) n d' = 0 := Subtype.ext hz
  obtain ⟨b, hb⟩ := orderSmallSingularApproximation_homologous n d' hd'
  refine ⟨orderTightToNerve P (n + 1) d', orderTightToNerve_mem_inc _ _,
    orderTightToNerve_length _ _, ?_, b - a, ?_⟩
  · rw [orderTightToNerve_boundary, hd', map_zero]
  · aesop

end FiniteChains.Comb
