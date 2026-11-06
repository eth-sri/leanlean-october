module

public import RequestProject.RoseCoverBoundary

@[expose] public section

namespace FiniteChains.PresModel
open Comb
universe u
variable {α P : Type u} [PartialOrder P] (f : P → Rose α) (hf : IsPosetCover f)

/-- Actual incidence edges over the positive selected half of each rose generator. -/
def roseCoverGeneratorEdges : Set (StrictOrdEdge P) :=
  {e | ∃ i, (strictOrderCxMap f hf.strictMono).onE e = roseMidEdge i true}

/-- Restrict the actual finite chain to its selected generator incidences. -/
noncomputable def roseCoverGeneratorCoordinates :
    (StrictOrdEdge P →₀ ℤ) →ₗ[ℤ] (roseCoverGeneratorEdges f hf →₀ ℤ) :=
  Finsupp.lsubtypeDomain (roseCoverGeneratorEdges f hf)

@[simp] theorem roseCoverGeneratorCoordinates_apply (c : StrictOrdEdge P →₀ ℤ)
    (e : roseCoverGeneratorEdges f hf) : roseCoverGeneratorCoordinates f hf c e = c e.val := rfl

end FiniteChains.PresModel
