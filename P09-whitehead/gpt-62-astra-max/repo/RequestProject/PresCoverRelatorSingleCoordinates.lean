module

public import RequestProject.PresCoverRelatorNaturality

@[expose] public section

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J P : Type u} [PartialOrder P] (w : J → List (α × Bool))
  (f : P → PresPos w) (hf : IsPosetCover f) (hpos : ∀ j, 0 < (w j).length)

/-- An actual single coordinate triangle has exactly its single lifted-apex coefficient. -/
theorem presCoverRelatorChain_single_triangle (p : PresCoverRelator w f) (n : ℤ) :
    presCoverRelatorChain w f hf hpos
      (Finsupp.single (presCoverRelatorTriangle w f hf hpos p) n) = Finsupp.single p n := by
  apply Finsupp.comapDomain_single

/-- Actual triangles outside all coordinate-triangle fibres contribute no relator coefficients. -/
theorem presCoverRelatorChain_single_off_coordinates (t : StrictOrdTri P) (n : ℤ)
    (ht : ∀ j, (strictOrderCxMap f hf.strictMono).onF t ≠ presRelatorFirstTriangle w hpos j) :
    presCoverRelatorChain w f hf hpos (Finsupp.single t n) = 0 := by
  classical
  grind [presCoverRelatorChain_apply, presCoverRelatorTriangle_projection]

end FiniteChains.PresModel
