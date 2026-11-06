module

public import RequestProject.TopologicalSingular.BasedTriangleHurewicz
public import RequestProject.TopologicalSingular.SimplexLinearHomotopy
public import RequestProject.TopologicalSingular.SimplexPrismRetraction

@[expose] public section

namespace FiniteChains.TopologicalSingular
open scoped unitInterval Topology
variable {X : Type u} [TopologicalSpace X] {x : X}

theorem basedTriangleSquare_const
    (h : ∀ i : Fin 3,
      face i (ContinuousMap.const (Domain 2) x) = ContinuousMap.const (Domain 1) x) :
    basedTriangleSquare (ContinuousMap.const (Domain 2) x) h = GenLoop.const := by
  apply GenLoop.ext
  intro z
  rfl

end FiniteChains.TopologicalSingular
