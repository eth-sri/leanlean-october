module

public import Mathlib.Topology.Homotopy.Basic
public import Mathlib.Topology.Homeomorph.Lemmas

@[expose] public section

open scoped unitInterval Topology

namespace ContinuousMap.Homotopy

variable {J Y : Type*} {A : J → Type*} [TopologicalSpace Y] [∀ j, TopologicalSpace (A j)]
  {f g : C((Σ j, A j), Y)}

/-- Homotopies on the summands assemble along the disjoint-union topology. -/
def sigmaFamily (H : ∀ j, (f.comp (ContinuousMap.sigmaMk j)).Homotopy
    (g.comp (ContinuousMap.sigmaMk j))) : f.Homotopy g where
  toFun z := H z.2.1 (z.1, z.2.2)
  continuous_toFun :=
    (continuous_sigma (f := fun a : Σ j, A j × I => H a.1 (a.2.2, a.2.1))
      (fun j => (H j).continuous.comp continuous_swap)).comp
      (Homeomorph.sigmaProdDistrib.continuous.comp continuous_swap)
  map_zero_left z := (H z.1).apply_zero z.2
  map_one_left z := (H z.1).apply_one z.2

end ContinuousMap.Homotopy
