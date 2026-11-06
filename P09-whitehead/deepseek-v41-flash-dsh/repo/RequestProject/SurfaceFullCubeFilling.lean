module

public import RequestProject.BlockSpinePres
public import RequestProject.OrderCxConeNull
public import RequestProject.CellularHomotopyChain

@[expose] public section

/-! Concrete fillings of the cut-surface loops in the full cube quotient. -/
namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type u} [DecidableEq V] (A : CommRel V)

/-- Restore the deleted all-positive corner of the cube quotient. -/
def positiveCorner : QCube A :=
  ⟨∅, 0, by simp [IsSimplex], fun _ _ => rfl⟩

/-- The actual surface inclusion in the full cube quotient. -/
def surfaceFullCube (σ : NeSpx A) : QCube A := (posQCube σ).val

theorem surfaceFullCube_monotone : Monotone (surfaceFullCube A) :=
  posQCube_monotone

theorem positiveCorner_le_surface (σ : NeSpx A) :
    positiveCorner A ≤ surfaceFullCube A σ :=
  ⟨Finset.empty_subset _, fun _ _ => rfl⟩

/-- Every actual surface loop contracts through the restored positive corner. -/
theorem surfaceFullCube_loop_null {σ : NeSpx A}
    {p : List ((orderCx (NeSpx A)).E × Bool)}
    (hp : IsPath (orderCx (NeSpx A)).src (orderCx (NeSpx A)).tgt p σ σ) :
    Htpy (orderCx (QCube A)) (surfaceFullCube A σ) (surfaceFullCube A σ)
      (mapPath (orderCxMap (surfaceFullCube A) (surfaceFullCube_monotone A)) p) [] :=
  htpy_nil_mapPath_of_const_le (surfaceFullCube_monotone A) (surfaceFullCube_monotone A)
    (fun _ => le_refl _) (positiveCorner A) (positiveCorner_le_surface A) hp

end FiniteChains.Davis
