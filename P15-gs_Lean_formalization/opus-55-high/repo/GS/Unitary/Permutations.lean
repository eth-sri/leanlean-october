module

public import GS.Unitary.Support

@[expose] public section


/-! Permutations act by unitary simultaneous relabeling of complex entries. -/
noncomputable section
namespace GS.UnitaryGeometry
variable {n : ℕ}

def cPermMatrix (σ : Equiv.Perm (Fin n)) : CMat n :=
  fun i j => if i = σ j then 1 else 0




end GS.UnitaryGeometry
