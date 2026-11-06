
import GS.Unitary.Support



/-! Permutations act by unitary simultaneous relabeling of complex entries. -/
namespace GS.UnitaryGeometry

def cPermMatrix (σ : Equiv.Perm (Fin n)) : CMat n :=
  fun i j => if i = σ j then 1 else 0













end GS.UnitaryGeometry
