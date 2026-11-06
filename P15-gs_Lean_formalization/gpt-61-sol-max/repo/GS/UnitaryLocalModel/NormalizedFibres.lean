
import GS.UnitaryLocalModel.PolarTwo
import GS.UnitaryLocalModel.ChartFibres



/-!
# Exact fibres including the normalized outer unitary factors

Positive first-row and first-column middle blocks determine every outer unitary
factor, once the right anchor is fixed to the identity. The residual equality
is exactly equality of the complete middle family. These statements retain
all outer factors and do not restrict the image to a selected middle slice.
-/
open scoped ComplexOrder
namespace GS.UnitaryLocalModel


variable (Q : CMat q)

/-- Positivity is measured relative to the reference anchor entries. -/
def NormalizedPositiveAnchors  (o : Fin q)
    (N : Fin q → Fin q → CMat 2) : Prop :=
  (∀ i, ((Q i o)⁻¹ • N i o).PosDef) ∧
  (∀ j, ((Q o j)⁻¹ • N o j).PosDef)


end GS.UnitaryLocalModel
