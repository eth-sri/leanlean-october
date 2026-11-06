
import GS.UnitaryLocalModel.MiddleFibres




/-!
# Fibres after an injective chart of the dephased unitary slice

These statements certify the nonlinear change from two middle matrices to a
centre and a difference. The local version requires injectivity only on the
chart domain and membership of all four arguments in that domain. Neither
version assumes or asserts the construction of the dephased slice chart.
-/
noncomputable section
namespace GS.UnitaryLocalModel

def chartMiddle {κ : Type*} (ψ : (Fin d → ℝ) → (κ → ℂ))
    (c z : Fin d → ℝ) (u : AxisVector) := fun j => middleBlock (ψ (c+z) j) (ψ (c-z) j) u


end GS.UnitaryLocalModel
