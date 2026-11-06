
import GS.Frobenius



/-!
# Frobenius projections in the two-factor calculation

Theorems concern the explicit linear spaces of supported skew matrices. The
identification of these spaces with a manifold tangent bundle is a SEPARATE
obligation in `Specifications.lean`.

-/

open Matrix
namespace GS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def IsSkew (A : Matrix ι ι ℝ) : Prop := Aᵀ = -A







def MaskSymmetric (p : ι → ι → Prop) : Prop := ∀ i j, p i j ↔ p j i





























end GS
