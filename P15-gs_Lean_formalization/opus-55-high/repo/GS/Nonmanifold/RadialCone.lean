module

public import GS.Nonmanifold.CircleRetract

@[expose] public section


/-!
# The punctured determinantal cone is (0,infinity) times its link

All spaces carry their actual subtype/product topologies. Normalization is
performed only away from zero. The radial homeomorphism and the circle retract
below are genuine constructions, but are not a proof of the local homology
calculation at zero or of its shift under a Euclidean product.
-/
noncomputable section
open Matrix GS GS.Extensions
namespace GS.Nonmanifold

variable {κ : Type*} [Fintype κ]

def frobeniusRadius (W : Matrix (Fin 2) κ ℝ) : ℝ := Real.sqrt (frobSq W)

theorem continuous_frobeniusRadius : Continuous (frobeniusRadius : Matrix (Fin 2) κ ℝ → ℝ) :=
  Real.continuous_sqrt.comp continuous_frobSq

theorem frobeniusRadius_sq (W : Matrix (Fin 2) κ ℝ) :
    frobeniusRadius W ^ 2 = frobSq W := Real.sq_sqrt (frobSq_nonneg W)

end GS.Nonmanifold
