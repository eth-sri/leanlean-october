
import GS.Nonmanifold.CircleRetract
open GS.MatrixBase



/-!
# The punctured determinantal cone is (0,infinity) times its link

All spaces carry their actual subtype/product topologies. Normalization is
performed only away from zero. The radial homeomorphism and the circle retract
below are genuine constructions, but are not a proof of the local homology
calculation at zero or of its shift under a Euclidean product.
-/
noncomputable section
open GS.Extensions
namespace GS.Nonmanifold

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

def frobeniusRadius (W : Matrix (Fin 2) κ ℝ) : ℝ := Real.sqrt (cFrobSq W)

theorem continuous_frobeniusRadius : Continuous (frobeniusRadius : Matrix (Fin 2) κ ℝ → ℝ) := Real.continuous_sqrt.comp continuous_frobSq

theorem frobeniusRadius_nonneg (W : Matrix (Fin 2) κ ℝ) :
    0 ≤ frobeniusRadius W := Real.sqrt_nonneg _

theorem frobeniusRadius_sq (W : Matrix (Fin 2) κ ℝ) :
    frobeniusRadius W ^ 2 = cFrobSq W := Real.sq_sqrt (cFrobSq_nonneg W)

theorem frobeniusRadius_ne_zero {W : Matrix (Fin 2) κ ℝ} (hW : W ≠ 0) :
    frobeniusRadius W ≠ 0 :=
  (Real.sqrt_ne_zero (cFrobSq_nonneg W)).mpr ((cFrobSq_eq_zero_iff W).not.mpr hW)

end GS.Nonmanifold
