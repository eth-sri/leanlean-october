module

public import GS.Nonmanifold.CircleRetract

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# The punctured determinantal cone is (0,infinity) times its link

All spaces carry their actual subtype/product topologies. Normalization is
performed only away from zero. The radial homeomorphism and the circle retract
below are genuine constructions, but are not a proof of the local homology
calculation at zero or of its shift under a Euclidean product.
-/
noncomputable section
open Matrix GS GS.Extensions
open scoped BigOperators
namespace GS.Nonmanifold

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

def frobeniusRadius (W : Matrix (Fin 2) κ ℝ) : ℝ := Real.sqrt (frobSq W)

theorem continuous_frobeniusRadius : Continuous (frobeniusRadius : Matrix (Fin 2) κ ℝ → ℝ) := by
  exact Real.continuous_sqrt.comp continuous_frobSq

theorem frobeniusRadius_nonneg (W : Matrix (Fin 2) κ ℝ) :
    0 ≤ frobeniusRadius W := Real.sqrt_nonneg _

theorem frobeniusRadius_sq (W : Matrix (Fin 2) κ ℝ) :
    frobeniusRadius W ^ 2 = frobSq W := Real.sq_sqrt (frobSq_nonneg W)

theorem frobeniusRadius_pos {W : Matrix (Fin 2) κ ℝ} (hW : W ≠ 0) :
    0 < frobeniusRadius W := Real.sqrt_pos.2 (frobSq_pos_of_ne_zero hW)

theorem frobeniusRadius_ne_zero {W : Matrix (Fin 2) κ ℝ} (hW : W ≠ 0) :
    frobeniusRadius W ≠ 0 := ne_of_gt (frobeniusRadius_pos hW)

end GS.Nonmanifold
