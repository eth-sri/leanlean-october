module
public import Mathlib.Tactic
import Batteries.Tactic.Alias
import OAI.NumberTheory.DirichletL.MeanSquare.CanonicalTailBounds

public import OAI.NumberTheory.DirichletL.Descent.CubeSource
public import OAI.NumberTheory.DirichletL.Descent.FirstWholeMarkedColumns

@[expose] public section

namespace OAI


open scoped BigOperators Classical

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseInitialArithmetic
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι] (p : ι→ActualEisensteinCubic.O) (hp : ∀ i,p i≠0)


include hp in
theorem cube_whole_support_dyad (b : CubeCoordinates ι) (B : ℝ) (hB : 0≤B)
    (hl : ‖eisEmbedding (primeProduct p b.support b.leftExponent)‖^2≤B)
    (hr : ‖eisEmbedding (primeProduct p b.support b.rightExponent)‖^2≤B) :
    primeProductNorm p b.support≤B^2 := by solve_by_elim [_root_.OAI.SecondPassArithmetic.cubeCoordinates_radical_bound]

end SevenEighths.InverseMoment



end OAI
