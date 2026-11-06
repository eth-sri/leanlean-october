module

public import GS.UnitaryLocalModel.NormalizationAlgebra
public import Mathlib.Topology.Instances.Matrix

@[expose] public section


/-!
# Continuity of anchor dephasing

The anchor condition is open, and the explicit phase normalization is
continuous wherever its row and column anchors are nonzero. These statements
apply to arbitrary continuous parameter families of the original factors.
-/

noncomputable section

namespace GS.UnitaryLocalModel

variable {q : ℕ}

theorem isOpen_anchorNonzero (Q : CMat q) (o : Fin q) :
    IsOpen {A : CMat q | AnchorNonzero Q A o} := by
  apply IsOpen.and <;> simp only [Set.setOf_forall] <;>
    exact isOpen_iInter_of_finite fun i => isOpen_const.and (isOpen_ne_fun (by fun_prop) continuous_const)

theorem continuousAt_dephase {Q A : CMat q} {o : Fin q} (ha : AnchorNonzero Q A o) :
    ContinuousAt (fun M : CMat q => dephase Q M o) A := by
  have h (a b : Fin q) (h₁ : Q a b ≠ 0) (h₂ : A a b ≠ 0) : ContinuousAt (fun M : CMat q => phase (M a b / Q a b)) A :=
    (continuousAt_id.div (by fun_prop) (by simp_all) : ContinuousAt phase _).comp ((continuous_apply_apply a b).continuousAt.div_const _)
  exact continuousAt_pi.2 fun i => continuousAt_pi.2 fun j => ((((h i o (ha.1 i).1 (ha.1 i).2).star.mul
    (continuous_apply_apply i j).continuousAt).mul (h o j (ha.2 j).1 (ha.2 j).2).star).mul (h o o (ha.1 o).1 (ha.1 o).2))

end GS.UnitaryLocalModel
