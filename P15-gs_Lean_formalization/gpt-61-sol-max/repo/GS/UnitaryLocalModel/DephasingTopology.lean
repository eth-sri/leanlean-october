
import GS.UnitaryLocalModel.NormalizationAlgebra
import Mathlib.Topology.Instances.Matrix



/-!
# Continuity of anchor dephasing

The anchor condition is open, and the explicit phase normalization is
continuous wherever its row and column anchors are nonzero. These statements
apply to arbitrary continuous parameter families of the original factors.
-/


namespace GS.UnitaryLocalModel


theorem continuousAt_phase {z : ℂ} (hz : z ≠ 0) : ContinuousAt phase z := by
  apply continuousAt_id.div
    (Complex.continuous_ofReal.continuousAt.comp continuous_norm.continuousAt)
  change (‖z‖ : ℂ) ≠ 0
  exact_mod_cast norm_ne_zero_iff.mpr hz

theorem isOpen_anchorNonzero (Q : CMat q) (o : Fin q) :
    IsOpen {A : CMat q | AnchorNonzero Q A o} := by
  
  apply IsOpen.and <;>
    simp only [Set.ofPred_forall] <;>
    apply isOpen_iInter_of_finite <;>
    intro i <;>
    exact isOpen_const.and (isOpen_ne_fun (by fun_prop) continuous_const)

theorem continuousAt_dephase {Q A : CMat q} {o : Fin q}
    (ha : AnchorNonzero Q A o) :
    ContinuousAt (fun M : CMat q => dephase Q M o) A := by
  have hp (i j : Fin q) (hQ : Q i j ≠ 0) (hA : A i j ≠ 0) :=
    (continuousAt_phase (div_ne_zero hA hQ)).comp (f := fun M : CMat q => M i j / Q i j) ((continuous_apply_apply i j).continuousAt.div_const _)
  apply continuousAt_pi.mpr
  intro i
  apply continuousAt_pi.mpr
  intro j
  exact (((hp i o (ha.1 i).1 (ha.1 i).2).star.mul
    (continuous_apply_apply i j).continuousAt).mul
    (hp o j (ha.2 j).1 (ha.2 j).2).star).mul
    (hp o o (ha.1 o).1 (ha.1 o).2)

end GS.UnitaryLocalModel
