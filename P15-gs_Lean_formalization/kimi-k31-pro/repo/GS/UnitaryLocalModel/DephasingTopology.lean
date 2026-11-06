module

public import GS.UnitaryLocalModel.NormalizationAlgebra
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Continuity of anchor dephasing

The anchor condition is open, and the explicit phase normalization is
continuous wherever its row and column anchors are nonzero. These statements
apply to arbitrary continuous parameter families of the original factors.
-/

noncomputable section
open Matrix GS GS.UnitaryNonmanifold

namespace GS.UnitaryLocalModel

variable {q : ℕ}

theorem continuousAt_phase {z : ℂ} (hz : z ≠ 0) : ContinuousAt phase z := by
  apply continuousAt_id.div
    (Complex.continuous_ofReal.continuousAt.comp continuous_norm.continuousAt)
  change (‖z‖ : ℂ) ≠ 0
  exact_mod_cast norm_ne_zero_iff.mpr hz

theorem isOpen_anchorNonzero (Q : CMat q) (o : Fin q) :
    IsOpen {A : CMat q | AnchorNonzero Q A o} := by
  unfold AnchorNonzero
  apply IsOpen.and
  · simp only [Set.setOf_forall]
    apply isOpen_iInter_of_finite
    intro i
    exact isOpen_const.and (isOpen_ne_fun
      (show Continuous (fun A : CMat q => A i o) from by fun_prop) continuous_const)
  · simp only [Set.setOf_forall]
    apply isOpen_iInter_of_finite
    intro j
    exact isOpen_const.and (isOpen_ne_fun
      (show Continuous (fun A : CMat q => A o j) from by fun_prop) continuous_const)

theorem continuousAt_rowPhase {Q A : CMat q} {o : Fin q}
    (ha : AnchorNonzero Q A o) (i : Fin q) :
    ContinuousAt (fun M : CMat q => rowPhase Q M o i) A := by
  have he : ContinuousAt (fun M : CMat q => M i o / Q i o) A :=
    (show Continuous (fun M : CMat q => M i o) from by fun_prop).continuousAt.div_const _
  exact ContinuousAt.comp (f := fun M : CMat q => M i o / Q i o)
    (g := phase) (continuousAt_phase (div_ne_zero (ha.1 i).2 (ha.1 i).1)) he

theorem continuousAt_colPhase {Q A : CMat q} {o : Fin q}
    (ha : AnchorNonzero Q A o) (j : Fin q) :
    ContinuousAt (fun M : CMat q => colPhase Q M o j) A := by
  have he : ContinuousAt (fun M : CMat q => M o j / Q o j) A :=
    (show Continuous (fun M : CMat q => M o j) from by fun_prop).continuousAt.div_const _
  exact ContinuousAt.comp (f := fun M : CMat q => M o j / Q o j)
    (g := phase) (continuousAt_phase (div_ne_zero (ha.2 j).2 (ha.2 j).1)) he

theorem continuousAt_dephase {Q A : CMat q} {o : Fin q}
    (ha : AnchorNonzero Q A o) :
    ContinuousAt (fun M : CMat q => dephase Q M o) A := by
  apply continuousAt_pi.mpr
  intro i
  apply continuousAt_pi.mpr
  intro j
  exact (((continuousAt_rowPhase ha i).star.mul
    (continuous_apply_apply i j).continuousAt).mul
    (continuousAt_colPhase ha j).star).mul (continuousAt_rowPhase ha o)

section ParameterFamilies

variable {E : Type*} [TopologicalSpace E] {x : E}
  {A B : E → CMat q} {U V : E → Fin q → CMat 2}
  {Q : CMat q} {o : Fin q}

end ParameterFamilies
end GS.UnitaryLocalModel
