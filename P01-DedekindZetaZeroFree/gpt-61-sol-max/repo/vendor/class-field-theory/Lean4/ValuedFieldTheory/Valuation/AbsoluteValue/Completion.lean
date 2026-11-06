module

public import Mathlib

public import ValuedFieldTheory.Valuation.AbsoluteValue.Extension
public import ValuedFieldTheory.Valuation.AbsoluteValue.Nonarchimedean
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.Analysis.Normed.Module.Completion
public import Mathlib.Analysis.Normed.Unbundled.RingSeminorm

@[expose] public section


/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/







set_option autoImplicit false

/-!
# Completions of absolute-valued fields

This file supplies the canonical absolute value, completion maps, density,
and complete-target universal property for real-valued absolute values.  An
extension is expressed directly by AbsoluteValue.Extends; no extra
container is introduced.  The base-to-completion algebra instance is the
canonical one inherited from WithAbs; algebras between different completions
remain explicit.
-/

noncomputable section

open scoped Topology

namespace AbsoluteValue

universe u v w

section
variable {K : Type u} [Field K] (vK : AbsoluteValue K ℝ)
include K vK
/-- The norm absolute value on the completion attached to `vK`. -/
noncomputable def completionAbsoluteValue
      :
    AbsoluteValue vK.Completion ℝ :=
  NormedField.toAbsoluteValue vK.Completion

/-- The extended absolute value on the completion agrees with the original value
on embedded elements. -/
@[simp]
theorem completionAbsoluteValue_coe
      (x : K) :
    completionAbsoluteValue vK (x : vK.Completion) = vK x := by
  change ‖(x : vK.Completion)‖ = vK x
  rw [UniformSpace.Completion.norm_coe]
  rfl


















/-- The field equipped with its completion absolute value is complete. -/
theorem completionAbsoluteValue_complete
      :
    CompleteSpace (WithAbs (completionAbsoluteValue vK)) := by
  let e := WithAbs.equiv (completionAbsoluteValue vK)
  have he : Isometry e :=
    AddMonoidHomClass.isometry_of_norm e.toRingHom fun _ ↦ rfl
  exact (completeSpace_congr (e := e.toEquiv) he.isUniformEmbedding).2 inferInstance

/-- Nontriviality passes to the completion absolute value. -/
theorem completionAbsoluteValue_isNontrivial
     
    (hvK : vK.IsNontrivial) :
    (completionAbsoluteValue vK).IsNontrivial := by
  rcases hvK with ⟨x, hx0, hx1⟩
  refine ⟨(x : vK.Completion), ?_, ?_⟩
  · simp_all
  · simpa using hx1

/-- The canonical embedding of an absolute-valued field in its completion. -/
noncomputable def toCompletion
       :=
  UniformSpace.Completion.coeRingHom.comp
    (WithAbs.equiv vK).symm.toRingHom

/-- The canonical map into the completion sends an element to its constant Cauchy class. -/
@[simp]
theorem toCompletion_apply
      (x : K) :
    toCompletion vK x = ((WithAbs.equiv vK).symm x : vK.Completion) :=
  rfl

/-- The canonical completion embedding agrees with the completion algebra map. -/
@[simp]
theorem toCompletion_eq_algebraMap
      (x : K) :
    toCompletion vK x = algebraMap K vK.Completion x :=
  rfl

/-- The canonical copy of a field is dense in its completion. -/
theorem denseRange_toCompletion
      :
    DenseRange (toCompletion vK) := by
  change DenseRange
    (UniformSpace.Completion.coe' ∘ WithAbs.toAbs vK)
  exact
    (@UniformSpace.Completion.denseRange_coe (WithAbs vK) inferInstance).comp
      (WithAbs.toAbs_surjective vK).denseRange
      (@UniformSpace.Completion.continuous_coe (WithAbs vK) inferInstance)
end


 noncomputable def baseToExtensionCompletion
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (wL : AbsoluteValue L ℝ)  :=
  UniformSpace.Completion.coeRingHom.comp
    (algebraMap (WithAbs vK) (WithAbs wL))

section
variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (wL : AbsoluteValue L ℝ)
    (hw : Extends vK wL)
include K L vK wL hw
private theorem baseToExtensionCompletion_norm
      (x : WithAbs vK) :
    ‖baseToExtensionCompletion vK wL x‖ = ‖x‖ := by
  change
    ‖((algebraMap (WithAbs vK) (WithAbs wL)) x : wL.Completion)‖ = ‖x‖
  rw [UniformSpace.Completion.norm_coe, WithAbs.norm_eq_apply_ofAbs,
    WithAbs.norm_eq_apply_ofAbs, WithAbs.ofAbs_algebraMap]
  exact hw x.ofAbs

 theorem baseToExtensionCompletion_isometry
      :
    Isometry (baseToExtensionCompletion vK wL) :=
  AddMonoidHomClass.isometry_of_norm _
    (baseToExtensionCompletion_norm vK wL hw)

/-- The isometric embedding between completions induced by an exact extension
of absolute values. -/
noncomputable def completionMap
      :
    vK.Completion →+* wL.Completion :=
  UniformSpace.Completion.extensionHom
    (baseToExtensionCompletion vK wL)
    (baseToExtensionCompletion_isometry vK wL hw).continuous

private theorem completionMap_withAbs_coe
      (x : WithAbs vK) :
    completionMap vK wL hw (x : vK.Completion) =
      baseToExtensionCompletion vK wL x :=
  UniformSpace.Completion.extensionHom_coe
    (baseToExtensionCompletion vK wL)
    (baseToExtensionCompletion_isometry vK wL hw).continuous x

/-- On the canonical copy of the base field, the map between completions is
the original algebra map followed by the canonical completion map. -/
@[simp]
theorem completionMap_coe
      (x : K) :
    completionMap vK wL hw (algebraMap K vK.Completion x) =
      toCompletion wL (algebraMap K L x) := by
  change completionMap vK wL hw
      (((WithAbs.equiv vK).symm x : WithAbs vK) : vK.Completion) =
    (((WithAbs.equiv wL).symm (algebraMap K L x) : WithAbs wL) :
      wL.Completion)
  rw [completionMap_withAbs_coe]
  rfl

/-- The map induced between completions is an isometry. -/
theorem completionMap_isometry
      :
    Isometry (completionMap vK wL hw) :=
  (baseToExtensionCompletion_isometry vK wL hw).completion_extension

/-- The algebra structure on the extension completion induced by the
completion map.  It is deliberately explicit rather than a global instance. -/
@[reducible] noncomputable def completionAlgebra
       :=
  (completionMap vK wL hw).toAlgebra

/-- The algebra structure on the completion uses the canonical completion embedding. -/
@[simp]
theorem completionAlgebra_algebraMap
      (x : vK.Completion) :
    @algebraMap vK.Completion wL.Completion _ _
        (completionAlgebra vK wL hw) x = completionMap vK wL hw x :=
  rfl
end


section
variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
include K L
/-- The algebra structure on an extension completion induced by the dense
copy of the extension field.  It is deliberately explicit. -/
@[reducible] noncomputable def extensionCompletionAlgebra
     
    (wL : AbsoluteValue L ℝ)  :=
  ((toCompletion wL).comp (algebraMap K L)).toAlgebra

/-- The canonical dense embedding as an algebra homomorphism. -/
noncomputable def toCompletionAlgHom
     
    (wL : AbsoluteValue L ℝ) :
    letI := extensionCompletionAlgebra (K := K) wL
    L →ₐ[K] wL.Completion := by
  letI := extensionCompletionAlgebra (K := K) wL
  exact
    { __ := toCompletion wL
      commutes' _ := rfl }

/-- The scalar tower `K → K_v → L_w` supplied by an exact extension. -/
theorem completion_isScalarTower
     
    (vK : AbsoluteValue K ℝ) (wL : AbsoluteValue L ℝ)
    (hw : Extends vK wL) :
    letI hK := extensionCompletionAlgebra (K := K) wL
    letI : SMul K wL.Completion := hK.toSMul
    letI := completionAlgebra vK wL hw
    IsScalarTower K vK.Completion wL.Completion := by
  let hK := extensionCompletionAlgebra (K := K) wL
  let  := hK.toSMul
  let := completionAlgebra vK wL hw
  exact IsScalarTower.of_algebraMap_eq fun x ↦
    (completionMap_coe vK wL hw x).symm

/-- The completion absolute value on `L_w` extends that on `K_v`. -/
theorem completionAbsoluteValue_extends
     
    (vK : AbsoluteValue K ℝ) (wL : AbsoluteValue L ℝ)
    (hw : Extends vK wL) :
    letI := completionAlgebra vK wL hw
    Extends (completionAbsoluteValue vK) (completionAbsoluteValue wL) := by
  let := completionAlgebra vK wL hw
  intro x
  change ‖algebraMap vK.Completion wL.Completion x‖ = ‖x‖
  exact (completionMap_isometry vK wL hw).norm_map_of_map_zero
    (map_zero _) x
end


/-- Nonarchimedeanness passes to the completion absolute value. -/
theorem completionAbsoluteValue_isNonarchimedean
    {K : Type u} [Field K] (vK : AbsoluteValue K ℝ)
    (hvK : IsNonarchimedean (vK : K → ℝ)) :
    IsNonarchimedean
      (completionAbsoluteValue vK : vK.Completion → ℝ) := by
  rw [isNonarchimedean_iff_bounded_nat]
  refine ⟨1, fun n ↦ ?_⟩
  rw [← map_natCast (algebraMap K vK.Completion) n,
    ← toCompletion_eq_algebraMap vK (n : K)]
  change completionAbsoluteValue vK
    (((WithAbs.equiv vK).symm (n : K) : WithAbs vK) :
      vK.Completion) ≤ 1
  rw [completionAbsoluteValue_coe]
  change vK (n : K) ≤ 1
  apply hvK.apply_natCast_le_one <;> aesop











































section CompleteTarget

variable {K : Type u} {D : Type w} [Field K] [Field D]

































































































end CompleteTarget

section CompleteTargetTower

variable {K : Type u} {L : Type v} {D : Type w}
variable [Field K] [Field L] [Field D] [Algebra K L]
















































end CompleteTargetTower

end AbsoluteValue

end
