module

public import ValuedFieldTheory.Valuation.AbsoluteValue.Completion
public import ValuedFieldTheory.Valuation.Completion.TensorProductDecomposition
public import ValuedFieldTheory.Valuation.Completion.TensorProductProductFormulas

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/





set_option autoImplicit false

/-!
# Compatibility of local degree, norm, and trace

The canonical decomposition of the completion tensor-product decomposition gives the sum of the local
degrees and the product/sum formulas for norm and trace.  Since the global
norm and trace lie in `K`, their Lean statements are mapped into `K_v`.
-/

noncomputable section

open scoped BigOperators TensorProduct
open ValuationTheory.Completion

namespace AlgebraicNumberTheory
namespace Valuations

universe u v

/-- Every local completion is finite-dimensional over `K_v`.  This is
derived from the completion tensor-product decomposition by projecting from its finite product. -/
theorem completionModuleFinite
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L) :
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    Module.Finite vK.Completion w.1.Completion := by
  let : ∀ w : AbsoluteValueExtension vK L,
      Algebra vK.Completion w.1.Completion :=
    fun w ↦ AbsoluteValue.completionAlgebra vK w.1 w.2
  let : Module.Finite vK.Completion (vK.Completion ⊗[K] L) :=
    inferInstance
  let : Module.Finite vK.Completion
      (∀ w : AbsoluteValueExtension vK L, w.1.Completion) :=
    Module.Finite.equiv (completionTensorDecomposition_left vK hvK).toLinearEquiv
  exact moduleFiniteOfPi
    (fun w : AbsoluteValueExtension vK L ↦ w.1.Completion) w









end Valuations
end AlgebraicNumberTheory

end
