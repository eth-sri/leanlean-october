module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Analysis.Complex.Basic
public import DedekindZetaZeroFree.Algebra.LinearAlgebra.FunctionInterpolation

@[expose] public section

noncomputable section
open scoped Classical BigOperators
namespace DedekindZetaZeroFree.KPLiteralTensor.KernelAndHCRange.CoreGeneration.FiniteScalarEvaluation
 theorem finite_evaluation_reconstruction {X : Type*}
    (S : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ S] :
    ∃ (n m : ℕ) (x : Fin m → X) (A : Fin n → Fin m → ℂ)
      (b : Fin n → S),
      ∀ (h : S) (y : X), h.val y = ∑ j, (∑ i, A j i * h.val (x i)) * (b j).val y := by
  obtain ⟨n, x, b, hb⟩ := FiniteFunctionSpaces.exists_finite_evaluation_interpolation S
  refine ⟨n, n, x, fun j i => if i = j then 1 else 0, b, ?_⟩
  simpa [ite_mul] using hb

end DedekindZetaZeroFree.KPLiteralTensor.KernelAndHCRange.CoreGeneration.FiniteScalarEvaluation

end
