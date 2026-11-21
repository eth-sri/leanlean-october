module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas

public section

noncomputable section

open scoped Classical

namespace DedekindZetaZeroFree.FiniteFunctionSpaces

private def pointEvaluation {X : Type*} (S : Submodule ℂ (X → ℂ)) (x : X) :
    Module.Dual ℂ S := (LinearMap.proj x).comp S.subtype

theorem exists_finite_evaluation_interpolation {X : Type*}
    (S : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ S] :
    ∃ (n : ℕ) (x : Fin n → X) (b : Fin n → S),
      ∀ (f : S) (y : X), f.val y = ∑ i, f.val (x i) * (b i).val y := by
  have hs : ⊤ ≤ Submodule.span ℂ (Set.range (pointEvaluation S)) := by
    apply le_of_eq
    symm
    apply Submodule.span_eq_top_of_ne_zero
    intro f hf
    obtain ⟨x, hx⟩ : ∃ x, f.val x ≠ 0 := by
      by_contra! h
      exact hf (Subtype.ext (funext h))
    exact ⟨pointEvaluation S x, ⟨x, rfl⟩, hx⟩
  let B := Module.Basis.ofSpan hs
  let := FiniteDimensional.fintypeBasisIndex B
  let B' := B.reindex (Fintype.equivFin _)
  have hB : Set.range B' ⊆ Set.range (pointEvaluation S) := by
    rw [Module.Basis.range_reindex]
    exact Module.Basis.ofSpan_subset hs
  choose x hx using fun i => hB (Set.mem_range_self i)
  let e := Module.evalEquiv ℂ S
  refine ⟨_, x, fun i => e.symm (B'.dualBasis i), ?_⟩
  intro f y
  change pointEvaluation S y f = _
  have he := congrArg (fun l : Module.Dual ℂ (Module.Dual ℂ S) => l (pointEvaluation S y))
    (B'.dualBasis.sum_repr (Module.Dual.eval ℂ S f))
  change _ = pointEvaluation S y f at he
  change _ = ∑ i, pointEvaluation S (x i) f * pointEvaluation S y (e.symm (B'.dualBasis i))
  simpa only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    Module.Basis.dualBasis_repr, Module.Dual.eval_apply, ← hx, e,
    Module.apply_evalEquiv_symm_apply] using he.symm

end DedekindZetaZeroFree.FiniteFunctionSpaces
