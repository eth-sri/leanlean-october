module

public import GS.Extensions.OriginalUniform
public import GS.Specifications
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
public import Mathlib.Analysis.SpecialFunctions.Exponential

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Discharging the local exponential-chart input

The analytic input is mathlib's strict derivative of exp at zero followed by
its inverse function theorem. No injectivity or same-fibres axiom is added.

The auxiliary operator norm is local to the first proof. The exported result
only involves the existing matrix topology, not an identification of that norm
with the Frobenius norm or with the default product norm.
-/

noncomputable section
open Matrix Filter
namespace GS.Continuation
open GS.Extensions

/-- The actual matrix exponential is injective on an open neighbourhood of zero.
Uses the v4.19 spelling `NormedSpace.exp`; newer docs omit that argument. -/
theorem exists_open_matrixExp_injective (n : ℕ) :
    ∃ V : Set (Mat n), IsOpen V ∧ (0 : Mat n) ∈ V ∧ Set.InjOn (@matrixExp n) V := by
  letI : NormedRing (Mat n) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Mat n) := Matrix.linftyOpNormedAlgebra
  have hd : HasStrictFDerivAt (NormedSpace.exp : Mat n → Mat n)
      (ContinuousLinearEquiv.refl ℝ (Mat n) : Mat n →L[ℝ] Mat n) 0 := by
    simpa only [ContinuousLinearEquiv.coe_refl, ContinuousLinearMap.one_def] using (hasStrictFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := Mat n))
  obtain ⟨V, hsub, hV, hzero⟩ := mem_nhds_iff.mp hd.eventually_left_inverse
  refine ⟨V, hV, hzero, fun A hA B hB hab => ?_⟩
  have := hsub hA
  have := hsub hB
  simp_all [matrixExp_eq_exp]

/-- The original f and g have the same fibres on one uniformly small K_eta.
There is no chart, sign, normalization, or fibre hypothesis in this statement.
It does NOT assert that f(K_eta) covers a neighbourhood in the whole GS set. -/
theorem original_same_fibres (hq : 0 < q) (Q₀ : Mat q)
    (hQ₀ : Orthogonal Q₀) (hentries : ∀ i j, Q₀ i j ≠ 0) :
    ∃ η : ℝ, 0 < η ∧ ∀ p ∈ originalK q η, ∀ p' ∈ originalK q η,
      originalF Q₀ p = originalF Q₀ p' ↔ originalG p = originalG p' := by
  obtain ⟨V, hV, hzero, hinj⟩ := exists_open_matrixExp_injective q
  refine original_same_fibres_of_open_chart hq Q₀ hentries V hV hzero fun A hA B hB he => hinj hA hB ?_
  simpa only [originalPsi, ← Matrix.mul_assoc, hQ₀.1, Matrix.one_mul] using congrArg (Q₀ᵀ * ·) he

end GS.Continuation
