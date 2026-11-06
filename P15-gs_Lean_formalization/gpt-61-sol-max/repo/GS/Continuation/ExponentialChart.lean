
import GS.Extensions.OriginalUniform
import GS.Specifications
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential



/-!
# Discharging the local exponential-chart input

The analytic input is mathlib's strict derivative of exp at zero followed by
its inverse function theorem. No injectivity or same-fibres axiom is added.

The auxiliary operator norm is local to the first proof. The exported result
only involves the existing matrix topology, not an identification of that norm
with the Frobenius norm or with the default product norm.
-/

namespace GS.Continuation

theorem exists_matrixExpChart (n : ℕ) :
    ∃ e : OpenPartialHomeomorph (Mat n) (Mat n),
      (e : Mat n → Mat n) = NormedSpace.exp ∧ (0 : Mat n) ∈ e.source := by
  letI : NormedRing (Mat n) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Mat n) := Matrix.linftyOpNormedAlgebra
  have hd : HasStrictFDerivAt (NormedSpace.exp : Mat n → Mat n)
      (ContinuousLinearEquiv.refl ℝ (Mat n) : Mat n →L[ℝ] Mat n) 0 := by
    simpa only [ContinuousLinearEquiv.coe_refl, ContinuousLinearMap.one_def] using!
      (hasStrictFDerivAt_exp_zero  (𝔸 := Mat n))
  exact ⟨hd.toOpenPartialHomeomorph _, rfl,
    hd.mem_toOpenPartialHomeomorph_source⟩

end GS.Continuation
