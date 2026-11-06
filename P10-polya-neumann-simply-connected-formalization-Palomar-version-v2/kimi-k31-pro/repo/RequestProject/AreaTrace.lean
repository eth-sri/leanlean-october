module

public import RequestProject.Area

/-!
# Trace of the curvature operator (Lemma 4.7, `tr L_E = |Ω|/2`)

For a continuous unitary family `U` and a bounded measurable weight `b`, the operator
`∫₀^L b U^* D_N U dθ` has diagonal sum `∫₀^L b dθ` in the standard basis (`tr D_N = 1` and the
trace is invariant under unitary conjugation). Applied to `Q_E = (1/4) ∫ b W^* D_N W` and to
`L_E = V_E Q_E V_E^*`, this gives `tr Q_E = tr L_E = (1/4) ∫₀^L b`, where `b` is the signed area
density; Green's formula `∫₀^L b = 2|Ω|` (not formalized here) turns this into the paper's
`tr L_E = |Ω|/2`.

Mathlib has no trace-class operators, so the trace is written as the sum of the diagonal
entries in the standard basis `(eₙ)` of `ℓ²(ℕ₀)`.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ComplexConjugate Real Topology

noncomputable section

namespace PolyaNeumann

lemma norm_adjoint_unitary_basisVec {U : Ell2 →L[ℂ] Ell2}
    (hU : U ∈ unitary (Ell2 →L[ℂ] Ell2)) (k : ℕ) :
    ‖ContinuousLinearMap.adjoint U (basisVec k)‖ = 1 := by
  have h := ContinuousLinearMap.norm_map_of_mem_unitary (Unitary.star_mem hU) (basisVec k)
  rw [ContinuousLinearMap.star_eq_adjoint] at h
  simpa using h

end PolyaNeumann

end
