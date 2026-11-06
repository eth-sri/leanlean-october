module

public import RequestProject.PlanarTypes

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

public section

open MeasureTheory Set Filter



namespace PolyaNeumann

lemma norm_adjoint_unitary_basisVec {U : ComplexEnd Ell2}
    (hU : U ∈ unitary (ComplexEnd Ell2)) (k : ℕ) :
    ‖ContinuousLinearMap.adjoint U (basisVec k)‖ = 1 := by
  have h1 : U * ContinuousLinearMap.adjoint U = 1 := by
    exact (Unitary.mem_iff.mp hU).2
  have h2 : ‖ContinuousLinearMap.adjoint U (basisVec k)‖ ^ 2 = ‖basisVec k‖ ^ 2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ),
      ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.mul_apply, h1,
      ContinuousLinearMap.one_apply]
  have h3 : ‖basisVec k‖ = 1 := by
    rw [basisVec, lp.norm_single (by norm_num)]; simp
  have := norm_nonneg (ContinuousLinearMap.adjoint U (basisVec k))
  nlinarith

end PolyaNeumann
