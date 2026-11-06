module

public import Mathlib.Algebra.Field.Periodic

public import RequestProject.PlanarTypes

public import RequestProject.PlanarGeometry

public import RequestProject.Shift
public import RequestProject.Defs
public import RequestProject.Picard

/-!
# Boundary transport and its monodromy (Sections 4 and 10 of the paper)

For a closed Lipschitz boundary curve `γ : [0, L] → ∂Ω` (`L = 2π`) and an energy
`E = k² > 0`, the transport `W_E` solves
`W_E' = C_E W_E`, `W_E(0) = I`, with
`C_E(θ) = -(i k / 2) (γ'(θ) S_N^* + conj (γ'(θ)) S_N)`,
and the monodromy is `U_E = V_E^*`, `V_E = W_E(L)`.
We phrase the differential equation in its integral form, which is the meaning of the
almost-everywhere equation for absolutely continuous solutions.
-/

@[expose] public section

open scoped ComplexConjugate
open MeasureTheory

noncomputable section

namespace PolyaNeumann

/-- A positively oriented, constant-speed (rescaled arclength) Lipschitz parametrization
`γ` of the boundary of `Ω` over the period `L = 2π`.  Positive orientation is expressed
through Green's formula: the signed area integral `∫₀^L Im(conj(γ) γ') dθ` equals `2|Ω|`
(for a Jordan parametrization of the boundary it is `±2|Ω|`, with the sign giving the
orientation). -/
structure IsBoundaryParam (Ω : PlanarSet) (γ : ComplexCurve) : Prop where
  lipschitz : ∃ K, LipschitzWith K γ
  periodic : Function.Periodic γ circlePeriod
  injOn : Set.InjOn γ (Set.Ico 0 circlePeriod)
  image : γ '' boundaryInterval = frontier Ω
  const_speed : ∃ c : ℝ, 0 < c ∧ ∀ᵐ θ, ‖deriv γ θ‖ = c
  area : ∫ θ in (0 : ℝ)..circlePeriod, (conj (γ θ) * deriv γ θ).im = 2 * (volume Ω).toReal

/-- The transport coefficient
`C_E(θ) = -(i √E / 2) (γ'(θ) S_N^* + conj(γ'(θ)) S_N)`. -/
def transportCoeff (γ : ComplexCurve) (E : ℝ) (θ : ℝ) : ComplexEnd Ell2 :=
  (-(Complex.I * (Real.sqrt E : ℂ)) / 2) •
    (deriv γ θ • ContinuousLinearMap.adjoint shiftN + conj (deriv γ θ) • shiftN)

/-- `W` is a transport for `γ` at energy `E`: it is continuous on `[0, L]` and solves
`W(θ) = I + ∫₀^θ C_E(s) W(s) ds` there. -/
def IsTransport (γ : ComplexCurve) (E : ℝ) (W : ℝ → ComplexEnd Ell2) : Prop :=
  ContinuousOn W boundaryInterval ∧
  ∀ θ ∈ boundaryInterval, W θ = 1 + ∫ s in (0 : ℝ)..θ, transportCoeff γ E s * W s

/-- The monodromy `U_E = W_E(L)^*`. -/
def monodromy (W : ℝ → ComplexEnd Ell2) : ComplexEnd Ell2 :=
  ContinuousLinearMap.adjoint (W circlePeriod)

/-- `‖U - I‖ > 0` as soon as `U ≠ I`. -/
lemma norm_sub_one_pos {U : ComplexEnd Ell2} (h : U ≠ 1) : 0 < ‖U - 1‖ :=
  norm_pos_iff.mpr (sub_ne_zero.mpr h)

lemma transportCoeff_aestronglyMeasurable γ E :
    AEStronglyMeasurable (transportCoeff γ E) volume := by
  have hg : Continuous fun z : ℂ => (-(Complex.I * (Real.sqrt E : ℂ)) / 2) •
      (z • ContinuousLinearMap.adjoint shiftN + conj z • shiftN) := by
    fun_prop
  exact hg.comp_aestronglyMeasurable (measurable_deriv γ).aestronglyMeasurable

lemma transportCoeff_norm_le (γ : ComplexCurve) (E : ℝ) {K : NNReal} (hK : LipschitzWith K γ)
    (θ : ℝ) : ‖transportCoeff γ E θ‖ ≤ ‖(-(Complex.I * (Real.sqrt E : ℂ)) / 2)‖ *
      (K * ‖(ContinuousLinearMap.adjoint shiftN : ComplexEnd Ell2)‖ + K * ‖shiftN‖) := by
  have hd : ‖deriv γ θ‖ ≤ K := norm_deriv_le_of_lipschitz hK
  unfold transportCoeff
  rw [norm_smul]
  gcongr
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_smul]; gcongr
  · rw [norm_smul, Complex.norm_conj]; gcongr

section
variable (γ : ComplexCurve) {K } (hK : LipschitzWith K γ) (E : ℝ)
include γ K hK E

/-- Lemma 10.2 (existence): for a Lipschitz curve the transport equation has a solution. -/
theorem transport_exists_of_lipschitz : ∃ W : ℝ → ComplexEnd Ell2, IsTransport γ E W :=
  exists_volterra_solution (transportCoeff_aestronglyMeasurable γ E)
    (transportCoeff_norm_le γ E hK) circlePeriod

/-- Lemma 10.2 (uniqueness): the transport is unique on `[0, L]`. -/
theorem transport_unique_of_lipschitz  (hW : IsTransport γ E W)
    (hW' : IsTransport γ E W') : Set.EqOn W W' boundaryInterval :=
  volterra_unique (transportCoeff_aestronglyMeasurable γ E) (transportCoeff_norm_le γ E hK)
    circlePeriod hW.1 hW'.1 hW.2 hW'.2

end


/-- A periodic curve takes all its values on one closed period. -/
lemma mem_image_Icc_of_periodic {γ : ComplexCurve}
    (hper : Function.Periodic γ circlePeriod) θ : γ θ ∈ γ '' boundaryInterval := by
  simpa only [← hper.image_Icc Real.two_pi_pos 0, zero_add] using
    (Set.mem_range_self (f := γ) θ)

lemma IsBoundaryParam.mem_frontier (hγ : IsBoundaryParam Ω γ) s : γ s ∈ frontier Ω := by
  rw [← hγ.image]
  exact mem_image_Icc_of_periodic hγ.periodic s

lemma transport_zero (hW : IsTransport γ E W) : W 0 = 1 := by
  have := hW.2 0 ⟨le_rfl, by positivity⟩
  simpa using this

end PolyaNeumann

end
