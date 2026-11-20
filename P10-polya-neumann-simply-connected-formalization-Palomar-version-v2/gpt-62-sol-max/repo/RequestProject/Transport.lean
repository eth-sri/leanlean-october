module

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

open scoped ComplexConjugate Real
open MeasureTheory Set

noncomputable section

namespace PolyaNeumann

/-- A positively oriented, constant-speed (rescaled arclength) Lipschitz parametrization
`γ` of the boundary of `Ω` over the period `L = 2π`.  Positive orientation is expressed
through Green's formula: the signed area integral `∫₀^L Im(conj(γ) γ') dθ` equals `2|Ω|`
(for a Jordan parametrization of the boundary it is `±2|Ω|`, with the sign giving the
orientation). -/
structure IsBoundaryParam (Ω : Set ℂ) (γ : ℝ → ℂ) : Prop where
  lipschitz : ∃ K, LipschitzWith K γ
  periodic : Function.Periodic γ (2 * π)
  injOn : Set.InjOn γ (Set.Ico 0 (2 * π))
  image : γ '' Set.Icc 0 (2 * π) = frontier Ω
  const_speed : ∃ c : ℝ, 0 < c ∧ ∀ᵐ θ, ‖deriv γ θ‖ = c
  area : ∫ θ in (0 : ℝ)..(2 * π), (conj (γ θ) * deriv γ θ).im = 2 * (volume Ω).toReal

section

variable (γ : ℝ → ℂ) (E : ℝ)
include γ E

/-- The transport coefficient
`C_E(θ) = -(i √E / 2) (γ'(θ) S_N^* + conj(γ'(θ)) S_N)`. -/
def transportCoeff  (θ : ℝ) : Ell2 →L[ℂ] Ell2 :=
  (-(Complex.I * (Real.sqrt E : ℂ)) / 2) •
    (deriv γ θ • ContinuousLinearMap.adjoint shiftN + conj (deriv γ θ) • shiftN)

/-- `W` is a transport for `γ` at energy `E`: it is continuous on `[0, L]` and solves
`W(θ) = I + ∫₀^θ C_E(s) W(s) ds` there. -/
def IsTransport  (W : ℝ → Ell2 →L[ℂ] Ell2) : Prop :=
  ContinuousOn W (Set.Icc 0 (2 * π)) ∧
  ∀ θ ∈ Set.Icc 0 (2 * π), W θ = 1 + ∫ s in (0 : ℝ)..θ, transportCoeff γ E s * W s

end

/-- The monodromy `U_E = W_E(L)^*`. -/
def monodromy (W : ℝ → Ell2 →L[ℂ] Ell2) : Ell2 →L[ℂ] Ell2 :=
  ContinuousLinearMap.adjoint (W (2 * π))

/-- `‖U - I‖ > 0` as soon as `U ≠ I`. -/
lemma norm_sub_one_pos {U : Ell2 →L[ℂ] Ell2} (h : U ≠ 1) : 0 < ‖U - 1‖ :=
  norm_pos_iff.mpr (sub_ne_zero.mpr h)

section

variable (γ : ℝ → ℂ) (E : ℝ)
include γ E

lemma transportCoeff_aestronglyMeasurable  :
    AEStronglyMeasurable (transportCoeff γ E) volume := by
  have hg : Continuous fun z : ℂ => (-(Complex.I * (Real.sqrt E : ℂ)) / 2) •
      (z • ContinuousLinearMap.adjoint shiftN + conj z • shiftN) := by
    have := Complex.continuous_conj
    fun_prop
  exact hg.comp_aestronglyMeasurable (measurable_deriv γ).aestronglyMeasurable

lemma transportCoeff_norm_le  {K : NNReal} (hK : LipschitzWith K γ)
    (θ : ℝ) : ‖transportCoeff γ E θ‖ ≤ ‖(-(Complex.I * (Real.sqrt E : ℂ)) / 2)‖ *
      (K * ‖(ContinuousLinearMap.adjoint shiftN : Ell2 →L[ℂ] Ell2)‖ + K * ‖shiftN‖) := by
  have hd : ‖deriv γ θ‖ ≤ K := norm_deriv_le_of_lipschitz hK
  unfold transportCoeff
  rw [norm_smul]
  gcongr
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_smul]; gcongr
  · rw [norm_smul, Complex.norm_conj]; gcongr

end

lemma intervalIntegrable_of_norm_le {V : Type*} [NormedAddCommGroup V] {f : ℝ → V}
    (hf : AEStronglyMeasurable f volume) {B : ℝ} (hB : ∀ t, ‖f t‖ ≤ B) (a b : ℝ) :
    IntervalIntegrable f volume a b :=
  (intervalIntegrable_const (c := B)).mono_fun' hf.restrict (.of_forall hB)

lemma intervalIntegrable_transportCoeff_apply {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
    (E : ℝ) {y : ℝ → Ell2} {a b : ℝ} (hy : ContinuousOn y (uIcc a b)) :
    IntervalIntegrable (fun s => transportCoeff γ E s (y s)) volume a b := by
  obtain ⟨M, hC⟩ : ∃ M : ℝ, ∀ s, ‖transportCoeff γ E s‖ ≤ M := ⟨_, transportCoeff_norm_le γ E hK⟩
  refine IntervalIntegrable.mono_fun' (hy.norm.const_mul M).intervalIntegrable ?_ ?_
  · exact (ContinuousLinearMap.apply ℂ Ell2).flip.aestronglyMeasurable_comp₂
      (transportCoeff_aestronglyMeasurable γ E).restrict
      ((hy.mono uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc)
  · exact .of_forall fun s => ((transportCoeff γ E s).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hC s) (norm_nonneg _))

section

variable (γ : ℝ → ℂ) {K : NNReal} (hK : LipschitzWith K γ) (E : ℝ)
include γ K hK E

/-- Lemma 10.2 (existence): for a Lipschitz curve the transport equation has a solution. -/
theorem transport_exists_of_lipschitz  : ∃ W : ℝ → Ell2 →L[ℂ] Ell2, IsTransport γ E W :=
  exists_volterra_solution (transportCoeff_aestronglyMeasurable γ E)
    (transportCoeff_norm_le γ E hK) (2 * π)

/-- Lemma 10.2 (uniqueness): the transport is unique on `[0, L]`. -/
theorem transport_unique_of_lipschitz  {W W' : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W)
    (hW' : IsTransport γ E W') : Set.EqOn W W' (Set.Icc 0 (2 * π)) :=
  volterra_unique (transportCoeff_aestronglyMeasurable γ E) (transportCoeff_norm_le γ E hK)
    (2 * π) hW.1 hW'.1 hW.2 hW'.2

end

end PolyaNeumann

end
