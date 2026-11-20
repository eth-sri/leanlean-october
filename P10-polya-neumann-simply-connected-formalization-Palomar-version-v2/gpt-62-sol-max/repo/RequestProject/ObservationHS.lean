module

public import RequestProject.FourierLipschitz
public import RequestProject.SmallTransport
public import RequestProject.CutCorrection
public import RequestProject.PeriodicLipschitz

/-!
# Lemma 6.3: the periodic projected observation is Hilbert–Schmidt into `H¹(𝕋)`

For a transport `W` of a Lipschitz curve, let `c_E = (V_E^* - I) e₀` and let `Π^c_E` be the
orthogonal projection onto `c_E^⊥` (`cutProj`). The projected observation
`v ↦ O_E Π^c_E v = ⟨e₀, W(·) Π^c_E v⟩` has matching endpoint values (Lemma 6.4), and its row
`r(θ) = Π^c_E W(θ)^* e₀` is Lipschitz on `[0, L]`. Extending `r` periodically and applying the
difference-quotient estimate of `FourierLipschitz.lean` gives, for every orthonormal family
`(vⱼ)` of `ℓ²`, the Fourier coefficients of the periodized row paired with `vⱼ`
are the coefficients of the projected observation on the cut. The row bounds below
allow the Fourier Hilbert–Schmidt estimates to be applied to these rows.
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open Real Filter MeasureTheory
open scoped InnerProductSpace

/-! ### The projected observation row -/

lemma cutProj_apply_self (c : Ell2) : cutProj c c = 0 := by
  rw [cutProj_eq_starProjection]
  exact Submodule.starProjection_orthogonalComplement_singleton_eq_zero c

lemma inner_cutProj_left (c x y : Ell2) : ⟪cutProj c x, y⟫_ℂ = ⟪x, cutProj c y⟫_ℂ := by
  rw [cutProj_eq_starProjection]
  exact Submodule.inner_starProjection_left_eq_right (ℂ ∙ c)ᗮ x y

lemma norm_cutProj_apply_le (c x : Ell2) : ‖cutProj c x‖ ≤ ‖x‖ := by
  rw [cutProj_eq_starProjection]
  exact Submodule.norm_starProjection_apply_le (ℂ ∙ c)ᗮ x

section

variable (W : ℝ → Ell2 →L[ℂ] Ell2)
include W

/-- The row `r_E(θ) = Π^c_E W(θ)^* e₀` of the projected observation. -/
def projObsRow  (θ : ℝ) : Ell2 :=
  cutProj (cutC (W (2 * π)) (basisVec 0)) (ContinuousLinearMap.adjoint (W θ) (basisVec 0))

lemma observation_cutProj_eq  (v : Ell2) (θ : ℝ) :
    observation W (cutProj (cutC (W (2 * π)) (basisVec 0)) v) θ = ⟪projObsRow W θ, v⟫_ℂ := by
  rw [observation, projObsRow, inner_cutProj_left, ContinuousLinearMap.adjoint_inner_left]

end

lemma projObsRow_endpoint {γ : ℝ → ℂ} {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2}
    (hW : IsTransport γ E W) : projObsRow W (2 * π) = projObsRow W 0 := by
  have h0 : W 0 = 1 := by
    have := hW.2 0 ⟨le_rfl, by positivity⟩
    simpa using this
  unfold projObsRow
  rw [h0]
  have : ContinuousLinearMap.adjoint (W (2 * π)) (basisVec 0) =
      cutC (W (2 * π)) (basisVec 0) + basisVec 0 := by
    simp [cutC]
  rw [this, map_add, cutProj_apply_self, zero_add, ← ContinuousLinearMap.star_eq_adjoint, star_one]
  rfl

section

variable {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W)
include γ K hK E W hW

lemma norm_projObsRow_sub_le  {θ₁ θ₂ : ℝ}
    (h₁ : θ₁ ∈ Set.Icc 0 (2 * π)) (h₂ : θ₂ ∈ Set.Icc 0 (2 * π)) :
    ‖projObsRow W θ₁ - projObsRow W θ₂‖ ≤ Real.sqrt E * shiftConst * K * |θ₁ - θ₂| := by
  unfold projObsRow
  rw [← map_sub, ← ContinuousLinearMap.sub_apply, ← map_sub]
  refine (norm_cutProj_apply_le _ _).trans ?_
  refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
  rw [LinearIsometryEquiv.norm_map, show ‖basisVec 0‖ = 1 by simp [basisVec], mul_one]
  exact norm_transport_sub_le_lip hK hW h₁ h₂


end

end PolyaNeumann
