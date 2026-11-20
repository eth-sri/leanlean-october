module

public import RequestProject.ObservationHS
public import RequestProject.CorrectedKernelCont

/-!
# Lemma 6.3: continuity in the energy of the projected observation in Hilbert–Schmidt norm

Let `W_E` be the transports of a Lipschitz curve and `E₀` an energy with
`c_{E₀} = (V_{E₀}^* - I) e₀ ≠ 0`. For an orthonormal family `(vⱼ)` of `ℓ²`, write
`cⱼ^E(n)` for the Fourier coefficients on `[0, L]` of `O_E Π^c_E vⱼ`. The following estimates bound the supremum and Lipschitz norms of the difference of the
projected observation rows by quantities that vanish as `E → E₀`.

The proof avoids derivatives. The difference of rows
`D_E(θ) = Π^c_E W_E(θ)^* e₀ - Π^c_{E₀} W_{E₀}(θ)^* e₀` has matching endpoint values and a
Lipschitz constant that tends to `0`: the increments of `W_E - W_{E₀}` are integrals of
`C_E W_E - C_{E₀} W_{E₀}`, which is uniformly small, and `Π^c_E → Π^c_{E₀}` in norm. The
difference-quotient estimate of `FourierLipschitz.lean` then bounds the `H¹` part by
`π² Lip(D_E)² / 4`, and Bessel's inequality bounds the `L²` part by `sup ‖D_E‖²`.
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open Real MeasureTheory Set Filter Topology
open scoped InnerProductSpace ComplexConjugate

variable {γ : ℝ → ℂ} {K : NNReal} {Ws : ℝ → ℝ → Ell2 →L[ℂ] Ell2}

open ContinuousLinearMap (adjoint) in
private lemma norm_cutProj_adjoint_diff_le {c c' : Ell2} {X X' : Ell2 →L[ℂ] Ell2}
    {a b : ℝ} (ha : ‖X' - X‖ ≤ a) (hb : ‖X‖ ≤ b) :
    ‖cutProj c' (adjoint X' (basisVec 0)) - cutProj c (adjoint X (basisVec 0))‖ ≤
      a + ‖cutProj c' - cutProj c‖ * b := by
  have hadj (A : Ell2 →L[ℂ] Ell2) : ‖adjoint A (basisVec 0)‖ ≤ ‖A‖ := by
    simpa [norm_basisVec_zero] using (adjoint A).le_opNorm (basisVec 0)
  rw [show cutProj c' (adjoint X' (basisVec 0)) - cutProj c (adjoint X (basisVec 0)) =
      cutProj c' (adjoint (X' - X) (basisVec 0)) + (cutProj c' - cutProj c) (adjoint X (basisVec 0)) by
    simp only [map_sub, ContinuousLinearMap.sub_apply]; abel]
  exact (norm_add_le _ _).trans (add_le_add
    ((norm_cutProj_apply_le _ _).trans ((hadj _).trans ha))
    ((ContinuousLinearMap.le_opNorm _ _).trans (by gcongr; exact (hadj _).trans hb)))

section

variable (hK : LipschitzWith K γ) {E E' : ℝ} {W W' : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W) (hW' : IsTransport γ E' W') {d : ℝ} (hd : ∀ s ∈ Icc 0 (2 * π), ‖W' s - W s‖ ≤ d) {θ₁ θ₂ : ℝ} (h₁ : θ₁ ∈ Icc 0 (2 * π)) (h₂ : θ₂ ∈ Icc 0 (2 * π))
include hK E E' W W' hW hW' d hd θ₁ θ₂ h₁ h₂

/-- Lipschitz bound for the difference of two projected observation rows. -/
lemma norm_projObsRow_diff_sub_le  :
    ‖(projObsRow W' θ₁ - projObsRow W θ₁) - (projObsRow W' θ₂ - projObsRow W θ₂)‖ ≤
      (|Real.sqrt E' - Real.sqrt E| * shiftConst * K + Real.sqrt E * shiftConst * K * d +
        ‖cutProj (cutC (W' (2 * π)) (basisVec 0)) - cutProj (cutC (W (2 * π)) (basisVec 0))‖ *
          (Real.sqrt E * shiftConst * K)) * |θ₁ - θ₂| := by
  rw [add_mul, mul_assoc (‖_‖)]
  have hΔ := norm_transport_diff_sub_le hK hW hW' hd h₁ h₂
  rw [show (W' θ₁ - W θ₁) - (W' θ₂ - W θ₂) = (W' θ₁ - W' θ₂) - (W θ₁ - W θ₂) by abel] at hΔ
  have h := norm_cutProj_adjoint_diff_le (c := cutC (W (2 * π)) (basisVec 0))
    (c' := cutC (W' (2 * π)) (basisVec 0)) hΔ
    (norm_transport_sub_le_lip hK hW h₁ h₂)
  convert h using 2
  simp only [projObsRow, map_sub, ContinuousLinearMap.sub_apply]
  abel

end

/-- Pointwise bound for the difference of two projected observation rows. -/
lemma norm_projObsRow_diff_le (hK : LipschitzWith K γ) {E : ℝ}
    {W W' : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W) {d : ℝ}
    (hd : ∀ s ∈ Icc 0 (2 * π), ‖W' s - W s‖ ≤ d) {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * π)) :
    ‖projObsRow W' θ - projObsRow W θ‖ ≤
      d + ‖cutProj (cutC (W' (2 * π)) (basisVec 0)) - cutProj (cutC (W (2 * π)) (basisVec 0))‖ := by
  simpa only [projObsRow, mul_one] using norm_cutProj_adjoint_diff_le
    (c := cutC (W (2 * π)) (basisVec 0)) (c' := cutC (W' (2 * π)) (basisVec 0))
    (hd θ hθ) (norm_transport_le_one hK hW hθ)

/-- Continuity of the projection `Π^c_E` in the energy at `E₀` when `c_{E₀} ≠ 0`. -/
theorem tendsto_cutProj_energy (hK : LipschitzWith K γ) (hWs : ∀ E, IsTransport γ E (Ws E))
    (E₀ : ℝ) (hc : cutC (Ws E₀ (2 * π)) (basisVec 0) ≠ 0) :
    Tendsto (fun E => cutProj (cutC (Ws E (2 * π)) (basisVec 0))) (𝓝 E₀)
      (𝓝 (cutProj (cutC (Ws E₀ (2 * π)) (basisVec 0)))) := by
  have hC := tendsto_cutC_energy hK hWs E₀
  have hn :=
    (Complex.continuous_ofReal.tendsto _).comp (hC.norm.pow 2)
  have h0 : ((‖cutC (Ws E₀ (2 * π)) (basisVec 0)‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    simp_all
  unfold cutProj
  exact tendsto_const_nhds.sub ((hn.inv₀ h0).smul (tendsto_rankOne hC hC))

/-- The difference of projected observation rows at energies `E` and `E₀`. -/
def projObsRowDiff (Ws : ℝ → ℝ → Ell2 →L[ℂ] Ell2) (E₀ E : ℝ) : ℝ → Ell2 :=
  fun θ => projObsRow (Ws E) θ - projObsRow (Ws E₀) θ

lemma projObsRowDiff_endpoint (hWs : ∀ E, IsTransport γ E (Ws E)) (E₀ E : ℝ) :
    projObsRowDiff Ws E₀ E (2 * π) = projObsRowDiff Ws E₀ E 0 := by
  simp [projObsRowDiff, projObsRow_endpoint (hWs E), projObsRow_endpoint (hWs E₀)]

section

variable (hK : LipschitzWith K γ) (hWs : ∀ E, IsTransport γ E (Ws E)) (E₀ : ℝ) (hc : cutC (Ws E₀ (2 * π)) (basisVec 0) ≠ 0)
include hK hWs E₀ hc

/-- The row difference has a Lipschitz periodization and a sup bound, both with constants
tending to `0` as `E → E₀`. -/
lemma projObsRowDiff_data  :
    ∃ Lf Bf : ℝ → ℝ, Tendsto Lf (𝓝 E₀) (𝓝 0) ∧ Tendsto Bf (𝓝 E₀) (𝓝 0) ∧
      ∀ E, LipschitzWith (Lf E).toNNReal (periodize (projObsRowDiff Ws E₀ E)) ∧
        ∀ θ ∈ Icc 0 (2 * π), ‖projObsRowDiff Ws E₀ E θ‖ ≤ Bf E := by
  obtain ⟨R, hR⟩ := exists_curve_displacement_bound hK
  set pf : ℝ → ℝ := fun E =>
    ‖cutProj (cutC (Ws E (2 * π)) (basisVec 0)) - cutProj (cutC (Ws E₀ (2 * π)) (basisVec 0))‖
  have hp :=
    tendsto_iff_norm_sub_tendsto_zero.mp (tendsto_cutProj_energy hK hWs E₀ hc)
  have hD := tendsto_transportDist K R E₀
  have hsq : Tendsto (fun E => |Real.sqrt E - Real.sqrt E₀|) (𝓝 E₀) (𝓝 0) := by
    have : Continuous fun E => |Real.sqrt E - Real.sqrt E₀| := by fun_prop
    simpa using this.tendsto E₀
  refine ⟨fun E => |Real.sqrt E - Real.sqrt E₀| * shiftConst * K +
      Real.sqrt E₀ * shiftConst * K * transportDist K R E₀ E + pf E * (Real.sqrt E₀ * shiftConst * K),
    fun E => transportDist K R E₀ E + pf E, ?_, ?_, fun E => ⟨?_, ?_⟩⟩
  · have := ((hsq.mul_const shiftConst).mul_const (K : ℝ)).add
      ((hD.const_mul (Real.sqrt E₀ * shiftConst * K)).add
        (hp.mul_const (Real.sqrt E₀ * shiftConst * K)))
    simpa only [zero_mul, mul_zero, add_zero, add_assoc] using this
  · simpa only [add_zero] using hD.add hp
  · have hd : ∀ s ∈ Icc 0 (2 * π), ‖Ws E s - Ws E₀ s‖ ≤ transportDist K R E₀ E :=
      fun s hs => norm_transport_sub_le hK hR (hWs E₀) (hWs E) hs
    have hend := projObsRowDiff_endpoint hWs E₀ E
    refine lipschitzWith_periodize (fun x hx y hy => ?_) hend
    refine (norm_projObsRow_diff_sub_le hK (hWs E₀) (hWs E) hd hx hy).trans ?_
    exact mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal _) (abs_nonneg _)
  · intro θ hθ
    exact norm_projObsRow_diff_le hK (hWs E₀)
      (fun s hs => norm_transport_sub_le hK hR (hWs E₀) (hWs E) hs) hθ

end

end PolyaNeumann
