module

public import RequestProject.PlanarTypes

public import RequestProject.PlanarGeometry

public import RequestProject.CurveContinuity

/-!
# Energy derivative of the monodromy (Lemma 4.7, curvature formula)

For a closed Lipschitz curve `γ` and `E > 0`, the endpoint `V_E = W_E(L)` of the transport is
differentiable in `E` (in operator norm), with
`V_E^* ∂_E V_E = -i Q_E`, `Q_E = (1/4) ∫₀^L b W_E^* D_N W_E dθ`,
where `b = Im(conj(γ - γ(0)) γ')` is the signed area density.

The proof uses the variation identity of `CurveContinuity.lean` for the same curve at two
energies `E, E'`: with `G = coeffOf 1 (γ - γ(0))` and `C₁ = coeffOf 1 γ'`,
`V_{E'}^* V_E - 1 = (√E - √E') ∫₀^L W_{E'}^* (√E' C₁ G - √E G C₁) W_E`,
together with the commutator identity `[C₁, G] = -(i/2) b D_N` (from Lemma 4.2).
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ComplexConjugate Real Topology

noncomputable section

namespace PolyaNeumann

/-- The signed area density `b(θ) = Im(conj(γ(θ) - γ(0)) γ'(θ))`; for a positively oriented
Jordan parametrization `∫₀^L b = 2|Ω|`. -/
def areaDensity (γ : ComplexCurve) θ  := (conj (γ θ - γ 0) * deriv γ θ).im

/-- The curvature operator `Q_E = (1/4) ∫₀^L b W^* D_N W dθ`. -/
def curvatureOp (γ : ComplexCurve) (W : ℝ → ComplexEnd Ell2) : ComplexEnd Ell2 :=
  (1 / 4 : ℝ) • ∫ θ in (0 : ℝ)..circlePeriod, areaDensity γ θ • (star (W θ) * diagN * W θ)

lemma coeffOf_eq_sqrt_smul (E : ℝ) (z : ℂ) : coeffOf E z = Real.sqrt E • coeffOf 1 z := by
  unfold coeffOf
  rw [Real.sqrt_one, real_smul_eq_coe_smul_clm, smul_smul]
  push_cast
  ring

/-- The commutator identity `[C₁(a), C₁(b)] = -(i/2) Im(a conj b) D_N`. -/
lemma coeffOf_one_commutator (a b : ℂ) :
    coeffOf 1 a * coeffOf 1 b - coeffOf 1 b * coeffOf 1 a =
      (-(Complex.I / 2) * ((a * conj b).im : ℂ)) • diagN := by
  have hD := shift_commutator
  have him : ((a * conj b).im : ℂ) = (a * conj b - conj a * b) / (2 * Complex.I) := by
    rw [Complex.im_eq_sub_conj]; simp 
  rw [him, ← hD]
  unfold coeffOf
  simp  [add_mul, mul_add]
  match_scalars <;> field_simp <;> ring_nf <;> simp 

lemma norm_transportCoeff_le_const   (hK : LipschitzWith K γ) E s :
    ‖transportCoeff γ E s‖ ≤ Real.sqrt E * shiftConst * K := by
  refine (norm_coeffOf_le E _).trans ?_
  have := norm_deriv_le_of_lipschitz hK (x₀ := s)
  have := shiftConst_nonneg
  gcongr

section
variable {γ : ComplexCurve} {K } (hK : LipschitzWith K γ) {R } (hR : ∀ θ ∈ boundaryInterval, ‖γ θ - γ 0‖ ≤ R)

include γ K hK R hR in
/-- Uniform continuity of the transport in the energy:
`‖W_{E'}(θ) - W_E(θ)‖ ≤ |√E - √E'| κ R (1 + L (√E' + √E) κ K)` on `[0, L]`. -/
lemma norm_transport_sub_le  
    (hW : IsTransport γ E W) (hW' : IsTransport γ E' W')  (hθ : θ ∈ boundaryInterval) :
    ‖W' θ - W θ‖ ≤ |Real.sqrt E - Real.sqrt E'| * shiftConst * R *
      (1 + 2 * π * ((Real.sqrt E' + Real.sqrt E) * shiftConst * K)) := by
  have hπ : (0 : ℝ) ≤ 2 * π := by positivity
  have hκ := shiftConst_nonneg
  set ε := |Real.sqrt E - Real.sqrt E'| * shiftConst * R with hεdef
  set F : ℝ → ComplexEnd Ell2 := fun θ => coeffOf E (γ θ - γ 0) - coeffOf E' (γ θ - γ 0)
    with hF
  have hFL : LipschitzOnWith _ F boundaryInterval :=
    ((lipschitzWith_coeffOf hK E (γ 0)).sub (lipschitzWith_coeffOf hK E' (γ 0))).lipschitzOnWith
  have hFd : ∀ᵐ θ, θ ∈ Ioo 0 circlePeriod →
      HasDerivAt F (transportCoeff γ E θ - transportCoeff γ E' θ) θ := by
    filter_upwards [hK.ae_differentiableAt (μ := volume)] with θ h1 _
    exact (hasDerivAt_coeffOf h1.hasDerivAt E (γ 0)).sub
      (hasDerivAt_coeffOf h1.hasDerivAt E' (γ 0))
  have hF0 : F 0 = 0 := by simp [hF, coeffOf_zero]
  have hFb : ∀ s ∈ boundaryInterval, ‖F s‖ ≤ ε := by
    intro s hs
    refine (norm_coeffOf_sub_coeffOf_le E E' _).trans ?_
    rw [hεdef]
    gcongr
    exact hR s hs
  have hvar := volterra_variation_at (transportCoeff_aestronglyMeasurable γ E)
    (transportCoeff_norm_le γ E hK) hW.1 hW.2 (transportCoeff_aestronglyMeasurable γ E')
    (transportCoeff_norm_le γ E' hK) (transportCoeff_star γ E') hW'.1 hW'.2 hπ hFL hFd hF0 θ hθ
  have hsub : Icc 0 θ ⊆ boundaryInterval := Icc_subset_Icc le_rfl hθ.2
  have hint := norm_volterra_variation_le (transportCoeff_aestronglyMeasurable γ E)
    (transportCoeff_norm_le γ E hK) (transportCoeff_aestronglyMeasurable γ E')
    (transportCoeff_norm_le γ E' hK) hθ.1 (fun s hs => hFb s (hsub hs))
    (fun s hs => norm_le_one_of_mem_unitary (transport_mem_unitary hK hW (hsub hs)))
    (fun s hs => norm_le_one_of_mem_unitary
      (Unitary.star_mem (transport_mem_unitary hK hW' (hsub hs))))
  have hU := transport_mem_unitary hK hW hθ
  have hU' := transport_mem_unitary hK hW' hθ
  have hn1  := norm_le_one_of_mem_unitary hU
  have hn1'  := norm_le_one_of_mem_unitary hU'
  have hn1s  := norm_le_one_of_mem_unitary (Unitary.star_mem hU')
  have hcoef : ∫ s in (0 : ℝ)..θ,
      (‖transportCoeff γ E' s‖ + ‖transportCoeff γ E s‖) ≤
      2 * π * ((Real.sqrt E' + Real.sqrt E) * shiftConst * K) := by
    calc ∫ s in (0)..θ, (‖transportCoeff γ E' s‖ + ‖transportCoeff γ E s‖)
        ≤ ∫ s in (0)..θ, ((Real.sqrt E' + Real.sqrt E) * shiftConst * K) := by
          refine intervalIntegral.integral_mono_on hθ.1 ?_ intervalIntegrable_const
            fun s _ => ?_
          · exact (intervalIntegrable_of_bounded (transportCoeff_aestronglyMeasurable _ _).norm
              (fun s => by rw [norm_norm]; exact transportCoeff_norm_le _ _ hK s) _ _).add
              (intervalIntegrable_of_bounded (transportCoeff_aestronglyMeasurable _ _).norm
              (fun s => by rw [norm_norm]; exact transportCoeff_norm_le _ _ hK s) _ _)
          · have := norm_transportCoeff_le_const hK E' s
            have := norm_transportCoeff_le_const hK E s
            linarith
      _ = θ * ((Real.sqrt E' + Real.sqrt E) * shiftConst * K) := by
          rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
      _ ≤ _ := by
          gcongr
          exact hθ.2
  have hε0  := (norm_nonneg _).trans (hFb 0 ⟨le_rfl, hπ⟩)
  have hkey : ‖star (W' θ) * W θ - 1‖ ≤
      ε * (1 + 2 * π * ((Real.sqrt E' + Real.sqrt E) * shiftConst * K)) := by
    rw [hvar]
    refine (norm_add_le _ _).trans ?_
    have h1 : ‖star (W' θ) * F θ * W θ‖ ≤ ε := by
      refine (norm_mul_le _ _).trans ?_
      refine (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)).trans ?_
      have := hFb θ hθ
      calc ‖star (W' θ)‖ * ‖F θ‖ * ‖W θ‖ ≤ 1 * ε * 1 := by gcongr
        _ = ε := by ring
    have h2 := mul_le_mul_of_nonneg_left hcoef hε0
    nlinarith
  have heq : W' θ - W θ = -(W' θ * (star (W' θ) * W θ - 1)) := by
    rw [mul_sub, ← mul_assoc, (Unitary.mem_iff.mp hU').2, one_mul, mul_one, neg_sub]
  rw [heq, norm_neg]
  refine (norm_mul_le _ _).trans ?_
  calc ‖W' θ‖ * ‖star (W' θ) * W θ - 1‖ ≤ 1 * ‖star (W' θ) * W θ - 1‖ := by gcongr
    _ ≤ _ := by rw [one_mul]; exact hkey

/-- The integrand `W'^* (√E' C₁ G - √E G C₁) W` of the energy variation identity, with
`C₁ = coeffOf 1 γ'` and `G = coeffOf 1 (γ - γ(0))`. -/
def energyIntegrand (γ : ComplexCurve) (E E' : ℝ) (W W' : ℝ → ComplexEnd Ell2) (θ : ℝ) :
    ComplexEnd Ell2 :=
  star (W' θ) * (Real.sqrt E' • (coeffOf 1 (deriv γ θ) * coeffOf 1 (γ θ - γ 0)) -
    Real.sqrt E • (coeffOf 1 (γ θ - γ 0) * coeffOf 1 (deriv γ θ))) * W θ

/-- The energy variation identity for a closed curve:
`V_{E'}^* V_E - 1 = (√E - √E') ∫₀^L W_{E'}^* (√E' C₁ G - √E G C₁) W_E`. -/
lemma energy_variation {γ : ComplexCurve} {K : NNReal} (hK : LipschitzWith K γ)
    (hclosed : γ circlePeriod = γ 0) {E E' : ℝ} {W W' : ℝ → ComplexEnd Ell2}
    (hW : IsTransport γ E W) (hW' : IsTransport γ E' W') :
    star (W' circlePeriod) * W circlePeriod - 1 =
      (Real.sqrt E - Real.sqrt E') •
        ∫ θ in (0 : ℝ)..circlePeriod, energyIntegrand γ E E' W W' θ := by
  have hπ : (0 : ℝ) ≤ 2 * π := by positivity
  set F : ℝ → ComplexEnd Ell2 := fun θ => coeffOf E (γ θ - γ 0) - coeffOf E' (γ θ - γ 0)
    with hF
  have hFL : LipschitzOnWith _ F boundaryInterval :=
    ((lipschitzWith_coeffOf hK E (γ 0)).sub (lipschitzWith_coeffOf hK E' (γ 0))).lipschitzOnWith
  have hFd : ∀ᵐ θ, θ ∈ Ioo 0 circlePeriod →
      HasDerivAt F (transportCoeff γ E θ - transportCoeff γ E' θ) θ := by
    filter_upwards [hK.ae_differentiableAt (μ := volume)] with θ h1 _
    exact (hasDerivAt_coeffOf h1.hasDerivAt E (γ 0)).sub
      (hasDerivAt_coeffOf h1.hasDerivAt E' (γ 0))
  have hF0 : F 0 = 0 := by simp [hF, coeffOf_zero]
  have hF2 : F circlePeriod = 0 := by simp [hF, hclosed, coeffOf_zero]
  rw [volterra_variation (transportCoeff_aestronglyMeasurable γ E) (transportCoeff_norm_le γ E hK)
    hW.1 hW.2 (transportCoeff_aestronglyMeasurable γ E') (transportCoeff_norm_le γ E' hK)
    (transportCoeff_star γ E') hW'.1 hW'.2 hπ hFL hFd hF0 hF2,
    ← intervalIntegral.integral_smul]
  congr 1
  funext s
  simp  [hF, energyIntegrand, transportCoeff_eq_coeffOf]
  rw [coeffOf_eq_sqrt_smul E (γ s - γ 0), coeffOf_eq_sqrt_smul E' (γ s - γ 0),
    coeffOf_eq_sqrt_smul E (deriv γ s), coeffOf_eq_sqrt_smul E' (deriv γ s), ← sub_smul]
  simp only [smul_mul_assoc, mul_smul_comm, smul_sub, smul_smul, mul_sub, sub_mul]
  ring

section
include γ K hK R hR

lemma norm_coeffOf_one_mul_le  (hθ : θ ∈ boundaryInterval) :
    ‖coeffOf 1 (deriv γ θ) * coeffOf 1 (γ θ - γ 0)‖ ≤ shiftConst * K * (shiftConst * R) ∧
      ‖coeffOf 1 (γ θ - γ 0) * coeffOf 1 (deriv γ θ)‖ ≤ shiftConst * K * (shiftConst * R) := by
  have hκ := shiftConst_nonneg
  have hC1 : ‖coeffOf 1 (deriv γ θ)‖ ≤ shiftConst * K := by
    refine (norm_coeffOf_le 1 _).trans ?_
    rw [Real.sqrt_one, one_mul]
    exact mul_le_mul_of_nonneg_left (norm_deriv_le_of_lipschitz hK) hκ
  have hG : ‖coeffOf 1 (γ θ - γ 0)‖ ≤ shiftConst * R := by
    refine (norm_coeffOf_le 1 _).trans ?_
    bound
  have hGn := norm_nonneg (coeffOf 1 (γ θ - γ 0))
  have hCn := norm_nonneg (coeffOf 1 (deriv γ θ))
  refine ⟨(norm_mul_le _ _).trans (mul_le_mul hC1 hG hGn (by positivity)), ?_⟩
  rw [mul_comm (shiftConst * K)]
  exact?

lemma norm_energyCore_le (E E' : ℝ) {θ : ℝ} (hθ : θ ∈ boundaryInterval) :
    ‖Real.sqrt E' • (coeffOf 1 (deriv γ θ) * coeffOf 1 (γ θ - γ 0)) -
      Real.sqrt E • (coeffOf 1 (γ θ - γ 0) * coeffOf 1 (deriv γ θ))‖ ≤
      (Real.sqrt E' + Real.sqrt E) * (shiftConst * K * (shiftConst * R)) := by
  obtain ⟨h1, h2⟩ := norm_coeffOf_one_mul_le hK hR hθ
  refine (norm_sub_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    Real.norm_of_nonneg (Real.sqrt_nonneg _), add_mul]
  gcongr

lemma norm_energyIntegrand_le  
    (hW : IsTransport γ E W) (hW' : IsTransport γ E' W')  (hθ : θ ∈ boundaryInterval) :
    ‖energyIntegrand γ E E' W W' θ‖ ≤
      (Real.sqrt E' + Real.sqrt E) * (shiftConst * K * (shiftConst * R)) := by
  have hn1  := norm_le_one_of_mem_unitary (transport_mem_unitary hK hW hθ)
  have hn1s  :=
    norm_le_one_of_mem_unitary (Unitary.star_mem (transport_mem_unitary hK hW' hθ))
  refine (norm_mul_le _ _).trans ?_
  refine (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)).trans ?_
  have hX := norm_energyCore_le hK hR E E' hθ
  have h0 := (norm_nonneg _).trans hX
  calc _ ≤ 1 * ((Real.sqrt E' + Real.sqrt E) * (shiftConst * K * (shiftConst * R))) * 1 := by
        gcongr
    _ = _ := by ring

end


lemma aestronglyMeasurable_energy_aux {μ : Measure ℝ} {W W' C G : ℝ → ComplexEnd Ell2}
    (h4 : AEStronglyMeasurable (fun θ => star (W' θ)) μ) (hC : AEStronglyMeasurable C μ)
    (hG : AEStronglyMeasurable G μ) (hW : AEStronglyMeasurable W μ) (a b : ℝ) :
    AEStronglyMeasurable (fun θ => star (W' θ) * (a • (C θ * G θ) - b • (G θ * C θ)) * W θ) μ :=
  (h4.mul (((hC.mul hG).const_smul a).sub ((hG.mul hC).const_smul b))).mul hW

lemma intervalIntegrable_energyIntegrand   (hK : LipschitzWith K γ)
     
    (hW : IsTransport γ E W) (hW' : IsTransport γ E' W') :
    IntervalIntegrable (energyIntegrand γ E E' W W') volume 0 circlePeriod := by
  have hπ : (0 : ℝ) ≤ 2 * π := by positivity
  obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := boundaryInterval)
    (f := fun θ => γ θ - γ 0) (hK.continuous.sub continuous_const).continuousOn
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hπ]
  have hG  :=
    (lipschitzWith_coeffOf hK 1 (γ 0)).continuous
  have hC1 : AEStronglyMeasurable (fun θ => coeffOf 1 (deriv γ θ))
      (volume.restrict boundaryInterval) := (transportCoeff_aestronglyMeasurable γ 1).restrict
  have hGm : AEStronglyMeasurable (fun θ => coeffOf 1 (γ θ - γ 0))
      (volume.restrict boundaryInterval) := hG.continuousOn.aestronglyMeasurable measurableSet_Icc
  have h4 : AEStronglyMeasurable (fun θ => star (W' θ)) (volume.restrict boundaryInterval) :=
    hW'.1.star.aestronglyMeasurable measurableSet_Icc
  have hm : AEStronglyMeasurable (energyIntegrand γ E E' W W')
      (volume.restrict boundaryInterval) :=
    aestronglyMeasurable_energy_aux h4 hC1 hGm (hW.1.aestronglyMeasurable measurableSet_Icc) _ _
  exact Integrable.of_bound hm _ ((ae_restrict_iff' measurableSet_Icc).mpr
    (Eventually.of_forall fun θ hθ => norm_energyIntegrand_le hK hR hW hW' hθ))

include γ K hK R hR in
/-- The integral in the energy variation identity is continuous in the second energy. -/
lemma norm_integral_energyIntegrand_sub_le {E E' : ℝ}
    {W W' : ℝ → ComplexEnd Ell2} (hW : IsTransport γ E W) (hW' : IsTransport γ E' W') :
    ‖(∫ θ in (0 : ℝ)..circlePeriod, energyIntegrand γ E E' W W' θ) -
        ∫ θ in (0 : ℝ)..circlePeriod, energyIntegrand γ E E W W θ‖ ≤
      |Real.sqrt E - Real.sqrt E'| * (shiftConst * K * (shiftConst * R)) *
        ((Real.sqrt E' + Real.sqrt E) * (shiftConst * R *
          (1 + 2 * π * ((Real.sqrt E' + Real.sqrt E) * shiftConst * K))) + 1) * circlePeriod := by
  have hπ : (0 : ℝ) ≤ 2 * π := by positivity
  rw [← intervalIntegral.integral_sub (intervalIntegrable_energyIntegrand hK hW hW')
    (intervalIntegrable_energyIntegrand hK hW hW)]
  refine (intervalIntegral.norm_integral_le_of_norm_le_const fun θ hθ => ?_).trans
    (by rw [sub_zero, abs_of_nonneg hπ])
  have hθ' : θ ∈ boundaryInterval := by
    grind
  set a := shiftConst * K * (shiftConst * R)
  set X' := Real.sqrt E' • (coeffOf 1 (deriv γ θ) * coeffOf 1 (γ θ - γ 0)) -
      Real.sqrt E • (coeffOf 1 (γ θ - γ 0) * coeffOf 1 (deriv γ θ))
  have hX'  := norm_energyCore_le hK hR E E' hθ'
  have hXX : energyIntegrand γ E E' W W' θ - energyIntegrand γ E E W W θ =
      (star (W' θ) - star (W θ)) * X' * W θ +
        star (W θ) * ((Real.sqrt E' - Real.sqrt E) •
          (coeffOf 1 (deriv γ θ) * coeffOf 1 (γ θ - γ 0))) * W θ := by
    simp only [energyIntegrand, X', sub_smul, smul_sub, mul_sub, sub_mul, mul_smul_comm]
    abel
  rw [hXX]
  have hd := norm_transport_sub_le hK hR hW hW' hθ'
  have hn1  := norm_le_one_of_mem_unitary (transport_mem_unitary hK hW hθ')
  have hn1s  :=
    norm_le_one_of_mem_unitary (Unitary.star_mem (transport_mem_unitary hK hW hθ'))
  have ha := (norm_coeffOf_one_mul_le hK hR hθ').1
  have ha0  := (norm_nonneg _).trans ha
  refine (norm_add_le _ _).trans ?_
  have e1 : ‖(star (W' θ) - star (W θ)) * X' * W θ‖ ≤ |Real.sqrt E - Real.sqrt E'| * shiftConst * R *
      (1 + 2 * π * ((Real.sqrt E' + Real.sqrt E) * shiftConst * K)) *
        ((Real.sqrt E' + Real.sqrt E) * a) := by
    refine (norm_mul_le _ _).trans ?_
    refine (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)).trans ?_
    rw [← star_sub, norm_star]
    calc ‖W' θ - W θ‖ * ‖X'‖ * ‖W θ‖ ≤ ‖W' θ - W θ‖ * ‖X'‖ * 1 := by gcongr
      _ ≤ _ := by
        rw [mul_one]
        exact mul_le_mul hd hX' (norm_nonneg _) ((norm_nonneg _).trans hd)
  have e2 : ‖star (W θ) * ((Real.sqrt E' - Real.sqrt E) •
      (coeffOf 1 (deriv γ θ) * coeffOf 1 (γ θ - γ 0))) * W θ‖ ≤
      |Real.sqrt E - Real.sqrt E'| * a := by
    refine (norm_mul_le _ _).trans ?_
    refine (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)).trans ?_
    rw [norm_smul, Real.norm_eq_abs, abs_sub_comm]
    calc ‖star (W θ)‖ * (|Real.sqrt E - Real.sqrt E'| *
          ‖coeffOf 1 (deriv γ θ) * coeffOf 1 (γ θ - γ 0)‖) * ‖W θ‖
        ≤ 1 * (|Real.sqrt E - Real.sqrt E'| * a) * 1 := by gcongr
      _ = _ := by ring
  linarith

end


section
variable {γ } {K } (hK : LipschitzWith K γ) {Ws : ℝ → ℝ → ComplexEnd Ell2} (hWs : ∀ E, IsTransport γ E (Ws E)) (E : ℝ)
include γ K hK Ws hWs E

/-- Continuity of the transport in the energy, uniformly on `[0, L]`. -/
lemma tendsto_transport_energy 
    (hθ : θ ∈ boundaryInterval) : Tendsto (fun E' => Ws E' θ) (𝓝 E) (𝓝 (Ws E θ)) := by
  obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := boundaryInterval)
    (f := fun θ => γ θ - γ 0) (hK.continuous.sub continuous_const).continuousOn
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hc : Continuous (fun E' => |Real.sqrt E - Real.sqrt E'| * shiftConst * R *
      (1 + 2 * π * ((Real.sqrt E' + Real.sqrt E) * shiftConst * K))) := by fun_prop
  have hb := hc.tendsto E
  simp   at hb
  exact squeeze_zero (fun _ => norm_nonneg _)
    (fun E' => norm_transport_sub_le hK hR (hWs E) (hWs E') hθ) hb

/-- Continuity of the integral of the energy variation identity in the second energy. -/
lemma tendsto_integral_energyIntegrand :
    Tendsto (fun E' => ∫ θ in (0 : ℝ)..circlePeriod, energyIntegrand γ E E' (Ws E) (Ws E') θ) (𝓝 E)
      (𝓝 (∫ θ in (0 : ℝ)..circlePeriod, energyIntegrand γ E E (Ws E) (Ws E) θ)) := by
  obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := boundaryInterval)
    (f := fun θ => γ θ - γ 0) (hK.continuous.sub continuous_const).continuousOn
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hc : Continuous (fun E' => |Real.sqrt E - Real.sqrt E'| *
      (shiftConst * K * (shiftConst * R)) * ((Real.sqrt E' + Real.sqrt E) * (shiftConst * R *
        (1 + 2 * π * ((Real.sqrt E' + Real.sqrt E) * shiftConst * K))) + 1) * circlePeriod) := by
    fun_prop
  have hb := hc.tendsto E
  simp   at hb
  exact squeeze_zero (fun _ => norm_nonneg _)
    (fun E' => norm_integral_energyIntegrand_sub_le hK hR (hWs E) (hWs E')) hb

end


section
variable {γ } {K } (hK : LipschitzWith K γ) (hclosed : γ circlePeriod = γ 0) {Ws : ℝ → ℝ → ComplexEnd Ell2} (hWs : ∀ E, IsTransport γ E (Ws E)) {E : ℝ} (hE : 0 < E)

include γ K hK hclosed Ws hWs E hE in
/-- **Lemma 4.7 (curvature formula).** For a closed Lipschitz curve and `E > 0`, the endpoint
`V_E = W_E(L)` of the transport is differentiable in the energy (in operator norm), with
`∂_E V_E = -i V_E Q_E`, `Q_E = (1/4) ∫₀^L b W_E^* D_N W_E dθ`. -/
theorem hasDerivAt_transport_energy :
    HasDerivAt (fun E => Ws E circlePeriod)
      (-(Complex.I • (Ws E circlePeriod * curvatureOp γ (Ws E)))) E := by
  have hπ : (0 : ℝ) ≤ 2 * π := by positivity
  have h2π : circlePeriod ∈ boundaryInterval := ⟨hπ, le_rfl⟩
  set s := Real.sqrt E with hsdef
  have hs  := Real.sqrt_pos.mpr hE
  set V : ℝ → ComplexEnd Ell2 := fun E' => Ws E' circlePeriod with hVdef
  set I : ℝ → ComplexEnd Ell2 :=
    fun E' => ∫ θ in (0)..circlePeriod, energyIntegrand γ E E' (Ws E) (Ws E') θ with hIdef
  have hslope : ∀ E', 0 < E' → E' ≠ E →
      slope V E E' = (Real.sqrt E' + s)⁻¹ • (V E' * I E') := by
    intro E' hpos hne
    have hvar := energy_variation hK hclosed (hWs E) (hWs E')
    have hU := transport_mem_unitary hK (hWs E') h2π
    have hVV  := (Unitary.mem_iff.mp hU).2
    have hdiff : Ws E' circlePeriod - Ws E circlePeriod = (Real.sqrt E' - s) •
        (Ws E' circlePeriod * ∫ θ in (0 : ℝ)..circlePeriod, energyIntegrand γ E E' (Ws E) (Ws E') θ) := by
      have : Ws E' circlePeriod - Ws E circlePeriod =
          -(Ws E' circlePeriod * (star (Ws E' circlePeriod) * Ws E circlePeriod - 1)) := by
        rw [mul_sub, ← mul_assoc, hVV, one_mul, mul_one, neg_sub]
      rw [this, hvar, mul_smul_comm, ← neg_smul, neg_sub]
    rw [slope_def_module, hdiff, smul_smul]
    congr 1
    have hne' : Real.sqrt E' - s ≠ 0 := by
      intro h
      apply hne
      have h2 := congrArg (· ^ 2) (sub_eq_zero.mp h)
      simp only [hsdef, Real.sq_sqrt hpos.le, Real.sq_sqrt hE.le] at h2
      exact h2
    have hEE : E' - E = (Real.sqrt E' - s) * (Real.sqrt E' + s) := by
      rw [hsdef]
      ring_nf
      rw [Real.sq_sqrt hpos.le, Real.sq_sqrt hE.le]
    rw [hEE]
    field_simp
  have hV  := tendsto_transport_energy hK hWs E h2π
  have hI  := tendsto_integral_energyIntegrand hK hWs E
  have hsq  :=
    ((Real.continuous_sqrt.tendsto E).add_const s).inv₀ (by positivity)
  have hval : (s + s)⁻¹ • (V E * I E) = -(Complex.I • (Ws E circlePeriod * curvatureOp γ (Ws E))) := by
    simp only [hVdef, hIdef]
    have hIE : ∫ θ in (0 : ℝ)..circlePeriod, energyIntegrand γ E E (Ws E) (Ws E) θ =
        ((s : ℂ) * (-(Complex.I / 2))) •
          ∫ θ in (0 : ℝ)..circlePeriod, areaDensity γ θ • (star (Ws E θ) * diagN * Ws E θ) := by
      rw [← intervalIntegral.integral_smul]
      congr 1
      funext θ
      simp only [energyIntegrand]
      rw [← smul_sub, coeffOf_one_commutator, areaDensity, mul_comm (conj _) (deriv γ θ)]
      simp only [smul_mul_assoc, mul_smul_comm, real_smul_eq_coe_smul_clm, smul_smul]
      congr 1
      ring
    rw [hIE, curvatureOp]
    simp only [mul_smul_comm, real_smul_eq_coe_smul_clm, smul_smul, ← neg_smul]
    congr 1
    have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    push_cast
    field_simp
    ring
  rw [hasDerivAt_iff_tendsto_slope, ← hval]
  refine ((hsq.smul (hV.mul hI)).mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Ioi_mem_nhds hE)] with E' hne hpos
  exact (hslope E' hpos hne).symm

/-- `D_N` is self-adjoint. -/
lemma star_diagN : star diagN = diagN := by
  rw [← shift_commutator, star_sub, star_mul, star_mul, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_adjoint]

lemma areaDensity_aestronglyMeasurable  (hγ : Continuous γ) :
    AEStronglyMeasurable (areaDensity γ) volume := by
  have h1 : AEStronglyMeasurable (fun θ => conj (γ θ - γ 0)) volume :=
    (Complex.continuous_conj.comp (hγ.sub continuous_const)).aestronglyMeasurable
  exact Complex.continuous_im.comp_aestronglyMeasurable
    (h1.mul (measurable_deriv γ).aestronglyMeasurable)

lemma abs_areaDensity_le   (hK : LipschitzWith K γ) 
    (hR : ∀ θ ∈ boundaryInterval, ‖γ θ - γ 0‖ ≤ R)  (hθ : θ ∈ boundaryInterval) :
    |areaDensity γ θ| ≤ R * K := by
  refine (Complex.abs_im_le_norm _).trans ?_
  rw [norm_mul, Complex.norm_conj]
  exact mul_le_mul (hR θ hθ) (norm_deriv_le_of_lipschitz hK) (norm_nonneg _)
    ((norm_nonneg _).trans (hR θ hθ))

/-- Integrability of `θ ↦ b(θ) U(θ)^* D_N U(θ)` for a continuous unitary family `U` and a
bounded measurable weight `b`. -/
lemma intervalIntegrable_conj_diagN {U : ℝ → ComplexEnd Ell2}
    (hU : ContinuousOn U boundaryInterval)
    (hunit : ∀ θ ∈ boundaryInterval, U θ ∈ unitary (ComplexEnd Ell2))
    {b : RealMap} (hb : AEStronglyMeasurable b volume) {B : ℝ}
    (hbB : ∀ θ ∈ boundaryInterval, |b θ| ≤ B) :
    IntervalIntegrable (fun θ => b θ • (star (U θ) * diagN * U θ)) volume 0 circlePeriod := by
  have hπ : (0 : ℝ) ≤ 2 * π := by positivity
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hπ]
  have hm : AEStronglyMeasurable (fun θ => b θ • (star (U θ) * diagN * U θ))
      (volume.restrict boundaryInterval) :=
    hb.restrict.smul (((hU.star.aestronglyMeasurable measurableSet_Icc).mul_const _).mul
      (hU.aestronglyMeasurable measurableSet_Icc))
  refine Integrable.of_bound hm (B * ‖diagN‖) ((ae_restrict_iff' measurableSet_Icc).mpr
    (Eventually.of_forall fun θ hθ => ?_))
  have h1  := norm_le_one_of_mem_unitary (hunit θ hθ)
  have h2  := norm_le_one_of_mem_unitary (Unitary.star_mem (hunit θ hθ))
  rw [norm_smul, Real.norm_eq_abs]
  have hB  := (abs_nonneg _).trans (hbB θ hθ)
  gcongr
  · exact hbB θ hθ
  · calc ‖star (U θ) * diagN * U θ‖ ≤ ‖star (U θ)‖ * ‖diagN‖ * ‖U θ‖ :=
          (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ 1 * ‖diagN‖ * 1 := by gcongr
      _ = ‖diagN‖ := by ring

/-- The curvature operator `Q_E` is self-adjoint. -/
theorem curvatureOp_star   (hK : LipschitzWith K γ) 
     (hW : IsTransport γ E W) :
    star (curvatureOp γ W) = curvatureOp γ W := by
  obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := boundaryInterval)
    (f := fun θ => γ θ - γ 0) (hK.continuous.sub continuous_const).continuousOn
  have hint := intervalIntegrable_conj_diagN hW.1 (fun θ hθ => transport_mem_unitary hK hW hθ)
    (areaDensity_aestronglyMeasurable hK.continuous) (fun θ hθ => abs_areaDensity_le hK hR hθ)
  unfold curvatureOp
  rw [star_smul, star_trivial]
  congr 1
  have := (starL' ℝ (A := ComplexEnd Ell2)).toContinuousLinearMap.intervalIntegral_comp_comm hint
  simp only [ContinuousLinearEquiv.coe_coe, starL'_apply] at this
  rw [← this]
  congr 1
  funext θ
  rw [star_smul, star_trivial, star_mul, star_mul, star_star, star_diagN, mul_assoc]

include γ K hK hclosed Ws hWs E hE in
/-- Lemma 4.7: the monodromy `U_E = V_E^*` is differentiable in `E > 0` (in operator norm),
with `∂_E U_E = i Q_E U_E`. -/
theorem hasDerivAt_monodromy_energy :
    HasDerivAt (fun E => monodromy (Ws E))
      (Complex.I • (curvatureOp γ (Ws E) * monodromy (Ws E))) E := by
  have h := (hasDerivAt_transport_energy hK hclosed hWs hE).star
  simp  [monodromy, ← ContinuousLinearMap.star_eq_adjoint]
  convert h using 1
  rw [star_neg, star_smul, star_mul, curvatureOp_star hK (hWs E), Complex.star_def,
    Complex.conj_I, neg_smul, neg_neg]

end


end PolyaNeumann

end
