module

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

/-- A Lipschitz curve has bounded displacement from its initial point. -/
lemma exists_curve_displacement_bound {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) :
    ∃ R : ℝ, ∀ θ ∈ Icc 0 (2 * π), ‖γ θ - γ 0‖ ≤ R :=
  isCompact_Icc.exists_bound_of_continuousOn (hK.continuous.sub continuous_const).continuousOn

section

variable (γ : ℝ → ℂ)
include γ

/-- The signed area density `b(θ) = Im(conj(γ(θ) - γ(0)) γ'(θ))`; for a positively oriented
Jordan parametrization `∫₀^L b = 2|Ω|`. -/
def areaDensity  (θ : ℝ) : ℝ := (conj (γ θ - γ 0) * deriv γ θ).im

/-- The curvature operator `Q_E = (1/4) ∫₀^L b W^* D_N W dθ`. -/
def curvatureOp  (W : ℝ → Ell2 →L[ℂ] Ell2) : Ell2 →L[ℂ] Ell2 :=
  (1 / 4 : ℝ) • ∫ θ in (0 : ℝ)..(2 * π), areaDensity γ θ • (star (W θ) * diagN * W θ)

end

lemma coeffOf_eq_sqrt_smul (E : ℝ) (z : ℂ) : coeffOf E z = Real.sqrt E • coeffOf 1 z := by
  unfold coeffOf
  rw [Real.sqrt_one, real_smul_eq_coe_smul_clm, smul_smul]
  congr 1
  push_cast
  ring

/-- The commutator identity `[C₁(a), C₁(b)] = -(i/2) Im(a conj b) D_N`. -/
lemma coeffOf_one_commutator (a b : ℂ) :
    coeffOf 1 a * coeffOf 1 b - coeffOf 1 b * coeffOf 1 a =
      (-(Complex.I / 2) * ((a * conj b).im : ℂ)) • diagN := by
  have hD := shift_commutator
  set S := shiftN
  set T := ContinuousLinearMap.adjoint shiftN
  have him : ((a * conj b).im : ℂ) = (a * conj b - conj a * b) / (2 * Complex.I) := by
    rw [Complex.im_eq_sub_conj]; simp
  rw [him, ← hD]
  unfold coeffOf
  simp only [Real.sqrt_one, Complex.ofReal_one, mul_one, add_mul, mul_add,
    smul_add, smul_sub, smul_mul_assoc, mul_smul_comm, smul_smul]
  match_scalars <;> field_simp <;> ring_nf <;> simp [Complex.I_sq]

/-- Uniform continuity of the transport in the energy:
`‖W_{E'}(θ) - W_E(θ)‖ ≤ |√E - √E'| κ R (1 + L (√E' + √E) κ K)` on `[0, L]`. -/
lemma norm_transport_sub_le {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) {R : ℝ}
    (hR : ∀ θ ∈ Icc 0 (2 * π), ‖γ θ - γ 0‖ ≤ R) {E E' : ℝ} {W W' : ℝ → Ell2 →L[ℂ] Ell2}
    (hW : IsTransport γ E W) (hW' : IsTransport γ E' W') {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * π)) :
    ‖W' θ - W θ‖ ≤ |Real.sqrt E - Real.sqrt E'| * shiftConst * R *
      (1 + 2 * π * ((Real.sqrt E' + Real.sqrt E) * shiftConst * K)) := by
  let ε := |Real.sqrt E - Real.sqrt E'| * shiftConst * R
  have hκ := shiftConst_nonneg
  have hε : ∀ s ∈ Icc 0 (2 * π), ‖transportPrimitive γ γ E E' s‖ ≤ ε := fun s hs =>
    (norm_coeffOf_sub_coeffOf_le E E' _).trans (by dsimp [ε]; gcongr; exact hR s hs)
  have hi : ∫ s in (0 : ℝ)..θ, (‖transportCoeff γ E' s‖ + ‖transportCoeff γ E s‖) ≤
      2 * π * ((Real.sqrt E' + Real.sqrt E) * shiftConst * K) := by
    let C := (Real.sqrt E' + Real.sqrt E) * shiftConst * K
    calc _ ≤ ∫ _ in (0 : ℝ)..θ, C :=
          intervalIntegral.integral_mono_on hθ.1
            ((intervalIntegrable_norm_transportCoeff hK E' 0 θ).add
              (intervalIntegrable_norm_transportCoeff hK E 0 θ)) intervalIntegrable_const (fun s _ => by
                dsimp [C]; rw [add_mul, add_mul]; exact add_le_add
                  (norm_transportCoeff_le_const hK E' s) (norm_transportCoeff_le_const hK E s))
      _ = θ * C := by simp [intervalIntegral.integral_const]
      _ ≤ _ := mul_le_mul_of_nonneg_right hθ.2 (by dsimp [C]; positivity)
  have hε0 := (norm_nonneg _).trans (hε θ hθ)
  exact (norm_transport_variation_le hK hK hW hW' hε hθ).trans
    (by nlinarith [hε θ hθ, mul_le_mul_of_nonneg_left hi hε0])

/-- The integrand `W'^* (√E' C₁ G - √E G C₁) W` of the energy variation identity, with
`C₁ = coeffOf 1 γ'` and `G = coeffOf 1 (γ - γ(0))`. -/
def energyIntegrand (γ : ℝ → ℂ) (E E' : ℝ) (W W' : ℝ → Ell2 →L[ℂ] Ell2) (θ : ℝ) :
    Ell2 →L[ℂ] Ell2 :=
  star (W' θ) * (Real.sqrt E' • (coeffOf 1 (deriv γ θ) * coeffOf 1 (γ θ - γ 0)) -
    Real.sqrt E • (coeffOf 1 (γ θ - γ 0) * coeffOf 1 (deriv γ θ))) * W θ

/-- The energy variation identity for a closed curve:
`V_{E'}^* V_E - 1 = (√E - √E') ∫₀^L W_{E'}^* (√E' C₁ G - √E G C₁) W_E`. -/
lemma energy_variation {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
    (hclosed : γ (2 * π) = γ 0) {E E' : ℝ} {W W' : ℝ → Ell2 →L[ℂ] Ell2}
    (hW : IsTransport γ E W) (hW' : IsTransport γ E' W') :
    star (W' (2 * π)) * W (2 * π) - 1 =
      (Real.sqrt E - Real.sqrt E') •
        ∫ θ in (0 : ℝ)..(2 * π), energyIntegrand γ E E' W W' θ := by
  rw [transport_variation_at hK hK hW hW' ⟨Real.two_pi_pos.le, le_rfl⟩]
  simp only [transportPrimitive, hclosed, sub_self, coeffOf_zero, mul_zero, zero_mul, zero_add,
    ← intervalIntegral.integral_smul]
  congr 1
  funext s
  simp only [energyIntegrand, transportCoeff_eq_coeffOf]
  rw [coeffOf_eq_sqrt_smul E (γ s - γ 0), coeffOf_eq_sqrt_smul E' (γ s - γ 0),
    coeffOf_eq_sqrt_smul E (deriv γ s), coeffOf_eq_sqrt_smul E' (deriv γ s), ← sub_smul]
  simp only [smul_mul_assoc, mul_smul_comm, smul_sub, smul_smul, mul_sub, sub_mul]
  congr 1; congr 1; ring

section

variable {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) {R : ℝ} (hR : ∀ θ ∈ Icc 0 (2 * π), ‖γ θ - γ 0‖ ≤ R)
include γ K hK R hR

lemma norm_coeffOf_one_mul_le  {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * π)) :
    ‖coeffOf 1 (deriv γ θ) * coeffOf 1 (γ θ - γ 0)‖ ≤ shiftConst * K * (shiftConst * R) ∧
      ‖coeffOf 1 (γ θ - γ 0) * coeffOf 1 (deriv γ θ)‖ ≤ shiftConst * K * (shiftConst * R) := by
  have hκ := shiftConst_nonneg
  have hC1 : ‖coeffOf 1 (deriv γ θ)‖ ≤ shiftConst * K := by
    refine (norm_coeffOf_le 1 _).trans ?_
    rw [Real.sqrt_one, one_mul]
    exact mul_le_mul_of_nonneg_left (norm_deriv_le_of_lipschitz hK) hκ
  have hG : ‖coeffOf 1 (γ θ - γ 0)‖ ≤ shiftConst * R := by
    refine (norm_coeffOf_le 1 _).trans ?_
    rw [Real.sqrt_one, one_mul]
    exact mul_le_mul_of_nonneg_left (hR θ hθ) hκ
  exact ⟨norm_mul_le_of_le hC1 hG, by simpa [mul_comm] using norm_mul_le_of_le hG hC1⟩

lemma norm_energyCore_le  (E E' : ℝ) {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * π)) :
    ‖Real.sqrt E' • (coeffOf 1 (deriv γ θ) * coeffOf 1 (γ θ - γ 0)) -
      Real.sqrt E • (coeffOf 1 (γ θ - γ 0) * coeffOf 1 (deriv γ θ))‖ ≤
      (Real.sqrt E' + Real.sqrt E) * (shiftConst * K * (shiftConst * R)) := by
  obtain ⟨h1, h2⟩ := norm_coeffOf_one_mul_le hK hR hθ
  refine (norm_sub_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    Real.norm_of_nonneg (Real.sqrt_nonneg _), add_mul]
  gcongr

lemma norm_energyIntegrand_le  {E E' : ℝ} {W W' : ℝ → Ell2 →L[ℂ] Ell2}
    (hW : IsTransport γ E W) (hW' : IsTransport γ E' W') {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * π)) :
    ‖energyIntegrand γ E E' W W' θ‖ ≤
      (Real.sqrt E' + Real.sqrt E) * (shiftConst * K * (shiftConst * R)) := by
  unfold energyIntegrand
  exact le_trans (((CStarRing.norm_mul_coe_unitary _ ⟨_, transport_mem_unitary hK hW hθ⟩).trans
    (CStarRing.norm_coe_unitary_mul ⟨_, Unitary.star_mem (transport_mem_unitary hK hW' hθ)⟩ _)).le)
    (norm_energyCore_le hK hR E E' hθ)

end

private lemma aestronglyMeasurable_energy_aux {μ : Measure ℝ} {W W' C G : ℝ → Ell2 →L[ℂ] Ell2}
    (h4 : AEStronglyMeasurable (fun θ => star (W' θ)) μ) (hC : AEStronglyMeasurable C μ)
    (hG : AEStronglyMeasurable G μ) (hW : AEStronglyMeasurable W μ) (a b : ℝ) :
    AEStronglyMeasurable (fun θ => star (W' θ) * (a • (C θ * G θ) - b • (G θ * C θ)) * W θ) μ :=
  (h4.mul (((hC.mul hG).const_smul a).sub ((hG.mul hC).const_smul b))).mul hW

private lemma aestronglyMeasurable_energyIntegrand {γ : ℝ → ℂ} {K : NNReal}
    (hK : LipschitzWith K γ) {E E' : ℝ} {W W' : ℝ → Ell2 →L[ℂ] Ell2}
    (hW : IsTransport γ E W) (hW' : IsTransport γ E' W') :
    AEStronglyMeasurable (energyIntegrand γ E E' W W') (volume.restrict (Icc 0 (2 * π))) := by
  have hG := (lipschitzWith_coeffOf hK 1 (γ 0)).continuous.aestronglyMeasurable (μ := volume) |>.restrict
    (s := Icc 0 (2 * π))
  have hC : AEStronglyMeasurable (fun θ => coeffOf 1 (deriv γ θ))
      (volume.restrict (Icc 0 (2 * π))) := (transportCoeff_aestronglyMeasurable γ 1).restrict
  have hW₁ := hW.1.aestronglyMeasurable (μ := volume) measurableSet_Icc
  have hW₂ := hW'.1.star.aestronglyMeasurable (μ := volume) measurableSet_Icc
  exact aestronglyMeasurable_energy_aux hW₂ hC hG hW₁ _ _


section

variable {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) {Ws : ℝ → ℝ → Ell2 →L[ℂ] Ell2} (hWs : ∀ E, IsTransport γ E (Ws E)) (E : ℝ)
include γ K hK Ws hWs E

/-- Continuity of the transport in the energy, uniformly on `[0, L]`. -/
lemma tendsto_transport_energy  {θ : ℝ}
    (hθ : θ ∈ Icc 0 (2 * π)) : Tendsto (fun E' => Ws E' θ) (𝓝 E) (𝓝 (Ws E θ)) := by
  obtain ⟨R, hR⟩ := exists_curve_displacement_bound hK
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hc : Continuous (fun E' => |Real.sqrt E - Real.sqrt E'| * shiftConst * R *
      (1 + 2 * π * ((Real.sqrt E' + Real.sqrt E) * shiftConst * K))) := by fun_prop
  have hb := hc.tendsto E
  simp  [sub_self, abs_zero, zero_mul] at hb
  exact squeeze_zero (fun _ => norm_nonneg _)
    (fun E' => norm_transport_sub_le hK hR (hWs E) (hWs E') hθ) hb

/-- Continuity of the integral of the energy variation identity in the second energy. -/
lemma tendsto_integral_energyIntegrand  :
    Tendsto (fun E' => ∫ θ in (0 : ℝ)..(2 * π), energyIntegrand γ E E' (Ws E) (Ws E') θ) (𝓝 E)
      (𝓝 (∫ θ in (0 : ℝ)..(2 * π), energyIntegrand γ E E (Ws E) (Ws E) θ)) := by
  obtain ⟨R, hR⟩ := exists_curve_displacement_bound hK
  have hR₀ := (norm_nonneg _).trans (hR 0 ⟨le_rfl, Real.two_pi_pos.le⟩)
  have hκ := shiftConst_nonneg
  let B := (Real.sqrt (E + 1) + Real.sqrt E) * (shiftConst * K * (shiftConst * R))
  simp only [intervalIntegral.integral_of_le Real.two_pi_pos.le, ← integral_Icc_eq_integral_Ioc]
  apply MeasureTheory.tendsto_integral_filter_of_dominated_convergence (fun _ => B)
  · exact .of_forall fun E' => aestronglyMeasurable_energyIntegrand hK (hWs E) (hWs E')
  · filter_upwards [Iio_mem_nhds (show E < E + 1 by linarith)] with E' hE'
    refine ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ =>
      (norm_energyIntegrand_le hK hR (hWs E) (hWs E') hθ).trans ?_
    dsimp [B]
    gcongr
    exact (mem_Iio.mp hE').le
  · exact integrable_const _
  · refine ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ => ?_
    have hW := tendsto_transport_energy hK hWs E hθ
    have hE := Real.continuous_sqrt.tendsto E
    unfold energyIntegrand
    exact (hW.star.mul ((hE.smul tendsto_const_nhds).sub tendsto_const_nhds)).mul
      tendsto_const_nhds

end

/-- **Lemma 4.7 (curvature formula).** For a closed Lipschitz curve and `E > 0`, the endpoint
`V_E = W_E(L)` of the transport is differentiable in the energy (in operator norm), with
`∂_E V_E = -i V_E Q_E`, `Q_E = (1/4) ∫₀^L b W_E^* D_N W_E dθ`. -/
theorem hasDerivAt_transport_energy {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
    (hclosed : γ (2 * π) = γ 0) {Ws : ℝ → ℝ → Ell2 →L[ℂ] Ell2}
    (hWs : ∀ E, IsTransport γ E (Ws E)) {E : ℝ} (hE : 0 < E) :
    HasDerivAt (fun E => Ws E (2 * π))
      (-(Complex.I • (Ws E (2 * π) * curvatureOp γ (Ws E)))) E := by
  have hπ : (0 : ℝ) ≤ 2 * π := by positivity
  have h2π : (2 * π) ∈ Icc 0 (2 * π) := ⟨hπ, le_rfl⟩
  obtain ⟨R, hR⟩ := exists_curve_displacement_bound hK
  set s := Real.sqrt E with hsdef
  have hs := Real.sqrt_pos.mpr hE
  set V : ℝ → Ell2 →L[ℂ] Ell2 := fun E' => Ws E' (2 * π) with hVdef
  set I : ℝ → Ell2 →L[ℂ] Ell2 :=
    fun E' => ∫ θ in (0 : ℝ)..(2 * π), energyIntegrand γ E E' (Ws E) (Ws E') θ with hIdef
  have hslope : ∀ E', 0 < E' → E' ≠ E →
      slope V E E' = (Real.sqrt E' + s)⁻¹ • (V E' * I E') := by
    intro E' hpos hne
    simp  [hIdef]
    have hvar := energy_variation hK hclosed (hWs E) (hWs E')
    have hU := transport_mem_unitary hK (hWs E') h2π
    have hVV := (Unitary.mem_iff.mp hU).2
    have hdiff : Ws E' (2 * π) - Ws E (2 * π) = (Real.sqrt E' - s) •
        (Ws E' (2 * π) * ∫ θ in (0 : ℝ)..(2 * π), energyIntegrand γ E E' (Ws E) (Ws E') θ) := by
      have : Ws E' (2 * π) - Ws E (2 * π) =
          -(Ws E' (2 * π) * (star (Ws E' (2 * π)) * Ws E (2 * π) - 1)) := by
        rw [mul_sub, ← mul_assoc, hVV, one_mul, mul_one, neg_sub]
      rw [this, hvar, mul_smul_comm, ← neg_smul, neg_sub]
    rw [slope_def_module, hdiff, smul_smul]
    congr 1
    have hne' : Real.sqrt E' - s ≠ 0 := by
      intro h
      apply hne
      have h2 := congrArg (· ^ 2) (sub_eq_zero.mp h)
      simp  [hsdef, Real.sq_sqrt hpos.le, Real.sq_sqrt hE.le] at h2
      assumption
    have hsum : Real.sqrt E' + s ≠ 0 := by positivity
    have hEE : E' - E = (Real.sqrt E' - s) * (Real.sqrt E' + s) := by
      rw [hsdef]
      ring_nf
      rw [Real.sq_sqrt hpos.le, Real.sq_sqrt hE.le]
    rw [hEE]
    field_simp
  have hV := tendsto_transport_energy hK hWs E h2π
  have hI : Tendsto I (𝓝 E) (𝓝 (I E)) := tendsto_integral_energyIntegrand hK hWs E
  have hsq : Tendsto (fun E' => (Real.sqrt E' + s)⁻¹) (𝓝 E) (𝓝 ((s + s)⁻¹)) :=
    ((Real.continuous_sqrt.tendsto E).add_const s).inv₀ (by positivity)
  have hval : (s + s)⁻¹ • (V E * I E) = -(Complex.I • (Ws E (2 * π) * curvatureOp γ (Ws E))) := by
    simp  [hVdef, hIdef]
    have hIE : ∫ θ in (0 : ℝ)..(2 * π), energyIntegrand γ E E (Ws E) (Ws E) θ =
        ((s : ℂ) * (-(Complex.I / 2))) •
          ∫ θ in (0 : ℝ)..(2 * π), areaDensity γ θ • (star (Ws E θ) * diagN * Ws E θ) := by
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
  simp_all

/-- `D_N` is self-adjoint. -/
lemma star_diagN : star diagN = diagN := by
  rw [← shift_commutator, star_sub, star_mul, star_mul, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_adjoint]

section

variable {γ : ℝ → ℂ}
include γ

lemma areaDensity_aestronglyMeasurable  (hγ : Continuous γ) :
    AEStronglyMeasurable (areaDensity γ) volume := by
  have h1 : AEStronglyMeasurable (fun θ => conj (γ θ - γ 0)) volume :=
    (Complex.continuous_conj.comp (hγ.sub continuous_const)).aestronglyMeasurable
  exact Complex.continuous_im.comp_aestronglyMeasurable
    (h1.mul (measurable_deriv γ).aestronglyMeasurable)

lemma abs_areaDensity_le  {K : NNReal} (hK : LipschitzWith K γ) {R : ℝ}
    (hR : ∀ θ ∈ Icc 0 (2 * π), ‖γ θ - γ 0‖ ≤ R) {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * π)) :
    |areaDensity γ θ| ≤ R * K := by
  unfold areaDensity
  refine (Complex.abs_im_le_norm _).trans ?_
  rw [norm_mul, Complex.norm_conj]
  exact mul_le_mul (hR θ hθ) (norm_deriv_le_of_lipschitz hK) (norm_nonneg _)
    ((norm_nonneg _).trans (hR θ hθ))

end

lemma intervalIntegrable_of_abs_le {b : ℝ → ℝ} (hb : AEStronglyMeasurable b volume) {B : ℝ}
    (hB : ∀ θ ∈ Icc 0 (2 * π), |b θ| ≤ B) : IntervalIntegrable b volume 0 (2 * π) := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le Real.two_pi_pos.le]
  exact Integrable.of_bound hb.restrict B <| (ae_restrict_iff' measurableSet_Icc).2 <|
    .of_forall fun θ hθ => by simpa only [Real.norm_eq_abs] using hB θ hθ

/-- A bounded measurable weight times a continuous operator family is integrable. -/
lemma intervalIntegrable_areaDensity {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) :
    IntervalIntegrable (areaDensity γ) volume 0 (2 * π) := by
  obtain ⟨R, hR⟩ := exists_curve_displacement_bound hK
  exact intervalIntegrable_of_abs_le (areaDensity_aestronglyMeasurable hK.continuous)
    (fun θ hθ => abs_areaDensity_le hK hR hθ)

lemma intervalIntegrable_conj_diagN {U : ℝ → Ell2 →L[ℂ] Ell2}
    (hU : ContinuousOn U (Icc 0 (2 * π)))
    {b : ℝ → ℝ} (hb : AEStronglyMeasurable b volume) {B : ℝ}
    (hbB : ∀ θ ∈ Icc 0 (2 * π), |b θ| ≤ B) :
    IntervalIntegrable (fun θ => b θ • (star (U θ) * diagN * U θ)) volume 0 (2 * π) := by
  refine (intervalIntegrable_of_abs_le hb hbB).smul_continuousOn ?_
  rw [uIcc_of_le Real.two_pi_pos.le]
  exact (hU.star.mul continuousOn_const).mul hU

section

variable {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
include γ K hK

/-- The curvature operator `Q_E` is self-adjoint. -/
theorem curvatureOp_star  {E : ℝ}
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W) :
    star (curvatureOp γ W) = curvatureOp γ W := by
  obtain ⟨R, hR⟩ := exists_curve_displacement_bound hK
  have hint := intervalIntegrable_conj_diagN hW.1
    (areaDensity_aestronglyMeasurable hK.continuous) (fun θ hθ => abs_areaDensity_le hK hR hθ)
  unfold curvatureOp
  rw [star_smul]
  congr 1
  have := (starL' ℝ (A := Ell2 →L[ℂ] Ell2)).toContinuousLinearMap.intervalIntegral_comp_comm hint
  simp only [ContinuousLinearEquiv.coe_coe, starL'_apply] at this
  rw [← this]
  congr 1
  funext θ
  rw [star_smul, star_trivial, star_mul, star_mul, star_star, star_diagN, mul_assoc]

/-- Lemma 4.7: the monodromy `U_E = V_E^*` is differentiable in `E > 0` (in operator norm),
with `∂_E U_E = i Q_E U_E`. -/
theorem hasDerivAt_monodromy_energy 
    (hclosed : γ (2 * π) = γ 0) {Ws : ℝ → ℝ → Ell2 →L[ℂ] Ell2}
    (hWs : ∀ E, IsTransport γ E (Ws E)) {E : ℝ} (hE : 0 < E) :
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
