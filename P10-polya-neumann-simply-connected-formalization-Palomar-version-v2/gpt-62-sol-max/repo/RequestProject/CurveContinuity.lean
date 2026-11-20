module

public import Mathlib.Analysis.Calculus.Rademacher
public import RequestProject.Observation

/-!
# Continuity of the monodromy under uniform convergence of curves (Lemma 10.6)

If closed Lipschitz curves `γₙ` converge uniformly to a closed Lipschitz curve `γ` with
uniformly bounded lengths `∫₀^L |γₙ'|`, and `Eₙ → E`, then `U_{γₙ}(Eₙ) → U_γ(E)` in operator
norm.

The proof is the paper's: with `Fₙ` a primitive of `C - Cₙ` vanishing at both endpoints,
the variation identity and an integration by parts give
`Vₙ^* V - I = ∫₀^L Wₙ^* (Cₙ Fₙ - Fₙ C) W`, whence
`‖Vₙ^* V - I‖ ≤ ‖Fₙ‖_∞ ∫₀^L (‖Cₙ‖ + ‖C‖) → 0`.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ComplexConjugate Real Topology

noncomputable section

namespace PolyaNeumann

section Generic

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  [StarRing A] [StarModule ℝ A] [NormedStarGroup A]
variable {C C' : ℝ → A} {M M' L : ℝ} {W W' F : ℝ → A}


section

variable (hC : AEStronglyMeasurable C volume) (hM : ∀ s, ‖C s‖ ≤ M) (hW : ContinuousOn W (Icc 0 L)) (eW : ∀ θ ∈ Icc 0 L, W θ = 1 + ∫ s in (0 : ℝ)..θ, C s * W s) (hC' : AEStronglyMeasurable C' volume) (hM' : ∀ s, ‖C' s‖ ≤ M') (hskew' : ∀ s, star (C' s) = -C' s) (hW' : ContinuousOn W' (Icc 0 L)) (eW' : ∀ θ ∈ Icc 0 L, W' θ = 1 + ∫ s in (0 : ℝ)..θ, C' s * W' s) (hL : 0 ≤ L) {KF : NNReal} (hF : LipschitzOnWith KF F (Icc 0 L)) (hFd : ∀ᵐ θ, θ ∈ Ioo 0 L → HasDerivAt F (C θ - C' θ) θ) (hF0 : F 0 = 0)
include hC hM hW eW hC' hM' hskew' hW' eW' hL KF hF hFd hF0

/-- The variation identity with an integration by parts, at every point of `[0, L]`: if
`F' = C - C'` almost everywhere and `F(0) = 0`, then
`W'(θ)^* W(θ) - 1 = W'(θ)^* F(θ) W(θ) + ∫₀^θ W'^* (C' F - F C) W`. -/
theorem volterra_variation_at  :
    ∀ θ ∈ Icc 0 L, star (W' θ) * W θ - 1 = star (W' θ) * F θ * W θ +
      ∫ s in (0 : ℝ)..θ, star (W' s) * (C' s * F s - F s * C s) * W s := by
  have hW0 : W 0 = 1 := by simp_all
  have hW0' : W' 0 = 1 := by simp_all
  obtain ⟨_, hK⟩ := volterra_lipschitzOn hC hM hW eW
  obtain ⟨_, hK'⟩ := volterra_lipschitzOn hC' hM' hW' eW'
  have hs := star_isometry.lipschitz.comp_lipschitzOnWith hK'
  obtain ⟨_, hleft⟩ := exists_lipschitzOnWith_mul isCompact_Icc hs hK
  obtain ⟨_, hsf⟩ := exists_lipschitzOnWith_mul isCompact_Icc hs hF
  obtain ⟨_, hright⟩ := exists_lipschitzOnWith_mul isCompact_Icc hsf hK
  have hGL := hleft.sub hright
  let g : ℝ → A := fun s => star (W' s) * (C' s * F s - F s * C s) * W s
  have hI := (intervalIntegrable_iff_integrableOn_Icc_of_le hL).mp
    (intervalIntegrable_of_bounded hC hM 0 L)
  have hI' := (intervalIntegrable_iff_integrableOn_Icc_of_le hL).mp
    (intervalIntegrable_of_bounded hC' hM' 0 L)
  have hgi : IntegrableOn g (Icc 0 L) :=
    ((hI'.mul_continuousOn hF.continuousOn isCompact_Icc).sub
      (hI.continuousOn_mul hF.continuousOn isCompact_Icc)).continuousOn_mul hW'.star
        isCompact_Icc |>.mul_continuousOn hW isCompact_Icc
  have hd := volterra_ae_hasDerivAt hC hM hW eW
  have hds := volterra_ae_hasDerivAt_star hC' hM' hskew' hW' eW'
  have hP := eq_add_integral_of_ae_hasDerivAt hGL hgi (by
    filter_upwards [hd, hds, hFd] with θ h1 h2 h3 hmem
    have := ((h2 hmem).mul (h1 hmem)).sub (((h2 hmem).mul (h3 hmem)).mul (h1 hmem))
    convert this using 1
    · rfl
    · simp only [g, Pi.mul_apply]; noncomm_ring)
  intro θ hθ
  have := hP θ hθ
  simp [hW0, hW0', hF0, g] at this
  grind


end

omit [CompleteSpace A] [StarModule ℝ A] [NormedStarGroup A] in
/-- The norm estimate in the variation identity. -/
theorem norm_volterra_variation_le (hC : AEStronglyMeasurable C volume) (hM : ∀ s, ‖C s‖ ≤ M)
    (hC' : AEStronglyMeasurable C' volume) (hM' : ∀ s, ‖C' s‖ ≤ M') (hL : 0 ≤ L)
    {ε : ℝ} (hFε : ∀ θ ∈ Icc 0 L, ‖F θ‖ ≤ ε) (hWn : ∀ θ ∈ Icc 0 L, ‖W θ‖ ≤ 1)
    (hW'n : ∀ θ ∈ Icc 0 L, ‖star (W' θ)‖ ≤ 1) :
    ‖∫ s in (0 : ℝ)..L, star (W' s) * (C' s * F s - F s * C s) * W s‖ ≤
      ε * ∫ s in (0 : ℝ)..L, (‖C' s‖ + ‖C s‖) := by
  have hC₀ := intervalIntegrable_of_bounded hC hM 0 L
  have hC₀' := intervalIntegrable_of_bounded hC' hM' 0 L
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.norm_integral_le_of_norm_le hL
    (Eventually.of_forall fun t ht => ?_) ((hC₀'.norm.add hC₀.norm).const_mul ε)
  have ht' := Ioc_subset_Icc_self ht
  have h := (norm_sub_le (C' t * F t) (F t * C t)).trans (add_le_add
    (norm_mul_le_of_le le_rfl (hFε t ht')) (norm_mul_le_of_le (hFε t ht') le_rfl))
  simpa only [mul_add, one_mul, mul_one, mul_comm ‖C' t‖ ε] using
    (norm_mul_le_of_le (norm_mul_le_of_le (hW'n t ht') h) (hWn t ht'))

end Generic

/-! ### The boundary transport -/

/-- The matrix `-(i √E / 2) (z S_N^* + conj(z) S_N)`; the transport coefficient is
`C_E(θ) = coeffOf E (γ'(θ))`. -/
def coeffOf (E : ℝ) (z : ℂ) : Ell2 →L[ℂ] Ell2 :=
  (-(Complex.I * (Real.sqrt E : ℂ)) / 2) •
    (z • ContinuousLinearMap.adjoint shiftN + conj z • shiftN)

lemma transportCoeff_eq_coeffOf (γ : ℝ → ℂ) (E θ : ℝ) :
    transportCoeff γ E θ = coeffOf E (deriv γ θ) := rfl

/-- The constant `κ = (‖S_N^*‖ + ‖S_N‖) / 2`. -/
def shiftConst : ℝ := (‖(ContinuousLinearMap.adjoint shiftN : Ell2 →L[ℂ] Ell2)‖ + ‖shiftN‖) / 2

lemma shiftConst_nonneg : 0 ≤ shiftConst := by unfold shiftConst; positivity

lemma coeffOf_sub (E : ℝ) (z w : ℂ) : coeffOf E z - coeffOf E w = coeffOf E (z - w) := by
  unfold coeffOf
  rw [map_sub]
  module

lemma coeffOf_zero (E : ℝ) : coeffOf E 0 = 0 := by simp [coeffOf]

lemma norm_I_mul_div_two (r : ℝ) : ‖(-(Complex.I * (r : ℂ)) / 2)‖ = |r| / 2 := by simp

lemma norm_shiftPart_le (z : ℂ) :
    ‖z • ContinuousLinearMap.adjoint shiftN + conj z • shiftN‖ ≤ 2 * shiftConst * ‖z‖ := by
  unfold shiftConst
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Complex.norm_conj]
  linarith

lemma norm_coeffOf_le (E : ℝ) (z : ℂ) : ‖coeffOf E z‖ ≤ Real.sqrt E * shiftConst * ‖z‖ := by
  unfold coeffOf
  rw [norm_smul, norm_I_mul_div_two, abs_of_nonneg (Real.sqrt_nonneg E)]
  calc Real.sqrt E / 2 * ‖z • ContinuousLinearMap.adjoint shiftN + conj z • shiftN‖
      ≤ Real.sqrt E / 2 * (2 * shiftConst * ‖z‖) := by
        gcongr; exact norm_shiftPart_le z
    _ = _ := by ring

lemma norm_coeffOf_sub_coeffOf_le (E E' : ℝ) (z : ℂ) :
    ‖coeffOf E z - coeffOf E' z‖ ≤ |Real.sqrt E - Real.sqrt E'| * shiftConst * ‖z‖ := by
  have hsplit : coeffOf E z - coeffOf E' z =
      (-(Complex.I * ((Real.sqrt E - Real.sqrt E' : ℝ) : ℂ)) / 2) •
        (z • ContinuousLinearMap.adjoint shiftN + conj z • shiftN) := by
    unfold coeffOf; push_cast; module
  rw [hsplit, norm_smul, norm_I_mul_div_two]
  calc |Real.sqrt E - Real.sqrt E'| / 2 *
        ‖z • ContinuousLinearMap.adjoint shiftN + conj z • shiftN‖
      ≤ |Real.sqrt E - Real.sqrt E'| / 2 * (2 * shiftConst * ‖z‖) := by
        gcongr; exact norm_shiftPart_le z
    _ = _ := by ring

lemma hasDerivAt_coeffOf {γ : ℝ → ℂ} {γ' : ℂ} {θ : ℝ} (h : HasDerivAt γ γ' θ) (E : ℝ) (c : ℂ) :
    HasDerivAt (fun θ => coeffOf E (γ θ - c)) (coeffOf E γ') θ := by
  have h1 := h.sub_const c
  have h2 := h1.star
  exact ((h1.smul_const (ContinuousLinearMap.adjoint shiftN)).add
    (h2.smul_const shiftN)).const_smul (-(Complex.I * (Real.sqrt E : ℂ)) / 2)

lemma lipschitzWith_coeffOf {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) (E : ℝ) (c : ℂ) :
    LipschitzWith (Real.sqrt E * shiftConst * K).toNNReal (fun θ => coeffOf E (γ θ - c)) := by
  refine LipschitzWith.of_dist_le' fun x y => ?_
  rw [dist_eq_norm, coeffOf_sub, sub_sub_sub_cancel_right]
  refine (norm_coeffOf_le E _).trans ?_
  rw [mul_assoc _ (K : ℝ)]
  have := hK.dist_le_mul x y
  rw [dist_eq_norm] at this
  exact have h0 := mul_nonneg (Real.sqrt_nonneg E) shiftConst_nonneg; mul_le_mul_of_nonneg_left this h0

/-- Unitary operators have norm at most one. -/
lemma norm_le_one_of_mem_unitary {U : Ell2 →L[ℂ] Ell2} (hU : U ∈ unitary (Ell2 →L[ℂ] Ell2)) :
    ‖U‖ ≤ 1 := by
  have h1 := CStarRing.norm_coe_unitary_mul (⟨U, hU⟩ : unitary (Ell2 →L[ℂ] Ell2)) 1
  simp   at h1
  rw [h1]
  exact ContinuousLinearMap.norm_id_le

lemma norm_coeffOf_sub_coeffOf_le' (E E' : ℝ) (z z' : ℂ) :
    ‖coeffOf E z - coeffOf E' z'‖ ≤
      |Real.sqrt E - Real.sqrt E'| * shiftConst * ‖z‖ + Real.sqrt E' * shiftConst * ‖z - z'‖ := by
  have : coeffOf E z - coeffOf E' z' = (coeffOf E z - coeffOf E' z) + coeffOf E' (z - z') := by
    rw [← coeffOf_sub]; abel
  rw [this]
  exact (norm_add_le _ _).trans
    (add_le_add (norm_coeffOf_sub_coeffOf_le E E' z) (norm_coeffOf_le E' _))

section

variable {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
include γ K hK

lemma norm_transportCoeff_le_const (E s : ℝ) :
    ‖transportCoeff γ E s‖ ≤ Real.sqrt E * shiftConst * K := by
  rw [transportCoeff_eq_coeffOf]
  refine (norm_coeffOf_le E _).trans ?_
  have := norm_deriv_le_of_lipschitz hK (x₀ := s)
  have := shiftConst_nonneg
  gcongr

lemma intervalIntegrable_norm_transportCoeff (E a b : ℝ) :
    IntervalIntegrable (fun s => ‖transportCoeff γ E s‖) volume a b :=
  intervalIntegrable_of_bounded (transportCoeff_aestronglyMeasurable γ E).norm
    (fun s => by simpa using norm_transportCoeff_le_const hK E s) a b

lemma integral_norm_transportCoeff_le 
    (E : ℝ) :
    ∫ θ in (0 : ℝ)..(2 * π), ‖transportCoeff γ E θ‖ ≤
      Real.sqrt E * shiftConst * ∫ θ in (0 : ℝ)..(2 * π), ‖deriv γ θ‖ := by
  rw [← intervalIntegral.integral_const_mul]
  have hd : ∀ s, ‖deriv γ s‖ ≤ K := fun s => norm_deriv_le_of_lipschitz hK
  refine intervalIntegral.integral_mono_on (by positivity) ?_ ?_ fun θ _ => ?_
  · exact intervalIntegrable_norm_transportCoeff hK E _ _
  · refine (intervalIntegrable_of_bounded (measurable_deriv γ).aestronglyMeasurable.norm
      (B := K) (fun s => by simp_all) _ _).const_mul _
  exact norm_coeffOf_le E _

/-- The values of the transport of a Lipschitz curve are unitary. -/
lemma transport_mem_unitary  {E : ℝ}
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W) {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * π)) :
    W θ ∈ unitary (Ell2 →L[ℂ] Ell2) :=
  Unitary.mem_iff.mpr (volterra_unitary (transportCoeff_aestronglyMeasurable γ E)
    (transportCoeff_norm_le γ E hK) (transportCoeff_star γ E) hW.1 hW.2 θ hθ)

end

/-- The primitive of the difference of the two transport coefficients, based at zero. -/
def transportPrimitive (γ γ' : ℝ → ℂ) (E E' : ℝ) (θ : ℝ) : Ell2 →L[ℂ] Ell2 :=
  coeffOf E (γ θ - γ 0) - coeffOf E' (γ' θ - γ' 0)

/-- Integration by parts for transports along two curves, at any point of the cut interval. -/
theorem transport_variation_at {γ γ' : ℝ → ℂ} {K K' : NNReal} (hK : LipschitzWith K γ)
    (hK' : LipschitzWith K' γ') {E E' : ℝ} {W W' : ℝ → Ell2 →L[ℂ] Ell2}
    (hW : IsTransport γ E W) (hW' : IsTransport γ' E' W') {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * π)) :
    let F := transportPrimitive γ γ' E E'
    star (W' θ) * W θ - 1 = star (W' θ) * F θ * W θ +
      ∫ s in (0 : ℝ)..θ, star (W' s) * (transportCoeff γ' E' s * F s - F s * transportCoeff γ E s) * W s := by
  dsimp only
  let F := transportPrimitive γ γ' E E'
  have hFL : LipschitzOnWith _ F (Icc 0 (2 * π)) :=
    ((lipschitzWith_coeffOf hK E (γ 0)).sub (lipschitzWith_coeffOf hK' E' (γ' 0))).lipschitzOnWith
  have hFd : ∀ᵐ θ, θ ∈ Ioo 0 (2 * π) →
      HasDerivAt F (transportCoeff γ E θ - transportCoeff γ' E' θ) θ := by
    filter_upwards [hK.ae_differentiableAt (μ := volume),
      hK'.ae_differentiableAt (μ := volume)] with θ h1 h2 _
    exact (hasDerivAt_coeffOf h1.hasDerivAt E (γ 0)).sub
      (hasDerivAt_coeffOf h2.hasDerivAt E' (γ' 0))
  have hF0 : F 0 = 0 := by simp [F, transportPrimitive, coeffOf_zero]
  exact volterra_variation_at (transportCoeff_aestronglyMeasurable γ E) (transportCoeff_norm_le γ E hK)
    hW.1 hW.2 (transportCoeff_aestronglyMeasurable γ' E') (transportCoeff_norm_le γ' E' hK')
    (transportCoeff_star γ' E') hW'.1 hW'.2 Real.two_pi_pos.le hFL hFd hF0 θ hθ

/-- The norm bound corresponding to the transport variation identity. At an endpoint of two
closed curves the primitive term vanishes. -/
theorem norm_transport_variation_le {γ γ' : ℝ → ℂ} {K K' : NNReal} (hK : LipschitzWith K γ)
    (hK' : LipschitzWith K' γ') {E E' : ℝ} {W W' : ℝ → Ell2 →L[ℂ] Ell2}
    (hW : IsTransport γ E W) (hW' : IsTransport γ' E' W') {ε : ℝ}
    (hε : ∀ s ∈ Icc 0 (2 * π), ‖transportPrimitive γ γ' E E' s‖ ≤ ε)
    {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * π)) :
    ‖W' θ - W θ‖ ≤ ‖transportPrimitive γ γ' E E' θ‖ +
      ε * ∫ s in (0 : ℝ)..θ, (‖transportCoeff γ' E' s‖ + ‖transportCoeff γ E s‖) := by
  let U t (ht : t ∈ Icc 0 (2 * π)) : unitary (Ell2 →L[ℂ] Ell2) := ⟨W t, transport_mem_unitary hK hW ht⟩
  let V t (ht : t ∈ Icc 0 (2 * π)) : unitary (Ell2 →L[ℂ] Ell2) :=
    ⟨star (W' t), Unitary.star_mem (transport_mem_unitary hK' hW' ht)⟩
  have he : ‖star (W' θ) * (W θ - W' θ)‖ = ‖W θ - W' θ‖ :=
    CStarRing.norm_coe_unitary_mul (V θ hθ) _
  rw [mul_sub, (Unitary.mem_iff.mp (transport_mem_unitary hK' hW' hθ)).1] at he
  rw [norm_sub_rev (W' θ) (W θ), ← he, transport_variation_at hK hK' hW hW' hθ]
  have hsub : Icc 0 θ ⊆ Icc 0 (2 * π) := Icc_subset_Icc le_rfl hθ.2
  refine (norm_add_le _ _).trans (add_le_add ?_ (norm_volterra_variation_le
    (transportCoeff_aestronglyMeasurable γ E) (transportCoeff_norm_le γ E hK)
    (transportCoeff_aestronglyMeasurable γ' E') (transportCoeff_norm_le γ' E' hK') hθ.1
    (fun s hs => hε s (hsub hs)) (fun s hs => norm_le_one_of_mem_unitary (U s (hsub hs)).2)
    (fun s hs => norm_le_one_of_mem_unitary (V s (hsub hs)).2)))
  exact ((CStarRing.norm_mul_coe_unitary _ (U θ hθ)).trans
    (CStarRing.norm_coe_unitary_mul (V θ hθ) _)).le

/-- **Lemma 10.6 (continuity under uniform curve convergence).** Let `γₙ, γ` be closed
Lipschitz curves on `[0, L]` such that `γₙ → γ` uniformly on `[0, L]` and the lengths
`∫₀^L |γₙ'|` are uniformly bounded. If `Eₙ → E`, then `U_{γₙ}(Eₙ) → U_γ(E)` in operator
norm. -/
theorem monodromy_tendsto_of_tendstoUniformlyOn {γ : ℝ → ℂ} {γs : ℕ → ℝ → ℂ} {K : NNReal}
    {Ks : ℕ → NNReal} (hK : LipschitzWith K γ) (hKs : ∀ n, LipschitzWith (Ks n) (γs n))
    (hclosed : γ (2 * π) = γ 0) (hclosed' : ∀ n, γs n (2 * π) = γs n 0)
    (hunif : TendstoUniformlyOn γs γ atTop (Icc 0 (2 * π)))
    (hlen : ∃ B, ∀ n, ∫ θ in (0 : ℝ)..(2 * π), ‖deriv (γs n) θ‖ ≤ B)
    {E : ℝ} {Es : ℕ → ℝ} (hE : Tendsto Es atTop (𝓝 E))
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W)
    {Ws : ℕ → ℝ → Ell2 →L[ℂ] Ell2} (hWs : ∀ n, IsTransport (γs n) (Es n) (Ws n)) :
    Tendsto (fun n => monodromy (Ws n)) atTop (𝓝 (monodromy W)) := by
  obtain ⟨B, hB⟩ := hlen
  have hπ : (0 : ℝ) ≤ 2 * π := by positivity
  have h0mem : (0 : ℝ) ∈ Icc 0 (2 * π) := ⟨le_rfl, hπ⟩
  obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc 0 (2 * π)) hK.continuous.continuousOn
  have hR0 := (norm_nonneg _).trans (hR 0 h0mem)
  have hκ := shiftConst_nonneg
  set κ := shiftConst
  set s0 := Real.sqrt E with hs0
  have hs00 := Real.sqrt_nonneg E
  set A0 := ∫ θ in (0 : ℝ)..(2 * π), ‖transportCoeff γ E θ‖ with hA0def
  have hA0 : 0 ≤ A0 := intervalIntegral.integral_nonneg hπ fun _ _ => norm_nonneg _
  set B' := max B 0
  have hB' : 0 ≤ B' := le_max_right _ _
  set c1 := 2 * κ * (R + s0 + 1) with hc1def
  set c2 := (s0 + 1) * κ * B' + A0 with hc2def
  have hc1 : 0 ≤ c1 := by positivity
  have hc2 : 0 ≤ c2 := by positivity
  have hbound : ∀ n, ∀ η, 0 ≤ η → η ≤ 1 → |s0 - Real.sqrt (Es n)| ≤ η →
      (∀ θ ∈ Icc 0 (2 * π), ‖γ θ - γs n θ‖ ≤ η) →
      ‖monodromy (Ws n) - monodromy W‖ ≤ η * c1 * c2 := by
    intro n η hη0 hη1 hηE hηγ
    have hsq : Real.sqrt (Es n) ≤ s0 + 1 := by
      have := (abs_le.mp hηE).1
      linarith
    have hε : ∀ θ ∈ Icc 0 (2 * π),
        ‖coeffOf E (γ θ - γ 0) - coeffOf (Es n) (γs n θ - γs n 0)‖ ≤ η * c1 := by
      intro θ hθ
      refine (norm_coeffOf_sub_coeffOf_le' _ _ _ _).trans ?_
      have h1 : ‖γ θ - γ 0‖ ≤ 2 * R := (norm_sub_le _ _).trans (by grind)
      have h2 : ‖(γ θ - γ 0) - (γs n θ - γs n 0)‖ ≤ 2 * η := by
        rw [show (γ θ - γ 0) - (γs n θ - γs n 0) = (γ θ - γs n θ) - (γ 0 - γs n 0) by ring]
        exact (norm_sub_le _ _).trans (by grind)
      calc |s0 - Real.sqrt (Es n)| * κ * ‖γ θ - γ 0‖ +
            Real.sqrt (Es n) * κ * ‖(γ θ - γ 0) - (γs n θ - γs n 0)‖
          ≤ η * κ * (2 * R) + (s0 + 1) * κ * (2 * η) := by
            gcongr
        _ = η * c1 := by ring
    have hvar := norm_transport_variation_le hK (hKs n) hW (hWs n) hε ⟨hπ, le_rfl⟩
    simp only [transportPrimitive, hclosed, hclosed' n, sub_self, coeffOf_zero, norm_zero, zero_add] at hvar
    have hint : ∫ s in (0 : ℝ)..(2 * π),
        (‖transportCoeff (γs n) (Es n) s‖ + ‖transportCoeff γ E s‖) ≤ c2 := by
      rw [intervalIntegral.integral_add (intervalIntegrable_norm_transportCoeff (hKs n) _ _ _)
        (intervalIntegrable_norm_transportCoeff hK _ _ _)]
      have h3 := integral_norm_transportCoeff_le (hKs n) (Es n)
      have h4 : 0 ≤ ∫ θ in (0 : ℝ)..(2 * π), ‖deriv (γs n) θ‖ :=
        intervalIntegral.integral_nonneg hπ fun _ _ => norm_nonneg _
      have h5 : Real.sqrt (Es n) * κ * ∫ θ in (0 : ℝ)..(2 * π), ‖deriv (γs n) θ‖ ≤
          (s0 + 1) * κ * B' := by
        gcongr
        exact (hB n).trans (le_max_left _ _)
      rw [hc2def]
      linarith
    simp only [monodromy, ← ContinuousLinearMap.star_eq_adjoint, ← star_sub, norm_star]
    exact hvar.trans (by gcongr)
  rw [Metric.tendsto_nhds]
  intro ε hε
  set η := min 1 (ε / (2 * (c1 * c2 + 1))) with hηdef
  have hηpos : 0 < η := lt_min one_pos (by positivity)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηε : η * c1 * c2 < ε := by
    have h1 : η ≤ ε / (2 * (c1 * c2 + 1)) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at h1
    nlinarith [mul_nonneg hc1 hc2]
  have hsqrt : Tendsto (fun n => Real.sqrt (Es n)) atTop (𝓝 s0) :=
    (Real.continuous_sqrt.tendsto E).comp hE
  filter_upwards [Metric.tendsto_nhds.mp hsqrt η hηpos,
    Metric.tendstoUniformlyOn_iff.mp hunif η hηpos] with n hn1 hn2
  rw [dist_eq_norm]
  refine lt_of_le_of_lt (hbound n η hηpos.le hη1 ?_ ?_) hηε
  · rw [Real.dist_eq] at hn1
    rw [abs_sub_comm]; gcongr
  · intro θ hθ
    rw [← dist_eq_norm]; exact (hn2 θ hθ).le

end PolyaNeumann

end
