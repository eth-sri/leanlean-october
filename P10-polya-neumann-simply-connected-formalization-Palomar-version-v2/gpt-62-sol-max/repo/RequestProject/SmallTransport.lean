module

public import RequestProject.HerglotzForm
public import RequestProject.Area

/-!
# Small-energy estimates for the transport (Lemma 8.2 and the kernel bounds of Lemma 8.4)

For a Lipschitz curve and `0 < E ≤ 1` (wave number `k = √E`):

* `norm_transport_sub_one_le`: `‖W_E(θ) - I‖ ≤ c k` on `[0, L]`;
* `norm_transport_sub_le_lip`: `‖W_E(θ₁) - W_E(θ₂)‖ ≤ c k |θ₁ - θ₂|`;
* `transport_coord_zero`: the zeroth row of the transport equation,
  `⟨e₀, W(θ) x⟩ = ⟨e₀, x⟩ + ∫₀^θ (-(i k)/2) γ' √2 ⟨e₁, W x⟩`;
* the function `b_E(θ) = ⟨e₀, W(θ)(I + V^*) e₀⟩` satisfies `|b_E - 2| ≤ C E` and
  `b_E(θ) = b_E(0) + ∫₀^θ b'_E` with `|b'_E| ≤ C E` (`smallB_*`);
* `a_E = 2 Im ⟨e₀, V e₀⟩ = -E ∫₀^L Im(conj(γ - γ(0)) γ') + O(E^{3/2})` (`smallA_*`);
* the Volterra kernel `w(θ, s) = ⟨e₀, W(θ) W(s)^* e₀⟩` satisfies
  `w(θ, s) = w(θ, 0) + ∫₀^s ρ(θ, t) dt` with `ρ(t, t) = 0` and
  `|ρ(θ₁, t) - ρ(θ₂, t)| ≤ C E |θ₁ - θ₂|` (`kernelRho_*`).
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ComplexConjugate Real InnerProductSpace Interval

noncomputable section

namespace PolyaNeumann

/-- The transport at energy `0` is the identity. -/
lemma isTransport_zero (γ : ℝ → ℂ) : IsTransport γ 0 (fun _ => 1) := by
  refine ⟨continuousOn_const, fun θ _ => ?_⟩
  have h0 : ∀ s, transportCoeff γ 0 s = 0 := fun s => by
    simp [transportCoeff]
  simp_all

/-- `‖W_E(θ) - I‖ ≤ c √E` for `0 ≤ E ≤ 1`. -/
lemma norm_transport_sub_one_le {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ E, 0 ≤ E → E ≤ 1 → ∀ W : ℝ → Ell2 →L[ℂ] Ell2, IsTransport γ E W →
      ∀ θ ∈ Icc 0 (2 * π), ‖W θ - 1‖ ≤ c * Real.sqrt E := by
  set R : ℝ := K * (2 * π) with hR
  have hR0 : 0 ≤ R := by positivity
  have hRb : ∀ θ ∈ Icc 0 (2 * π), ‖γ θ - γ 0‖ ≤ R := fun θ hθ => by
    have := hK.dist_le_mul θ 0
    rw [dist_eq_norm, Real.dist_eq, sub_zero, abs_of_nonneg hθ.1] at this
    exact this.trans (by rw [hR]; gcongr; simp_all)
  have hκ := shiftConst_nonneg
  refine ⟨shiftConst * R * (1 + 2 * π * (1 * shiftConst * K)), by positivity,
    fun E hE0 hE1 W hW θ hθ => ?_⟩
  have h := norm_transport_sub_le hK hRb (isTransport_zero γ) hW hθ
  have hs1 := Real.sqrt_le_one.mpr hE1
  have hs0 := Real.sqrt_nonneg E
  simp  [zero_sub, abs_neg, abs_of_nonneg hs0, add_zero] at h
  calc ‖W θ - 1‖ ≤ Real.sqrt E * shiftConst * R *
        (1 + 2 * π * (Real.sqrt E * shiftConst * K)) := h
    _ ≤ Real.sqrt E * shiftConst * R * (1 + 2 * π * (1 * shiftConst * K)) := by gcongr
    _ = _ := by ring

section

variable {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W)
include γ K hK E W hW

/-- Values of the transport have norm at most one. -/
lemma norm_transport_le_one  {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * π)) :
    ‖W θ‖ ≤ 1 :=
  norm_le_one_of_mem_unitary (transport_mem_unitary hK hW hθ)

/-- Lipschitz bound for the transport with constant proportional to `√E`. -/
lemma norm_transport_sub_le_lip  {θ₁ θ₂ : ℝ}
    (h₁ : θ₁ ∈ Icc 0 (2 * π)) (h₂ : θ₂ ∈ Icc 0 (2 * π)) :
    ‖W θ₁ - W θ₂‖ ≤ Real.sqrt E * shiftConst * K * |θ₁ - θ₂| := by
  have hC := transportCoeff_aestronglyMeasurable γ E
  have hM := transportCoeff_norm_le γ E hK
  rw [hW.2 θ₁ h₁, hW.2 θ₂ h₂, add_sub_add_left_eq_sub,
    intervalIntegral.integral_interval_sub_left (intervalIntegrable_mul_of_continuousOn hC hM hW.1 h₁)
      (intervalIntegrable_mul_of_continuousOn hC hM hW.1 h₂)]
  refine intervalIntegral.norm_integral_le_of_norm_le_const fun t ht => ?_
  have ht' : t ∈ Icc 0 (2 * π) := by
    have := uIoc_subset_uIcc ht
    rw [mem_uIcc] at this
    rcases this with h | h
    · exact ⟨h₂.1.trans h.1, h.2.trans h₁.2⟩
    · exact ⟨h₁.1.trans h.1, h.2.trans h₂.2⟩
  calc ‖transportCoeff γ E t * W t‖ ≤ ‖transportCoeff γ E t‖ * ‖W t‖ := norm_mul_le _ _
    _ ≤ (Real.sqrt E * shiftConst * K) * 1 :=
        mul_le_mul (norm_transportCoeff_le_const hK E t) (norm_transport_le_one hK hW ht')
          (norm_nonneg _) (by have := shiftConst_nonneg; positivity)
    _ = _ := mul_one _

end

section

variable (γ : ℝ → ℂ) (E s : ℝ) (x : Ell2)
include γ E s x

/-- The zeroth coordinate of `C_E(s) x`. -/
lemma transportCoeff_coord_zero  :
    (transportCoeff γ E s x : ℕ → ℂ) 0 =
      (-(Complex.I * (Real.sqrt E : ℂ)) / 2) * (deriv γ s * ((Real.sqrt 2 : ℂ) * (x : ℕ → ℂ) 1)) := by
  rw [transportCoeff_apply_coord]
  simp [shiftWeight]

end

/-- Coordinates are bounded by the norm. -/
lemma norm_coord_le (x : Ell2) (n : ℕ) : ‖(x : ℕ → ℂ) n‖ ≤ ‖x‖ := by
  have := lp.norm_apply_le_norm (p := 2) (by norm_num) x n
  assumption

section

variable {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W) (x : Ell2) {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * π))
include γ K hK E W hW x θ hθ

/-- The zeroth row of the transport equation. -/
lemma transport_coord_zero  :
    (W θ x : ℕ → ℂ) 0 = (x : ℕ → ℂ) 0 + ∫ s in (0 : ℝ)..θ,
      (-(Complex.I * (Real.sqrt E : ℂ)) / 2) *
        (deriv γ s * ((Real.sqrt 2 : ℂ) * (W s x : ℕ → ℂ) 1)) := by
  rw [transport_coord_eq hK hW x 0 hθ]
  simp  [transportCoeff_coord_zero]

end

/-- `⟨e_n, x⟩` is the `n`-th coordinate. -/
lemma inner_basisVec (x : Ell2) (n : ℕ) : ⟪basisVec n, x⟫_ℂ = (x : ℕ → ℂ) n := by simp [basisVec, inner_single]

/-- The coordinates of `e_n`. -/
lemma basisVec_coord (n m : ℕ) : (basisVec n : ℕ → ℂ) m = if m = n then 1 else 0 := by simp [basisVec, Pi.single_apply]

/-- The size of the transport coefficient term. -/
lemma norm_coeffTerm_le {E : ℝ} {d z : ℂ} {K : ℝ} (hd : ‖d‖ ≤ K) :
    ‖(-(Complex.I * (Real.sqrt E : ℂ)) / 2) * (d * ((Real.sqrt 2 : ℂ) * z))‖ ≤
      Real.sqrt E * K * ‖z‖ := by
  have h2 : ‖(Real.sqrt 2 : ℂ)‖ ≤ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    simp
  have hE : ‖(-(Complex.I * (Real.sqrt E : ℂ)) / 2)‖ = Real.sqrt E / 2 := by
    simp
  rw [norm_mul, norm_mul, norm_mul, hE]
  have : 0 ≤ Real.sqrt E := Real.sqrt_nonneg _
  have hK := (norm_nonneg _).trans hd
  calc Real.sqrt E / 2 * (‖d‖ * (‖(Real.sqrt 2 : ℂ)‖ * ‖z‖)) ≤
      Real.sqrt E / 2 * (K * (2 * ‖z‖)) := by gcongr
    _ = _ := by ring

section

variable (W : ℝ → Ell2 →L[ℂ] Ell2)
include W

/-- The vector `s_E = (I + V_E^*) e₀`. -/
def radialVec  : Ell2 :=
  basisVec 0 + ContinuousLinearMap.adjoint (W (2 * π)) (basisVec 0)

/-- `b_E(θ) = ⟨e₀, W(θ) s_E⟩`. -/
def smallB  (θ : ℝ) : ℂ := (W θ (radialVec W) : ℕ → ℂ) 0

end

/-- The derivative of `b_E`. -/
def smallBDer (γ : ℝ → ℂ) (E : ℝ) (W : ℝ → Ell2 →L[ℂ] Ell2) (t : ℝ) : ℂ :=
  (-(Complex.I * (Real.sqrt E : ℂ)) / 2) *
    (deriv γ t * ((Real.sqrt 2 : ℂ) * (W t (radialVec W) : ℕ → ℂ) 1))

/-- `a_E = 2 Im ⟨e₀, V_E e₀⟩`. -/
def smallA (W : ℝ → Ell2 →L[ℂ] Ell2) : ℝ := 2 * ((W (2 * π) (basisVec 0) : ℕ → ℂ) 0).im

section

variable {γ : ℝ → ℂ}
include γ

lemma transport_zero_eq  {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2}
    (hW : IsTransport γ E W) : W 0 = 1 := by
  have := hW.2 0 ⟨le_rfl, by positivity⟩
  simpa using this

lemma smallB_eq  {K : NNReal} (hK : LipschitzWith K γ) {E : ℝ}
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W) {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * π)) :
    smallB W θ = smallB W 0 + ∫ t in (0 : ℝ)..θ, smallBDer γ E W t := by
  unfold smallB smallBDer
  rw [transport_coord_zero hK hW _ hθ, transport_zero_eq hW, ContinuousLinearMap.one_apply]

end

lemma norm_adjoint_sub_one {X : Ell2 →L[ℂ] Ell2} :
    ‖ContinuousLinearMap.adjoint X - 1‖ = ‖X - 1‖ := by
  rw [← ContinuousLinearMap.adjoint.norm_map (X - 1), map_sub,
    ← ContinuousLinearMap.star_eq_adjoint (1 : Ell2 →L[ℂ] Ell2), star_one]

section

variable {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
include γ K hK

/-- `‖s_E‖ ≤ 2`. -/
lemma norm_radialVec_le  {E : ℝ}
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W) : ‖radialVec W‖ ≤ 2 := by
  have h1 : ‖basisVec 0‖ = 1 := by simp [basisVec]
  have hV : ‖ContinuousLinearMap.adjoint (W (2 * π))‖ ≤ 1 := by
    rw [ContinuousLinearMap.adjoint.norm_map]
    exact norm_transport_le_one hK hW ⟨by positivity, le_rfl⟩
  unfold radialVec
  refine (norm_add_le _ _).trans ?_
  have := (ContinuousLinearMap.adjoint (W (2 * π))).le_opNorm (basisVec 0)
  rw [h1] at this ⊢
  nlinarith

/-- `|b'_E| ≤ C E`. -/
lemma norm_smallBDer_le  :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ E, 0 ≤ E → E ≤ 1 → ∀ W : ℝ → Ell2 →L[ℂ] Ell2, IsTransport γ E W →
      ∀ t ∈ Icc 0 (2 * π), ‖smallBDer γ E W t‖ ≤ C * E := by
  obtain ⟨c, hc0, hc⟩ := norm_transport_sub_one_le hK
  refine ⟨K * (3 * c), by positivity, fun E hE0 hE1 W hW t ht => ?_⟩
  refine (norm_coeffTerm_le (norm_deriv_le_of_lipschitz hK)).trans ?_
  have hL : (2 * π) ∈ Icc 0 (2 * π) := ⟨by positivity, le_rfl⟩
  have hs1 : (radialVec W : ℕ → ℂ) 1 =
      ((ContinuousLinearMap.adjoint (W (2 * π)) - 1) (basisVec 0) : ℕ → ℂ) 1 := by
    simp [radialVec, basisVec_coord]
  have hsplit : (W t (radialVec W) : ℕ → ℂ) 1 =
      ((W t - 1) (radialVec W) : ℕ → ℂ) 1 + (radialVec W : ℕ → ℂ) 1 := by
    simp
  have h1 : ‖(W t (radialVec W) : ℕ → ℂ) 1‖ ≤ 3 * c * Real.sqrt E := by
    rw [hsplit, hs1]
    refine (norm_add_le _ _).trans ?_
    have e1 : ‖((W t - 1) (radialVec W) : ℕ → ℂ) 1‖ ≤ c * Real.sqrt E * 2 :=
      (norm_coord_le _ _).trans (((W t - 1).le_opNorm _).trans
        (mul_le_mul (hc E hE0 hE1 W hW t ht) (norm_radialVec_le hK hW) (norm_nonneg _)
          (by positivity)))
    have e2 : ‖((ContinuousLinearMap.adjoint (W (2 * π)) - 1) (basisVec 0) : ℕ → ℂ) 1‖ ≤
        c * Real.sqrt E := by
      refine (norm_coord_le _ _).trans (((_ : Ell2 →L[ℂ] Ell2).le_opNorm _).trans ?_)
      rw [show ‖basisVec 0‖ = 1 by simp [basisVec], mul_one, norm_adjoint_sub_one]
      tauto
    linarith
  have := Real.mul_self_sqrt hE0
  calc Real.sqrt E * K * ‖(W t (radialVec W) : ℕ → ℂ) 1‖ ≤
      Real.sqrt E * K * (3 * c * Real.sqrt E) := by gcongr
    _ = K * (3 * c) * E := by linear_combination (↑K * (3 * c)) * this

end

private lemma coeffOf_mul_zero_im (z w : ℂ) :
    (((coeffOf 1 z * coeffOf 1 w) (basisVec 0) : ℕ → ℂ) 0).im =
      (conj z * w).im / 2 := by
  have hs : (Real.sqrt 2 : ℂ)^2 = 2 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hrow (a : ℂ) (u : Ell2) (n : ℕ) : (coeffOf 1 a u : ℕ → ℂ) n =
      (-Complex.I / 2) * (a * (shiftWeight n * (u : ℕ → ℂ) (n + 1)) +
        conj a * (shiftN u : ℕ → ℂ) n) := by
    simp only [coeffOf, ← shiftNAdj_eq_adjoint, Real.sqrt_one, Complex.ofReal_one, mul_one, neg_div,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, lp.coeFn_smul, lp.coeFn_add,
      Pi.smul_apply, Pi.add_apply, smul_eq_mul, shiftNAdj_apply]
  have h : ((coeffOf 1 z * coeffOf 1 w) (basisVec 0) : ℕ → ℂ) 0 = -z * conj w / 2 := by
    rw [ContinuousLinearMap.mul_apply, hrow, hrow, shiftN_apply_succ]
    norm_num [basisVec_coord, shiftWeight]
    linear_combination (z * conj w / 4) * ((Real.sqrt 2 : ℂ)^2 * Complex.I_sq) -
      (z * conj w / 4) * hs
  rw [h, show -z * conj w / 2 = -(conj (conj z * w)) / 2 by simp]
  simp [add_comm]

/-- At zero comparison energy the variation identity gives the quadratic term
of the monodromy; replacing the remaining transport by the identity costs `O(E^{3/2})`. -/
lemma smallA_approx {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
    (hclosed : γ (2 * π) = γ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ E, 0 ≤ E → E ≤ 1 → ∀ W : ℝ → Ell2 →L[ℂ] Ell2, IsTransport γ E W →
      |smallA W + E * ∫ θ in (0 : ℝ)..(2 * π), areaDensity γ θ| ≤ C * E * Real.sqrt E := by
  obtain ⟨c, hc0, hc⟩ := norm_transport_sub_one_le hK
  obtain ⟨R, hR⟩ := exists_curve_displacement_bound hK
  let B (t : ℝ) := coeffOf 1 (γ t - γ 0) * coeffOf 1 (deriv γ t)
  let M := shiftConst * K * (shiftConst * R)
  have hL : (0 : ℝ) ≤ 2 * π := by positivity
  have hB t (ht : t ∈ Icc 0 (2 * π)) := (norm_coeffOf_one_mul_le hK hR ht).2
  have hM := (norm_nonneg _).trans (hB 0 ⟨le_rfl, hL⟩)
  haveI : SecondCountableTopologyEither ℝ (Ell2 →L[ℂ] Ell2) :=
    secondCountableTopologyEither_of_left _ _
  have hBm : AEStronglyMeasurable B (volume.restrict (Icc 0 (2 * π))) :=
    ((lipschitzWith_coeffOf hK 1 (γ 0)).continuous.continuousOn.aestronglyMeasurable
      measurableSet_Icc).mul (transportCoeff_aestronglyMeasurable γ 1).restrict
  have hi :=
    Integrable.of_bound hBm _ ((ae_restrict_iff' measurableSet_Icc).mpr (Eventually.of_forall hB))
  refine ⟨2 * (M * c * (2 * π)), by positivity, fun E hE0 hE1 W hW => ?_⟩
  have hWi : IntervalIntegrable (fun t => B t * W t) volume 0 (2 * π) := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hL]
    apply Integrable.of_bound (hBm.mul (hW.1.aestronglyMeasurable measurableSet_Icc)) M
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    refine (norm_mul_le _ _).trans ?_
    calc ‖B t‖ * ‖W t‖ ≤ M * 1 :=
           mul_le_mul (hB t ht) (norm_transport_le_one hK hW ht) (norm_nonneg _) hM
       _ = M := mul_one M
  have hBi : IntervalIntegrable B volume 0 (2 * π) := by rwa [intervalIntegrable_iff_integrableOn_Icc_of_le hL]
  have hvar : W (2 * π) - 1 = (-E) • ∫ t in (0 : ℝ)..(2 * π), B t * W t := by
    have h := energy_variation hK hclosed hW (isTransport_zero γ)
    have heq : energyIntegrand γ E 0 W (fun _ => 1) = fun t => -(Real.sqrt E • (B t * W t)) := by
      funext t
      simp [energyIntegrand, B]
    simp only [Real.sqrt_zero, sub_zero, star_one] at h
    rw [heq, intervalIntegral.integral_neg, intervalIntegral.integral_smul, smul_neg, smul_smul,
      Real.mul_self_sqrt hE0] at h
    simpa [neg_smul] using h
  have herr : ‖(∫ t in (0 : ℝ)..(2 * π), B t * W t) - ∫ t in (0 : ℝ)..(2 * π), B t‖ ≤
      (M * (c * Real.sqrt E)) * (2 * π) := by
    rw [← intervalIntegral.integral_sub hWi hBi]
    refine (intervalIntegral.norm_integral_le_of_norm_le_const fun t ht => ?_).trans_eq (by
      rw [sub_zero, abs_of_nonneg hL])
    rw [uIoc_of_le hL] at ht
    have ht' : t ∈ Icc 0 (2 * π) := ⟨ht.1.le, ht.2⟩
    rw [show B t * W t - B t = B t * (W t - 1) by simp [mul_sub] ]
    exact (norm_mul_le _ _).trans (mul_le_mul (hB _ ht') (hc E hE0 hE1 W hW _ ht') (norm_nonneg _) hM)
  let ℓ := Complex.imCLM.comp
    (((lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 0).comp
      (ContinuousLinearMap.apply ℂ Ell2 (basisVec 0))).restrictScalars ℝ)
  have hℓ (T : Ell2 →L[ℂ] Ell2) : ℓ T = ((T (basisVec 0) : ℕ → ℂ) 0).im := rfl
  have hnorm (T : Ell2 →L[ℂ] Ell2) : |ℓ T| ≤ ‖T‖ :=
    (Complex.abs_im_le_norm _).trans ((norm_coord_le _ _).trans
      (by simpa [basisVec] using T.le_opNorm (basisVec 0)))
  have hmain : ℓ (∫ t in (0 : ℝ)..(2 * π), B t) = (∫ t in (0 : ℝ)..(2 * π), areaDensity γ t) / 2 := by
    rw [← ℓ.intervalIntegral_comp_comm hBi, ← intervalIntegral.integral_div]
    exact intervalIntegral.integral_congr (fun t _ => coeffOf_mul_zero_im _ _)
  have hval := congrArg ℓ hvar
  rw [map_sub, map_smul, hℓ, hℓ, ContinuousLinearMap.one_apply, basisVec_coord, if_pos rfl,
    Complex.one_im, sub_zero] at hval
  have heq : smallA W + E * ∫ t in (0 : ℝ)..(2 * π), areaDensity γ t =
      -2 * E * ℓ ((∫ t in (0 : ℝ)..(2 * π), B t * W t) - ∫ t in (0 : ℝ)..(2 * π), B t) := by
    rw [smallA, hval, map_sub, hmain]
    ring
  rw [heq, abs_mul, abs_mul, abs_of_nonneg hE0]
  calc _ ≤ 2 * E * ((M * (c * Real.sqrt E)) * (2 * π)) := by
        norm_num only [abs_of_neg (by norm_num : (-2 : ℝ) < 0), neg_neg]
        gcongr
        exact (hnorm _).trans herr
    _ = _ := by ring

/-- The `s`-derivative `ρ(θ, t)` of the Volterra kernel `w(θ, s) = ⟨e₀, W(θ) W(s)^* e₀⟩`. -/
def kernelRho (γ : ℝ → ℂ) (E : ℝ) (W : ℝ → Ell2 →L[ℂ] Ell2) (θ t : ℝ) : ℂ :=
  conj ((-(Complex.I * (Real.sqrt E : ℂ)) / 2) * (deriv γ t * ((Real.sqrt 2 : ℂ) *
    (W t (ContinuousLinearMap.adjoint (W θ) (basisVec 0)) : ℕ → ℂ) 1)))

/-- `w(θ, s) = conj ⟨e₀, W(s) W(θ)^* e₀⟩`. -/
lemma volterraKernel_eq_conj (W : ℝ → Ell2 →L[ℂ] Ell2) (θ s : ℝ) :
    volterraKernel W θ s =
      conj ((W s (ContinuousLinearMap.adjoint (W θ) (basisVec 0)) : ℕ → ℂ) 0) := by
  rw [volterraKernel, ← ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.adjoint_inner_right, ← inner_conj_symm, inner_basisVec]

section

variable {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W)
include γ K hK E W hW

/-- The Volterra kernel is the integral of `ρ` in its second variable. -/
lemma volterraKernel_eq_integral  (θ : ℝ) {s : ℝ}
    (hs : s ∈ Icc 0 (2 * π)) :
    volterraKernel W θ s = volterraKernel W θ 0 + ∫ t in (0 : ℝ)..s, kernelRho γ E W θ t := by
  rw [volterraKernel_eq_conj, volterraKernel_eq_conj, transport_coord_zero hK hW _ hs,
    transport_zero_eq hW, map_add, ← intervalIntegral.intervalIntegral_conj]
  rfl

/-- `ρ(t, t) = 0`. -/
lemma kernelRho_diag  {t : ℝ} (ht : t ∈ Icc 0 (2 * π)) :
    kernelRho γ E W t t = 0 := by
  have hu := transport_mem_unitary hK hW ht
  rw [Unitary.mem_iff, ContinuousLinearMap.star_eq_adjoint] at hu
  have : W t (ContinuousLinearMap.adjoint (W t) (basisVec 0)) = basisVec 0 := by
    rw [← ContinuousLinearMap.mul_apply, hu.2, ContinuousLinearMap.one_apply]
  simp [kernelRho, this, basisVec_coord]

end

/-- `ρ` is Lipschitz in its first variable with constant `O(E)`. -/
lemma norm_kernelRho_sub_le {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) {E : ℝ}
    (hE : 0 ≤ E) {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W) {θ₁ θ₂ t : ℝ}
    (h₁ : θ₁ ∈ Icc 0 (2 * π)) (h₂ : θ₂ ∈ Icc 0 (2 * π)) (ht : t ∈ Icc 0 (2 * π)) :
    ‖kernelRho γ E W θ₁ t - kernelRho γ E W θ₂ t‖ ≤
      K * (shiftConst * K) * E * |θ₁ - θ₂| := by
  unfold kernelRho
  rw [← map_sub, Complex.norm_conj, ← mul_sub, ← mul_sub, ← mul_sub]
  refine (norm_coeffTerm_le (norm_deriv_le_of_lipschitz hK)).trans ?_
  have hz : (W t (ContinuousLinearMap.adjoint (W θ₁) (basisVec 0)) : ℕ → ℂ) 1 -
      (W t (ContinuousLinearMap.adjoint (W θ₂) (basisVec 0)) : ℕ → ℂ) 1 =
      (W t (ContinuousLinearMap.adjoint (W θ₁ - W θ₂) (basisVec 0)) : ℕ → ℂ) 1 := by
    simp 
  rw [hz]
  have hb1 : ‖basisVec 0‖ = 1 := by simp [basisVec]
  have h1 : ‖(W t (ContinuousLinearMap.adjoint (W θ₁ - W θ₂) (basisVec 0)) : ℕ → ℂ) 1‖ ≤
      Real.sqrt E * shiftConst * K * |θ₁ - θ₂| := by
    refine (norm_coord_le _ _).trans (((W t).le_opNorm _).trans ?_)
    refine (mul_le_mul (norm_transport_le_one hK hW ht)
      ((ContinuousLinearMap.adjoint (W θ₁ - W θ₂)).le_opNorm _) (norm_nonneg _) zero_le_one).trans ?_
    rw [one_mul, hb1, mul_one, ContinuousLinearMap.adjoint.norm_map]
    exact norm_transport_sub_le_lip hK hW h₁ h₂
  have hsE := Real.mul_self_sqrt hE
  calc Real.sqrt E * K * ‖(W t (ContinuousLinearMap.adjoint (W θ₁ - W θ₂) (basisVec 0)) :
        ℕ → ℂ) 1‖ ≤ Real.sqrt E * K * (Real.sqrt E * shiftConst * K * |θ₁ - θ₂|) := by
        gcongr
    _ = _ := by linear_combination (↑K * (shiftConst * ↑K) * |θ₁ - θ₂|) * hsE

/-- For a closed Lipschitz curve, the signed area integral does not depend on the base point:
`∫ Im(conj(γ - γ(0)) γ') = ∫ Im(conj γ · γ')`. -/
lemma integral_areaDensity_eq {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
    (hclosed : γ (2 * π) = γ 0) :
    ∫ θ in (0 : ℝ)..(2 * π), areaDensity γ θ = ∫ θ in (0 : ℝ)..(2 * π), signedAreaDensity γ θ := by
  have hloc : LocallyIntegrable (deriv γ) volume := locallyIntegrable_of_bounded
      (measurable_deriv γ).aestronglyMeasurable (norm_deriv_le_of_lipschitzWith hK)
  have hint : IntervalIntegrable (deriv γ) volume 0 (2 * π) :=
    (hloc.integrableOn_isCompact isCompact_uIcc).intervalIntegrable
  have hint1 : IntervalIntegrable (fun θ => conj (γ 0) * deriv γ θ) volume 0 (2 * π) :=
    hint.const_mul _
  have hint2 : IntervalIntegrable (fun θ => Complex.imCLM (conj (γ 0) * deriv γ θ)) volume 0
      (2 * π) := ⟨Complex.imCLM.integrable_comp hint1.1, Complex.imCLM.integrable_comp hint1.2⟩
  have hA := intervalIntegrable_areaDensity hK
  have h1 : (fun θ => signedAreaDensity γ θ) =
      fun θ => areaDensity γ θ + Complex.imCLM (conj (γ 0) * deriv γ θ) := by
    funext θ; simp only [areaDensity, signedAreaDensity, map_sub, sub_mul, Complex.sub_im,
      Complex.imCLM_apply]; ring
  have h0 : ∫ θ in (0 : ℝ)..(2 * π), Complex.imCLM (conj (γ 0) * deriv γ θ) = 0 := by
    rw [Complex.imCLM.intervalIntegral_comp_comm hint1, intervalIntegral.integral_const_mul,
      integral_deriv_of_lipschitz hK, hclosed, sub_self, mul_zero, map_zero]
  simp_all

/-- Quantitative form of Lemma 8.2: `a_E ≤ -|Ω| E` for small `E > 0`. -/
theorem smallA_le_neg {Ω : Set ℂ} {γ : ℝ → ℂ} (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    (hγ : IsBoundaryParam Ω γ) :
    ∃ δ > 0, δ ≤ 1 ∧ ∀ E, 0 < E → E < δ → ∀ W : ℝ → Ell2 →L[ℂ] Ell2, IsTransport γ E W →
      smallA W ≤ -((volume Ω).toReal * E) := by
  obtain ⟨K, hK⟩ := hγ.lipschitz
  have hclosed : γ (2 * π) = γ 0 := by simpa using hγ.periodic 0
  obtain ⟨C, hC0, hC⟩ := smallA_approx hK hclosed
  set v := (volume Ω).toReal with hv
  have hvpos := ENNReal.toReal_pos
    (hL.1.1.measure_pos volume hL.1.2.nonempty).ne' hb.measure_lt_top.ne
  have harea : ∫ θ in (0 : ℝ)..(2 * π), areaDensity γ θ = 2 * v := by
    rw [integral_areaDensity_eq hK hclosed]; exact hγ.area
  refine ⟨min 1 ((v / (C + 1)) ^ 2), lt_min one_pos (by positivity), min_le_left _ _,
    fun E hE hEδ W hW => ?_⟩
  have hE1 := (hEδ.trans_le (min_le_left _ _)).le
  have hE2 := hEδ.trans_le (min_le_right _ _)
  have hs : Real.sqrt E < v / (C + 1) := by
    rw [show v / (C + 1) = Real.sqrt ((v / (C + 1)) ^ 2) from
      (Real.sqrt_sq (by positivity)).symm]
    gcongr
  have hs' : (C + 1) * Real.sqrt E < v := by
    rw [lt_div_iff₀ (by positivity)] at hs; linarith
  have h := hC E hE.le hE1 W hW
  rw [harea] at h
  have h2 := (abs_le.mp h).2
  have hsq := Real.sqrt_nonneg E
  nlinarith [mul_lt_mul_of_pos_left hs' hE]


end PolyaNeumann

end
