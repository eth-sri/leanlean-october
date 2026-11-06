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

/-- `‖W_E(θ) - I‖ ≤ c √E` for `0 ≤ E ≤ 1`. -/
local notation "Φ2" => Icc 0

lemma norm_transport_sub_one_le   (hK : LipschitzWith K γ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ E, 0 ≤ E → E ≤ 1 → ∀ W : ℝ → Ell2 →L[ℂ] Ell2, IsTransport γ E W →
      ∀ θ ∈ Φ2 (2 * π), ‖W θ - 1‖ ≤ c * Real.sqrt E := by
  set R := K * (2 * π) with hR
  have hR0 : 0 ≤ R := by positivity
  have hRb : ∀ θ ∈ Φ2 (2 * π), ‖γ θ - γ 0‖ ≤ R := fun θ hθ => by
    have := hK.dist_le_mul θ 0
    rw [dist_eq_norm, Real.dist_eq, sub_zero, abs_of_nonneg hθ.1] at this
    exact this.trans (by rw [hR]; gcongr; exact hθ.2)
  have hκ := shiftConst_nonneg
  refine ⟨shiftConst * R * (1 + 2 * π * (1 * shiftConst * K)), by positivity,
    fun E hE0 hE1 W hW θ hθ => ?_⟩
  have h := norm_transport_sub_le hK hRb (show IsTransport γ 0 (fun _ => 1) by
    refine ⟨continuousOn_const, fun θ _ => ?_⟩
    have h0 : ∀ s, transportCoeff γ 0 s = 0 := fun s => by
      simp [transportCoeff]
    simp [h0]) hW hθ
  have hs1 := Real.sqrt_le_one.mpr hE1
  have hs0 := Real.sqrt_nonneg E
  simp [abs_of_nonneg hs0] at h
  calc _ ≤ _ := h
    _ ≤ Real.sqrt E * shiftConst * R * (1 + 2 * π * (1 * shiftConst * K)) := by gcongr
    _ = _ := by ring

/-- Values of the transport have norm at most one. -/
lemma norm_transport_le_one   (hK : LipschitzWith K γ) 
     (hW : IsTransport γ E W)  (hθ : θ ∈ Φ2 (2 * π)) :
    ‖W θ‖ ≤ 1 :=
  norm_le_one_of_mem_unitary (transport_mem_unitary hK hW hθ)

/-- Lipschitz bound for the transport with constant proportional to `√E`. -/
lemma norm_transport_sub_le_lip   (hK : LipschitzWith K γ) 
     (hW : IsTransport γ E W) 
    (h₁ : θ₁ ∈ Φ2 (2 * π)) (h₂ : θ₂ ∈ Φ2 (2 * π)) :
    ‖W θ₁ - W θ₂‖ ≤ Real.sqrt E * shiftConst * K * |θ₁ - θ₂| := by
  have hC := transportCoeff_aestronglyMeasurable γ E
  have hM := transportCoeff_norm_le γ E hK
  rw [hW.2 θ₁ h₁, hW.2 θ₂ h₂, add_sub_add_left_eq_sub,
    intervalIntegral.integral_interval_sub_left (intervalIntegrable_mul_of_continuousOn hC hM hW.1 h₁)
      (intervalIntegrable_mul_of_continuousOn hC hM hW.1 h₂)]
  refine intervalIntegral.norm_integral_le_of_norm_le_const fun t ht => ?_
  calc _ ≤ _ := norm_mul_le _ _
    _ ≤ _ :=
        mul_le_mul (norm_transportCoeff_le_const hK E t) (norm_transport_le_one hK hW (by
          have := uIoc_subset_uIcc ht
          rw [mem_uIcc] at this
          rcases this with h | h
          · exact ⟨h₂.1.trans h.1, h.2.trans h₁.2⟩
          · exact ⟨h₁.1.trans h.1, h.2.trans h₂.2⟩))
          (norm_nonneg _) (by have := shiftConst_nonneg; positivity)
    _ = _ := mul_one _

/-- The zeroth coordinate of `C_E(s) x`. -/
local notation "Φ1" => Real.sqrt 2

lemma transportCoeff_coord_zero γ E s x :
    (transportCoeff γ E s x : ℕ → ℂ) 0 =
      (-(Complex.I * (Real.sqrt E : ℂ)) / 2) * (deriv γ s * ((Φ1 : ℂ) * (x : ℕ → ℂ) 1)) := by
  rw [transportCoeff_apply_coord]
  simp [shiftWeight]

/-- The first coordinate of `C_E(s) x`. -/
lemma transportCoeff_coord_one γ E s x :
    (transportCoeff γ E s x : ℕ → ℂ) 1 =
      (-(Complex.I * (Real.sqrt E : ℂ)) / 2) * (deriv γ s * (x : ℕ → ℂ) 2 +
        conj (deriv γ s) * ((Φ1 : ℂ) * (x : ℕ → ℂ) 0)) := by
  rw [transportCoeff_apply_coord]
  simp [shiftWeight]

/-- Coordinates are bounded by the norm. -/
lemma norm_coord_le (x : Ell2) n : ‖(x : ℕ → ℂ) n‖ ≤ ‖x‖ := by
  exact lp.norm_apply_le_norm (p := 2) (by norm_num) x n

/-- The zeroth row of the transport equation. -/
lemma transport_coord_zero   (hK : LipschitzWith K γ) 
     (hW : IsTransport γ E W) x 
    (hθ : θ ∈ Φ2 (2 * π)) :
    (W θ x : ℕ → ℂ) 0 = (x : ℕ → ℂ) 0 + ∫ s in 0..θ,
      (-(Complex.I * (Real.sqrt E : ℂ)) / 2) *
        (deriv γ s * ((Φ1 : ℂ) * (W s x : ℕ → ℂ) 1)) := by
  rw [transport_coord_eq hK hW x 0 hθ]
  simp [transportCoeff_coord_zero]

/-- The first row of the transport equation. -/
lemma transport_coord_one   (hK : LipschitzWith K γ) 
     (hW : IsTransport γ E W) x 
    (hθ : θ ∈ Φ2 (2 * π)) :
    (W θ x : ℕ → ℂ) 1 = (x : ℕ → ℂ) 1 + ∫ s in 0..θ,
      (-(Complex.I * (Real.sqrt E : ℂ)) / 2) * (deriv γ s * (W s x : ℕ → ℂ) 2 +
        conj (deriv γ s) * ((Φ1 : ℂ) * (W s x : ℕ → ℂ) 0)) := by
  rw [transport_coord_eq hK hW x 1 hθ]
  simp [transportCoeff_coord_one]

/-- `⟨e_n, x⟩` is the `n`-th coordinate. -/
lemma inner_basisVec x n : ⟪basisVec n, x⟫_ℂ = (x : ℕ → ℂ) n := by
  simp [basisVec, inner_single]

/-- The coordinates of `e_n`. -/
lemma basisVec_coord n m : (basisVec n : ℕ → ℂ) m = if m = n then 1 else 0 := by
  simp [basisVec, Pi.single_apply]

/-- The size of the transport coefficient term. -/
lemma norm_coeffTerm_le    (hd : ‖d‖ ≤ K) :
    ‖(-(Complex.I * (Real.sqrt E : ℂ)) / 2) * (d * ((Φ1 : ℂ) * z))‖ ≤
      Real.sqrt E * K * ‖z‖ := by
  have h2 : ‖(Φ1 : ℂ)‖ ≤ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    nlinarith [Real.sq_sqrt (show 0 ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  rw [norm_mul, norm_mul, norm_mul, show ‖(-(Complex.I * (Real.sqrt E : ℂ)) / 2)‖ = Real.sqrt E / 2 by
    rw [norm_div, norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    simp]
  have hK := (norm_nonneg _).trans hd
  calc _ ≤
      Real.sqrt E / 2 * (K * (2 * ‖z‖)) := by gcongr
    _ = _ := by ring

/-- The vector `s_E = (I + V_E^*) e₀`. -/
local notation "Φ0" => basisVec 0

def radialVec (W : ℝ → Ell2 →L[ℂ] Ell2) : Ell2 :=
  Φ0 + ContinuousLinearMap.adjoint (W (2 * π)) (Φ0)

/-- `b_E(θ) = ⟨e₀, W(θ) s_E⟩`. -/
def smallB (W : ℝ → Ell2 →L[ℂ] Ell2) (θ : ℝ) : ℂ := (W θ (radialVec W) : ℕ → ℂ) 0

/-- The derivative of `b_E`. -/
def smallBDer (γ : ℝ → ℂ) (E : ℝ) (W : ℝ → Ell2 →L[ℂ] Ell2) (t : ℝ) : ℂ :=
  (-(Complex.I * (Real.sqrt E : ℂ)) / 2) *
    (deriv γ t * ((Φ1 : ℂ) * (W t (radialVec W) : ℕ → ℂ) 1))

/-- `a_E = 2 Im ⟨e₀, V_E e₀⟩`. -/
def smallA (W : ℝ → Ell2 →L[ℂ] Ell2) : ℝ := 2 * ((W (2 * π) (Φ0) : ℕ → ℂ) 0).im

lemma transport_zero_eq   
    (hW : IsTransport γ E W) : W 0 = 1 := by
  simpa using hW.2 0 ⟨le_rfl, by positivity⟩

lemma smallB_eq   (hK : LipschitzWith K γ) 
     (hW : IsTransport γ E W)  (hθ : θ ∈ Φ2 (2 * π)) :
    smallB W θ = smallB W 0 + ∫ t in 0..θ, smallBDer γ E W t := by
  unfold smallB smallBDer
  rw [transport_coord_zero hK hW _ hθ, transport_zero_eq hW, ContinuousLinearMap.one_apply]

lemma norm_adjoint_sub_one {X : Ell2 →L[ℂ] Ell2} :
    ‖ContinuousLinearMap.adjoint X - 1‖ = ‖X - 1‖ := by
  rw [← ContinuousLinearMap.adjoint.norm_map (X - 1), map_sub,
    ← ContinuousLinearMap.star_eq_adjoint (1 : Ell2 →L[ℂ] Ell2), star_one]

/-- `‖s_E‖ ≤ 2`. -/
lemma norm_radialVec_le   (hK : LipschitzWith K γ) 
     (hW : IsTransport γ E W) : ‖radialVec W‖ ≤ 2 := by
  have h1 : ‖Φ0‖ = 1 := by simp [basisVec]
  have hV : ‖ContinuousLinearMap.adjoint (W (2 * π))‖ ≤ 1 := by
    rw [ContinuousLinearMap.adjoint.norm_map]
    exact norm_transport_le_one hK hW ⟨by positivity, le_rfl⟩
  unfold radialVec
  refine (norm_add_le _ _).trans ?_
  have := (ContinuousLinearMap.adjoint (W (2 * π))).le_opNorm (Φ0)
  rw [h1] at this ⊢
  nlinarith

/-- `|b'_E| ≤ C E`. -/
lemma norm_smallBDer_le   (hK : LipschitzWith K γ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ E, 0 ≤ E → E ≤ 1 → ∀ W : ℝ → Ell2 →L[ℂ] Ell2, IsTransport γ E W →
      ∀ t ∈ Φ2 (2 * π), ‖smallBDer γ E W t‖ ≤ C * E := by
  obtain ⟨c, hc0, hc⟩ := norm_transport_sub_one_le hK
  refine ⟨K * (3 * c), by positivity, fun E hE0 hE1 W hW t ht => ?_⟩
  refine (norm_coeffTerm_le (norm_deriv_le_of_lipschitz hK)).trans ?_
  have hs1 : (radialVec W) 1 =
      ((ContinuousLinearMap.adjoint (W (2 * π)) - 1) (Φ0)) 1 := by
    simp [radialVec, basisVec_coord]
  have h1 : ‖(W t (radialVec W)) 1‖ ≤ 3 * c * Real.sqrt E := by
    rw [show (W t (radialVec W)) 1 = ((W t - 1) (radialVec W)) 1 + (radialVec W) 1 by
      simp, hs1]
    refine (norm_add_le _ _).trans ?_
    have e1 : ‖((W t - 1) (radialVec W)) 1‖ ≤ c * Real.sqrt E * 2 :=
      (norm_coord_le _ _).trans (((W t - 1).le_opNorm _).trans
        (mul_le_mul (hc E hE0 hE1 W hW t ht) (norm_radialVec_le hK hW) (norm_nonneg _)
          (by positivity)))
    have e2 : ‖((ContinuousLinearMap.adjoint (W (2 * π)) - 1) (Φ0)) 1‖ ≤
        c * Real.sqrt E := by
      refine (norm_coord_le _ _).trans (((_ : Ell2 →L[ℂ] Ell2).le_opNorm _).trans ?_)
      rw [show ‖Φ0‖ = 1 by simp [basisVec], mul_one, norm_adjoint_sub_one]
      exact hc E hE0 hE1 W hW _ ⟨by positivity, le_rfl⟩
    linarith
  calc _ ≤
      Real.sqrt E * K * (3 * c * Real.sqrt E) := by gcongr
    _ = _ := by linear_combination (↑K * (3 * c)) * Real.mul_self_sqrt hE0

/-- Bounded measurable functions are interval integrable. -/
lemma intervalIntegrable_of_norm_le {f : ℝ → ℂ} (hf : AEStronglyMeasurable f volume) 
    (hB : ∀ t, ‖f t‖ ≤ B) a b : IntervalIntegrable f volume a b :=
  (intervalIntegrable_const (c := B)).mono_fun' hf.restrict (Eventually.of_forall hB)

/-- The rows of the transport equation are interval integrable on subintervals. -/
lemma transport_coord_intervalIntegrable'   (hK : LipschitzWith K γ)
      (hW : IsTransport γ E W) v n 
    (ht : t ∈ Φ2 (2 * π)) :
    IntervalIntegrable (fun s => (transportCoeff γ E s (W s v) : ℕ → ℂ) n) volume 0 t :=
  (transport_coord_intervalIntegrable hK hW v n).mono_set (by
    rw [uIcc_of_le ht.1, uIcc_of_le (by positivity)]
    exact Icc_subset_Icc le_rfl ht.2)

/-- `a_E = -E ∫₀^L Im(conj(γ - γ(0)) γ') + O(E^{3/2})`. -/
lemma smallA_approx  {K : NNReal} (hK : LipschitzWith K γ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ E, 0 ≤ E → E ≤ 1 → ∀ W : ℝ → Ell2 →L[ℂ] Ell2, IsTransport γ E W →
      |smallA W + E * ∫ θ in 0..(2 * π), areaDensity γ θ| ≤ C * E * Real.sqrt E := by
  obtain ⟨c₁, hc₁0, hc₁⟩ := norm_transport_sub_one_le hK
  set C₂ : ℝ := π * (K * c₁ + K * 2 * c₁) with hC₂
  have hconjc : Continuous fun t => conj (γ t - γ 0) :=
    Complex.continuous_conj.comp (hK.continuous.sub continuous_const)
  refine ⟨2 * ((2 * π) * (K * C₂)), by positivity, fun E hE0 hE1 W hW => ?_⟩
  have hL : 2 * π ∈ Φ2 (2 * π) := ⟨by positivity, le_rfl⟩
  have hsE := Real.mul_self_sqrt hE0
  set c := -(Complex.I * (Real.sqrt E)) / 2 with hc
  have hc2 : c * c = -E / 4 := by
    rw [hc]
    have : (Real.sqrt E : ℂ) * Real.sqrt E = E := by exact_mod_cast hsE
    linear_combination ((Real.sqrt E : ℂ) ^ 2 / 4) * Complex.I_sq + (-1 / 4) * this
  have hdK := fun t => norm_deriv_le_of_lipschitz hK (x₀ := t)
  have h2 : ‖(Φ1 : ℂ)‖ ≤ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    nlinarith [Real.sq_sqrt (show 0 ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have hsq2 : (Φ1 : ℂ) * Φ1 = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
  -- the approximation `P t = c √2 conj(γ t - γ 0)` of the first coordinate
  set P : ℝ → ℂ := fun t => c * ((Φ1) * conj (γ t - γ 0)) with hP
  have hdmeas : AEStronglyMeasurable (deriv γ) volume := (measurable_deriv γ).aestronglyMeasurable
  have hP1 : ∀ t ∈ Φ2 (2 * π), ‖(W t (Φ0)) 1 - P t‖ ≤ Real.sqrt E * C₂ *
      Real.sqrt E := by
    intro t ht
    rw [transport_coord_one hK hW _ ht, basisVec_coord, if_neg (by norm_num), zero_add]
    have hPt : P t = ∫ s in 0..t, c * (conj (deriv γ s) * ((Φ1) * 1)) := by
      rw [intervalIntegral.integral_const_mul, mul_one, intervalIntegral.integral_mul_const,
        intervalIntegral_conj, integral_deriv_of_lipschitz hK]
      simp only [hP]; ring
    have hi1 : IntervalIntegrable (fun s => c * (deriv γ s * (W s (Φ0)) 2 +
        conj (deriv γ s) * ((Φ1 : ℂ) * (W s (Φ0)) 0))) volume 0 t := by
      simpa only [transportCoeff_coord_one] using transport_coord_intervalIntegrable' hK hW (Φ0) 1 ht
    rw [hPt, ← intervalIntegral.integral_sub hi1 (by
      refine intervalIntegrable_of_norm_le ?_ (B := ‖c‖ * (K * (2 * 1))) (fun s => ?_) 0 t
      · exact (((Complex.continuous_conj.comp_aestronglyMeasurable hdmeas).mul_const _).const_mul
          _)
      · rw [norm_mul, norm_mul, norm_mul, Complex.norm_conj]
        gcongr
        · exact hdK s
        · simp)]
    have hb : ∀ s ∈ Ι 0 t, ‖c * (deriv γ s * (W s (Φ0) : ℕ → ℂ) 2 +
        conj (deriv γ s) * ((Φ1) * (W s (Φ0)) 0)) -
        c * (conj (deriv γ s) * ((Φ1) * 1))‖ ≤
          Real.sqrt E / 2 * (K * (c₁ * Real.sqrt E) + K * (2 * (c₁ * Real.sqrt E))) := by
      intro s hs
      rw [uIoc_of_le ht.1] at hs
      have hWs := hc₁ E hE0 hE1 W hW s ⟨hs.1.le, hs.2.trans ht.2⟩
      have hb1 : ‖Φ0‖ = 1 := by simp [basisVec]
      have e0 : ‖(W s (Φ0)) 0 - 1‖ ≤ c₁ * Real.sqrt E := by
        have : (W s (Φ0)) 0 - 1 = ((W s - 1) (Φ0)) 0 := by
          simp [basisVec_coord]
        rw [this]
        refine (norm_coord_le _ _).trans (((W s - 1).le_opNorm _).trans ?_)
        rw [hb1, mul_one]; exact hWs
      rw [← mul_sub, norm_mul, show ‖c‖ = Real.sqrt E / 2 by
        rw [hc, norm_div, norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg E)]
        simp]
      gcongr
      rw [show deriv γ s * (W s (Φ0)) 2 +
          conj (deriv γ s) * ((Φ1) * (W s (Φ0)) 0) -
          conj (deriv γ s) * ((Φ1) * 1) = deriv γ s * (W s (Φ0)) 2 +
          conj (deriv γ s) * ((Φ1) * ((W s (Φ0)) 0 - 1)) by ring]
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_mul]; exact mul_le_mul (hdK s) (by
          have : (W s (Φ0) : ℕ → ℂ) 2 = ((W s - 1) (Φ0)) 2 := by
            simp [basisVec_coord]
          rw [this]
          refine (norm_coord_le _ _).trans (((W s - 1).le_opNorm _).trans ?_)
          rw [hb1, mul_one]; exact hWs) (norm_nonneg _) (by positivity)
      · rw [norm_mul, norm_mul, Complex.norm_conj]
        exact mul_le_mul (hdK s) (mul_le_mul h2 e0 (norm_nonneg _) (by norm_num))
          (by positivity) (by positivity)
    refine (intervalIntegral.norm_integral_le_of_norm_le_const hb).trans ?_
    rw [sub_zero, abs_of_nonneg ht.1]
    have : Real.sqrt E / 2 * (K * (c₁ * Real.sqrt E) + K * (2 * (c₁ * Real.sqrt E))) * t ≤
        Real.sqrt E / 2 * (K * (c₁ * Real.sqrt E) + K * (2 * (c₁ * Real.sqrt E))) * (2 * π) := by
      gcongr; exact ht.2
    refine this.trans (le_of_eq ?_)
    rw [hC₂]; ring
  -- the zeroth coordinate of `V e₀`
  have hV := transport_coord_zero hK hW (Φ0) hL
  rw [basisVec_coord, if_pos rfl] at hV
  have hWint : IntervalIntegrable (fun t => c * (deriv γ t * ((Φ1) *
      (W t (Φ0)) 1))) volume 0 (2 * π) := by
    simpa only [transportCoeff_coord_zero] using transport_coord_intervalIntegrable' hK hW (Φ0) 0 hL
  have hmain : ∫ t in 0..(2 * π), c * (deriv γ t * ((Φ1 : ℂ) * P t)) =
      -E / 2 * ∫ t in 0..(2 * π), conj (γ t - γ 0) * deriv γ t := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [hP]
    linear_combination (2 * conj (γ t - γ 0) * deriv γ t) * hc2 +
      c * c * conj (γ t - γ 0) * deriv γ t * hsq2
  -- assemble
  have hdiff : ‖((W (2 * π) (Φ0) : ℕ → ℂ) 0 - 1) -
      -E / 2 * ∫ t in 0..(2 * π), conj (γ t - γ 0) * deriv γ t‖ ≤
        2 * π * (K * C₂) * E * Real.sqrt E := by
    rw [hV, add_sub_cancel_left, ← hmain, ← intervalIntegral.integral_sub hWint (by
      obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Φ2 (2 * π))
        (f := P) (by simp only [hP]; exact (continuous_const.mul (continuous_const.mul hconjc)).continuousOn)
      have hm : AEStronglyMeasurable (fun t => c * (deriv γ t * ((Φ1) * P t)))
          (volume.restrict (Ι 0 (2 * π))) := by
        have hPc : Continuous P := by simp only [hP]; exact continuous_const.mul (continuous_const.mul hconjc)
        exact ((hdmeas.mul (hPc.aestronglyMeasurable.const_mul _)).const_mul _).restrict
      refine (intervalIntegrable_const (c := ‖c‖ * (K * (2 * B)))).mono_fun' hm ?_
      rw [uIoc_of_le (by positivity)]
      refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun t ht => ?_)
      dsimp only
      rw [norm_mul, norm_mul, norm_mul]
      gcongr
      · exact hdK t
      · exact hB t ⟨ht.1.le, ht.2⟩)]
    have hb : ∀ t ∈ Ι 0 (2 * π), ‖c * (deriv γ t * ((Φ1 : ℂ) *
        (W t (Φ0)) 1)) - c * (deriv γ t * ((Φ1) * P t))‖ ≤
          Real.sqrt E * K * (Real.sqrt E * C₂ * Real.sqrt E) := by
      intro t ht
      rw [uIoc_of_le (by positivity)] at ht
      rw [show c * (deriv γ t * ((Φ1) * (W t (Φ0)) 1)) -
          c * (deriv γ t * ((Φ1) * P t)) =
          c * (deriv γ t * ((Φ1) * ((W t (Φ0)) 1 - P t))) by ring]
      refine (norm_coeffTerm_le (hdK t)).trans ?_
      gcongr
      exact hP1 t ⟨ht.1.le, ht.2⟩
    refine (intervalIntegral.norm_integral_le_of_norm_le_const hb).trans (le_of_eq ?_)
    rw [sub_zero, abs_of_nonneg (by positivity)]
    linear_combination (2 * π * K * C₂ * Real.sqrt E) * hsE
  have him := (Complex.abs_im_le_norm _).trans hdiff
  rw [Complex.sub_im, Complex.sub_im, Complex.one_im, sub_zero] at him
  rw [(show (-E / 2 * ∫ t in 0..(2 * π), conj (γ t - γ 0) * deriv γ t).im = -E / 2 * ∫ θ in 0..(2 * π), areaDensity γ θ by
    rw [← (show (∫ t in 0..(2 * π), conj (γ t - γ 0) * deriv γ t).im = ∫ θ in 0..(2 * π), areaDensity γ θ by
      have hint : IntervalIntegrable (fun t => conj (γ t - γ 0) * deriv γ t) volume 0 (2 * π) := by
        obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Φ2 (2 * π))
          (f := fun t => conj (γ t - γ 0)) hconjc.continuousOn
        refine (intervalIntegrable_const (c := B * K)).mono_fun' ((hconjc.aestronglyMeasurable.mul hdmeas).restrict) ?_
        rw [uIoc_of_le (by positivity)]
        refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun t ht => ?_)
        dsimp only
        rw [norm_mul]
        exact mul_le_mul (hB t ⟨ht.1.le, ht.2⟩) (hdK t) (norm_nonneg _)
          ((norm_nonneg _).trans (hB 0 ⟨le_rfl, by positivity⟩))
      have := Complex.imCLM.intervalIntegral_comp_comm hint
      simp only [Complex.imCLM_apply] at this
      rw [← this]
      rfl)]
    simp [Complex.mul_im])] at him
  unfold smallA
  rw [show 2 * ((W (2 * π) (Φ0)) 0).im + E * ∫ θ in 0..(2 * π),
      areaDensity γ θ = 2 * (((W (2 * π) (Φ0)) 0).im -
        -E / 2 * ∫ θ in 0..(2 * π), areaDensity γ θ) by ring, abs_mul, abs_two]
  linarith

/-- The `s`-derivative `ρ(θ, t)` of the Volterra kernel `w(θ, s) = ⟨e₀, W(θ) W(s)^* e₀⟩`. -/
def kernelRho (γ : ℝ → ℂ) (E : ℝ) (W : ℝ → Ell2 →L[ℂ] Ell2) (θ t : ℝ) : ℂ :=
  conj ((-(Complex.I * (Real.sqrt E : ℂ)) / 2) * (deriv γ t * ((Φ1 : ℂ) *
    (W t (ContinuousLinearMap.adjoint (W θ) (Φ0)) : ℕ → ℂ) 1)))

/-- `w(θ, s) = conj ⟨e₀, W(s) W(θ)^* e₀⟩`. -/
lemma volterraKernel_eq_conj W θ s :
    volterraKernel W θ s =
      conj ((W s (ContinuousLinearMap.adjoint (W θ) (Φ0)) : ℕ → ℂ) 0) := by
  rw [volterraKernel, ← ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.adjoint_inner_right, ← inner_conj_symm, inner_basisVec]

/-- The Volterra kernel is the integral of `ρ` in its second variable. -/
lemma volterraKernel_eq_integral   (hK : LipschitzWith K γ) 
     (hW : IsTransport γ E W) θ 
    (hs : s ∈ Φ2 (2 * π)) :
    volterraKernel W θ s = volterraKernel W θ 0 + ∫ t in 0..s, kernelRho γ E W θ t := by
  rw [volterraKernel_eq_conj, volterraKernel_eq_conj, transport_coord_zero hK hW _ hs,
    transport_zero_eq hW, ContinuousLinearMap.one_apply, map_add, ← intervalIntegral_conj]
  rfl

/-- `ρ(t, t) = 0`. -/
lemma kernelRho_diag   (hK : LipschitzWith K γ) 
     (hW : IsTransport γ E W)  (ht : t ∈ Φ2 (2 * π)) :
    kernelRho γ E W t t = 0 := by
  have hu := transport_mem_unitary hK hW ht
  rw [Unitary.mem_iff, ContinuousLinearMap.star_eq_adjoint] at hu
  simp [kernelRho, show W t (ContinuousLinearMap.adjoint (W t) (Φ0)) = Φ0 by
    rw [← ContinuousLinearMap.mul_apply, hu.2, ContinuousLinearMap.one_apply], basisVec_coord]

/-- `ρ` is Lipschitz in its first variable with constant `O(E)`. -/
lemma norm_kernelRho_sub_le   (hK : LipschitzWith K γ) 
    (hE : 0 ≤ E)  (hW : IsTransport γ E W) 
    (h₁ : θ₁ ∈ Φ2 (2 * π)) (h₂ : θ₂ ∈ Φ2 (2 * π)) (ht : t ∈ Φ2 (2 * π)) :
    ‖kernelRho γ E W θ₁ t - kernelRho γ E W θ₂ t‖ ≤
      K * (shiftConst * K) * E * |θ₁ - θ₂| := by
  unfold kernelRho
  rw [← map_sub, Complex.norm_conj, ← mul_sub, ← mul_sub, ← mul_sub]
  refine (norm_coeffTerm_le (norm_deriv_le_of_lipschitz hK)).trans ?_
  rw [show (W t (ContinuousLinearMap.adjoint (W θ₁) (Φ0))) 1 - (W t (ContinuousLinearMap.adjoint (W θ₂) (Φ0))) 1 = (W t (ContinuousLinearMap.adjoint (W θ₁ - W θ₂) (Φ0))) 1 by
    simp]
  have h1 : ‖(W t (ContinuousLinearMap.adjoint (W θ₁ - W θ₂) (Φ0))) 1‖ ≤
      Real.sqrt E * shiftConst * K * |θ₁ - θ₂| := by
    refine (norm_coord_le _ _).trans (((W t).le_opNorm _).trans ?_)
    refine (mul_le_mul (norm_transport_le_one hK hW ht)
      ((ContinuousLinearMap.adjoint (W θ₁ - W θ₂)).le_opNorm _) (norm_nonneg _) zero_le_one).trans ?_
    rw [one_mul, show ‖Φ0‖ = 1 by simp [basisVec], mul_one, ContinuousLinearMap.adjoint.norm_map]
    exact norm_transport_sub_le_lip hK hW h₁ h₂
  calc _ ≤ Real.sqrt E * K * (Real.sqrt E * shiftConst * K * |θ₁ - θ₂|) := by
        gcongr
    _ = _ := by linear_combination (↑K * (shiftConst * ↑K) * |θ₁ - θ₂|) * Real.mul_self_sqrt hE

end PolyaNeumann

end
