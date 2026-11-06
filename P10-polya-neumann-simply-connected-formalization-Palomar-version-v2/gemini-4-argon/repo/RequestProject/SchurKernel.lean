module

public import RequestProject.HerglotzSchur

/-!
# The kernel part of the small-energy Schur complement (Lemma 8.4, kernel estimate)

Let `w(θ, s) = ⟨e₀, W(θ) W(s)^* e₀⟩` be the Volterra kernel of the transport, `b_E` the function
`smallB`, `β_E = b_E - 2` and `a_E = smallA W`. The kernel

  `r(θ, s) = i sgn(θ - s) (w(θ, s) - 1) - a_E⁻¹ β_E(θ) conj(β_E(s))`

(`schurKernel`) is periodic in both variables on `[0, L]²` (`L = 2π`) and absolutely continuous in
`s`, with an `s`-derivative `ρ` (`schurRho`) that is Lipschitz in `θ` with constant `O(E)` once
`|a_E| ≳ E`. For a bounded measurable `g` with `∫₀^L g = 0` and primitive `G`,

  `Re ∫ conj(g) i (T_E - T_E^*) g - |∫ conj(b_E) g|² / a_E
      = Re ∫ conj(g) 2i G + Re ∫ conj(g(θ)) ∫ r(θ, s) g(s) ds dθ`   (`re_volterra_sub_schur_eq`),

and the last term is bounded by `C E (∫₀^L |G - c|)²` for every constant `c`
(`norm_schurKernel_form_le`, from the double integration by parts `norm_kernel_form_le`).
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ComplexConjugate Real InnerProductSpace Interval

noncomputable section

namespace PolyaNeumann

/-- `β_E = b_E - 2`. -/
def schurBeta (W : ℝ → Ell2 →L[ℂ] Ell2) (θ : ℝ) : ℂ := smallB W θ - 2

/-- The jump part `i sgn(θ - s) (w(θ, s) - 1)` of the kernel. -/
def schurKernel0 (W : ℝ → Ell2 →L[ℂ] Ell2) (θ s : ℝ) : ℂ :=
  if s ≤ θ then Complex.I * (volterraKernel W θ s - 1) else -(Complex.I * (volterraKernel W θ s - 1))

/-- The corrected periodic kernel `r(θ, s) = i sgn(θ - s)(w(θ, s) - 1) - a⁻¹ β(θ) conj(β(s))`. -/
def schurKernel (W : ℝ → Ell2 →L[ℂ] Ell2) (θ s : ℝ) : ℂ :=
  schurKernel0 W θ s - schurBeta W θ * conj (schurBeta W s) / (smallA W : ℂ)

/-- The `s`-derivative of the jump part. -/
def schurRho0 (γ : ℝ → ℂ) (E : ℝ) (W : ℝ → Ell2 →L[ℂ] Ell2) (θ t : ℝ) : ℂ :=
  if t ≤ θ then Complex.I * kernelRho γ E W θ t else -(Complex.I * kernelRho γ E W θ t)

/-- The `s`-derivative of the corrected kernel. -/
def schurRho (γ : ℝ → ℂ) (E : ℝ) (W : ℝ → Ell2 →L[ℂ] Ell2) (θ t : ℝ) : ℂ :=
  schurRho0 γ E W θ t - schurBeta W θ * conj (smallBDer γ E W t) / (smallA W : ℂ)

variable {γ : ℝ → ℂ} {K : NNReal} {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2}

local notation "Φ0" => IsTransport γ E W

local notation "Φ1" => Icc 0

local notation "Φ4" => LipschitzWith K γ

local notation "Φ11" => volterraKernel W

lemma volterraKernel_diag (hK : Φ4) (hW : Φ0) 
    (hθ : θ ∈ Φ1 (2 * π)) : Φ11 θ θ = 1 := by
  have hu := transport_mem_unitary hK hW hθ
  rw [Unitary.mem_iff, ContinuousLinearMap.star_eq_adjoint] at hu
  rw [volterraKernel, ← ContinuousLinearMap.mul_apply, hu.2, ContinuousLinearMap.one_apply]
  simp [basisVec]

lemma conj_volterraKernel W θ s :
    conj (volterraKernel W s θ) = volterraKernel W θ s := by
  rw [volterraKernel, volterraKernel, inner_conj_symm, ← ContinuousLinearMap.adjoint_inner_right,
    ContinuousLinearMap.adjoint_inner_left]

local notation "Φ10" => smallB W

lemma volterraKernel_add_end (hW : Φ0) θ :
    Φ11 θ (2 * π) + Φ11 θ 0 = Φ10 θ := by
  rw [volterraKernel, volterraKernel, transport_zero_eq hW, smallB, ← inner_basisVec,
    ← inner_add_right, ← map_add, radialVec, ← ContinuousLinearMap.star_eq_adjoint (1 : Ell2 →L[ℂ] Ell2),
    star_one, ContinuousLinearMap.one_apply, add_comm]

local notation "Φ5" => smallA W

lemma smallB_end_sub (hK : Φ4) (hW : Φ0) :
    Φ10 (2 * π) - smallB W 0 = Complex.I * Φ5 := by
  have hu := transport_mem_unitary hK hW ⟨by positivity, le_rfl⟩
  rw [Unitary.mem_iff, ContinuousLinearMap.star_eq_adjoint] at hu
  have h1 : W (2 * π) (ContinuousLinearMap.adjoint (W (2 * π)) (basisVec 0)) = basisVec 0 := by
    rw [← ContinuousLinearMap.mul_apply, hu.2, ContinuousLinearMap.one_apply]
  unfold smallB radialVec smallA
  rw [transport_zero_eq hW, ContinuousLinearMap.one_apply, map_add, h1]
  simp [show (ContinuousLinearMap.adjoint (W (2 * π)) (basisVec 0)) 0 = conj ((W (2 * π) (basisVec 0)) 0) by
    rw [← inner_basisVec, ← inner_basisVec, ContinuousLinearMap.adjoint_inner_right,
      inner_conj_symm], basisVec_coord]
  apply Complex.ext <;> simp <;> ring

lemma intervalIntegrable_conj' {f : ℝ → ℂ} {a b : ℝ} (hf : IntervalIntegrable f volume a b) :
    IntervalIntegrable (fun t => conj (f t)) volume a b :=
  ⟨Complex.conjCLE.toContinuousLinearMap.integrable_comp hf.1,
    Complex.conjCLE.toContinuousLinearMap.integrable_comp hf.2⟩

local notation "Φ9" => kernelRho γ E W

lemma kernelRho_intervalIntegrable (hK : Φ4) (hW : Φ0) (θ : ℝ)
    {t : ℝ} (ht : t ∈ Φ1 (2 * π)) : IntervalIntegrable (Φ9 θ) volume 0 t := by
  have := transport_coord_intervalIntegrable' hK hW
    (ContinuousLinearMap.adjoint (W θ) (basisVec 0)) 0 ht
  simp [transportCoeff_coord_zero] at this
  exact intervalIntegrable_conj' this

local notation "Φ2" => smallBDer γ E W

lemma smallBDer_intervalIntegrable (hK : Φ4) (hW : Φ0)
     (ht : t ∈ Φ1 (2 * π)) : IntervalIntegrable (Φ2) volume 0 t := by
  have := transport_coord_intervalIntegrable' hK hW (radialVec W) 0 ht
  simp [transportCoeff_coord_zero] at this
  exact this

local notation "Φ7" => schurBeta W

local notation "Φ8" => schurBeta W 0

lemma schurBeta_eq (hK : Φ4) (hW : Φ0) 
    (hs : s ∈ Φ1 (2 * π)) :
    Φ7 s = Φ8 + ∫ t in 0..s, Φ2 t := by
  rw [schurBeta, schurBeta, smallB_eq hK hW hs]
  ring

local notation "Φ3" => schurRho0 γ E W

lemma schurRho0_intervalIntegrable (hK : Φ4) (hW : Φ0) 
    (hθ : θ ∈ Φ1 (2 * π)) (hs : s ∈ Φ1 (2 * π)) :
    IntervalIntegrable (Φ3 θ) volume 0 s := by
  have hi :=
    kernelRho_intervalIntegrable hK hW θ hs
  rcases le_or_gt s θ with hsθ | hθs
  · refine (hi.const_mul Complex.I).congr fun t ht => ?_
    rw [uIoc_of_le hs.1] at ht
    exact (if_pos (ht.2.trans hsθ)).symm
  · have hiθ :=
      kernelRho_intervalIntegrable hK hW θ hθ
    exact (show IntervalIntegrable (Φ3 θ) volume 0 θ by
      refine (hiθ.const_mul Complex.I).congr fun t ht => ?_
      rw [uIoc_of_le hθ.1] at ht
      exact (if_pos ht.2).symm).trans (by
      refine ((hiθ.symm.trans hi).const_mul Complex.I).neg.congr fun t ht => ?_
      rw [uIoc_of_le hθs.le] at ht
      exact (if_neg (not_le.mpr ht.1)).symm)

local notation "Φ6" => schurRho γ E W

local notation "Φ12" => schurKernel0 W

lemma schurKernel_eq_integral (hK : Φ4) (hW : Φ0) {θ s : ℝ}
    (hθ : θ ∈ Φ1 (2 * π)) (hs : s ∈ Φ1 (2 * π)) :
    schurKernel W θ s = schurKernel W θ 0 + ∫ t in 0..s, Φ6 θ t := by
  rw [show ∫ t in 0..s, Φ6 θ t = (∫ t in 0..s, Φ3 θ t) - Φ7 θ * conj (∫ t in 0..s, Φ2 t) / (Φ5) by
    unfold schurRho
    rw [intervalIntegral.integral_sub (schurRho0_intervalIntegrable hK hW hθ hs) (((intervalIntegrable_conj' (smallBDer_intervalIntegrable hK hW hs)).const_mul _).div_const _), intervalIntegral.integral_div,
      intervalIntegral.integral_const_mul, intervalIntegral_conj], schurKernel, schurKernel, show Φ12 θ s = Φ12 θ 0 + ∫ t in 0..s, Φ3 θ t by
    have h0 : Φ12 θ 0 = Complex.I * (Φ11 θ 0 - 1) := if_pos hθ.1
    rw [h0]
    rcases le_or_gt s θ with hsθ | hθs
    · have hc : ∫ t in 0..s, Φ3 θ t =
          ∫ t in 0..s, Complex.I * Φ9 θ t := by
        refine intervalIntegral.integral_congr fun t ht => ?_
        rw [uIcc_of_le hs.1] at ht
        exact if_pos (ht.2.trans hsθ)
      rw [schurKernel0, if_pos hsθ, hc, intervalIntegral.integral_const_mul,
        volterraKernel_eq_integral hK hW θ hs]
      ring
    · have hθs' := hθ
      have hi :=
        kernelRho_intervalIntegrable hK hW θ hs
      have hiθ :=
        kernelRho_intervalIntegrable hK hW θ hθ
      have e2 := volterraKernel_eq_integral hK hW θ hθ
      rw [volterraKernel_diag hK hW hθ] at e2
      rw [← intervalIntegral.integral_add_adjacent_intervals (by
        refine (hiθ.const_mul Complex.I).congr fun t ht => ?_
        rw [uIoc_of_le hθ.1] at ht
        exact (if_pos ht.2).symm) (by
        refine ((hiθ.symm.trans hi).const_mul Complex.I).neg.congr fun t ht => ?_
        rw [uIoc_of_le hθs.le] at ht
        exact (if_neg (not_le.mpr ht.1)).symm), (show ∫ t in 0..θ, Φ3 θ t = ∫ t in 0..θ, Complex.I * Φ9 θ t by
        refine intervalIntegral.integral_congr fun t ht => ?_
        rw [uIcc_of_le hθ.1] at ht
        exact if_pos ht.2), (show ∫ t in θ..s, Φ3 θ t = ∫ t in θ..s, -(Complex.I * Φ9 θ t) by
        refine intervalIntegral.integral_congr fun t ht => ?_
        rw [uIcc_of_le hθs.le] at ht
        rcases eq_or_lt_of_le ht.1 with h | h
        · subst h; simp [schurRho0, kernelRho_diag hK hW hθ]
        · exact if_neg (not_le.mpr h)),
        intervalIntegral.integral_neg, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul, schurKernel0, if_neg (not_le.mpr hθs),
        ← intervalIntegral.integral_interval_sub_left hi hiθ, volterraKernel_eq_integral hK hW θ hs]
      linear_combination (2 * Complex.I) * e2,
    schurBeta_eq hK hW hs, map_add]
  ring

lemma schurKernel0_of_le (hK : Φ4) (hW : Φ0) 
    (hθ : θ ∈ Φ1 (2 * π)) (hθs : θ ≤ s) :
    Φ12 θ s = -(Complex.I * (Φ11 θ s - 1)) := by
  unfold schurKernel0
  split_ifs with h
  · have:= le_antisymm h hθs
    subst this
    rw [volterraKernel_diag hK hW hθ]; ring
  · rfl

lemma schurKernel_end_right (hK : Φ4) (hW : Φ0)
    (ha : Φ5 ≠ 0)  (hθ : θ ∈ Φ1 (2 * π)) :
    schurKernel W θ (2 * π) = schurKernel W θ 0 := by
  have ha' := Complex.ofReal_ne_zero.mpr ha
  have hb := smallB_end_sub hK hW
  have hk := volterraKernel_add_end hW θ
  unfold schurKernel
  rw [schurKernel0_of_le hK hW hθ hθ.2, show Φ12 θ 0 =
    Complex.I * (Φ11 θ 0 - 1) from if_pos hθ.1, show conj (Φ7 (2 * π)) = conj (Φ8) - Complex.I * Φ5 by
      rw [show Φ7 (2 * π) = Φ8 + Complex.I * Φ5 by
        unfold schurBeta; linear_combination hb, map_add, map_mul, Complex.conj_I, Complex.conj_ofReal]; ring]
  field_simp
  unfold schurBeta
  linear_combination (-(Complex.I * Φ5)) * hk

lemma norm_schurBeta_sub_le (hK : Φ4) (hW : Φ0) 
    (hB : ∀ t ∈ Φ1 (2 * π), ‖Φ2 t‖ ≤ B) 
    (h₁ : θ₁ ∈ Φ1 (2 * π)) (h₂ : θ₂ ∈ Φ1 (2 * π)) :
    ‖Φ7 θ₁ - Φ7 θ₂‖ ≤ B * |θ₁ - θ₂| := by
  rw [schurBeta_eq hK hW h₁, schurBeta_eq hK hW h₂, add_sub_add_left_eq_sub,
    intervalIntegral.integral_interval_sub_left (smallBDer_intervalIntegrable hK hW h₁)
      (smallBDer_intervalIntegrable hK hW h₂)]
  refine intervalIntegral.norm_integral_le_of_norm_le_const fun t ht => hB t ?_
  have := uIoc_subset_uIcc ht
  rw [mem_uIcc] at this
  rcases this with h | h
  · exact ⟨h₂.1.trans h.1, h.2.trans h₁.2⟩
  · exact ⟨h₁.1.trans h.1, h.2.trans h₂.2⟩

lemma norm_schurRho_sub_le (hK : Φ4) (hE : 0 ≤ E) (hW : Φ0)
     (hB : ∀ t ∈ Φ1 (2 * π), ‖Φ2 t‖ ≤ B)
     (h₁ : θ₁ ∈ Φ1 (2 * π)) (h₂ : θ₂ ∈ Φ1 (2 * π))
    (ht : t ∈ Φ1 (2 * π)) :
    ‖Φ6 θ₁ t - Φ6 θ₂ t‖ ≤
      (K * (shiftConst * K) * E + B * B / |Φ5|) * |θ₁ - θ₂| := by
  have hB0 := (norm_nonneg _).trans (hB t ht)
  rw [show Φ6 θ₁ t - Φ6 θ₂ t = Φ3 θ₁ t - Φ3 θ₂ t - (Φ7 θ₁ - Φ7 θ₂) * conj (Φ2 t) / (Φ5) by
    unfold schurRho; ring]
  refine (norm_sub_le _ _).trans ?_
  have h2 : ‖(Φ7 θ₁ - Φ7 θ₂) * conj (Φ2 t) / (Φ5)‖ ≤
      B * B / |Φ5| * |θ₁ - θ₂| := by
    rw [norm_div, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs]
    rcases eq_or_ne (Φ5) 0 with h0 | h0
    · simp [h0]
    · rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right (abs_pos.mpr h0)]
      calc _ ≤ _ :=
            mul_le_mul (norm_schurBeta_sub_le hK hW hB h₁ h₂) (hB t ht) (norm_nonneg _)
              (by positivity)
        _ = _ := by ring
  linarith [show ‖Φ3 θ₁ t - Φ3 θ₂ t‖ ≤ K * (shiftConst * K) * E * |θ₁ - θ₂| by
    set M := K * (shiftConst * K) * E with hM
    have hd : ∀ θ ∈ Φ1 (2 * π), ‖Φ9 θ t‖ ≤ M * |θ - t| := by
      intro θ hθ
      have := norm_kernelRho_sub_le hK hE hW hθ ht ht
      rwa [kernelRho_diag hK hW ht, sub_zero] at this
    have hI := Complex.norm_I
    unfold schurRho0
    split_ifs with ha hb hb
    · rw [← mul_sub, norm_mul, hI, one_mul]; exact norm_kernelRho_sub_le hK hE hW h₁ h₂ ht
    · push_neg at hb
      calc _
          ≤ _ := by
            rw [sub_neg_eq_add, ← mul_add, norm_mul, hI, one_mul]; exact norm_add_le _ _
        _ ≤ _ := add_le_add (hd θ₁ h₁) (hd θ₂ h₂)
        _ = _ := by
            rw [abs_of_nonneg (by linarith), abs_of_neg (by linarith),
              abs_of_nonneg (by linarith)]; ring
    · push_neg at ha
      calc _
          ≤ _ := by
            rw [← neg_add', ← mul_add, norm_neg, norm_mul, hI, one_mul]; exact norm_add_le _ _
        _ ≤ _ := add_le_add (hd θ₁ h₁) (hd θ₂ h₂)
        _ = _ := by
            rw [abs_of_neg (by linarith), abs_of_nonneg (by linarith),
              abs_of_neg (by linarith)]; ring
    · rw [neg_sub_neg, ← mul_sub, norm_mul, hI, one_mul, norm_sub_rev]
      exact norm_kernelRho_sub_le hK hE hW h₁ h₂ ht]

lemma norm_schurRho_le (hK : Φ4) (hE : 0 ≤ E) (hW : Φ0)
     (hB : ∀ t ∈ Φ1 (2 * π), ‖Φ2 t‖ ≤ B)
     (hθ : θ ∈ Φ1 (2 * π)) (ht : t ∈ Φ1 (2 * π)) :
    ‖Φ6 θ t‖ ≤ K * (shiftConst * K) * E * (2 * π) +
      (‖Φ8‖ + B * (2 * π)) * B / |Φ5| := by
  have hB0 := (norm_nonneg _).trans (hB t ht)
  unfold schurRho
  exact (norm_sub_le _ _).trans (add_le_add (by
    unfold schurRho0
    split_ifs <;> simpa using (show ‖Φ9 θ t‖ ≤ K * (shiftConst * K) * E * (2 * π) by
      have := norm_kernelRho_sub_le hK hE hW hθ ht ht
      rw [kernelRho_diag hK hW ht, sub_zero] at this
      refine this.trans (mul_le_mul_of_nonneg_left (by
        rw [abs_le]; constructor <;> linarith [hθ.1, hθ.2, ht.1, ht.2]) ?_)
      have := shiftConst_nonneg; positivity)) (by
      rw [norm_div, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs]
      exact div_le_div_of_nonneg_right (mul_le_mul (by
        have := norm_schurBeta_sub_le hK hW hB hθ ⟨le_rfl, by positivity⟩
        rw [sub_zero, abs_of_nonneg hθ.1] at this
        have h3 : ‖Φ7 θ‖ ≤ ‖Φ8‖ + ‖Φ7 θ - Φ8‖ := by
          have := norm_add_le (Φ8) (Φ7 θ - Φ8)
          rwa [add_sub_cancel] at this
        nlinarith [hθ.2]) (hB t ht) (norm_nonneg _)
        (by positivity)) (abs_nonneg _)))

lemma schurRho_aestronglyMeasurable (hK : Φ4) (hW : Φ0)
    {θ : ℝ} (hθ : θ ∈ Φ1 (2 * π)) :
    AEStronglyMeasurable (Φ6 θ) (volume.restrict (Φ1 (2 * π))) := by
  have hL : 2 * π ∈ Φ1 (2 * π) := ⟨by positivity, le_rfl⟩
  exact ((intervalIntegrable_iff_integrableOn_Icc_of_le (by positivity)).mp ((schurRho0_intervalIntegrable hK hW hθ hL).sub (((intervalIntegrable_conj' (smallBDer_intervalIntegrable hK hW hL)).const_mul _).div_const _))).aestronglyMeasurable

/-- **Kernel estimate.** For a bounded measurable `g` with `∫₀^L g = 0`, primitive `G`, and any
constant `c`, the corrected kernel form is bounded by `M (∫₀^L |G - c|)²` with
`M = K (κ K) E + B² / |a_E|`, where `B` bounds `|b'_E|`. -/
theorem norm_schurKernel_form_le (hK : Φ4) (hE : 0 ≤ E) (hW : Φ0)
    (ha : Φ5 ≠ 0)  (hB : ∀ t ∈ Φ1 (2 * π), ‖Φ2 t‖ ≤ B)
     {Bg} (hg : AEStronglyMeasurable g volume) (hgB : ∀ t, ‖g t‖ ≤ Bg)
    (hG : ∫ t in 0..(2 * π), g t = 0) c :
    ‖∫ θ in 0..(2 * π), conj (g θ) * ∫ s in 0..(2 * π), schurKernel W θ s * g s‖ ≤
      (K * (shiftConst * K) * E + B * B / |Φ5|) *
        (∫ t in 0..(2 * π), ‖(∫ u in 0..t, g u) - c‖) ^ 2 := by
  have hB0 := (norm_nonneg _).trans (hB 0 ⟨le_rfl, by positivity⟩)
  exact norm_kernel_form_le (by positivity) (by
    have := shiftConst_nonneg; positivity) hg hgB
    (fun θ hθ => schurRho_aestronglyMeasurable hK hW hθ)
    (fun θ hθ t ht => norm_schurRho_le hK hE hW hB hθ ht)
    (fun θ hθ s hs => schurKernel_eq_integral hK hW hθ hs)
    (fun θ₁ h₁ θ₂ h₂ t ht => norm_schurRho_sub_le hK hE hW hB h₁ h₂ ht)
    (fun θ hθ => schurKernel_end_right hK hW ha hθ)
    (fun s hs => (by
      have ha' := Complex.ofReal_ne_zero.mpr ha
      have hb := smallB_end_sub hK hW
      have hk : Φ11 (2 * π) s + volterraKernel W 0 s = conj (Φ10 s) := by
        rw [← conj_volterraKernel W (2 * π) s, ← conj_volterraKernel W 0 s, ← map_add,
          volterraKernel_add_end hW]
      unfold schurKernel
      rw [schurKernel0_of_le hK hW ⟨le_rfl, by positivity⟩ hs.1, show Φ12 (2 * π) s =
        Complex.I * (Φ11 (2 * π) s - 1) from if_pos hs.2]
      field_simp
      unfold schurBeta
      rw [map_sub, map_ofNat]
      linear_combination (Complex.I * Φ5) * hk - (conj (Φ10 s) - 2) * hb)) hG c

lemma smallB_continuousOn (hW : Φ0) :
    ContinuousOn (Φ10) (Φ1 (2 * π)) := by
  refine (continuousOn_const.inner (hW.1.clm_apply continuousOn_const) : ContinuousOn (fun s => ⟪basisVec 0, W s (radialVec W)⟫_ℂ) (Φ1 (2 * π))).congr fun s _ => ?_
  beta_reduce
  rw [smallB, inner_basisVec]

theorem re_volterra_sub_schur_eq (hK : Φ4) (hE : 0 ≤ E)
    (hW : Φ0) (ha : Φ5 ≠ 0) {g : ℝ → ℂ} {Bg : ℝ}
    (hg : AEStronglyMeasurable g volume) (hgB : ∀ t, ‖g t‖ ≤ Bg)
    (hG : ∫ t in 0..(2 * π), g t = 0) {h : ℝ → ℂ}
    (hh : IntervalIntegrable (fun θ => conj (g θ) * h θ) volume 0 (2 * π)) :
    (∫ θ in 0..(2 * π), conj (g θ) *
        (2 * h θ + Complex.I * (volterraOp W g θ - volterraOpAdj W g θ))).re -
      ‖∫ θ in 0..(2 * π), conj (Φ10 θ) * g θ‖ ^ 2 / Φ5 =
    (∫ θ in 0..(2 * π), conj (g θ) *
        (2 * h θ + Complex.I * (2 * ∫ s in 0..θ, g s))).re +
      (∫ θ in 0..(2 * π), conj (g θ) *
        ∫ s in 0..(2 * π), schurKernel W θ s * g s).re := by
  have hL : 0 ≤ 2 * π := by positivity
  have hgi : IntervalIntegrable g volume 0 (2 * π) := intervalIntegrable_of_norm_le hg hgB _ _
  have hcg :=
    intervalIntegrable_conj' hgi
  set Y := ∫ θ in 0..(2 * π), conj (Φ10 θ) * g θ with hY
  set Φ := fun θ => ∫ s in 0..(2 * π), schurKernel W θ s * g s with hΦ
  have i1 : IntervalIntegrable (fun θ => conj (g θ) *
      (2 * h θ + Complex.I * (2 * ∫ s in 0..θ, g s))) volume 0 (2 * π) := by
    refine ((hh.const_mul 2).add (hcg.mul_continuousOn
      (((show ContinuousOn (fun θ => ∫ s in 0..θ, g s) (uIcc 0 (2 * π)) by
        rw [uIcc_of_le hL]
        exact continuousOn_primitive_of_bound hL hg.restrict (fun t _ => hgB t)).const_smul 2).const_smul Complex.I))).congr fun θ _ => ?_
    simp; ring
  have i2 :=
    hcg.mul_continuousOn (by
      rw [uIcc_of_le hL]; exact (show ContinuousOn (fun θ => ∫ s in 0..(2 * π), schurKernel W θ s * g s) (Φ1 (2 * π)) by
        have hL : 0 ≤ 2 * π := by positivity
        set B := Real.sqrt E * K * 2 with hBdef
        have hB : ∀ t ∈ Φ1 (2 * π), ‖Φ2 t‖ ≤ B := fun t ht =>
          have h_inl : ‖Φ2 t‖ ≤ Real.sqrt E * K * 2 := by
            refine (norm_coeffTerm_le (norm_deriv_le_of_lipschitz hK)).trans ?_
            have h1 : ‖(W t (radialVec W)) 1‖ ≤ 2 :=
              (norm_coord_le _ _).trans (((W t).le_opNorm _).trans
                ((mul_le_mul (norm_transport_le_one hK hW ht) (norm_radialVec_le hK hW) (norm_nonneg _)
                  zero_le_one).trans (by norm_num)))
            gcongr
          h_inl
        set M := K * (shiftConst * K) * E + B * B / |Φ5| with hM
        set Bρ := K * (shiftConst * K) * E * (2 * π) +
            (‖Φ8‖ + B * (2 * π)) * B / |Φ5|
        have hgr : AEStronglyMeasurable g (volume.restrict (Φ1 (2 * π))) := hg.restrict
        have hgBr : ∀ t ∈ Φ1 (2 * π), ‖g t‖ ≤ Bg := fun t _ => hgB t
        have hrep : ∀ θ ∈ Φ1 (2 * π), ∫ s in 0..(2 * π), schurKernel W θ s * g s =
            -∫ t in 0..(2 * π), Φ6 θ t * ((∫ u in 0..t, g u) - 0) :=
          fun θ hθ => kernel_integral_eq hL hgr hgBr (schurRho_aestronglyMeasurable hK hW hθ)
            (fun t ht => norm_schurRho_le hK hE hW hB hθ ht)
            (fun s hs => schurKernel_eq_integral hK hW hθ hs) (schurKernel_end_right hK hW ha hθ) hG 0
        have hint : ∀ θ ∈ Φ1 (2 * π), IntervalIntegrable
            (fun t => Φ6 θ t * ((∫ u in 0..t, g u) - 0)) volume 0 (2 * π) := by
          intro θ hθ
          refine intervalIntegrable_of_restrict_bound
            ((schurRho_aestronglyMeasurable hK hW hθ).mul
              (((continuousOn_primitive_of_bound hL hgr hgBr).sub continuousOn_const).aestronglyMeasurable measurableSet_Icc))
            (B := Bρ * (Bg * (2 * π))) (fun t ht => ?_) ⟨le_rfl, hL⟩ ⟨hL, le_rfl⟩
          simp only [Pi.mul_apply, Pi.sub_apply, sub_zero]
          rw [norm_mul]
          exact mul_le_mul (norm_schurRho_le hK hE hW hB hθ ht) (norm_primitive_le hgBr ht)
            (norm_nonneg _) ((norm_nonneg _).trans (norm_schurRho_le hK hE hW hB hθ ht))
        have hBg := (norm_nonneg _).trans (hgB 0)
        have hM0 : 0 ≤ M := by have := shiftConst_nonneg; positivity
        refine (LipschitzOnWith.of_dist_le_mul (K := (M * (Bg * (2 * π)) * (2 * π)).toNNReal)
          fun θ₁ h₁ θ₂ h₂ => ?_).continuousOn
        rw [hrep θ₁ h₁, hrep θ₂ h₂, dist_eq_norm, Real.dist_eq,
          Real.coe_toNNReal _ (by positivity), neg_sub_neg,
          ← intervalIntegral.integral_sub (hint θ₂ h₂) (hint θ₁ h₁)]
        refine (intervalIntegral.norm_integral_le_of_norm_le_const (by
          intro t ht
          rw [uIoc_of_le hL] at ht
          have ht' : t ∈ Φ1 (2 * π) := ⟨ht.1.le, ht.2⟩
          rw [← sub_mul, norm_mul, sub_zero, norm_sub_rev]
          exact mul_le_mul (norm_schurRho_sub_le hK hE hW hB h₁ h₂ ht') (norm_primitive_le hgBr ht')
            (norm_nonneg _) (by positivity))).trans (le_of_eq ?_)
        rw [sub_zero, abs_of_nonneg hL]; ring))
  rw [intervalIntegral.integral_congr (show ∀ θ ∈ uIcc 0 (2 * π), conj (g θ) * (2 * h θ + Complex.I * (volterraOp W g θ - volterraOpAdj W g θ)) = conj (g θ) * (2 * h θ + Complex.I * (2 * ∫ s in 0..θ, g s)) + conj (g θ) * Φ θ + conj (g θ) * Φ7 θ * Y / (Φ5) by
    intro θ hθ
    rw [uIcc_of_le hL] at hθ
    simp [hΦ, show ∫ s in 0..(2 * π), schurKernel W θ s * g s = Complex.I * (volterraOp W g θ - volterraOpAdj W g θ) - 2 * Complex.I * (∫ s in 0..θ, g s) - Φ7 θ * (∫ s in 0..(2 * π), conj (Φ10 s) * g s) / (Φ5) by
      have hL : 2 * π ∈ Φ1 (2 * π) := ⟨by positivity, le_rfl⟩
      have hsub1 : uIcc 0 θ ⊆ uIcc 0 (2 * π) := by
        rw [uIcc_of_le hθ.1, uIcc_of_le hL.1]; exact Icc_subset_Icc le_rfl hθ.2
      have hsub2 : uIcc θ (2 * π) ⊆ uIcc 0 (2 * π) := by
        rw [uIcc_of_le hθ.2, uIcc_of_le hL.1]; exact Icc_subset_Icc hθ.1 le_rfl
      have hwc : ContinuousOn (Φ11 θ) (Φ1 (2 * π)) := by
        exact continuousOn_const.inner ((W θ).continuous.comp_continuousOn (((ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := Ell2) (F := Ell2)).continuous.comp_continuousOn hW.1).clm_apply continuousOn_const))
      rw [← uIcc_of_le hL.1] at hwc
      have hg1 := hgi.mono_set hsub1
      have hg2 := hgi.mono_set hsub2
      have hw1 :=
        hg1.continuousOn_mul (hwc.mono hsub1)
      have hw2 :=
        hg2.continuousOn_mul (hwc.mono hsub2)
      have A1 : IntervalIntegrable (fun s => Φ12 θ s * g s) volume 0 θ := by
        refine ((hw1.sub hg1).const_mul Complex.I).congr fun s hs => ?_
        rw [uIoc_of_le hθ.1] at hs
        simp only [schurKernel0, if_pos hs.2]; ring
      have A2 : IntervalIntegrable (fun s => Φ12 θ s * g s) volume θ (2 * π) := by
        refine ((hw2.sub hg2).const_mul Complex.I).neg.congr fun s hs => ?_
        rw [uIoc_of_le hθ.2] at hs
        simp only [schurKernel0, if_neg (not_le.mpr hs.1), Pi.neg_apply]; ring
      have I1 : ∫ s in 0..θ, Φ12 θ s * g s =
          Complex.I * (volterraOp W g θ - ∫ s in 0..θ, g s) := by
        rw [intervalIntegral.integral_congr (g := fun s => Complex.I *
          (Φ11 θ s * g s - g s)) (fun s hs => by
            rw [uIcc_of_le hθ.1] at hs
            simp only [schurKernel0, if_pos hs.2]; ring),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_sub hw1 hg1]
        rfl
      have hadj : volterraOpAdj W g θ = ∫ s in θ..(2 * π), Φ11 θ s * g s := by
        unfold volterraOpAdj
        simp only [conj_volterraKernel]
      have I2 : ∫ s in θ..(2 * π), Φ12 θ s * g s =
          -(Complex.I * (volterraOpAdj W g θ - ∫ s in θ..(2 * π), g s)) := by
        rw [intervalIntegral.integral_congr (g := fun s => -(Complex.I *
          (Φ11 θ s * g s - g s))) (fun s hs => by
            rw [uIcc_of_le hθ.2] at hs
            simp only [schurKernel0_of_le hK hW hθ hs.1]; ring),
          intervalIntegral.integral_neg, intervalIntegral.integral_const_mul,
          intervalIntegral.integral_sub hw2 hg2, hadj]
      have hbc : ContinuousOn (fun s => conj (Φ10 s)) (uIcc 0 (2 * π)) := by
        rw [uIcc_of_le hL.1]
        exact Complex.continuous_conj.comp_continuousOn (smallB_continuousOn hW)
      have hB1 :=
        hgi.continuousOn_mul hbc
      have hB2 : IntervalIntegrable (fun s => Φ7 θ * (conj (Φ7 s) * g s) /
          (Φ5)) volume 0 (2 * π) := by
        refine (((hB1.sub (hgi.const_mul 2)).const_mul (Φ7 θ)).div_const
          (Φ5)).congr fun s _ => ?_
        simp only [schurBeta, map_sub, map_ofNat]; ring
      have hrk : ∫ s in 0..(2 * π), Φ7 θ * (conj (Φ7 s) * g s) /
          Φ5 = Φ7 θ *
            (∫ s in 0..(2 * π), conj (Φ10 s) * g s) / Φ5 := by
        rw [intervalIntegral.integral_div, intervalIntegral.integral_const_mul]
        congr 2
        rw [intervalIntegral.integral_congr (g := fun s => conj (Φ10 s) * g s - 2 * g s)
          (fun s _ => by simp only [schurBeta, map_sub, map_ofNat]; ring),
          intervalIntegral.integral_sub hB1 (hgi.const_mul 2), intervalIntegral.integral_const_mul,
          hG, mul_zero, sub_zero]
      rw [intervalIntegral.integral_congr (g := fun s => Φ12 θ s * g s -
          Φ7 θ * (conj (Φ7 s) * g s) / (Φ5))
          (fun s _ => by simp only [schurKernel]; ring),
        intervalIntegral.integral_sub (A1.trans A2) hB2, hrk,
        ← intervalIntegral.integral_add_adjacent_intervals A1 A2, I1, I2, show ∫ s in θ..(2 * π), g s = -∫ s in 0..θ, g s by
          have := intervalIntegral.integral_add_adjacent_intervals hg1 hg2
          rw [hG] at this
          linear_combination this]
      ring, hY]
    ring), intervalIntegral.integral_add (i1.add i2) (((hcg.mul_continuousOn (show ContinuousOn (Φ7) (uIcc 0 (2 * π)) by
    rw [uIcc_of_le hL]; exact (smallB_continuousOn hW).sub continuousOn_const)).mul_const Y).div_const _),
    intervalIntegral.integral_add i1 i2, show ∫ θ in 0..(2 * π), conj (g θ) * Φ7 θ * Y / Φ5 = conj Y * Y / (Φ5) by
      have hbc : ContinuousOn (fun s => conj (Φ10 s)) (uIcc 0 (2 * π)) := by
        rw [uIcc_of_le hL]
        exact Complex.continuous_conj.comp_continuousOn (smallB_continuousOn hW)
      rw [intervalIntegral.integral_div, intervalIntegral.integral_mul_const]
      congr 2
      rw [intervalIntegral.integral_congr (g := fun θ => conj (conj (Φ10 θ) * g θ) -
          2 * conj (g θ)) (fun θ _ => by simp [schurBeta]; ring),
        intervalIntegral.integral_sub (intervalIntegrable_conj' (hgi.continuousOn_mul hbc)) (hcg.const_mul 2),
        intervalIntegral.integral_const_mul, intervalIntegral_conj, intervalIntegral_conj, hG,
        map_zero, mul_zero, sub_zero], Complex.conj_mul', Complex.add_re, Complex.add_re,
    ← Complex.ofReal_pow, ← Complex.ofReal_div, Complex.ofReal_re]
  ring

end PolyaNeumann