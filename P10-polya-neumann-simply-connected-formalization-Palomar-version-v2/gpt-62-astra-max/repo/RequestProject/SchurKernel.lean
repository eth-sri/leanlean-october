module

public import RequestProject.CircleAnalysisNotation

public import RequestProject.HerglotzSchur
public import RequestProject.PlanarNotation

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

section

variable (γ : ℝ → ℂ) (E : ℝ) (W : TransportPath) (θ s t : ℝ)
include W θ

/-- `β_E = b_E - 2`. -/
def schurBeta : ℂ := smallB W θ - 2

include s in
/-- The jump part `i sgn(θ - s) (w(θ, s) - 1)` of the kernel. -/
def schurKernel0 : ℂ :=
  if s ≤ θ then Complex.I * (volterraKernel W θ s - 1) else -(Complex.I * (volterraKernel W θ s - 1))

include s in
/-- The corrected periodic kernel `r(θ, s) = i sgn(θ - s)(w(θ, s) - 1) - a⁻¹ β(θ) conj(β(s))`. -/
def schurKernel : ℂ :=
  schurKernel0 W θ s - schurBeta W θ * conj (schurBeta W s) / (smallA W : ℂ)

include E t γ in
/-- The `s`-derivative of the jump part. -/
def schurRho0 : ℂ :=
  if t ≤ θ then Complex.I * kernelRho γ E W θ t else -(Complex.I * kernelRho γ E W θ t)

include E t γ in
/-- The `s`-derivative of the corrected kernel. -/
def schurRho : ℂ :=
  schurRho0 γ E W θ t - schurBeta W θ * conj (smallBDer γ E W t) / (smallA W : ℂ)

end

variable {γ : ℝ → ℂ} {K : NNReal} {E : ℝ} {W : TransportPath}

section

variable (hK : LipschitzWith K γ) (hW : IsTransport γ E W)

include hK hW in
lemma volterraKernel_diag {θ : ℝ}
    (hθ : θ ∈ angleInterval) : volterraKernel W θ θ = 1 := by
  have hu := transport_mem_unitary hK hW hθ
  rw [Unitary.mem_iff, ContinuousLinearMap.star_eq_adjoint] at hu
  rw [volterraKernel, ← ContinuousLinearMap.mul_apply, hu.2, ContinuousLinearMap.one_apply]
  simp [basisVec]

lemma conj_volterraKernel (W : TransportPath) (θ s : ℝ) :
    conj (volterraKernel W s θ) = volterraKernel W θ s := by
  rw [volterraKernel, volterraKernel, inner_conj_symm, ← ContinuousLinearMap.adjoint_inner_right,
    ContinuousLinearMap.adjoint_inner_left]

include hW in
lemma volterraKernel_add_end (θ : ℝ) :
    volterraKernel W θ anglePeriod + volterraKernel W θ 0 = smallB W θ := by
  rw [volterraKernel, volterraKernel, transport_zero hW, smallB, ← inner_basisVec,
    ← inner_add_right, ← map_add, radialVec, ← ContinuousLinearMap.star_eq_adjoint 1,
    star_one, ContinuousLinearMap.one_apply, add_comm]

include hW in
lemma volterraKernel_end_add (s : ℝ) :
    volterraKernel W anglePeriod s + volterraKernel W 0 s = conj (smallB W s) := by
  rw [← conj_volterraKernel W anglePeriod s, ← conj_volterraKernel W 0 s, ← map_add,
    volterraKernel_add_end hW]

include hK hW in
lemma smallB_end_sub :
    smallB W anglePeriod - smallB W 0 = Complex.I * smallA W := by
  have hu := transport_mem_unitary hK hW ⟨by positivity, le_rfl⟩
  rw [Unitary.mem_iff, ContinuousLinearMap.star_eq_adjoint] at hu
  have h1 : W anglePeriod (ContinuousLinearMap.adjoint (W anglePeriod) (basisVec 0)) = basisVec 0 := by
    rw [← ContinuousLinearMap.mul_apply, hu.2, ContinuousLinearMap.one_apply]
  have h2 : (ContinuousLinearMap.adjoint (W anglePeriod) (basisVec 0)) 0 =
      conj ((W anglePeriod (basisVec 0)) 0) := by
    rw [← inner_basisVec, ← inner_basisVec, ContinuousLinearMap.adjoint_inner_right,
      inner_conj_symm]
  unfold smallB radialVec smallA
  rw [transport_zero hW, ContinuousLinearMap.one_apply, map_add, h1]
  simp only [lp.coeFn_add, Pi.add_apply, h2, basisVec_coord]
  apply Complex.ext <;> simp <;> ring

end

lemma intervalIntegrable_conj' {f : ℝ → ℂ} {a b : ℝ} (hf : IntervalIntegrable f volume a b) :
    IntervalIntegrable (fun t => conj (f t)) volume a b :=
  ⟨Complex.conjCLE.toContinuousLinearMap.integrable_comp hf.1,
    Complex.conjCLE.toContinuousLinearMap.integrable_comp hf.2⟩

section

variable (hK : LipschitzWith K γ) (hE : 0 ≤ E) (hW : IsTransport γ E W) (θ : ℝ)
    (ha : smallA W ≠ 0)
include hW

include hK in
lemma kernelRho_intervalIntegrable
    {t : ℝ} (ht : t ∈ angleInterval) : IntervalIntegrable (kernelRho γ E W θ) volume 0 t := by
  have := transport_coord_intervalIntegrable' hK hW
    (ContinuousLinearMap.adjoint (W θ) (basisVec 0)) 0 ht
  simp [transportCoeff_coord_zero] at this
  exact intervalIntegrable_conj' this

include hK in
lemma smallBDer_intervalIntegrable
    {t : ℝ} (ht : t ∈ angleInterval) : IntervalIntegrable (smallBDer γ E W) volume 0 t := by
  have := transport_coord_intervalIntegrable' hK hW (radialVec W) 0 ht
  simp [transportCoeff_coord_zero] at this
  exact this

include hK in
lemma schurKernel0_eq_integral {θ s : ℝ}
    (hθ : θ ∈ angleInterval) (hs : s ∈ angleInterval) :
    schurKernel0 W θ s = schurKernel0 W θ 0 + ∫ t in (0 : ℝ)..s, schurRho0 γ E W θ t := by
  have h0 : schurKernel0 W θ 0 = Complex.I * (volterraKernel W θ 0 - 1) := if_pos hθ.1
  rw [h0]
  rcases le_or_gt s θ with hsθ | hθs
  · have hc : ∫ t in 0..s, schurRho0 γ E W θ t =
        ∫ t in 0..s, Complex.I * kernelRho γ E W θ t := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [uIcc_of_le hs.1] at ht
      exact if_pos (ht.2.trans hsθ)
    rw [schurKernel0, if_pos hsθ, hc, intervalIntegral.integral_const_mul,
      volterraKernel_eq_integral hK hW θ hs]
    ring
  · 
    have hi  :=
      kernelRho_intervalIntegrable hK hW θ hs
    have hiθ  :=
      kernelRho_intervalIntegrable hK hW θ hθ
    
    
    
    have c1 : ∫ t in 0..θ, schurRho0 γ E W θ t =
        ∫ t in 0..θ, Complex.I * kernelRho γ E W θ t := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [uIcc_of_le hθ.1] at ht
      exact if_pos ht.2
    have c2 : ∫ t in θ..s, schurRho0 γ E W θ t =
        ∫ t in θ..s, -(Complex.I * kernelRho γ E W θ t) := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [uIcc_of_le hθs.le] at ht
      rcases eq_or_lt_of_le ht.1 with h | h
      · subst h; simp [schurRho0, kernelRho_diag hK hW hθ]
      · exact if_neg (not_le.mpr h)
    
    
    have e2 := volterraKernel_eq_integral hK hW θ hθ
    rw [(volterraKernel_diag hK hW hθ)] at e2
    rw [← intervalIntegral.integral_add_adjacent_intervals (by
      refine (hiθ.const_mul Complex.I).congr fun t ht => ?_
      rw [uIoc_of_le hθ.1] at ht
      exact (if_pos ht.2).symm) (by
      refine ((hiθ.symm.trans hi).const_mul Complex.I).neg.congr fun t ht => ?_
      rw [uIoc_of_le hθs.le] at ht
      exact (if_neg (not_le.mpr ht.1)).symm), c1, c2,
      intervalIntegral.integral_neg, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, schurKernel0, if_neg (not_le.mpr hθs),
      ← intervalIntegral.integral_interval_sub_left hi hiθ, (volterraKernel_eq_integral hK hW θ hs)]
    simp [*]

include hK in
lemma schurBeta_eq {s : ℝ}
    (hs : s ∈ angleInterval) :
    schurBeta W s = schurBeta W 0 + ∫ t in (0 : ℝ)..s, smallBDer γ E W t := by
  rw [schurBeta, schurBeta, smallB_eq hK hW hs]
  ring

include hK in
lemma schurRho0_intervalIntegrable {θ s : ℝ}
    (hθ : θ ∈ angleInterval) (hs : s ∈ angleInterval) :
    IntervalIntegrable (schurRho0 γ E W θ) volume 0 s := by
  have hi  :=
    kernelRho_intervalIntegrable hK hW θ hs
  rcases le_or_gt s θ with hsθ | hθs
  · refine (hi.const_mul Complex.I).congr fun t ht => ?_
    rw [uIoc_of_le hs.1] at ht
    exact (if_pos (ht.2.trans hsθ)).symm
  · have hiθ  :=
      kernelRho_intervalIntegrable hK hW θ hθ
    have i1 : IntervalIntegrable (schurRho0 γ E W θ) volume 0 θ := by
      refine (hiθ.const_mul Complex.I).congr fun t ht => ?_
      rw [uIoc_of_le hθ.1] at ht
      exact (if_pos ht.2).symm
    
    apply i1.trans
    refine ((hiθ.symm.trans hi).const_mul Complex.I).neg.congr fun t ht => ?_
    rw [uIoc_of_le hθs.le] at ht
    exact (if_neg (not_le.mpr ht.1)).symm

include hK in
lemma schurKernel_eq_integral {θ s : ℝ}
    (hθ : θ ∈ angleInterval) (hs : s ∈ angleInterval) :
    schurKernel W θ s = schurKernel W θ 0 + ∫ t in (0 : ℝ)..s, schurRho γ E W θ t := by
  
  
  have hi1 : IntervalIntegrable (fun t => schurBeta W θ * conj (smallBDer γ E W t) /
      (smallA W)) volume 0 s := ((intervalIntegrable_conj' (smallBDer_intervalIntegrable hK hW hs)).const_mul _).div_const _
  have hint : ∫ t in 0..s, schurRho γ E W θ t =
      (∫ t in 0..s, schurRho0 γ E W θ t) -
        schurBeta W θ * conj (∫ t in 0..s, smallBDer γ E W t) / (smallA W) := by
    unfold schurRho
    rw [intervalIntegral.integral_sub (schurRho0_intervalIntegrable hK hW hθ hs) hi1, intervalIntegral.integral_div,
      intervalIntegral.integral_const_mul, intervalIntegral_conj]
  rw [hint, schurKernel, schurKernel, schurKernel0_eq_integral hK hW hθ hs,
    schurBeta_eq hK hW hs, map_add]
  ring

include hK in
lemma schurKernel0_of_le {θ s : ℝ}
    (hθ : θ ∈ angleInterval) (hθs : θ ≤ s) :
    schurKernel0 W θ s = -(Complex.I * (volterraKernel W θ s - 1)) := by
  unfold schurKernel0
  split_ifs with h
  · have  := le_antisymm h hθs
    subst this
    rw [volterraKernel_diag hK hW hθ]; ring
  · rfl

include hK ha in
lemma schurKernel_end_right {θ : ℝ} (hθ : θ ∈ angleInterval) :
    schurKernel W θ anglePeriod = schurKernel W θ 0 := by
  have ha'  := Complex.ofReal_ne_zero.mpr ha
  
  have hk := volterraKernel_add_end hW θ
  have hcb : conj (schurBeta W anglePeriod) = conj (schurBeta W 0) - Complex.I * smallA W := by
    have : schurBeta W anglePeriod = schurBeta W 0 + Complex.I * smallA W := by
      unfold schurBeta; linear_combination (smallB_end_sub hK hW)
    simp [*] <;> ring
  unfold schurKernel
  rw [schurKernel0_of_le hK hW hθ hθ.2, show schurKernel0 W θ 0 =
    Complex.I * (volterraKernel W θ 0 - 1) from if_pos hθ.1, hcb]
  field_simp
  unfold schurBeta
  grind

include hK ha in
lemma schurKernel_end_left {s : ℝ} (hs : s ∈ angleInterval) :
    schurKernel W anglePeriod s = schurKernel W 0 s := by
  have ha'  := Complex.ofReal_ne_zero.mpr ha
  have hb := smallB_end_sub hK hW
  have hk := volterraKernel_end_add hW s
  
  unfold schurKernel
  rw [schurKernel0_of_le hK hW (⟨le_rfl, by positivity⟩) hs.1, show schurKernel0 W anglePeriod s =
    Complex.I * (volterraKernel W anglePeriod s - 1) from if_pos hs.2]
  field_simp
  unfold schurBeta
  rw [map_sub, map_ofNat]
  grind

include hK in
lemma norm_schurBeta_sub_le {B : ℝ}
    (hB : ∀ t ∈ angleInterval, ‖smallBDer γ E W t‖ ≤ B) {θ₁ θ₂ : ℝ}
    (h₁ : θ₁ ∈ angleInterval) (h₂ : θ₂ ∈ angleInterval) :
    ‖schurBeta W θ₁ - schurBeta W θ₂‖ ≤ B * |θ₁ - θ₂| := by
  rw [schurBeta_eq hK hW h₁, schurBeta_eq hK hW h₂, add_sub_add_left_eq_sub,
    intervalIntegral.integral_interval_sub_left (smallBDer_intervalIntegrable hK hW h₁)
      (smallBDer_intervalIntegrable hK hW h₂)]
  refine intervalIntegral.norm_integral_le_of_norm_le_const fun t ht => hB t ?_
  grind

include hE hK in
lemma norm_schurRho0_sub_le
    {θ₁ θ₂ t : ℝ} (h₁ : θ₁ ∈ angleInterval) (h₂ : θ₂ ∈ angleInterval)
    (ht : t ∈ angleInterval) :
    ‖schurRho0 γ E W θ₁ t - schurRho0 γ E W θ₂ t‖ ≤ K * (shiftConst * K) * E * |θ₁ - θ₂| := by
  set M := K * (shiftConst * K) * E 
  have hd : ∀ θ ∈ angleInterval, ‖kernelRho γ E W θ t‖ ≤ M * |θ - t| := by
    intro θ hθ
    have := norm_kernelRho_sub_le hK hE hW hθ ht ht
    rwa [kernelRho_diag hK hW ht, sub_zero] at this
  have hI  := Complex.norm_I
  unfold schurRho0
  split_ifs with ha hb hb
  · rw [← mul_sub, norm_mul, hI, one_mul]; exact norm_kernelRho_sub_le hK hE hW h₁ h₂ ht
  · push_neg at hb
    calc _
        ≤ ‖kernelRho γ E W θ₁ t‖ + ‖kernelRho γ E W θ₂ t‖ := by
          rw [sub_neg_eq_add, ← mul_add, norm_mul, hI, one_mul]; exact norm_add_le _ _
      _ ≤ _ := add_le_add (hd θ₁ h₁) (hd θ₂ h₂)
      _ = _ := by
          grind
  · push_neg at ha
    calc _
        ≤ ‖kernelRho γ E W θ₁ t‖ + ‖kernelRho γ E W θ₂ t‖ := by
          rw [← neg_add', ← mul_add, norm_neg, norm_mul, hI, one_mul]; exact norm_add_le _ _
      _ ≤ _ := add_le_add (hd θ₁ h₁) (hd θ₂ h₂)
      _ = _ := by
          grind
  · rw [neg_sub_neg, ← mul_sub, norm_mul, hI, one_mul, norm_sub_rev]
    exact norm_kernelRho_sub_le hK hE hW h₁ h₂ ht

include hE hK in
lemma norm_schurRho_sub_le
    {B : ℝ} (hB : ∀ t ∈ angleInterval, ‖smallBDer γ E W t‖ ≤ B)
    {θ₁ θ₂ t : ℝ} (h₁ : θ₁ ∈ angleInterval) (h₂ : θ₂ ∈ angleInterval)
    (ht : t ∈ angleInterval) :
    ‖schurRho γ E W θ₁ t - schurRho γ E W θ₂ t‖ ≤
      (K * (shiftConst * K) * E + B * B / |smallA W|) * |θ₁ - θ₂| := by
  have hB0  := (norm_nonneg _).trans (hB t ht)
  let w₀ := (schurBeta W θ₁ - schurBeta W θ₂) * conj (smallBDer γ E W t)
  have e : schurRho γ E W θ₁ t - schurRho γ E W θ₂ t =
      (schurRho0 γ E W θ₁ t - schurRho0 γ E W θ₂ t) -
        w₀ / (smallA W) := by
    unfold schurRho; ring
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  have h2 : ‖w₀ / (smallA W)‖ ≤
      B * B / |smallA W| * |θ₁ - θ₂| := by
    rw [norm_div, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs]
    rcases eq_or_ne (smallA W) 0 with h0 | h0
    · simp [h0]
    · rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right (abs_pos.mpr h0)]
      calc _ ≤ (B * |θ₁ - θ₂|) * B :=
            mul_le_mul (norm_schurBeta_sub_le hK hW hB h₁ h₂) (hB t ht) (norm_nonneg _)
              (by positivity)
        _ = _ := by ring
  linarith [norm_schurRho0_sub_le hK hE hW h₁ h₂ ht]

include hE hK in
lemma norm_schurRho_le
    {B : ℝ} (hB : ∀ t ∈ angleInterval, ‖smallBDer γ E W t‖ ≤ B)
    {θ t : ℝ} (hθ : θ ∈ angleInterval) (ht : t ∈ angleInterval) :
    ‖schurRho γ E W θ t‖ ≤ K * (shiftConst * K) * E * anglePeriod +
      (‖schurBeta W 0‖ + B * anglePeriod) * B / |smallA W| := by
  
  have hB0  := (norm_nonneg _).trans (hB t ht)
  have hdist : |θ - t| ≤ anglePeriod := by
    grind
  
  
  
  
  refine (norm_sub_le _ _).trans (add_le_add (by
      unfold schurRho0
      split_ifs <;> simpa [norm_mul, Complex.norm_I] using (by
        have := norm_kernelRho_sub_le hK hE hW hθ ht ht
        rw [kernelRho_diag hK hW ht, sub_zero] at this
        refine this.trans (mul_le_mul_of_nonneg_left hdist ?_)
        have := shiftConst_nonneg; positivity)) ?_)
  rw [norm_div, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs]
  refine div_le_div_of_nonneg_right (mul_le_mul ?_ (hB t ht) (norm_nonneg _)
    (by positivity)) (abs_nonneg _)
  have := norm_schurBeta_sub_le hK hW hB hθ (⟨le_rfl, by positivity⟩)
  rw [sub_zero, abs_of_nonneg hθ.1] at this
  have h3 : ‖schurBeta W θ‖ ≤ ‖schurBeta W 0‖ + ‖schurBeta W θ - schurBeta W 0‖ := by
    have := norm_add_le (schurBeta W 0) (schurBeta W θ - schurBeta W 0)
    rwa [add_sub_cancel] at this
  nlinarith [hθ.2]

include hK in
lemma schurRho_aestronglyMeasurable
    {θ : ℝ} (hθ : θ ∈ angleInterval) :
    AEStronglyMeasurable (schurRho γ E W θ) (volume.restrict angleInterval) := by
  have hL : anglePeriod ∈ angleInterval := (by grind)
  
  exact ((intervalIntegrable_iff_integrableOn_Icc_of_le (by positivity)).mp ((schurRho0_intervalIntegrable hK hW hθ hL).sub
    (((intervalIntegrable_conj' (smallBDer_intervalIntegrable hK hW hL)).const_mul _).div_const _))).aestronglyMeasurable

include hE hK ha in
/-- **Kernel estimate.** For a bounded measurable `g` with `∫₀^L g = 0`, primitive `G`, and any
constant `c`, the corrected kernel form is bounded by `M (∫₀^L |G - c|)²` with
`M = K (κ K) E + B² / |a_E|`, where `B` bounds `|b'_E|`. -/
theorem norm_schurKernel_form_le {B : ℝ} (hB : ∀ t ∈ angleInterval, ‖smallBDer γ E W t‖ ≤ B)
    {g : ℝ → ℂ} {Bg : ℝ} (hg : AEStronglyMeasurable g volume) (hgB : ∀ t, ‖g t‖ ≤ Bg)
    (hG : ∫ₚ t, g t = 0) (c : ℂ) :
    ‖∫ₚ θ, conj (g θ) * ∫ₚ s, schurKernel W θ s * g s‖ ≤
      (K * (shiftConst * K) * E + B * B / |smallA W|) *
        (∫ₚ t, ‖(∫ u in (0 : ℝ)..t, g u) - c‖) ^ 2 := by
  have hB0  := (norm_nonneg _).trans (hB 0 ⟨le_rfl, by positivity⟩)
  
  refine norm_kernel_form_le (by positivity) ?_ hg hgB
    (fun θ hθ => schurRho_aestronglyMeasurable hK hW hθ)
    (fun θ hθ t ht => norm_schurRho_le hK hE hW hB hθ ht)
    (fun θ hθ s hs => schurKernel_eq_integral hK hW hθ hs)
    (fun θ₁ h₁ θ₂ h₂ t ht => norm_schurRho_sub_le hK hE hW hB h₁ h₂ ht)
    (fun θ hθ => schurKernel_end_right hK hW ha hθ)
    (fun s hs => schurKernel_end_left hK hW ha hs) hG c
  have := shiftConst_nonneg; positivity

lemma volterraKernel_continuousOn :
    ContinuousOn (volterraKernel W θ) angleInterval := by
  
  
  exact continuousOn_const.inner ((W θ).continuous.comp_continuousOn (((ContinuousLinearMap.adjoint  (E := Ell2) (F := Ell2)).continuous.comp_continuousOn hW.1).clm_apply continuousOn_const))

lemma smallB_continuousOn :
    ContinuousOn (smallB W) angleInterval := by
  have h : ContinuousOn (fun s => ⟪basisVec 0, W s (radialVec W)⟫_ℂ) angleInterval :=
    continuousOn_const.inner (hW.1.clm_apply continuousOn_const)
  refine h.congr fun s _ => ?_
  simp [smallB, inner_basisVec]

include hK in
/-- The kernel `r` acting on `g`, in terms of the Volterra operators. -/
lemma integral_schurKernel_mul_eq
    {g : ℝ → ℂ} (hgi : IntervalIntegrable g volume 0 anglePeriod)
    (hG : ∫ₚ t, g t = 0) {θ : ℝ} (hθ : θ ∈ angleInterval) :
    ∫ₚ s, schurKernel W θ s * g s =
      Complex.I * (volterraOp W g θ - volterraOpAdj W g θ) - 2 * Complex.I * (∫ s in (0 : ℝ)..θ, g s) -
        schurBeta W θ * (∫ₚ s, conj (smallB W s) * g s) / (smallA W : ℂ) := by
  have hL : anglePeriod ∈ angleInterval := (by grind)
  have hsub1 : uIcc 0 θ ⊆ uIcc 0 anglePeriod := by
    rw [uIcc_of_le hθ.1, uIcc_of_le hL.1]; exact Icc_subset_Icc le_rfl hθ.2
  have hsub2 : uIcc θ anglePeriod ⊆ uIcc 0 anglePeriod := by
    rw [uIcc_of_le hθ.2, uIcc_of_le hL.1]; exact Icc_subset_Icc hθ.1 le_rfl
  have hwc := volterraKernel_continuousOn hW θ
  rw [← uIcc_of_le hL.1] at hwc
  have hg1  := hgi.mono_set hsub1
  have hg2  := hgi.mono_set hsub2
  have hw1  :=
    hg1.continuousOn_mul (hwc.mono hsub1)
  have hw2  :=
    hg2.continuousOn_mul (hwc.mono hsub2)
  have A1 : IntervalIntegrable (fun s => schurKernel0 W θ s * g s) volume 0 θ := by
    refine ((hw1.sub hg1).const_mul Complex.I).congr fun s hs => ?_
    rw [uIoc_of_le hθ.1] at hs
    simp [schurKernel0, if_pos hs.2]; ring
  have A2 : IntervalIntegrable (fun s => schurKernel0 W θ s * g s) volume θ anglePeriod := by
    refine ((hw2.sub hg2).const_mul Complex.I).neg.congr fun s hs => ?_
    rw [uIoc_of_le hθ.2] at hs
    simp only [schurKernel0, if_neg (not_le.mpr hs.1), Pi.neg_apply]; ring
  have I1 : ∫ s in 0..θ, schurKernel0 W θ s * g s =
      Complex.I * (volterraOp W g θ - ∫ s in 0..θ, g s) := by
    rw [intervalIntegral.integral_congr (g := fun s => Complex.I *
      (volterraKernel W θ s * g s - g s)) (fun s hs => by
        rw [uIcc_of_le hθ.1] at hs
        simp [schurKernel0, if_pos hs.2]; ring),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_sub hw1 hg1]
    rfl
  have hadj : volterraOpAdj W g θ = ∫ s in θ..anglePeriod, volterraKernel W θ s * g s := by
    unfold volterraOpAdj
    simp only [conj_volterraKernel]
  have I2 : ∫ s in θ..anglePeriod, schurKernel0 W θ s * g s =
      -(Complex.I * (volterraOpAdj W g θ - ∫ s in θ..anglePeriod, g s)) := by
    rw [intervalIntegral.integral_congr (g := fun s => -(Complex.I *
      (volterraKernel W θ s * g s - g s))) (fun s hs => by
        rw [uIcc_of_le hθ.2] at hs
        simp only [schurKernel0_of_le hK hW hθ hs.1]; ring),
      intervalIntegral.integral_neg, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub hw2 hg2, hadj]
  have hsplit : ∫ s in θ..anglePeriod, g s = -∫ s in 0..θ, g s := by
    grind [intervalIntegral.integral_add_adjacent_intervals]
  have hbc : ContinuousOn (fun s => conj (smallB W s)) (uIcc 0 anglePeriod) := by
    rw [uIcc_of_le hL.1]
    exact Complex.continuous_conj.comp_continuousOn (smallB_continuousOn hW)
  have hB1  :=
    hgi.continuousOn_mul hbc
  
  have hrk : ∫ s in 0..anglePeriod, schurBeta W θ * (conj (schurBeta W s) * g s) /
      (smallA W) = schurBeta W θ *
        (∫ s in 0..anglePeriod, conj (smallB W s) * g s) / (smallA W) := by
    rw [intervalIntegral.integral_div, intervalIntegral.integral_const_mul]
    congr 2
    rw [intervalIntegral.integral_congr (g := fun s => conj (smallB W s) * g s - 2 * g s)
      (fun s _ => by simp [schurBeta, map_ofNat] <;> ring),
      intervalIntegral.integral_sub hB1 (hgi.const_mul 2), intervalIntegral.integral_const_mul,
      hG, mul_zero, sub_zero]
  rw [intervalIntegral.integral_congr (g := fun s => schurKernel0 W θ s * g s -
      schurBeta W θ * (conj (schurBeta W s) * g s) / (smallA W))
      (fun s _ => by simp only [schurKernel]; ring),
    intervalIntegral.integral_sub (A1.trans A2) (by
        refine (((hB1.sub (hgi.const_mul 2)).const_mul (schurBeta W θ)).div_const
          (smallA W)).congr fun s _ => ?_
        simp [schurBeta, map_ofNat] <;> ring), hrk,
    ← intervalIntegral.integral_add_adjacent_intervals A1 A2, I1, I2, hsplit]
  ring

include hK in
lemma norm_smallBDer_le_sqrt {t : ℝ}
    (ht : t ∈ angleInterval) : ‖smallBDer γ E W t‖ ≤ Real.sqrt E * K * 2 := by
  refine (norm_coeffTerm_le (norm_deriv_le_of_lipschitz hK)).trans ?_
  have h1 : ‖(W t (radialVec W)) 1‖ ≤ 2 :=
    (norm_coord_le _ _).trans (((W t).le_opNorm _).trans
      ((mul_le_mul (norm_transport_le_one hK hW ht) (norm_radialVec_le hK hW) (norm_nonneg _)
        zero_le_one).trans (by norm_num)))
  gcongr

include hE hK ha in
/-- `θ ↦ ∫₀^L r(θ, s) g(s) ds` is continuous on `[0, L]`. -/
lemma continuousOn_integral_schurKernel_mul {g : ℝ → ℂ} {Bg : ℝ}
    (hg : AEStronglyMeasurable g volume) (hgB : ∀ t, ‖g t‖ ≤ Bg)
    (hG : ∫ₚ t, g t = 0) :
    ContinuousOn (fun θ => ∫ₚ s, schurKernel W θ s * g s) angleInterval := by
  have hL : 0 ≤ anglePeriod := by positivity
  
  
  set B := Real.sqrt E * K * 2 
  have hB : ∀ t ∈ angleInterval, ‖smallBDer γ E W t‖ ≤ B := fun t ht =>
    norm_smallBDer_le_sqrt hK hW ht
  set M := K * (shiftConst * K) * E + B * B / |smallA W| 
  set Bρ := K * (shiftConst * K) * E * anglePeriod +
      (‖schurBeta W 0‖ + B * anglePeriod) * B / |smallA W|
  have hgr : AEStronglyMeasurable g (volume.restrict angleInterval) := hg.restrict
  have hgBr : ∀ t ∈ angleInterval, ‖g t‖ ≤ Bg := fun t _ => hgB t
  
  have hrep : ∀ θ ∈ angleInterval, ∫ s in 0..anglePeriod, schurKernel W θ s * g s =
      -∫ t in 0..anglePeriod, schurRho γ E W θ t * ((∫ u in 0..t, g u) - 0) :=
    fun θ hθ => kernel_integral_eq hL hgr hgBr (schurRho_aestronglyMeasurable hK hW hθ)
      (fun t ht => norm_schurRho_le hK hE hW hB hθ ht)
      (fun s hs => schurKernel_eq_integral hK hW hθ hs) (schurKernel_end_right hK hW ha hθ) hG 0
  have hint : ∀ θ ∈ angleInterval, IntervalIntegrable
      (fun t => schurRho γ E W θ t * ((∫ u in 0..t, g u) - 0)) volume 0 anglePeriod := by
    intro θ hθ
    refine intervalIntegrable_of_restrict_bound
      ((schurRho_aestronglyMeasurable hK hW hθ).mul
        (((continuousOn_primitive_of_bound hL hgr hgBr).sub continuousOn_const).aestronglyMeasurable measurableSet_Icc))
      (B := Bρ * (Bg * anglePeriod)) (fun t ht => ?_) (⟨le_rfl, hL⟩) (⟨hL, le_rfl⟩)
    simp
    exact mul_le_mul (norm_schurRho_le hK hE hW hB hθ ht) (norm_primitive_le hgBr ht)
      (norm_nonneg _) ((norm_nonneg _).trans (norm_schurRho_le hK hE hW hB hθ ht))
  have hBg  := (norm_nonneg _).trans (hgB 0)
  have hM0 : 0 ≤ M := by have := shiftConst_nonneg; positivity
  refine (LipschitzOnWith.of_dist_le_mul (K := (M * (Bg * anglePeriod) * anglePeriod).toNNReal)
    fun θ₁ h₁ θ₂ h₂ => ?_).continuousOn
  rw [hrep θ₁ h₁, hrep θ₂ h₂, dist_eq_norm, Real.dist_eq,
    Real.coe_toNNReal _ (by positivity), neg_sub_neg,
    ← intervalIntegral.integral_sub (hint θ₂ h₂) (hint θ₁ h₁)]
  
  refine (intervalIntegral.norm_integral_le_of_norm_le_const (by
      intro t ht
      rw [uIoc_of_le hL] at ht
      have ht' : t ∈ angleInterval := (by grind)
      rw [← sub_mul, norm_mul, sub_zero, norm_sub_rev]
      exact mul_le_mul (norm_schurRho_sub_le hK hE hW hB h₁ h₂ ht') (norm_primitive_le hgBr ht')
        (norm_nonneg _) (by positivity))).trans (le_of_eq ?_)
  simp [sub_zero] <;> ring

include hE hK ha in
/-- **Splitting of the Schur complement.** For a bounded measurable `g` with `∫₀^L g = 0` and
any `h` with `conj(g) h` integrable,

  `Re ∫ conj(g)(2h + i(T_E - T_E^*) g) - |∫ conj(b_E) g|² / a_E
      = Re ∫ conj(g)(2h + 2i G) + Re ∫ conj(g(θ)) ∫ r(θ, s) g(s) ds dθ`. -/
theorem re_volterra_sub_schur_eq {g : ℝ → ℂ} {Bg : ℝ}
    (hg : AEStronglyMeasurable g volume) (hgB : ∀ t, ‖g t‖ ≤ Bg)
    (hG : ∫ₚ t, g t = 0) {h : ℝ → ℂ}
    (hh : IntervalIntegrable (fun θ => conj (g θ) * h θ) volume 0 anglePeriod) :
    (∫ₚ θ, conj (g θ) *
        (2 * h θ + Complex.I * (volterraOp W g θ - volterraOpAdj W g θ))).re -
      ‖∫ₚ θ, conj (smallB W θ) * g θ‖ ^ 2 / smallA W =
    (∫ₚ θ, conj (g θ) *
        (2 * h θ + Complex.I * (2 * ∫ s in (0 : ℝ)..θ, g s))).re +
      (∫ₚ θ, conj (g θ) *
        ∫ₚ s, schurKernel W θ s * g s).re := by
  have hL : 0 ≤ anglePeriod := by positivity
  have hgi : IntervalIntegrable g volume 0 anglePeriod := intervalIntegrable_of_norm_le hg hgB _ _
  have hcg  :=
    intervalIntegrable_conj' hgi
  set Y := ∫ θ in 0..anglePeriod, conj (smallB W θ) * g θ with hY
  set Φ := fun θ => ∫ s in 0..anglePeriod, schurKernel W θ s * g s with hΦ
  
  have hGc : ContinuousOn (fun θ => ∫ s in 0..θ, g s) (uIcc 0 anglePeriod) := by
    rw [uIcc_of_le hL]
    exact continuousOn_primitive_of_bound hL hg.restrict (fun t _ => hgB t)
  
  have i1 : IntervalIntegrable (fun θ => conj (g θ) *
      (2 * h θ + Complex.I * (2 * ∫ s in 0..θ, g s))) volume 0 anglePeriod := by
    refine ((hh.const_mul 2).add (hcg.mul_continuousOn
      ((hGc.const_smul 2).const_smul Complex.I))).congr fun θ _ => ?_
    simp [smul_eq_mul] <;> ring
  have i2  :=
    hcg.mul_continuousOn (by
      rw [uIcc_of_le hL]; exact continuousOn_integral_schurKernel_mul hK hE hW ha hg hgB hG)
  
  have hpt : ∀ θ ∈ uIcc 0 anglePeriod, conj (g θ) *
      (2 * h θ + Complex.I * (volterraOp W g θ - volterraOpAdj W g θ)) =
      conj (g θ) * (2 * h θ + Complex.I * (2 * ∫ s in 0..θ, g s)) + conj (g θ) * Φ θ +
        conj (g θ) * schurBeta W θ * Y / (smallA W) := by
    intro θ hθ
    rw [uIcc_of_le hL] at hθ
    simp only [hΦ, integral_schurKernel_mul_eq hK hW hgi hG hθ, hY]
    ring
  have h3 : ∫ θ in 0..anglePeriod, conj (g θ) * schurBeta W θ * Y / (smallA W) =
      conj Y * Y / (smallA W) := by
    have hbc : ContinuousOn (fun s => conj (smallB W s)) (uIcc 0 anglePeriod) := by
      rw [uIcc_of_le hL]
      exact Complex.continuous_conj.comp_continuousOn (smallB_continuousOn hW)
    have hB1  :=
      hgi.continuousOn_mul hbc
    rw [intervalIntegral.integral_div, intervalIntegral.integral_mul_const]
    congr 2
    rw [intervalIntegral.integral_congr (g := fun θ => conj (conj (smallB W θ) * g θ) -
        2 * conj (g θ)) (fun θ _ => by simp [schurBeta, Complex.conj_conj] <;> ring),
      intervalIntegral.integral_sub (intervalIntegrable_conj' hB1) (hcg.const_mul 2),
      intervalIntegral.integral_const_mul, intervalIntegral_conj, intervalIntegral_conj, hG,
      map_zero, mul_zero, sub_zero]
  rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_add (i1.add i2) (((hcg.mul_continuousOn (by
      rw [uIcc_of_le hL]; exact (smallB_continuousOn hW).sub continuousOn_const)).mul_const Y).div_const _),
    intervalIntegral.integral_add i1 i2, h3, Complex.conj_mul', Complex.add_re, Complex.add_re,
    ← Complex.ofReal_pow, ← Complex.ofReal_div, Complex.ofReal_re]
  ring

end

end PolyaNeumann