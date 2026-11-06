module

public import RequestProject.PlanarTypes
public import Mathlib.Tactic.FunProp

public import RequestProject.PlanarGeometry

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
def schurBeta W θ  := smallB W θ - 2

/-- The jump part `i sgn(θ - s) (w(θ, s) - 1)` of the kernel. -/
def schurKernel0 W θ s  :=
  if s ≤ θ then Complex.I * (volterraKernel W θ s - 1) else -(Complex.I * (volterraKernel W θ s - 1))

/-- The corrected periodic kernel `r(θ, s) = i sgn(θ - s)(w(θ, s) - 1) - a⁻¹ β(θ) conj(β(s))`. -/
def schurKernel W θ s  :=
  schurKernel0 W θ s - schurBeta W θ * conj (schurBeta W s) / (smallA W : ℂ)

/-- The `s`-derivative of the jump part. -/
def schurRho0 γ E W θ t  :=
  if t ≤ θ then Complex.I * kernelRho γ E W θ t else -(Complex.I * kernelRho γ E W θ t)

/-- The `s`-derivative of the corrected kernel. -/
def schurRho γ E W θ t  :=
  schurRho0 γ E W θ t - schurBeta W θ * conj (smallBDer γ E W t) / (smallA W : ℂ)

variable {γ : ComplexCurve} {K : NNReal} {E : ℝ} {W : ℝ → ComplexEnd Ell2}

section
variable (hK : LipschitzWith K γ) (hW : IsTransport γ E W)

include hK hW in
lemma volterraKernel_diag 
    (hθ : θ ∈ boundaryInterval) : volterraKernel W θ θ = 1 := by
  have hu := transport_mem_unitary hK hW hθ
  rw [Unitary.mem_iff, ContinuousLinearMap.star_eq_adjoint] at hu
  rw [volterraKernel, ← ContinuousLinearMap.mul_apply, hu.2, ContinuousLinearMap.one_apply]
  simp [basisVec]

lemma volterraKernel_add_end (hW : IsTransport γ E W) θ :
    volterraKernel W θ circlePeriod + volterraKernel W θ 0 = smallB W θ := by
  rw [volterraKernel, volterraKernel, transport_zero hW, smallB, ← inner_basisVec,
    ← inner_add_right, ← map_add, radialVec, ← ContinuousLinearMap.star_eq_adjoint 1,
    star_one, ContinuousLinearMap.one_apply, add_comm]

lemma volterraKernel_end_add (hW : IsTransport γ E W) s :
    volterraKernel W circlePeriod s + volterraKernel W 0 s = conj (smallB W s) := by
  grind [conj_volterraKernel, volterraKernel_add_end]

include hK hW in
lemma smallB_end_sub :
    smallB W circlePeriod - smallB W 0 = Complex.I * smallA W := by
  have hu := transport_mem_unitary hK hW ⟨by positivity, le_rfl⟩
  rw [Unitary.mem_iff, ContinuousLinearMap.star_eq_adjoint] at hu
  have h1 : W circlePeriod (ContinuousLinearMap.adjoint (W circlePeriod) (basisVec 0)) = basisVec 0 := by
    rw [← ContinuousLinearMap.mul_apply, hu.2, ContinuousLinearMap.one_apply]
  have h2 : (ContinuousLinearMap.adjoint (W circlePeriod) (basisVec 0) : ComplexSeq) 0 =
      conj ((W circlePeriod (basisVec 0) : ComplexSeq) 0) := by
    rw [← inner_basisVec, ← inner_basisVec, ContinuousLinearMap.adjoint_inner_right,
      inner_conj_symm]
  unfold smallB radialVec smallA
  rw [transport_zero hW, ContinuousLinearMap.one_apply, map_add, h1]
  simp  [h2]
  apply Complex.ext <;> simp <;> ring

lemma intervalIntegrable_conj' {f : ComplexCurve}  (hf : IntervalIntegrable f volume a b) :
    IntervalIntegrable (fun t => conj (f t)) volume a b :=
  ⟨Complex.conjCLE.toContinuousLinearMap.integrable_comp hf.1,
    Complex.conjCLE.toContinuousLinearMap.integrable_comp hf.2⟩

include hK hW in
lemma kernelRho_intervalIntegrable θ
     (ht : t ∈ boundaryInterval) : IntervalIntegrable (kernelRho γ E W θ) volume 0 t := by
  have := transport_coord_intervalIntegrable' hK hW
    (ContinuousLinearMap.adjoint (W θ) (basisVec 0)) 0 ht
  simp  [transportCoeff_coord_zero] at this
  exact intervalIntegrable_conj' this

include hK hW in
lemma smallBDer_intervalIntegrable
     (ht : t ∈ boundaryInterval) : IntervalIntegrable (smallBDer γ E W) volume 0 t := by
  have := transport_coord_intervalIntegrable' hK hW (radialVec W) 0 ht
  simp  [transportCoeff_coord_zero] at this
  exact this

end


section
variable (hK : LipschitzWith K γ) (hW : IsTransport γ E W) {θ s } (hθ : θ ∈ boundaryInterval) (hs : s ∈ boundaryInterval)
local notation "schurRho0Fixed" => schurRho0 γ E W θ


include hK hW θ s hθ hs in
lemma schurKernel0_eq_integral :
    schurKernel0 W θ s = schurKernel0 W θ 0 + ∫ t in (0 : ℝ)..s, schurRho0Fixed t := by
  have h0 : schurKernel0 W θ 0 = Complex.I * (volterraKernel W θ 0 - 1) := if_pos hθ.1
  rw [h0]
  rcases le_or_gt s θ with hsθ | hθs
  · have hc : ∫ t in (0 : ℝ)..s, schurRho0Fixed t =
        ∫ t in (0 : ℝ)..s, Complex.I * kernelRho γ E W θ t := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [uIcc_of_le hs.1] at ht
      exact if_pos (ht.2.trans hsθ)
    rw [schurKernel0, if_pos hsθ, hc, intervalIntegral.integral_const_mul,
      volterraKernel_eq_integral hK hW θ hs]
    ring
  · have hi  :=
      kernelRho_intervalIntegrable hK hW θ hs
    have hiθ  :=
      kernelRho_intervalIntegrable hK hW θ hθ
    have hiθs  :=
      (hiθ.symm.trans hi)
    have i1 : IntervalIntegrable schurRho0Fixed volume 0 θ := by
      refine (hiθ.const_mul Complex.I).congr fun t ht => ?_
      rw [uIoc_of_le hθ.1] at ht
      exact (if_pos ht.2).symm
    have i2 : IntervalIntegrable schurRho0Fixed volume θ s := by
      refine (hiθs.const_mul Complex.I).neg.congr fun t ht => ?_
      rw [uIoc_of_le hθs.le] at ht
      exact (if_neg (not_le.mpr ht.1)).symm
    have c1 : ∫ t in (0 : ℝ)..θ, schurRho0Fixed t =
        ∫ t in (0 : ℝ)..θ, Complex.I * kernelRho γ E W θ t := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [uIcc_of_le hθ.1] at ht
      exact if_pos ht.2
    have c2 : ∫ t in θ..s, schurRho0Fixed t =
        ∫ t in θ..s, -(Complex.I * kernelRho γ E W θ t) := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [uIcc_of_le hθs.le] at ht
      rcases eq_or_lt_of_le ht.1 with h | h
      · subst h; simp [schurRho0, kernelRho_diag hK hW hθ]
      · exact if_neg (not_le.mpr h)
    have hdiag := volterraKernel_diag hK hW hθ
    have e1 := volterraKernel_eq_integral hK hW θ hs
    have e2 := volterraKernel_eq_integral hK hW θ hθ
    rw [hdiag] at e2
    rw [← intervalIntegral.integral_add_adjacent_intervals i1 i2, c1, c2,
      intervalIntegral.integral_neg, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, schurKernel0, if_neg (not_le.mpr hθs),
      ← intervalIntegral.integral_interval_sub_left hi hiθ, e1]
    linear_combination (2 * Complex.I) * e2

lemma schurBeta_eq (hK : LipschitzWith K γ) (hW : IsTransport γ E W) 
    (hs : s ∈ boundaryInterval) :
    schurBeta W s = schurBeta W 0 + ∫ t in (0 : ℝ)..s, smallBDer γ E W t := by
  rw [schurBeta, schurBeta, smallB_eq hK hW hs]
  ring

section
include hK hW θ s hθ hs

lemma schurRho0_intervalIntegrable :
    IntervalIntegrable schurRho0Fixed volume 0 s := by
  have hi  :=
    kernelRho_intervalIntegrable hK hW θ hs
  rcases le_or_gt s θ with hsθ | hθs
  · refine (hi.const_mul Complex.I).congr fun t ht => ?_
    rw [uIoc_of_le hs.1] at ht
    exact (if_pos (ht.2.trans hsθ)).symm
  · have hiθ  :=
      kernelRho_intervalIntegrable hK hW θ hθ
    have i1 : IntervalIntegrable schurRho0Fixed volume 0 θ := by
      refine (hiθ.const_mul Complex.I).congr fun t ht => ?_
      rw [uIoc_of_le hθ.1] at ht
      exact (if_pos ht.2).symm
    have i2 : IntervalIntegrable schurRho0Fixed volume θ s := by
      refine ((hiθ.symm.trans hi).const_mul Complex.I).neg.congr fun t ht => ?_
      rw [uIoc_of_le hθs.le] at ht
      exact (if_neg (not_le.mpr ht.1)).symm
    exact i1.trans i2

lemma schurKernel_eq_integral :
    schurKernel W θ s = schurKernel W θ 0 + ∫ t in (0 : ℝ)..s, schurRho γ E W θ t := by
  have hi0 := schurRho0_intervalIntegrable hK hW hθ hs
  have hb := smallBDer_intervalIntegrable hK hW hs
  have hi1 : IntervalIntegrable (fun t => schurBeta W θ * conj (smallBDer γ E W t) /
      (smallA W : ℂ)) volume 0 s := ((intervalIntegrable_conj' hb).const_mul _).div_const _
  have hint : ∫ t in (0 : ℝ)..s, schurRho γ E W θ t =
      (∫ t in (0 : ℝ)..s, schurRho0Fixed t) -
        schurBeta W θ * conj (∫ t in (0 : ℝ)..s, smallBDer γ E W t) / (smallA W : ℂ) := by
    unfold schurRho
    rw [intervalIntegral.integral_sub hi0 hi1, intervalIntegral.integral_div,
      intervalIntegral.integral_const_mul, intervalIntegral_conj]
  grind [schurKernel, schurKernel0_eq_integral, schurBeta_eq]

end


end


section
variable (hK : LipschitzWith K γ) (hW : IsTransport γ E W)
include hK hW

lemma schurKernel0_of_le 
    (hθ : θ ∈ boundaryInterval) (hθs : θ ≤ s) :
    schurKernel0 W θ s = -(Complex.I * (volterraKernel W θ s - 1)) := by
  grind only [schurKernel0, volterraKernel_diag]

lemma schurKernel_end_right
    (ha : smallA W ≠ 0)  (hθ : θ ∈ boundaryInterval) :
    schurKernel W θ circlePeriod = schurKernel W θ 0 := by
  have ha'  := Complex.ofReal_ne_zero.mpr ha
  have hb := smallB_end_sub hK hW
  have hk := volterraKernel_add_end hW θ
  have hcb : conj (schurBeta W circlePeriod) = conj (schurBeta W 0) - Complex.I * smallA W := by
    have : schurBeta W circlePeriod = schurBeta W 0 + Complex.I * smallA W := by
      unfold schurBeta; linear_combination hb
    measurability
  unfold schurKernel
  rw [schurKernel0_of_le hK hW hθ hθ.2, show schurKernel0 W θ 0 =
    Complex.I * (volterraKernel W θ 0 - 1) from if_pos hθ.1, hcb]
  grind only [schurBeta, smallA]

lemma schurKernel_end_left
    (ha : smallA W ≠ 0)  (hs : s ∈ boundaryInterval) :
    schurKernel W circlePeriod s = schurKernel W 0 s := by
  have ha'  := Complex.ofReal_ne_zero.mpr ha
  have hb := smallB_end_sub hK hW
  have hk := volterraKernel_end_add hW s
  have h0 : (0 : ℝ) ∈ boundaryInterval := ⟨le_rfl, by positivity⟩
  unfold schurKernel
  rw [schurKernel0_of_le hK hW h0 hs.1, show schurKernel0 W circlePeriod s =
    Complex.I * (volterraKernel W circlePeriod s - 1) from if_pos hs.2]
  unfold schurBeta
  rw [map_sub, map_ofNat]
  grind

lemma norm_schurBeta_sub_le 
    (hB : ∀ t ∈ boundaryInterval, ‖smallBDer γ E W t‖ ≤ B) 
    (h₁ : θ₁ ∈ boundaryInterval) (h₂ : θ₂ ∈ boundaryInterval) :
    ‖schurBeta W θ₁ - schurBeta W θ₂‖ ≤ B * |θ₁ - θ₂| := by
  rw [schurBeta_eq hK hW h₁, schurBeta_eq hK hW h₂, add_sub_add_left_eq_sub,
    intervalIntegral.integral_interval_sub_left (smallBDer_intervalIntegrable hK hW h₁)
      (smallBDer_intervalIntegrable hK hW h₂)]
  refine intervalIntegral.norm_integral_le_of_norm_le_const fun t ht => hB t ?_
  grind

end


lemma norm_schurRho0_sub_le (hK : LipschitzWith K γ) (hE : 0 ≤ E) (hW : IsTransport γ E W)
     (h₁ : θ₁ ∈ boundaryInterval) (h₂ : θ₂ ∈ boundaryInterval)
    (ht : t ∈ boundaryInterval) :
    ‖schurRho0 γ E W θ₁ t - schurRho0 γ E W θ₂ t‖ ≤ K * (shiftConst * K) * E * |θ₁ - θ₂| := by
  set M := K * (shiftConst * K) * E with hM
  have hd : ∀ θ ∈ boundaryInterval, ‖kernelRho γ E W θ t‖ ≤ M * |θ - t| := by
    intro θ hθ
    have := norm_kernelRho_sub_le hK hE hW hθ ht ht
    rwa [kernelRho_diag hK hW ht, sub_zero] at this
  have hI  := Complex.norm_I
  unfold schurRho0
  split_ifs with ha hb hb
  · rw [← mul_sub, norm_mul, hI, one_mul]; exact norm_kernelRho_sub_le hK hE hW h₁ h₂ ht
  · calc ‖Complex.I * kernelRho γ E W θ₁ t - -(Complex.I * kernelRho γ E W θ₂ t)‖
        ≤ ‖kernelRho γ E W θ₁ t‖ + ‖kernelRho γ E W θ₂ t‖ := by
          rw [sub_neg_eq_add, ← mul_add, norm_mul, hI, one_mul]; exact norm_add_le _ _
      _ ≤ M * |θ₁ - t| + M * |θ₂ - t| := add_le_add (hd θ₁ h₁) (hd θ₂ h₂)
      _ = M * |θ₁ - θ₂| := by
          grind
  · calc ‖-(Complex.I * kernelRho γ E W θ₁ t) - Complex.I * kernelRho γ E W θ₂ t‖
        ≤ ‖kernelRho γ E W θ₁ t‖ + ‖kernelRho γ E W θ₂ t‖ := by
          rw [← neg_add', ← mul_add, norm_neg, norm_mul, hI, one_mul]; exact norm_add_le _ _
      _ ≤ M * |θ₁ - t| + M * |θ₂ - t| := add_le_add (hd θ₁ h₁) (hd θ₂ h₂)
      _ = M * |θ₁ - θ₂| := by
          grind
  · rw [neg_sub_neg, ← mul_sub, norm_mul, hI, one_mul, norm_sub_rev]
    exact norm_kernelRho_sub_le hK hE hW h₁ h₂ ht

section
variable (hK : LipschitzWith K γ) (hE : 0 ≤ E) (hW : IsTransport γ E W) {B } (hB : ∀ t ∈ boundaryInterval, ‖smallBDer γ E W t‖ ≤ B)
include hK hE hW B hB

lemma norm_schurRho_sub_le
     (h₁ : θ₁ ∈ boundaryInterval) (h₂ : θ₂ ∈ boundaryInterval)
    (ht : t ∈ boundaryInterval) :
    ‖schurRho γ E W θ₁ t - schurRho γ E W θ₂ t‖ ≤
      (K * (shiftConst * K) * E + B * B / |smallA W|) * |θ₁ - θ₂| := by
  have hB0  := (norm_nonneg _).trans (hB t ht)
  have e : schurRho γ E W θ₁ t - schurRho γ E W θ₂ t =
      (schurRho0 γ E W θ₁ t - schurRho0 γ E W θ₂ t) -
        (schurBeta W θ₁ - schurBeta W θ₂) * conj (smallBDer γ E W t) / (smallA W : ℂ) := by
    unfold schurRho; ring
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  have h2 : ‖(schurBeta W θ₁ - schurBeta W θ₂) * conj (smallBDer γ E W t) / (smallA W : ℂ)‖ ≤
      B * B / |smallA W| * |θ₁ - θ₂| := by
    rw [norm_div, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs]
    rcases eq_or_ne (smallA W) 0 with h0 | h0
    · simp [h0]
    · rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right (abs_pos.mpr h0)]
      calc ‖schurBeta W θ₁ - schurBeta W θ₂‖ * ‖smallBDer γ E W t‖ ≤ (B * |θ₁ - θ₂|) * B :=
            mul_le_mul (norm_schurBeta_sub_le hK hW hB h₁ h₂) (hB t ht) (norm_nonneg _)
              (by positivity)
        _ = B * B * |θ₁ - θ₂| := by ring
  linarith [norm_schurRho0_sub_le hK hE hW h₁ h₂ ht]

lemma norm_schurRho_le
     (hθ : θ ∈ boundaryInterval) (ht : t ∈ boundaryInterval) :
    ‖schurRho γ E W θ t‖ ≤ K * (shiftConst * K) * E * circlePeriod +
      (‖schurBeta W 0‖ + B * circlePeriod) * B / |smallA W| := by
  have h0 : (0 : ℝ) ∈ boundaryInterval := ⟨le_rfl, by positivity⟩
  have hB0  := (norm_nonneg _).trans (hB t ht)
  have hdist : |θ - t| ≤ 2 * π := by
    grind
  have hk : ‖kernelRho γ E W θ t‖ ≤ K * (shiftConst * K) * E * circlePeriod := by
    have := norm_kernelRho_sub_le hK hE hW hθ ht ht
    rw [kernelRho_diag hK hW ht, sub_zero] at this
    refine this.trans (mul_le_mul_of_nonneg_left hdist ?_)
    have := shiftConst_nonneg; positivity
  have h0' : ‖schurRho0 γ E W θ t‖ ≤ K * (shiftConst * K) * E * circlePeriod := by
    unfold schurRho0
    split_ifs <;> simpa [] using hk
  have hβ : ‖schurBeta W θ‖ ≤ ‖schurBeta W 0‖ + B * circlePeriod := by
    have := norm_schurBeta_sub_le hK hW hB hθ h0
    rw [sub_zero, abs_of_nonneg hθ.1] at this
    have h3 : ‖schurBeta W θ‖ ≤ ‖schurBeta W 0‖ + ‖schurBeta W θ - schurBeta W 0‖ := by
      have := norm_add_le (schurBeta W 0) (schurBeta W θ - schurBeta W 0)
      rwa [add_sub_cancel] at this
    nlinarith [hθ.2]
  have h1 : ‖schurBeta W θ * conj (smallBDer γ E W t) / (smallA W : ℂ)‖ ≤
      (‖schurBeta W 0‖ + B * circlePeriod) * B / |smallA W| := by
    rw [norm_div, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs]
    exact div_le_div_of_nonneg_right (mul_le_mul hβ (hB t ht) (norm_nonneg _)
      (by positivity)) (abs_nonneg _)
  exact (norm_sub_le _ _).trans (add_le_add h0' h1)

end


section
variable (hK : LipschitzWith K γ) (hW : IsTransport γ E W)

include hK hW in
lemma schurRho_aestronglyMeasurable
     (hθ : θ ∈ boundaryInterval) :
    AEStronglyMeasurable (schurRho γ E W θ) (volume.restrict boundaryInterval) := by
  have hL : circlePeriod ∈ boundaryInterval := ⟨by positivity, le_rfl⟩
  have hi : IntervalIntegrable (schurRho γ E W θ) volume 0 circlePeriod :=
    (schurRho0_intervalIntegrable hK hW hθ hL).sub
      (((intervalIntegrable_conj' (smallBDer_intervalIntegrable hK hW hL)).const_mul _).div_const _)
  exact ((intervalIntegrable_iff_integrableOn_Icc_of_le (by positivity)).mp hi).aestronglyMeasurable

/-- **Kernel estimate.** For a bounded measurable `g` with `∫₀^L g = 0`, primitive `G`, and any
constant `c`, the corrected kernel form is bounded by `M (∫₀^L |G - c|)²` with
`M = K (κ K) E + B² / |a_E|`, where `B` bounds `|b'_E|`. -/
theorem norm_schurKernel_form_le (hK : LipschitzWith K γ) (hE : 0 ≤ E) (hW : IsTransport γ E W)
    (ha : smallA W ≠ 0)  (hB : ∀ t ∈ boundaryInterval, ‖smallBDer γ E W t‖ ≤ B)
      (hg : AEStronglyMeasurable g volume) (hgB : ∀ t, ‖g t‖ ≤ Bg)
    (hG : ∫ t in (0 : ℝ)..circlePeriod, g t = 0) c :
    ‖∫ θ in (0 : ℝ)..circlePeriod, conj (g θ) * ∫ s in (0 : ℝ)..circlePeriod, schurKernel W θ s * g s‖ ≤
      (K * (shiftConst * K) * E + B * B / |smallA W|) *
        (∫ t in (0 : ℝ)..circlePeriod, ‖(∫ u in (0 : ℝ)..t, g u) - c‖) ^ 2 := by
  have hB0  := (norm_nonneg _).trans (hB 0 ⟨le_rfl, by positivity⟩)
  have hM : 0 ≤ (K : ℝ) * (shiftConst * K) * E + B * B / |smallA W| := by
    have := shiftConst_nonneg; positivity
  exact norm_kernel_form_le (by positivity) hM hg hgB
    (fun θ hθ => schurRho_aestronglyMeasurable hK hW hθ)
    (fun θ hθ t ht => norm_schurRho_le hK hE hW hB hθ ht)
    (fun θ hθ s hs => schurKernel_eq_integral hK hW hθ hs)
    (fun θ₁ h₁ θ₂ h₂ t ht => norm_schurRho_sub_le hK hE hW hB h₁ h₂ ht)
    (fun θ hθ => schurKernel_end_right hK hW ha hθ)
    (fun s hs => schurKernel_end_left hK hW ha hs) hG c

lemma volterraKernel_continuousOn (hW : IsTransport γ E W) θ :
    ContinuousOn (volterraKernel W θ) boundaryInterval := by
  have h1  :=
    (ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := Ell2) (F := Ell2)).continuous.comp_continuousOn hW.1
  have h2 : ContinuousOn (fun s => W θ (ContinuousLinearMap.adjoint (W s) (basisVec 0)))
      boundaryInterval := (W θ).continuous.comp_continuousOn (h1.clm_apply continuousOn_const)
  exact continuousOn_const.inner h2

@[fun_prop]
lemma smallB_continuousOn (hW : IsTransport γ E W) :
    ContinuousOn (smallB W) boundaryInterval := by
  have h : ContinuousOn (fun s => ⟪basisVec 0, W s (radialVec W)⟫_ℂ) boundaryInterval :=
    continuousOn_const.inner (hW.1.clm_apply continuousOn_const)
  refine h.congr fun s _ => ?_
  beta_reduce
  rw [smallB, inner_basisVec]

include hK hW in
/-- The kernel `r` acting on `g`, in terms of the Volterra operators. -/
lemma integral_schurKernel_mul_eq
     (hgi : IntervalIntegrable g volume 0 circlePeriod)
    (hG : ∫ t in (0 : ℝ)..circlePeriod, g t = 0)  (hθ : θ ∈ boundaryInterval) :
    ∫ s in (0 : ℝ)..circlePeriod, schurKernel W θ s * g s =
      Complex.I * (volterraOp W g θ - volterraOpAdj W g θ) - 2 * Complex.I * (∫ s in (0 : ℝ)..θ, g s) -
        schurBeta W θ * (∫ s in (0 : ℝ)..circlePeriod, conj (smallB W s) * g s) / (smallA W : ℂ) := by
  have hL : circlePeriod ∈ boundaryInterval := ⟨by positivity, le_rfl⟩
  have hsub1 : uIcc 0 θ ⊆ uIcc 0 circlePeriod := by
    rw [uIcc_of_le hθ.1, uIcc_of_le hL.1]; exact Icc_subset_Icc le_rfl hθ.2
  have hsub2 : uIcc θ circlePeriod ⊆ uIcc 0 circlePeriod := by
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
    grind [schurKernel0]
  have A2 : IntervalIntegrable (fun s => schurKernel0 W θ s * g s) volume θ circlePeriod := by
    refine ((hw2.sub hg2).const_mul Complex.I).neg.congr fun s hs => ?_
    rw [uIoc_of_le hθ.2] at hs
    simp only [schurKernel0, if_neg (not_le.mpr hs.1), Pi.neg_apply]; ring
  have I1 : ∫ s in (0 : ℝ)..θ, schurKernel0 W θ s * g s =
      Complex.I * (volterraOp W g θ - ∫ s in (0 : ℝ)..θ, g s) := by
    rw [intervalIntegral.integral_congr (g := fun s => Complex.I *
      (volterraKernel W θ s * g s - g s)) (fun s hs => by
        rw [uIcc_of_le hθ.1] at hs
        grind [schurKernel0]),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_sub hw1 hg1]
    rfl
  have hadj : volterraOpAdj W g θ = ∫ s in θ..circlePeriod, volterraKernel W θ s * g s := by
    simp_all [volterraOpAdj, conj_volterraKernel]
  have I2 : ∫ s in θ..circlePeriod, schurKernel0 W θ s * g s =
      -(Complex.I * (volterraOpAdj W g θ - ∫ s in θ..circlePeriod, g s)) := by
    rw [intervalIntegral.integral_congr (g := fun s => -(Complex.I *
      (volterraKernel W θ s * g s - g s))) (fun s hs => by
        rw [uIcc_of_le hθ.2] at hs
        grind [schurKernel0_of_le]),
      intervalIntegral.integral_neg, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub hw2 hg2, hadj]
  have hsplit : ∫ s in θ..circlePeriod, g s = -∫ s in (0 : ℝ)..θ, g s := by
    have := intervalIntegral.integral_add_adjacent_intervals hg1 hg2
    grind
  have hbc : ContinuousOn (fun s => conj (smallB W s)) (uIcc 0 circlePeriod) := by
    rw [uIcc_of_le hL.1]
    fun_prop
  have hB1  :=
    hgi.continuousOn_mul hbc
  have hB2 : IntervalIntegrable (fun s => schurBeta W θ * (conj (schurBeta W s) * g s) /
      (smallA W : ℂ)) volume 0 circlePeriod := by
    refine (((hB1.sub (hgi.const_mul 2)).const_mul (schurBeta W θ)).div_const
      (smallA W)).congr fun s _ => ?_
    simp only [schurBeta, map_sub, map_ofNat]; ring
  have hrk : ∫ s in (0 : ℝ)..circlePeriod, schurBeta W θ * (conj (schurBeta W s) * g s) /
      (smallA W : ℂ) = schurBeta W θ *
        (∫ s in (0 : ℝ)..circlePeriod, conj (smallB W s) * g s) / (smallA W : ℂ) := by
    rw [intervalIntegral.integral_div, intervalIntegral.integral_const_mul]
    congr 2
    rw [intervalIntegral.integral_congr (g := fun s => conj (smallB W s) * g s - 2 * g s)
      (fun s _ => by simp only [schurBeta, map_sub, map_ofNat]; ring),
      intervalIntegral.integral_sub hB1 (hgi.const_mul 2), intervalIntegral.integral_const_mul,
      hG, mul_zero, sub_zero]
  rw [intervalIntegral.integral_congr (g := fun s => schurKernel0 W θ s * g s -
      schurBeta W θ * (conj (schurBeta W s) * g s) / (smallA W))
      (fun s _ => by simp only [schurKernel]; ring),
    intervalIntegral.integral_sub (A1.trans A2) hB2, hrk,
    ← intervalIntegral.integral_add_adjacent_intervals A1 A2, I1, I2, hsplit]
  ring

include hK hW in
lemma norm_smallBDer_le_sqrt 
    (ht : t ∈ boundaryInterval) : ‖smallBDer γ E W t‖ ≤ Real.sqrt E * K * 2 := by
  refine (norm_coeffTerm_le (norm_deriv_le_of_lipschitz hK)).trans ?_
  have h1 : ‖(W t (radialVec W) : ComplexSeq) 1‖ ≤ 2 :=
    (norm_coord_le _ _).trans (((W t).le_opNorm _).trans
      ((mul_le_mul (norm_transport_le_one hK hW ht) (norm_radialVec_le hK hW) (norm_nonneg _)
        zero_le_one).trans (by norm_num)))
  gcongr

end


section
variable (hK : LipschitzWith K γ) (hE : 0 ≤ E) (hW : IsTransport γ E W) (ha : smallA W ≠ 0) {g : ComplexCurve} {Bg } (hg : AEStronglyMeasurable g volume) (hgB : ∀ t, ‖g t‖ ≤ Bg) (hG : ∫ t in (0 : ℝ)..circlePeriod, g t = 0)
include hK hE hW ha g Bg hg hgB hG

/-- `θ ↦ ∫₀^L r(θ, s) g(s) ds` is continuous on `[0, L]`. -/
lemma continuousOn_integral_schurKernel_mul :
    ContinuousOn (fun θ => ∫ s in (0 : ℝ)..circlePeriod, schurKernel W θ s * g s) boundaryInterval := by
  have hL : (0 : ℝ) ≤ 2 * π := by positivity
  have h0 : (0 : ℝ) ∈ boundaryInterval := ⟨le_rfl, hL⟩
  have hL' : circlePeriod ∈ boundaryInterval := ⟨hL, le_rfl⟩
  set B := Real.sqrt E * K * 2 with hBdef
  have hB : ∀ t ∈ boundaryInterval, ‖smallBDer γ E W t‖ ≤ B := fun t ht =>
    norm_smallBDer_le_sqrt hK hW ht
  set M := K * (shiftConst * K) * E + B * B / |smallA W| with hM
  set Bρ := K * (shiftConst * K) * E * circlePeriod +
      (‖schurBeta W 0‖ + B * circlePeriod) * B / |smallA W|
  have hgr : AEStronglyMeasurable g (volume.restrict boundaryInterval) := hg.restrict
  have hgBr : ∀ t ∈ boundaryInterval, ‖g t‖ ≤ Bg := fun t _ => hgB t
  have hGc := continuousOn_primitive_of_bound hL hgr hgBr
  have hrep : ∀ θ ∈ boundaryInterval, ∫ s in (0 : ℝ)..circlePeriod, schurKernel W θ s * g s =
      -∫ t in (0 : ℝ)..circlePeriod, schurRho γ E W θ t * ((∫ u in (0 : ℝ)..t, g u) - 0) :=
    fun θ hθ => kernel_integral_eq hL hgr hgBr (schurRho_aestronglyMeasurable hK hW hθ)
      (fun t ht => norm_schurRho_le hK hE hW hB hθ ht)
      (fun s hs => schurKernel_eq_integral hK hW hθ hs) (schurKernel_end_right hK hW ha hθ) hG 0
  have hint : ∀ θ ∈ boundaryInterval, IntervalIntegrable
      (fun t => schurRho γ E W θ t * ((∫ u in (0 : ℝ)..t, g u) - 0)) volume 0 circlePeriod := by
    intro θ hθ
    refine intervalIntegrable_of_restrict_bound
      ((schurRho_aestronglyMeasurable hK hW hθ).mul
        ((hGc.sub continuousOn_const).aestronglyMeasurable measurableSet_Icc))
      (B := Bρ * (Bg * circlePeriod)) (fun t ht => ?_) h0 hL'
    simp only [Pi.mul_apply, Pi.sub_apply, sub_zero]
    rw [norm_mul]
    exact mul_le_mul (norm_schurRho_le hK hE hW hB hθ ht) (norm_primitive_le hgBr ht)
      (norm_nonneg _) ((norm_nonneg _).trans (norm_schurRho_le hK hE hW hB hθ ht))
  have hBg  := (norm_nonneg _).trans (hgB 0)
  have hM0 : 0 ≤ M := by have := shiftConst_nonneg; positivity
  refine (LipschitzOnWith.of_dist_le_mul (K := (M * (Bg * circlePeriod) * circlePeriod).toNNReal)
    fun θ₁ h₁ θ₂ h₂ => ?_).continuousOn
  rw [hrep θ₁ h₁, hrep θ₂ h₂, dist_eq_norm, Real.dist_eq,
    Real.coe_toNNReal _ (by positivity), neg_sub_neg,
    ← intervalIntegral.integral_sub (hint θ₂ h₂) (hint θ₁ h₁)]
  have hb : ∀ t ∈ Ι (0 : ℝ) circlePeriod, ‖schurRho γ E W θ₂ t * ((∫ u in (0 : ℝ)..t, g u) - 0) -
      schurRho γ E W θ₁ t * ((∫ u in (0 : ℝ)..t, g u) - 0)‖ ≤ M * |θ₁ - θ₂| * (Bg * circlePeriod) := by
    intro t ht
    rw [uIoc_of_le hL] at ht
    have ht' : t ∈ boundaryInterval := ⟨ht.1.le, ht.2⟩
    rw [← sub_mul, norm_mul, sub_zero, norm_sub_rev]
    exact mul_le_mul (norm_schurRho_sub_le hK hE hW hB h₁ h₂ ht') (norm_primitive_le hgBr ht')
      (norm_nonneg _) (by positivity)
  refine (intervalIntegral.norm_integral_le_of_norm_le_const hb).trans (le_of_eq ?_)
  rw [sub_zero, abs_of_nonneg hL]; ring

/-- **Splitting of the Schur complement.** For a bounded measurable `g` with `∫₀^L g = 0` and
any `h` with `conj(g) h` integrable,

  `Re ∫ conj(g)(2h + i(T_E - T_E^*) g) - |∫ conj(b_E) g|² / a_E
      = Re ∫ conj(g)(2h + 2i G) + Re ∫ conj(g(θ)) ∫ r(θ, s) g(s) ds dθ`. -/
theorem re_volterra_sub_schur_eq {h : ComplexCurve}
    (hh : IntervalIntegrable (fun θ => conj (g θ) * h θ) volume 0 circlePeriod) :
    (∫ θ in (0 : ℝ)..circlePeriod, conj (g θ) *
        (2 * h θ + Complex.I * (volterraOp W g θ - volterraOpAdj W g θ))).re -
      ‖∫ θ in (0 : ℝ)..circlePeriod, conj (smallB W θ) * g θ‖ ^ 2 / smallA W =
    (∫ θ in (0 : ℝ)..circlePeriod, conj (g θ) *
        (2 * h θ + Complex.I * (2 * ∫ s in (0 : ℝ)..θ, g s))).re +
      (∫ θ in (0 : ℝ)..circlePeriod, conj (g θ) *
        ∫ s in (0 : ℝ)..circlePeriod, schurKernel W θ s * g s).re := by
  have hL : (0 : ℝ) ≤ 2 * π := by positivity
  have hgi : IntervalIntegrable g volume 0 circlePeriod := intervalIntegrable_of_norm_le hg hgB _ _
  have hcg  :=
    intervalIntegrable_conj' hgi
  set Y := ∫ θ in (0)..circlePeriod, conj (smallB W θ) * g θ with hY
  set Φ := fun θ => ∫ s in (0)..circlePeriod, schurKernel W θ s * g s with hΦ
  have hΦc : ContinuousOn Φ (uIcc 0 circlePeriod) := by
    rw [uIcc_of_le hL]; exact continuousOn_integral_schurKernel_mul hK hE hW ha hg hgB hG
  have hGc : ContinuousOn (fun θ => ∫ s in (0 : ℝ)..θ, g s) (uIcc 0 circlePeriod) := by
    rw [uIcc_of_le hL]
    exact continuousOn_primitive_of_bound hL hg.restrict (fun t _ => hgB t)
  have hβc : ContinuousOn (schurBeta W) (uIcc 0 circlePeriod) := by
    rw [uIcc_of_le hL]; exact (smallB_continuousOn hW).sub continuousOn_const
  have i1 : IntervalIntegrable (fun θ => conj (g θ) *
      (2 * h θ + Complex.I * (2 * ∫ s in (0 : ℝ)..θ, g s))) volume 0 circlePeriod := by
    refine ((hh.const_mul 2).add (hcg.mul_continuousOn
      ((hGc.const_smul 2).const_smul Complex.I))).congr fun θ _ => ?_
    simp  ; ring
  have i2  :=
    hcg.mul_continuousOn hΦc
  have i3 : IntervalIntegrable (fun θ => conj (g θ) * schurBeta W θ * Y / (smallA W : ℂ))
      volume 0 circlePeriod := ((hcg.mul_continuousOn hβc).mul_const Y).div_const _
  have hpt : ∀ θ ∈ uIcc 0 circlePeriod, conj (g θ) *
      (2 * h θ + Complex.I * (volterraOp W g θ - volterraOpAdj W g θ)) =
      conj (g θ) * (2 * h θ + Complex.I * (2 * ∫ s in (0 : ℝ)..θ, g s)) + conj (g θ) * Φ θ +
        conj (g θ) * schurBeta W θ * Y / (smallA W : ℂ) := by
    intro θ hθ
    rw [uIcc_of_le hL] at hθ
    grind only [integral_schurKernel_mul_eq]
  have h3 : ∫ θ in (0 : ℝ)..circlePeriod, conj (g θ) * schurBeta W θ * Y / (smallA W : ℂ) =
      conj Y * Y / (smallA W : ℂ) := by
    have hbc : ContinuousOn (fun s => conj (smallB W s)) (uIcc 0 circlePeriod) := by
      rw [uIcc_of_le hL]
      fun_prop
    have hB1  :=
      hgi.continuousOn_mul hbc
    rw [intervalIntegral.integral_div, intervalIntegral.integral_mul_const]
    congr 2
    rw [intervalIntegral.integral_congr (g := fun θ => conj (conj (smallB W θ) * g θ) -
        2 * conj (g θ)) (fun θ _ => by simp only [schurBeta, map_mul, Complex.conj_conj]; ring),
      intervalIntegral.integral_sub (intervalIntegrable_conj' hB1) (hcg.const_mul 2),
      intervalIntegral.integral_const_mul, intervalIntegral_conj, intervalIntegral_conj, hG,
      map_zero, mul_zero, sub_zero]
  rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_add (i1.add i2) i3,
    intervalIntegral.integral_add i1 i2, h3, Complex.conj_mul', Complex.add_re, Complex.add_re,
    ← Complex.ofReal_pow, ← Complex.ofReal_div, Complex.ofReal_re]
  ring

end


end PolyaNeumann