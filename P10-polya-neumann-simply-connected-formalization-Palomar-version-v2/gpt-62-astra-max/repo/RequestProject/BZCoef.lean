module

public import RequestProject.ChainRule

/-!
# The pulled-back coefficient matrix `A = |det T| T⁻¹ T⁻ᵀ`

For a real-linear map `T : ℂ → ℂ` with matrix `[[a, b], [c, d]]` (`T 1 = a + i c`,
`T i = b + i d`), `bzCoef T = |det T|⁻¹ [[b² + d², -(ab + cd)], [-(ab + cd), a² + c²]]`, which is
`|det T| T⁻¹ T⁻ᵀ` when `det T ≠ 0`. It satisfies:

* `sesq_bzCoef_chain`: `∑ A_{ik} conj(g_i) g_k = |det T| ∑ |y_j|²` for `g = Tᵀ y`
  (this is the change of variables of the Dirichlet energy under the chain rule);
* `bzCoef_ellip`: `|det T| |ξ|² ≤ 2 ‖T‖² Re ∑ A_{ik} conj(ξ_i) ξ_k`;
* `abs_bzCoef_le`: `|A_{ik}| ≤ 2 ‖T‖² / |det T|`;
* `bzCoef_id`: `bzCoef id = 1`.
-/

@[expose] public section

open MeasureTheory Filter Topology Metric Set
open scoped ComplexConjugate

noncomputable section

namespace PolyaNeumann

section

variable (T : ℂ →L[ℝ] ℂ) (a : ℝ) (hT : T.det ≠ 0) (b c d : ℝ) (ξ : Fin 2 → ℂ)

lemma det_eq_of_clm :
    T.det = (T 1).re * (T Complex.I).im - (T Complex.I).re * (T 1).im := by
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix Complex.basisOneI, Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply]

include a b c d in
/-- The cofactor-type matrix `[[b² + d², -(ab + cd)], [-(ab + cd), a² + c²]]`. -/
def cofMat : Matrix (Fin 2) (Fin 2) ℝ :=
  !![b ^ 2 + d ^ 2, -(a * b + c * d); -(a * b + c * d), a ^ 2 + c ^ 2]

lemma sesq_cofMat_chain (y0 y1 : ℂ) :
    (∑ i, ∑ k, ((cofMat a b c d) i k : ℂ) * inner ℂ (![a * y0 + c * y1, b * y0 + d * y1] i)
      (![a * y0 + c * y1, b * y0 + d * y1] k)) =
      (((a * d - b * c) ^ 2 : ℝ) : ℂ) * (conj y0 * y0 + conj y1 * y1) := by
  simp only [Fin.sum_univ_two, cofMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
    RCLike.inner_apply, map_add, map_mul, Complex.conj_ofReal]
  push_cast
  ring

lemma sesq_cofMat :
    (∑ i, ∑ k, ((cofMat a b c d) i k : ℂ) * inner ℂ (ξ i) (ξ k)) =
      ((‖d * ξ 0 - c * ξ 1‖ ^ 2 + ‖b * ξ 0 - a * ξ 1‖ ^ 2 : ℝ) : ℂ) := by
  simp only [Fin.sum_univ_two, cofMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
    RCLike.inner_apply]
  push_cast
  rw [← Complex.conj_mul', ← Complex.conj_mul']
  simp <;> ring

lemma norm_sq_comb_le (P R : ℂ) :
    ‖(a : ℂ) * P - c * R‖ ^ 2 ≤ (a ^ 2 + c ^ 2) * (‖P‖ ^ 2 + ‖R‖ ^ 2) := by
  have h1 : ‖(a : ℂ) * P - c * R‖ ≤ |a| * ‖P‖ + |c| * ‖R‖ := by
    refine (norm_sub_le _ _).trans (le_of_eq ?_)
    simp [Complex.norm_real]
  
  
  
  calc _ ≤ (|a| * ‖P‖ + |c| * ‖R‖) ^ 2 := by gcongr
    _ ≤ _ := by
      rw [← (sq_abs a), ← (sq_abs c)]
      nlinarith [sq_nonneg (|a| * ‖R‖ - |c| * ‖P‖)]

/-- `D² |ξ|² ≤ (a² + b² + c² + d²) Q(ξ)` with `D = ad - bc` and `Q` the quadratic form of
`cofMat`. -/
lemma cofMat_lower :
    (a * d - b * c) ^ 2 * (‖ξ 0‖ ^ 2 + ‖ξ 1‖ ^ 2) ≤
      (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) * (‖d * ξ 0 - c * ξ 1‖ ^ 2 + ‖b * ξ 0 - a * ξ 1‖ ^ 2) := by
  set P := d * ξ 0 - c * ξ 1
  set R := b * ξ 0 - a * ξ 1
  have e0 : ((a * d - b * c : ℝ) : ℂ) * ξ 0 = a * P - c * R := by
    simp <;> ring
  have e1 : ((a * d - b * c : ℝ) : ℂ) * ξ 1 = b * P - d * R := by
    simp <;> ring
  have n0 : (a * d - b * c) ^ 2 * ‖ξ 0‖ ^ 2 = ‖(a : ℂ) * P - c * R‖ ^ 2 := by
    rw [← e0, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  have n1 : (a * d - b * c) ^ 2 * ‖ξ 1‖ ^ 2 = ‖(b : ℂ) * P - d * R‖ ^ 2 := by
    rw [← e1, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  have := norm_sq_comb_le a c P R
  have := norm_sq_comb_le b d P R
  nlinarith

include T in
/-- The coefficient matrix `|det T| T⁻¹ T⁻ᵀ` of the pulled-back Dirichlet form. -/
def bzCoef : Matrix (Fin 2) (Fin 2) ℝ :=
  |T.det|⁻¹ • cofMat (T 1).re (T Complex.I).re (T 1).im (T Complex.I).im

lemma sesq_bzCoef :
    (∑ i, ∑ k, ((bzCoef T) i k : ℂ) * inner ℂ (ξ i) (ξ k)) =
      ((|T.det|⁻¹ * (‖(T Complex.I).im * ξ 0 - (T 1).im * ξ 1‖ ^ 2 +
        ‖(T Complex.I).re * ξ 0 - (T 1).re * ξ 1‖ ^ 2) : ℝ) : ℂ) := by
  have := sesq_cofMat (T 1).re (T Complex.I).re (T 1).im (T Complex.I).im ξ
  simp only [bzCoef, Matrix.smul_apply, smul_eq_mul, Complex.ofReal_mul, mul_assoc,
    ← Finset.mul_sum] at this ⊢
  rw [this]

include hT in
/-- Under the chain rule `g = Tᵀ y`, the form of `bzCoef T` is `|det T| |y|²`. -/
lemma sesq_bzCoef_chain (y : Fin 2 → ℂ) :
    (∑ i, ∑ k, ((bzCoef T) i k : ℂ) *
      inner ℂ (∑ j, (coordRe j (T (coordDir i)) : ℂ) * y j)
        (∑ j, (coordRe j (T (coordDir k)) : ℂ) * y j)) =
      ((|T.det| * ∑ j, ‖y j‖ ^ 2 : ℝ) : ℂ) := by
  
  have hg : ∀ i, (∑ j, (coordRe j (T (coordDir i)) : ℂ) * y j) =
      ![(T 1).re * y 0 + (T 1).im * y 1, (T Complex.I).re * y 0 + (T Complex.I).im * y 1] i := by
    intro i; fin_cases i <;> simp [coordRe, coordDir, Fin.sum_univ_two]
  simp only [hg]
  simp only [bzCoef, Matrix.smul_apply, smul_eq_mul, Complex.ofReal_mul, mul_assoc,
    ← Finset.mul_sum]
  rw [(sesq_cofMat_chain (T 1).re (T Complex.I).re (T 1).im (T Complex.I).im (y 0) (y 1)), ← det_eq_of_clm, Fin.sum_univ_two, Complex.conj_mul', Complex.conj_mul']
  
  have h2 : ((T.det : ℝ) : ℂ) ^ 2 = ((|T.det| : ℝ) : ℂ) ^ 2 := by
    exact_mod_cast (sq_abs T.det).symm
  
  push_cast
  rw [h2]
  field_simp

lemma re_sesq_bzCoef_nonneg :
    0 ≤ (∑ i, ∑ k, ((bzCoef T) i k : ℂ) * inner ℂ (ξ i) (ξ k)).re := by
  rw [sesq_bzCoef, Complex.ofReal_re]
  positivity

include hT in
/-- Ellipticity: `|det T| |ξ|² ≤ 2 ‖T‖² Re ∑ A_{ik} conj(ξ_i) ξ_k`. -/
lemma bzCoef_ellip :
    |T.det| * ∑ i, ‖ξ i‖ ^ 2 ≤
      2 * ‖T‖ ^ 2 * (∑ i, ∑ k, ((bzCoef T) i k : ℂ) * inner ℂ (ξ i) (ξ k)).re := by
  rw [sesq_bzCoef, Complex.ofReal_re, Fin.sum_univ_two]
  set a := (T 1).re
  set b := (T Complex.I).re
  set c := (T 1).im
  set d := (T Complex.I).im
  set Q := ‖d * ξ 0 - c * ξ 1‖ ^ 2 + ‖b * ξ 0 - a * ξ 1‖ ^ 2
  
  have hlow := cofMat_lower a b c d ξ
  rw [← det_eq_of_clm, ← sq_abs] at hlow
  have h1 : a ^ 2 + c ^ 2 ≤ ‖T‖ ^ 2 := by
    have : ‖T 1‖ ≤ ‖T‖ := by simpa using T.le_opNorm 1
    have h := Complex.sq_norm (T 1)
    rw [Complex.normSq_apply] at h
    nlinarith [norm_nonneg (T 1)]
  have h2 : b ^ 2 + d ^ 2 ≤ ‖T‖ ^ 2 := by
    have : ‖T Complex.I‖ ≤ ‖T‖ := by simpa using T.le_opNorm Complex.I
    have h := Complex.sq_norm (T Complex.I)
    rw [Complex.normSq_apply] at h
    nlinarith [norm_nonneg (T Complex.I)]
  
  
  rw [show 2 * ‖T‖ ^ 2 * (|T.det|⁻¹ * Q) = (2 * ‖T‖ ^ 2 * Q) / |T.det| by field_simp]
  rw [le_div_iff₀ (abs_pos.mpr hT)]
  nlinarith

/-- `|A_{ik}| ≤ 2 ‖T‖² / |det T|`. -/
lemma abs_bzCoef_le (i k : Fin 2) :
    |bzCoef T i k| ≤ 2 * ‖T‖ ^ 2 / |T.det| := by
  set a := (T 1).re
  set b := (T Complex.I).re
  set c := (T 1).im
  set d := (T Complex.I).im
  have h1 : a ^ 2 + c ^ 2 ≤ ‖T‖ ^ 2 := by
    have : ‖T 1‖ ≤ ‖T‖ := by simpa using T.le_opNorm 1
    have h := Complex.sq_norm (T 1)
    rw [Complex.normSq_apply] at h
    nlinarith [norm_nonneg (T 1)]
  have h2 : b ^ 2 + d ^ 2 ≤ ‖T‖ ^ 2 := by
    have : ‖T Complex.I‖ ≤ ‖T‖ := by simpa using T.le_opNorm Complex.I
    have h := Complex.sq_norm (T Complex.I)
    rw [Complex.normSq_apply] at h
    nlinarith [norm_nonneg (T Complex.I)]
  simp [bzCoef, smul_eq_mul, abs_mul, abs_inv, abs_abs]
  rw [inv_mul_eq_div]
  gcongr
  fin_cases i <;> fin_cases k <;>
    simp only [cofMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Fin.zero_eta,
      Fin.mk_one] <;>
    rw [abs_le] <;> constructor <;>
    nlinarith [sq_nonneg (a + b), sq_nonneg (c + d), sq_nonneg (a - b), sq_nonneg (c - d),
      sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg d]

end

lemma bzCoef_id : bzCoef (ContinuousLinearMap.id ℝ ℂ) = 1 := by
  have hdet : (ContinuousLinearMap.id ℝ ℂ).det = 1 := by
    simp [det_eq_of_clm]
  ext i k
  fin_cases i <;> fin_cases k <;> simp [bzCoef, hdet, cofMat]

lemma measurable_bzCoef (i k : Fin 2) : Measurable fun T : ℂ →L[ℝ] ℂ => bzCoef T i k := by
  have hdet : Continuous fun T : ℂ →L[ℝ] ℂ => T.det := by
    simp_rw [det_eq_of_clm]; fun_prop
  have hc : Continuous fun T : ℂ →L[ℝ] ℂ =>
      cofMat (T 1).re (T Complex.I).re (T 1).im (T Complex.I).im i k := by
    fin_cases i <;> fin_cases k <;> simp [cofMat] <;> fun_prop
  exact hdet.measurable.norm.inv.mul hc.measurable

end PolyaNeumann

end
