module

public import NearlyMinimax.UniformInverseDerivatives


@[expose] public section

/-! Uniform derivative bounds for the actual inverse polynomials in similarity charts. -/

noncomputable section
namespace NearlyMinimax
open Polynomial
open scoped BigOperators Matrix.Norms.L2Operator
open RoughRegime.Upper RoughRegime.MatrixDeterminant

/-- A similarity to a Hermitian matrix, with controlled norm distortion and spectrum. -/
structure SpectralChart {K n : Type*} [RCLike K] [Fintype n] [DecidableEq n]
    (lo hi χ : ℝ) (A : Matrix n n K) where
  unit : (Matrix n n K)ˣ
  condition : ‖unit.val‖ * ‖(↑unit⁻¹ : Matrix n n K)‖ ≤ χ
  hermitian : (matrixSimilarity unit⁻¹ A).IsHermitian
  spectrum_mem : spectrum ℝ (matrixSimilarity unit⁻¹ A) ⊆ Set.Icc lo hi

section Similarity
variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]


section
variable (Q : (Matrix n n ℂ)ˣ) (A : Matrix n n ℂ)

@[simp] theorem matrixSimilarity_inverse :
    matrixSimilarity Q (matrixSimilarity Q⁻¹ A) = A := by
  simp [matrixSimilarity, Matrix.mul_assoc]

end

section
variable (lo hi : ℝ)

theorem normalizeMatrix_similarity (Q : (Matrix n n ℂ)ˣ) (A : Matrix n n ℂ) :
    normalizeMatrix lo hi (matrixSimilarity Q A) =
      matrixSimilarity Q (normalizeMatrix lo hi A) := by
  simp [normalizeMatrix, map_sub, map_smul]

theorem similar_complex_kernel_coefficient_bound (hlo : 0 < lo) (hlt : lo < hi)
    {A B : Matrix n n ℂ} {χ : ℝ} (hχ : 0 ≤ χ) (c : SpectralChart lo hi χ A)
    (η δ : ℝ) (hη : 0 < η) (hη1 : η < 1) (hδ : 0 ≤ δ)
    (hsmall : 4 * δ * perturbationConstant η ≤ 1)
    (hd : χ * ‖normalizeMatrix lo hi B - normalizeMatrix lo hi A‖ ≤ δ) (k : ℕ) :
    ‖aeval B (kernelCoefficientPolynomial lo hi k)‖ ≤
      (4 * χ) * (intervalRho lo hi / η) ^ k := by
  let Q := c.unit
  have hd' : ‖normalizeMatrix lo hi (matrixSimilarity Q⁻¹ B) -
      normalizeMatrix lo hi (matrixSimilarity Q⁻¹ A)‖ ≤ δ := by
    rw [normalizeMatrix_similarity, normalizeMatrix_similarity, ← map_sub]
    apply (matrixSimilarity_norm_le Q⁻¹ _).trans
    apply (mul_le_mul_of_nonneg_right _ (norm_nonneg _)).trans hd
    simpa only [Q, inv_inv, mul_comm] using c.condition
  have hc := complex_kernel_coefficient_bound lo hi hlo hlt
    (matrixSimilarity Q⁻¹ A) (matrixSimilarity Q⁻¹ B) c.hermitian c.spectrum_mem
    η δ hη hη1 hδ hsmall hd' k
  have he : aeval B (kernelCoefficientPolynomial lo hi k) =
      matrixSimilarity Q (aeval (matrixSimilarity Q⁻¹ B) (kernelCoefficientPolynomial lo hi k)) := by
    rw [← Polynomial.aeval_algHom_apply, matrixSimilarity_inverse]
  rw [he]
  calc
    _ ≤ ‖(Q : Matrix n n ℂ)‖ * ‖(↑Q⁻¹ : Matrix n n ℂ)‖ *
        ‖aeval (matrixSimilarity Q⁻¹ B) (kernelCoefficientPolynomial lo hi k)‖ :=
      matrixSimilarity_norm_le _ _
    _ ≤ χ * (4 * (intervalRho lo hi / η) ^ k) := mul_le_mul c.condition hc (norm_nonneg _) hχ
    _ = _ := by ring

end

end Similarity

/-- The real spectrum of the positive square determines the C⋆ norm. -/
theorem cstar_norm_eq_of_spectrum {A B : Type*} [NormedRing A] [NormedRing B]
    [StarRing A] [StarRing B] [CStarRing A] [CStarRing B] [Nontrivial A] [Nontrivial B]
    [NormedAlgebra ℝ A] [NormedAlgebra ℝ B]
    [IsometricContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
    [IsometricContinuousFunctionalCalculus ℝ B IsSelfAdjoint]
    (a : A) (b : B) (h : spectrum ℝ (star a * a) = spectrum ℝ (star b * b)) : ‖a‖ = ‖b‖ := by
  apply (mul_self_inj_of_nonneg (norm_nonneg _) (norm_nonneg _)).mp
  rw [← CStarRing.norm_star_mul_self, ← CStarRing.norm_star_mul_self]
  have ha := IsometricContinuousFunctionalCalculus.isGreatest_norm_spectrum (𝕜 := ℝ)
    (star a * a) (.star_mul_self a)
  rw [h] at ha
  exact ha.unique (IsometricContinuousFunctionalCalculus.isGreatest_norm_spectrum (𝕜 := ℝ)
    (star b * b) (.star_mul_self b))

section RealCharts
variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-- Real-to-complex matrix extension preserves the genuine operator norm. -/
theorem complexify_matrix_norm (A : Matrix n n ℝ) : ‖A.map Complex.ofReal‖ = ‖A‖ := by
  let φ := ofRealMatrixStarAlgHom (n := n)
  change ‖φ A‖ = ‖A‖
  apply cstar_norm_eq_of_spectrum
  rw [← map_star φ, ← map_mul φ]
  exact complexify_matrix_spectrum _ (Matrix.isHermitian_iff_isSelfAdjoint.mpr (.star_mul_self A))

def complexifyMatrixUnit (Q : (Matrix n n ℝ)ˣ) : (Matrix n n ℂ)ˣ :=
  Units.map Complex.ofRealHom.mapMatrix.toMonoidHom Q

section
variable (Q : (Matrix n n ℝ)ˣ)

@[simp] theorem complexifyMatrixUnit_coe :
    (complexifyMatrixUnit Q : Matrix n n ℂ) = (Q : Matrix n n ℝ).map Complex.ofReal := rfl

@[simp] theorem complexifyMatrixUnit_inv :
    complexifyMatrixUnit Q⁻¹ = (complexifyMatrixUnit Q)⁻¹ := by
  rfl

theorem complexifyMatrixUnit_condition :
    ‖(complexifyMatrixUnit Q : Matrix n n ℂ)‖ * ‖(↑(complexifyMatrixUnit Q)⁻¹ : Matrix n n ℂ)‖ =
      ‖(Q : Matrix n n ℝ)‖ * ‖(↑Q⁻¹ : Matrix n n ℝ)‖ := by
  simp [← complexifyMatrixUnit_inv, complexifyMatrixUnit_coe, complexify_matrix_norm]

theorem complexify_matrix_similarity (A : Matrix n n ℝ) :
    matrixSimilarity (complexifyMatrixUnit Q) (A.map Complex.ofReal) =
      (matrixSimilarity Q A).map Complex.ofReal := by
  change _ * _ * _ = ((Q : Matrix n n ℝ) * A * (↑Q⁻¹ : Matrix n n ℝ)).map Complex.ofReal
  rw [← complexifyMatrixUnit_inv, complexifyMatrixUnit_coe, complexifyMatrixUnit_coe]
  change Complex.ofRealHom.mapMatrix (Q : Matrix n n ℝ) * Complex.ofRealHom.mapMatrix A *
    Complex.ofRealHom.mapMatrix (↑Q⁻¹ : Matrix n n ℝ) =
    Complex.ofRealHom.mapMatrix ((Q : Matrix n n ℝ) * A * (↑Q⁻¹ : Matrix n n ℝ))
  simp

end

def SpectralChart.complexify {lo hi χ : ℝ} {A : Matrix n n ℝ} (c : SpectralChart lo hi χ A) :
    SpectralChart lo hi χ (A.map Complex.ofReal) where
  unit := complexifyMatrixUnit c.unit
  condition := (complexifyMatrixUnit_condition c.unit).trans_le c.condition
  hermitian := by
    rw [← complexifyMatrixUnit_inv, complexify_matrix_similarity]
    exact c.hermitian.map _ (fun x => by simp)
  spectrum_mem := by
    rw [← complexifyMatrixUnit_inv, complexify_matrix_similarity, complexify_matrix_spectrum _ c.hermitian]
    exact c.spectrum_mem

end RealCharts

/-- The same free-moment center conditions over real and complex scalars. -/
structure InverseDerivativeCenter (K : Type*) [RCLike K] (r : ℕ) (lo hi χ L : ℝ) where
  moments : incrementVariables r → K
  normBound : ‖moments‖ ≤ L
  chart (b : Bool) : SpectralChart lo hi χ (incrementCoordinateMatrix r b moments)

def InverseDerivativeCenter.complexify {r : ℕ} [NeZero r] {lo hi χ L : ℝ}
    (c : InverseDerivativeCenter ℝ r lo hi χ L) : InverseDerivativeCenter ℂ r lo hi χ L where
  moments := fun j => (c.moments j : ℂ)
  normBound := (pi_norm_le_iff_of_nonneg ((norm_nonneg _).trans c.normBound)).2 fun j => by
    simpa only [Complex.norm_real] using (norm_le_pi_norm c.moments j).trans c.normBound
  chart b := by
    cases b
    · exact (c.chart false).complexify
    · exact (c.chart true).complexify

section Neighborhood
variable (r : ℕ) [NeZero r]

def similarInverseCoordinateRadius (lo hi η χ : ℝ) : ℝ :=
  min 1 ((4 * perturbationConstant η)⁻¹ /
    (χ * max 1 (|(intervalHalfWidth lo hi)⁻¹| *
      (‖incrementCoordinateCLM r false‖ + ‖incrementCoordinateCLM r true‖))))

section
variable (lo hi η χ : ℝ)

theorem similarInverseCoordinateRadius_pos
    (hη : 0 < η) (hη1 : η < 1) (hχ : 0 < χ) :
    0 < similarInverseCoordinateRadius r lo hi η χ := by
  have hK := perturbationConstant_pos η hη hη1
  apply lt_min <;> positivity

theorem coordinate_similar_perturbation (hχ : 0 < χ)
    (z z₀ : incrementVariables r → ℂ)
    (hz : ‖z - z₀‖ < similarInverseCoordinateRadius r lo hi η χ)
    (F : (incrementVariables r → ℂ) →L[ℂ] Matrix (Fin r) (Fin r) ℂ)
    (hF : ‖F‖ ≤ ‖incrementCoordinateCLM r false‖ + ‖incrementCoordinateCLM r true‖) :
    χ * ‖normalizeMatrix lo hi (F z) - normalizeMatrix lo hi (F z₀)‖ ≤
      (4 * perturbationConstant η)⁻¹ := by
  let D := max 1 (|(intervalHalfWidth lo hi)⁻¹| *
    (‖incrementCoordinateCLM r false‖ + ‖incrementCoordinateCLM r true‖))
  have hD : 0 < D := (zero_lt_one : (0 : ℝ) < 1).trans_le (le_max_left _ _)
  have hz' :=
    hz.le.trans (min_le_right _ _)
  rw [normalizeMatrix_sub, norm_smul, Real.norm_eq_abs, ← map_sub]
  calc
    _ ≤ χ * (|(intervalHalfWidth lo hi)⁻¹| * (‖F‖ * ‖z - z₀‖)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (F.le_opNorm _) (abs_nonneg _)) hχ.le
    _ ≤ (χ * D) * ‖z - z₀‖ := by
      have hc : |(intervalHalfWidth lo hi)⁻¹| * ‖F‖ ≤ D :=
        (mul_le_mul_of_nonneg_left hF (abs_nonneg _)).trans (le_max_right _ _)
      have hh := mul_le_mul_of_nonneg_right hc (mul_nonneg hχ.le (norm_nonneg (z - z₀)))
      nlinarith only [hh]
    _ ≤ _ := by simpa only [mul_comm] using (le_div_iff₀ (mul_pos hχ hD)).mp hz'

end

def similarInverseEnvelope (lo hi q χ : ℝ) : ℝ :=
  |(intervalGeometricMean lo hi ^ (r + 1))⁻¹| *
    ((Fintype.card (Equiv.Perm (Fin r)) : ℝ) * (4 * χ) ^ (r + 1)) *
    ∑' k : ℕ, ((k + 1 : ℕ) : ℝ) ^ (r + 1) * q ^ k

def boundedNumeratorEnvelope (L Y : ℝ) (T : Matrix (Fin r) (Fin r) ℝ) : ℝ :=
  ∑ j : Fin r, (
    polynomialCoordinateBound (rawNumeratorPolynomial r T false j) (L + 1) +
      Y * polynomialCoordinateBound (rawNumeratorPolynomial r T true j) (L + 1))

def similarIncrementEnvelope (lo hi q χ L Y : ℝ) (T : Matrix (Fin r) (Fin r) ℝ) : ℝ :=
  similarInverseEnvelope r lo hi q χ * boundedNumeratorEnvelope r L Y T

theorem similarInverseEnvelope_nonneg (lo hi q χ : ℝ) (hq : 0 ≤ q) (hχ : 0 ≤ χ) :
    0 ≤ similarInverseEnvelope r lo hi q χ := by
  unfold similarInverseEnvelope
  apply mul_nonneg (by positivity)
  positivity

theorem bounded_numerator_complex_bound (L Y : ℝ) (hL : 0 ≤ L) (hY : 0 ≤ Y)
    (T : Matrix (Fin r) (Fin r) ℝ) (y : ℝ) (hy : |y| ≤ Y)
    (z : incrementVariables r → ℂ) (hz : ∀ j, ‖z j‖ ≤ L + 1) (i : Fin r) :
    ‖MvPolynomial.eval₂ Complex.ofRealHom z (numeratorPolynomial r T y i)‖ ≤
      polynomialCoordinateBound (rawNumeratorPolynomial r T false i) (L + 1) +
        Y * polynomialCoordinateBound (rawNumeratorPolynomial r T true i) (L + 1) := by
  simp only [numeratorPolynomial, MvPolynomial.eval₂_sub, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C]
  calc
    _ ≤ ‖MvPolynomial.eval₂ Complex.ofRealHom z (rawNumeratorPolynomial r T false i)‖ +
        ‖Complex.ofRealHom y * MvPolynomial.eval₂ Complex.ofRealHom z (rawNumeratorPolynomial r T true i)‖ :=
      norm_sub_le _ _
    _ ≤ _ := by
      apply add_le_add (polynomial_complex_coordinate_bound _ z _ hz)
      simpa using mul_le_mul hy (polynomial_complex_coordinate_bound _ z _ hz)
              (norm_nonneg _) hY

theorem actual_similar_increment_complex_neighborhood (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi)
    (η : ℝ) (hρη : intervalRho lo hi < η) (hη1 : η < 1)
    (χ : ℝ) (hχ : 0 < χ) (L Y : ℝ) (hL : 0 ≤ L) (hY : 0 ≤ Y)
    (T : Matrix (Fin r) (Fin r) ℝ) (y : ℝ) (hy : |y| ≤ Y)
    (c : InverseDerivativeCenter ℂ r lo hi χ L) (z : incrementVariables r → ℂ)
    (hz : ‖z - c.moments‖ < similarInverseCoordinateRadius r lo hi η χ) (m : ℕ) (i : Fin r) :
    ‖MvPolynomial.eval₂ Complex.ofRealHom z (incrementEntryPolynomial r lo hi T y m i)‖ ≤
      similarIncrementEnvelope r lo hi (intervalRho lo hi / η) χ L Y T := by
  have hρ := intervalRho_pos lo hi hlo hlt
  have hη := hρ.trans hρη
  have hq := div_pos hρ hη
  have hq1 := (div_lt_one hη).mpr hρη
  have hδ : 0 ≤ (4 * perturbationConstant η)⁻¹ :=
    (inv_pos.mpr (mul_pos (by norm_num) (perturbationConstant_pos η hη hη1))).le
  have hsmall : 4 * (4 * perturbationConstant η)⁻¹ * perturbationConstant η ≤ 1 := by
    have hK := ne_of_gt (perturbationConstant_pos η hη hη1)
    field_simp
    norm_num
  have hK (b : Bool) (a j : Fin r) (k : ℕ) :
      ‖PowerSeries.coeff k (kernelSeries lo hi (incrementCoordinateCLM r b z) a j)‖ ≤
        (4 * χ) * (intervalRho lo hi / η) ^ k := by
    have hF : ‖incrementCoordinateCLM r b‖ ≤
        ‖incrementCoordinateCLM r false‖ + ‖incrementCoordinateCLM r true‖ := by
      cases b
      · exact le_add_of_nonneg_right (norm_nonneg _)
      · exact le_add_of_nonneg_left (norm_nonneg _)
    have hd := coordinate_similar_perturbation r lo hi η χ hχ z c.moments hz _ hF
    simp only [kernelSeries, PowerSeries.coeff_mk]
    exact (matrix_entry_norm_le_l2 _ a j).trans
      (similar_complex_kernel_coefficient_bound lo hi hlo hlt hχ.le (c.chart b)
        η _ hη hη1 hδ hsmall (by cases b <;> exact hd) k)
  have hzR : ∀ j, ‖z j‖ ≤ L + 1 := by
    intro j
    apply (norm_le_pi_norm z j).trans
    calc
      ‖z‖ ≤ ‖z - c.moments‖ + ‖c.moments‖ := norm_le_norm_sub_add _ _
      _ ≤ 1 + L := add_le_add (hz.le.trans (min_le_left _ _)) c.normBound
      _ = _ := by ring
  have hI (j : Fin r) :
      ‖MvPolynomial.eval₂ Complex.ofRealHom z
        (MvPolynomial.rename Sum.inl (parentInverseEntryPolynomial lo hi r m i j))‖ ≤
        similarInverseEnvelope r lo hi (intervalRho lo hi / η) χ := by
    rw [MvPolynomial.eval₂_rename, coordinate_parent_valuation,
      parentInverseEntryPolynomial_eval_complex, norm_mul, Complex.norm_real]
    exact (mul_le_mul_of_nonneg_left
      (combined_truncation_uniform_bound _ _ _ (4 * χ) hq hq1 (by positivity) (hK false) (hK true) i j m)
      (abs_nonneg _)).trans_eq (by simp [similarInverseEnvelope, mul_assoc])
  simp only [incrementEntryPolynomial, MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul]
  calc
    _ ≤ ∑ j : Fin r, ‖MvPolynomial.eval₂ Complex.ofRealHom z
        (MvPolynomial.rename Sum.inl (parentInverseEntryPolynomial lo hi r m i j)) *
        MvPolynomial.eval₂ Complex.ofRealHom z (numeratorPolynomial r T y j)‖ := norm_sum_le _ _
    _ ≤ ∑ j : Fin r, similarInverseEnvelope r lo hi (intervalRho lo hi / η) χ *
        (polynomialCoordinateBound (rawNumeratorPolynomial r T false j) (L + 1) +
          Y * polynomialCoordinateBound (rawNumeratorPolynomial r T true j) (L + 1)) := by
      apply Finset.sum_le_sum
      intro j hj
      simpa using mul_le_mul (hI j) (bounded_numerator_complex_bound r L Y hL hY T y hy z hzR j)
              (norm_nonneg _) (similarInverseEnvelope_nonneg r lo hi _ χ hq.le hχ.le)
    _ = _ := by rw [← Finset.mul_sum]; rfl

end Neighborhood

section Derivatives
open RoughRegime.ComplexDerivativeBridge
variable (r : ℕ) [NeZero r]

private theorem norm_reindex_le {V W : Type*} [Fintype V] [Fintype W]
    (z : V → ℂ) (f : W → V) : ‖z ∘ f‖ ≤ ‖z‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg z)).mpr
  intro j
  exact norm_le_pi_norm z (f j)

def inverseDerivativeRate (lo hi η χ : ℝ) : ℝ :=
  Real.exp 1 / similarInverseCoordinateRadius r lo hi η χ

theorem inverseDerivativeRate_pos (lo hi η χ : ℝ) (hη : 0 < η) (hη1 : η < 1) (hχ : 0 < χ) :
    0 < inverseDerivativeRate r lo hi η χ :=
  div_pos (Real.exp_pos _) (similarInverseCoordinateRadius_pos r lo hi η χ hη hη1 hχ)

theorem similarIncrementEnvelope_nonneg (lo hi q χ L Y : ℝ)
    (hq : 0 ≤ q) (hχ : 0 ≤ χ) (hL : 0 ≤ L) (hY : 0 ≤ Y)
    (T : Matrix (Fin r) (Fin r) ℝ) : 0 ≤ similarIncrementEnvelope r lo hi q χ L Y T := by
  unfold similarIncrementEnvelope boundedNumeratorEnvelope
  apply mul_nonneg (similarInverseEnvelope_nonneg r lo hi q χ hq hχ)
  exact Finset.sum_nonneg (fun j hj => add_nonneg
    (polynomialCoordinateBound_nonneg _ _ (by positivity))
    (mul_nonneg hY (polynomialCoordinateBound_nonneg _ _ (by positivity))))

/-- The complete U5 analytic input: every order, the actual complexified polynomials,
and constants independent of truncation degree and the admissible center. -/
theorem paper_inverse_derivative_bound (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi)
    (η : ℝ) (hρη : intervalRho lo hi < η) (hη1 : η < 1)
    (χ : ℝ) (hχ : 0 < χ) (L Y : ℝ) (hL : 0 ≤ L) (hY : 0 ≤ Y)
    (T : Matrix (Fin r) (Fin r) ℝ) (y : ℝ) (hy : |y| ≤ Y)
    (c : InverseDerivativeCenter ℝ r lo hi χ L) (m k : ℕ) (i : Fin r)
    (v : Fin k → Fin (Fintype.card (incrementVariables r)) → ℝ) :
    ‖iteratedFDeriv ℝ k (fun x => MvPolynomial.eval x (incrementFinPolynomial r lo hi T y m i))
      (fun j => c.moments ((Fintype.equivFin (incrementVariables r)).symm j)) v‖ ≤
      similarIncrementEnvelope r lo hi (intervalRho lo hi / η) χ L Y T * (k.factorial : ℝ) *
        inverseDerivativeRate r lo hi η χ ^ k * ∏ j, ‖v j‖ := by
  have hη := (intervalRho_pos lo hi hlo hlt).trans hρη
  let e := Fintype.equivFin (incrementVariables r)
  let u := c.moments ∘ e.symm
  apply real_polynomial_derivative_bound _ u _ _
    (similarInverseCoordinateRadius_pos r lo hi η χ hη hη1 hχ) _ v
  intro z hz
  rw [complexify, MvPolynomial.eval_map, incrementFinPolynomial, MvPolynomial.eval₂_rename]
  apply actual_similar_increment_complex_neighborhood r lo hi hlo hlt η hρη hη1 χ hχ L Y hL hY T y hy
    c.complexify (z ∘ e) _ m i
  have he : z ∘ e - c.complexify.moments = (z - fun j => (u j : ℂ)) ∘ e := by
    ext j
    simp [InverseDerivativeCenter.complexify, u]
  rw [he]
  exact (norm_reindex_le _ e).trans_lt hz

def incrementFinVector (lo hi : ℝ) (T : Matrix (Fin r) (Fin r) ℝ) (y : ℝ) (m : ℕ) :
    (Fin (Fintype.card (incrementVariables r)) → ℝ) → Fin r → ℝ :=
  fun x i => MvPolynomial.eval x (incrementFinPolynomial r lo hi T y m i)

section
variable (lo hi : ℝ)

theorem incrementFinVector_contDiff (T : Matrix (Fin r) (Fin r) ℝ) (y : ℝ) (m : ℕ) :
    ContDiff ℝ ⊤ (incrementFinVector r lo hi T y m) :=
  contDiff_pi.mpr (fun i => RoughRegime.PolynomialDerivatives.polynomial_contDiff _)

/-- Vector-valued derivative endpoint in the fixed finite-coordinate norm. -/
theorem paper_inverse_vector_derivative_bound (hlo : 0 < lo) (hlt : lo < hi)
    (η : ℝ) (hρη : intervalRho lo hi < η) (hη1 : η < 1)
    (χ : ℝ) (hχ : 0 < χ) (L Y : ℝ) (hL : 0 ≤ L) (hY : 0 ≤ Y)
    (T : Matrix (Fin r) (Fin r) ℝ) (y : ℝ) (hy : |y| ≤ Y)
    (c : InverseDerivativeCenter ℝ r lo hi χ L) (m k : ℕ)
    (v : Fin k → Fin (Fintype.card (incrementVariables r)) → ℝ) :
    ‖iteratedFDeriv ℝ k (incrementFinVector r lo hi T y m)
      (fun j => c.moments ((Fintype.equivFin (incrementVariables r)).symm j)) v‖ ≤
      similarIncrementEnvelope r lo hi (intervalRho lo hi / η) χ L Y T * (k.factorial : ℝ) *
        inverseDerivativeRate r lo hi η χ ^ k * ∏ j, ‖v j‖ := by
  have hη := (intervalRho_pos lo hi hlo hlt).trans hρη
  have hM := similarIncrementEnvelope_nonneg r lo hi _ χ L Y
    (div_pos (intervalRho_pos lo hi hlo hlt) hη).le hχ.le hL hY T
  have hRate := inverseDerivativeRate_pos r lo hi η χ hη hη1 hχ
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  have hd := (ContinuousLinearMap.proj i : (Fin r → ℝ) →L[ℝ] ℝ).iteratedFDeriv_comp_left
    (x := fun j => c.moments ((Fintype.equivFin (incrementVariables r)).symm j))
    (incrementFinVector_contDiff r lo hi T y m).contDiffAt (show (k : WithTop ℕ∞) ≤ ⊤ from le_top)
  have he := congrArg (fun D => D v) hd
  change iteratedFDeriv ℝ k (fun x => MvPolynomial.eval x (incrementFinPolynomial r lo hi T y m i))
      (fun j => c.moments ((Fintype.equivFin (incrementVariables r)).symm j)) v =
    (iteratedFDeriv ℝ k (incrementFinVector r lo hi T y m)
      (fun j => c.moments ((Fintype.equivFin (incrementVariables r)).symm j)) v) i at he
  rw [← he]
  apply paper_inverse_derivative_bound <;> assumption

end

end Derivatives
end NearlyMinimax
