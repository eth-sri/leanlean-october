module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Complex.OrbitDifferentiation

@[expose] public section

namespace DedekindZetaZeroFree.KPCplxHarmonicPropagation

open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts KPCplxIntertwinerEigenvalues

open Filter Topology
open scoped Matrix.Norms.Elementwise



namespace RaisingCalculation
open MvPolynomial
open scoped Matrix Matrix.Norms.Elementwise

noncomputable def transverse : MvPolynomial (Fin 3) ℂ := X 0 + C Complex.I * X 1
theorem transverse_homogeneous (ℓ : ℕ) :
    (transverse ^ ℓ).IsHomogeneous ℓ := by
  simpa [transverse] using ((isHomogeneous_X ℂ (0 : Fin 3)).add
    ((isHomogeneous_X ℂ (1 : Fin 3)).C_mul Complex.I)).pow ℓ
theorem lap_mul_transverse (p : MvPolynomial (Fin 3) ℂ) :
    polynomialLaplacian (transverse * p) = transverse * polynomialLaplacian p +
      2 * (pderiv 0 p + C Complex.I * pderiv 1 p) := by
  simp [polynomialLaplacian, LinearMap.sum_apply, LinearMap.comp_apply,
    Fin.sum_univ_succ, transverse, pderiv_mul, pderiv_C_mul]
  ring
theorem transverse_direction (ℓ : ℕ) :
    pderiv 0 (transverse ^ ℓ) + C Complex.I * pderiv 1 (transverse ^ ℓ) = 0 := by
  simp only [pderiv_pow]
  simp [transverse, pderiv_C_mul, Pi.single_apply]
  have hI : (C Complex.I : MvPolynomial (Fin 3) ℂ) ^ 2 = -1 := by
    rw [← map_pow]; norm_num
  linear_combination (ℓ : MvPolynomial (Fin 3) ℂ) *
    (X 0 + C Complex.I * X 1) ^ (ℓ - 1) * hI
theorem transverse_harmonic (ℓ : ℕ) : transverse ^ ℓ ∈ harmonicPolynomials ℓ := by
  refine ⟨transverse_homogeneous ℓ, ?_⟩
  change polynomialLaplacian (transverse ^ ℓ) = 0
  induction ℓ with
  | zero => simp [polynomialLaplacian, LinearMap.sum_apply, LinearMap.comp_apply]
  | succ n ih =>
    rw [pow_succ', lap_mul_transverse, ih, transverse_direction]
    simp
theorem lap_mul_height (p : MvPolynomial (Fin 3) ℂ) :
    polynomialLaplacian (X 2 * p) = X 2 * polynomialLaplacian p + 2 * pderiv 2 p := by
  simp [polynomialLaplacian, LinearMap.sum_apply, LinearMap.comp_apply,
    Fin.sum_univ_succ, pderiv_mul]
  ring
theorem height_transverse_harmonic (ℓ : ℕ) :
    X 2 * transverse ^ ℓ ∈ harmonicPolynomials (ℓ + 1) := by
  constructor
  · simpa [Nat.add_comm] using (isHomogeneous_X ℂ (2 : Fin 3)).mul (transverse_homogeneous ℓ)
  · change polynomialLaplacian (X 2 * transverse ^ ℓ) = 0
    rw [lap_mul_height, (transverse_harmonic ℓ).2]
    simp [pderiv_pow, transverse, pderiv_C_mul, Pi.single_apply]

noncomputable def rowB (m : Matrix (Fin 2) (Fin 2) ℂ) : ℝ := ‖m 1 0‖ ^ 2 + ‖m 1 1‖ ^ 2
noncomputable def rowW (m : Matrix (Fin 2) (Fin 2) ℂ) : ℂ := 2 * m 1 0 * star (m 1 1) / (rowB m : ℂ)
theorem rowB_pos (g : ComplexGL2) : 0 < rowB g :=
  KPCplxRotatedKernelEstimates.bottomRowNormSq_pos g
theorem rowW_smooth : ContDiffOn ℝ (⊤ : ℕ∞) rowW {m | m.det ≠ 0} := by
  have h0 : ContDiff ℝ (⊤ : ℕ∞) (fun m : Matrix (Fin 2) (Fin 2) ℂ => m 1 0) := by fun_prop
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun m : Matrix (Fin 2) (Fin 2) ℂ => m 1 1) := by fun_prop
  have hb : ContDiff ℝ (⊤ : ℕ∞) rowB := (h0.norm_sq (𝕜 := ℂ)).add (h1.norm_sq (𝕜 := ℂ))
  unfold rowW
  simp only [div_eq_mul_inv]
  apply ContDiffOn.mul
  · exact ((contDiff_const.mul h0).mul (Complex.conjCLE.contDiff.comp h1)).contDiffOn
  · apply ContDiffOn.inv (Complex.ofRealCLM.contDiff.comp hb |>.contDiffOn)
    intro m hm
    exact Complex.ofReal_ne_zero.mpr (rowB_pos (Matrix.GeneralLinearGroup.mkOfDetNeZero m hm)).ne'
theorem rowW_left (a d : ℂˣ) (b : ℂ) (g : ComplexGL2) :
    rowW (upperTriangular a d b * g) = rowW g := by
  have hup : (upperTriangular a d b : Matrix (Fin 2) (Fin 2) ℂ) = !![(a : ℂ), b; 0, (d : ℂ)] := rfl
  have he : rowB (upperTriangular a d b * g) = ‖(d : ℂ)‖ ^ 2 * rowB g := by
    change rowB ((upperTriangular a d b : Matrix (Fin 2) (Fin 2) ℂ) * (g : Matrix (Fin 2) (Fin 2) ℂ)) = _
    rw [hup]
    simp [rowB, Matrix.mul_apply, Fin.sum_univ_two, norm_mul, mul_pow, mul_add]
  unfold rowW
  rw [he]
  change 2 * ((!![(a : ℂ), b; 0, (d : ℂ)] * (g : Matrix (Fin 2) (Fin 2) ℂ)) 1 0) *
    star ((!![(a : ℂ), b; 0, (d : ℂ)] * (g : Matrix (Fin 2) (Fin 2) ℂ)) 1 1) /
    (‖(d : ℂ)‖ ^ 2 * rowB g : ℝ) = _
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  change 2 * ((0 : ℂ) * (g : Matrix (Fin 2) (Fin 2) ℂ) 0 0 + (d : ℂ) * (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0) *
    star ((0 : ℂ) * (g : Matrix (Fin 2) (Fin 2) ℂ) 0 1 + (d : ℂ) * (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1) / _ = _
  simp only [zero_mul, zero_add, star_mul]
  rw [show 2 * ((d : ℂ) * (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0) * (star ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 1) * star (d : ℂ)) =
    ((d : ℂ) * star (d : ℂ)) * (2 * (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * star ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 1)) by ring]
  simp only [Complex.star_def, Complex.mul_conj']
  push_cast
  exact mul_div_mul_left _ _ (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr d.ne_zero)))
noncomputable def harmonicFunction (s : ℝ) (ℓ : ℕ) (g : ComplexGL2) : ℂ :=
  sphericalSection s g * rowW g ^ ℓ
theorem harmonicFunction_mem (s : ℝ) (ℓ : ℕ) :
    harmonicFunction s ℓ ∈ principalSeriesSubmodule s := by
  apply (principalSeries_mem_iff s _).mpr
  constructor
  · intro a d b g
    have hc := (sphericalSection s).property.1 a d b g
    unfold harmonicFunction
    rw [hc]
    change _ * _ * rowW ((upperTriangular a d b : Matrix (Fin 2) (Fin 2) ℂ) * (g : Matrix (Fin 2) (Fin 2) ℂ)) ^ ℓ = _
    rw [rowW_left]
    ring
  · have hs := ((principalSeries_mem_iff s _).mp (sphericalSection s).property).2
    have hh := hs.mul (rowW_smooth.pow ℓ)
    apply hh.congr
    intro m hm
    change m.det ≠ 0 at hm
    simp only [matrixFunction, dif_pos hm, harmonicFunction]
    rfl
noncomputable def harmonicSection (s : ℝ) (ℓ : ℕ) : PrincipalSeries s :=
  ⟨harmonicFunction s ℓ, harmonicFunction_mem s ℓ⟩

noncomputable def rowZ (m : Matrix (Fin 2) (Fin 2) ℂ) : ℂ := ((‖m 1 0‖ ^ 2 - ‖m 1 1‖ ^ 2 : ℝ) : ℂ) / (rowB m : ℂ)
theorem rowB_compact (k : ComplexSU2) : rowB k = 1 := by
  have hrow := congrArg (fun B : Matrix (Fin 2) (Fin 2) ℂ => (B 1 1).re)
    (Matrix.mem_unitaryGroup_iff.mp (Matrix.mem_specialUnitaryGroup_iff.mp k.property).1)
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply,
    Matrix.one_apply_eq] at hrow
  change (((k : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * (starRingEnd ℂ) ((k : Matrix (Fin 2) (Fin 2) ℂ) 1 0)) +
    ((k : Matrix (Fin 2) (Fin 2) ℂ) 1 1 * (starRingEnd ℂ) ((k : Matrix (Fin 2) (Fin 2) ℂ) 1 1))).re = 1 at hrow
  simpa only [rowB, Complex.mul_conj', Complex.add_re, ← Complex.ofReal_pow,
    Complex.ofReal_re] using hrow
theorem spherical_compact (s : ℝ) (k : ComplexSU2) :
    sphericalSection s (complexSU2Embedding k) = 1 := by
  have hd := (Matrix.mem_specialUnitaryGroup_iff.mp k.property).2
  change (Real.rpow (‖(k : Matrix (Fin 2) (Fin 2) ℂ).det‖ / rowB k) (1 + 2 * s) : ℂ) = 1
  rw [hd, rowB_compact]; simp
theorem rowW_compact (k : ComplexSU2) :
    rowW k = compactSphereCoordinate k 0 + Complex.I * compactSphereCoordinate k 1 := by
  simp only [rowW, rowB_compact, Complex.ofReal_one, div_one, compactSphereCoordinate,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  have hr := Complex.re_add_im ((k : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * star ((k : Matrix (Fin 2) (Fin 2) ℂ) 1 1))
  push_cast
  linear_combination 2 * hr.symm
theorem rowZ_compact (k : ComplexSU2) : rowZ k = compactSphereCoordinate k 2 := by
  simp [rowZ, rowB_compact, compactSphereCoordinate]

theorem harmonicSection_compact (s : ℝ) (ℓ : ℕ) :
    compactRestriction s (harmonicSection s ℓ) = polynomialCompactRestriction (transverse ^ ℓ) := by
  ext k
  change sphericalSection s (complexSU2Embedding k) * rowW k ^ ℓ =
    MvPolynomial.eval (compactSphereCoordinate k) (transverse ^ ℓ)
  rw [spherical_compact, rowW_compact]
  simp [transverse]

theorem harmonicSection_harmonic (s : ℝ) (ℓ : ℕ) :
    harmonicSection s ℓ ∈ harmonicKType s ℓ := by
  exact ⟨transverse ^ ℓ, transverse_harmonic ℓ, (harmonicSection_compact s ℓ).symm⟩

theorem height_harmonic_of_formula (s : ℝ) (ℓ : ℕ) (c : ℂ)
    (v : PrincipalSeries s)
    (hv : ∀ g, v g = c * rowZ g * harmonicSection s ℓ g) :
    v ∈ harmonicKType s (ℓ + 1) := by
  refine ⟨c • (X 2 * transverse ^ ℓ),
    (harmonicPolynomials (ℓ + 1)).smul_mem c (height_transverse_harmonic ℓ), ?_⟩
  ext k
  change MvPolynomial.eval (compactSphereCoordinate k) (c • (X 2 * transverse ^ ℓ)) =
    v (complexSU2Embedding k)
  rw [hv]
  change _ = c * rowZ k * (sphericalSection s (complexSU2Embedding k) * rowW k ^ ℓ)
  rw [spherical_compact, rowZ_compact, rowW_compact]
  simp [transverse, mul_assoc]

theorem height_ne_zero_of_formula (s : ℝ) (ℓ : ℕ) (c : ℂ) (hc : c ≠ 0)
    (v : PrincipalSeries s)
    (hv : ∀ g, v g = c * rowZ g * harmonicSection s ℓ g) : v ≠ 0 := by
  let g : ComplexGL2 := Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, 0; 1, 2] (by
    norm_num [Matrix.det_fin_two])
  have hZ : rowZ g = -(3 / 5 : ℂ) := by
    norm_num [rowZ, rowB, g]
  have hW : rowW g = (4 / 5 : ℂ) := by
    norm_num [rowW, rowB, g]
  have hS : sphericalSection s g ≠ 0 := by
    change (Real.rpow _ (1 + 2 * s) : ℂ) ≠ 0
    apply Complex.ofReal_ne_zero.mpr
    apply ne_of_gt
    apply Real.rpow_pos_of_pos
    apply div_pos
    · exact norm_pos_iff.mpr (Matrix.GeneralLinearGroup.det g).ne_zero
    · exact rowB_pos g
  intro he
  have hz := congrArg (fun f : PrincipalSeries s => f g) he
  change v g = 0 at hz
  rw [hv] at hz
  change c * rowZ g * (sphericalSection s g * rowW g ^ ℓ) = 0 at hz
  rw [hZ, hW] at hz
  exact (mul_ne_zero (mul_ne_zero hc (by norm_num))
    (mul_ne_zero hS (pow_ne_zero ℓ (by norm_num)))) hz

noncomputable def boostUnit (t : ℝ) : ℂˣ := Units.mk0 (Real.exp t : ℂ) (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero t))
noncomputable def boost (t : ℝ) : ComplexGL2 := diagonal (boostUnit t)

theorem boost_zero : boost 0 = 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [boost, diagonal, boostUnit, Matrix.one_apply]
theorem boost_bottom (g : ComplexGL2) (t : ℝ) :
    rowB (g * boost t) = ‖(g : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ^ 2 * Real.exp t ^ 2 + ‖(g : Matrix (Fin 2) (Fin 2) ℂ) 1 1‖ ^ 2 := by
  have hb : (boost t : Matrix (Fin 2) (Fin 2) ℂ) = !![(Real.exp t : ℂ), 0; 0, 1] := rfl
  change rowB ((g : Matrix (Fin 2) (Fin 2) ℂ) * (boost t : Matrix (Fin 2) (Fin 2) ℂ)) = _
  rw [hb]
  simp [rowB, Matrix.mul_apply, Fin.sum_univ_two, norm_mul, mul_pow, le_of_lt (Real.exp_pos t)]
theorem boost_transverse (g : ComplexGL2) (t : ℝ) :
    rowW (g * boost t) =
      (2 * (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * star ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 1)) * (Real.exp t : ℂ) / (rowB (g * boost t) : ℂ) := by
  have hb : (boost t : Matrix (Fin 2) (Fin 2) ℂ) = !![(Real.exp t : ℂ), 0; 0, 1] := rfl
  unfold rowW
  change 2 * (((g : Matrix (Fin 2) (Fin 2) ℂ) * (boost t : Matrix (Fin 2) (Fin 2) ℂ)) 1 0) *
    star (((g : Matrix (Fin 2) (Fin 2) ℂ) * (boost t : Matrix (Fin 2) (Fin 2) ℂ)) 1 1) / _ = _
  rw [hb]
  simp [Matrix.mul_apply, Fin.sum_univ_two, mul_assoc, mul_comm, mul_left_comm]
theorem boost_det_norm (g : ComplexGL2) (t : ℝ) :
    ‖((Matrix.GeneralLinearGroup.det (g * boost t) : ℂˣ) : ℂ)‖ =
      ‖((Matrix.GeneralLinearGroup.det g : ℂˣ) : ℂ)‖ * Real.exp t := by
  simp [map_mul, boost, diagonal, boostUnit, Matrix.det_fin_two, norm_mul, le_of_lt (Real.exp_pos t)]
theorem boost_bottom_hasDerivAt (g : ComplexGL2) :
    HasDerivAt (fun t : ℝ => rowB (g * boost t)) (2 * ‖(g : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ^ 2) 0 := by
  simp_rw [boost_bottom]
  convert ((Real.hasDerivAt_exp (0 : ℝ)).pow 2).const_mul (‖(g : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ^ 2) |>.add_const
    (‖(g : Matrix (Fin 2) (Fin 2) ℂ) 1 1‖ ^ 2) using 1 <;> simp <;> ring
theorem boost_transverse_hasDerivAt (g : ComplexGL2) :
    HasDerivAt (fun t : ℝ => rowW (g * boost t)) (-rowZ g * rowW g) 0 := by
  let A := ‖(g : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ^ 2
  let B := rowB g
  let W := 2 * (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * star ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 1)
  have hB : B ≠ 0 := (rowB_pos g).ne'
  have hh := ((Real.hasDerivAt_exp (0 : ℝ)).ofReal_comp.const_mul W).div
    (boost_bottom_hasDerivAt g).ofReal_comp (by simpa [boost_zero] using Complex.ofReal_ne_zero.mpr hB)
  simp only [Real.exp_zero, Complex.ofReal_one, mul_one, boost_zero, mul_one] at hh
  simp_rw [boost_transverse]
  convert hh using 1
  dsimp [rowZ, rowW, W, B, A, rowB]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr hB]
  ring

theorem boost_spherical_hasDerivAt (s : ℝ) (g : ComplexGL2) :
    HasDerivAt (fun t : ℝ => sphericalSection s (g * boost t))
      (-((1 + 2 * s : ℝ) : ℂ) * rowZ g * sphericalSection s g) 0 := by
  let a := ‖((Matrix.GeneralLinearGroup.det g : ℂˣ) : ℂ)‖
  let B := rowB g
  let A := ‖(g : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ^ 2
  let e := 1 + 2 * s
  have ha : 0 < a := norm_pos_iff.mpr (Matrix.GeneralLinearGroup.det g).ne_zero
  have hB : 0 < B := rowB_pos g
  have hz : rowB (g * boost 0) = B := by simp [boost_zero, B]
  have hq := ((Real.hasDerivAt_exp (0 : ℝ)).const_mul a).div
    (boost_bottom_hasDerivAt g) (by rw [hz]; exact hB.ne')
  have hp := hq.rpow_const (p := e) (Or.inl (by change a * Real.exp 0 / rowB (g * boost 0) ≠ 0; rw [hz]; positivity))
  have hh := hp.ofReal_comp
  have he : (fun t : ℝ => sphericalSection s (g * boost t)) =
      fun t : ℝ => (((a * Real.exp t / rowB (g * boost t)) ^ e : ℝ) : ℂ) := by
    funext t
    change (Real.rpow _ _ : ℂ) = _
    rw [boost_det_norm]
    rfl
  rw [he]
  convert hh using 1
  simp only [Real.exp_zero, mul_one, hz, Pi.div_apply]
  change -((e : ℝ) : ℂ) * rowZ g * ((a / B) ^ e : ℝ) = _
  have hepow : (a / B) ^ e = (a / B) ^ (e - 1) * (a / B) := by
    conv_rhs => rhs; rw [← Real.rpow_one (a / B)]
    rw [← Real.rpow_add (div_pos ha hB)]
    congr 1; ring
  rw [hepow]
  dsimp [rowZ, B, A, rowB]
  push_cast
  field_simp
  ring

theorem harmonic_boost_hasDerivAt (s : ℝ) (ℓ : ℕ) (g : ComplexGL2) :
    HasDerivAt (fun t : ℝ => harmonicSection s ℓ (g * boost t))
      (-(((ℓ : ℝ) + 1 + 2 * s : ℝ) : ℂ) * rowZ g * harmonicSection s ℓ g) 0 := by
  have hh := (boost_spherical_hasDerivAt s g).mul ((boost_transverse_hasDerivAt g).pow ℓ)
  simp only [boost_zero, mul_one] at hh
  change HasDerivAt (fun t : ℝ => sphericalSection s (g * boost t) * rowW (g * boost t) ^ ℓ) _ 0
  convert hh using 1
  change -(((ℓ : ℝ) + 1 + 2 * s : ℝ) : ℂ) * rowZ g *
    (sphericalSection s g * rowW g ^ ℓ) = _
  push_cast
  cases ℓ with
  | zero => simp
  | succ n =>
    simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, Pi.pow_apply,
      boost_zero, Units.val_one, Matrix.mul_one, pow_succ]
    ring
theorem rowZ_smooth : ContDiffOn ℝ (⊤ : ℕ∞) rowZ {m | m.det ≠ 0} := by
  have h0 : ContDiff ℝ (⊤ : ℕ∞) (fun m : Matrix (Fin 2) (Fin 2) ℂ => m 1 0) := by fun_prop
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun m : Matrix (Fin 2) (Fin 2) ℂ => m 1 1) := by fun_prop
  have hb : ContDiff ℝ (⊤ : ℕ∞) rowB := (h0.norm_sq (𝕜 := ℂ)).add (h1.norm_sq (𝕜 := ℂ))
  unfold rowZ
  simp only [div_eq_mul_inv]
  apply ContDiffOn.mul
  · exact (Complex.ofRealCLM.contDiff.comp ((h0.norm_sq (𝕜 := ℂ)).sub (h1.norm_sq (𝕜 := ℂ)))).contDiffOn
  · apply ContDiffOn.inv (Complex.ofRealCLM.contDiff.comp hb).contDiffOn
    intro m hm
    exact Complex.ofReal_ne_zero.mpr (rowB_pos (Matrix.GeneralLinearGroup.mkOfDetNeZero m hm)).ne'

theorem rowZ_left (a d : ℂˣ) (b : ℂ) (g : ComplexGL2) :
    rowZ (upperTriangular a d b * g) = rowZ g := by
  have hup : (upperTriangular a d b : Matrix (Fin 2) (Fin 2) ℂ) = !![(a : ℂ), b; 0, (d : ℂ)] := rfl
  change rowZ ((upperTriangular a d b : Matrix (Fin 2) (Fin 2) ℂ) * (g : Matrix (Fin 2) (Fin 2) ℂ)) = _
  rw [hup]
  simp [rowZ, rowB, Matrix.mul_apply, Fin.sum_univ_two, norm_mul, mul_pow]
  push_cast
  have hd : (‖(d : ℂ)‖ ^ 2 : ℂ) ≠ 0 := by
    exact pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr d.ne_zero))
  rw [← mul_sub, ← mul_add, mul_div_mul_left _ _ hd]

noncomputable def raisedSection (s : ℝ) (ℓ : ℕ) : PrincipalSeries s :=
  ⟨fun g => -(((ℓ : ℂ) + 1 + 2 * (s : ℂ))) * rowZ g * harmonicSection s ℓ g, by
    apply (principalSeries_mem_iff s _).mpr
    constructor
    · intro a d b g
      dsimp only
      rw [Matrix.GeneralLinearGroup.coe_mul, rowZ_left,
        (harmonicSection s ℓ).property.1]
      ring
    · have hs := ((principalSeries_mem_iff s _).mp (harmonicSection s ℓ).property).2
      have hh := ((contDiffOn_const (c := -((ℓ : ℂ) + 1 + 2 * (s : ℂ)))).mul rowZ_smooth).mul hs
      apply hh.congr
      intro m hm
      change m.det ≠ 0 at hm
      simp only [matrixFunction, dif_pos hm]
      rfl⟩

end RaisingCalculation

private theorem boost_quotient_tendsto (s : ℝ) (u D : PrincipalSeries s)
    (hd : ∀ g : ComplexGL2, HasDerivAt (fun t : ℝ => u (g * RaisingCalculation.boost t)) (D g) 0) :
    Tendsto (fun t : ℝ => (t⁻¹ : ℂ) • (rightTranslate s (RaisingCalculation.boost t) u - u))
      (𝓝[≠] (0 : ℝ)) (𝓝 D) := by
  apply KPCplxLoweringOrbitDifferentiation.orbit_quotient_tendsto
    s RaisingCalculation.boost _ RaisingCalculation.boost_zero u D hd
  have he : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => (Real.exp t : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp Real.contDiff_exp
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  fin_cases i <;> fin_cases j <;>
    simp [-Complex.ofReal_exp, RaisingCalculation.boost, RaisingCalculation.boostUnit, diagonal] <;>
    fun_prop (disch := assumption)

theorem nonzero_adjacent_raising (s : ℝ) (n : ℕ)
    (hcoeff : ((n : ℂ) + 1 + 2 * (s : ℂ)) ≠ 0)
    (U : Submodule ℂ (PrincipalSeries s))
    (hclosed : IsClosed (U : Set (PrincipalSeries s)))
    (hinv : ∀ (g : ComplexPGL2) (f : PrincipalSeries s), f ∈ U → pi s g f ∈ U)
    (hn : harmonicKType s n ≤ U) :
    ∃ v : PrincipalSeries s, v ∈ U ∧ v ∈ harmonicKType s (n + 1) ∧ v ≠ 0 := by
  let u := RaisingCalculation.harmonicSection s n
  let v := RaisingCalculation.raisedSection s n
  have hv (g : ComplexGL2) : v g = -((n : ℂ) + 1 + 2 * (s : ℂ)) *
      RaisingCalculation.rowZ g * RaisingCalculation.harmonicSection s n g := rfl
  have hder (g : ComplexGL2) : HasDerivAt (fun t : ℝ => u (g * RaisingCalculation.boost t)) (v g) 0 := by
    convert RaisingCalculation.harmonic_boost_hasDerivAt s n g using 1 <;> push_cast
    rfl
  have hu : u ∈ U := hn (RaisingCalculation.harmonicSection_harmonic s n)
  have hlim := boost_quotient_tendsto s u v hder
  have hmem : ∀ t : ℝ, (t⁻¹ : ℂ) • (rightTranslate s (RaisingCalculation.boost t) u - u) ∈ U := by
    intro t
    apply U.smul_mem
    apply U.sub_mem _ hu
    simpa only [pi_mk] using hinv (Matrix.ProjGenLinGroup.mk (RaisingCalculation.boost t)) u hu
  have hvU : v ∈ U := hclosed.mem_of_tendsto hlim (Filter.Eventually.of_forall hmem)
  exact ⟨v, hvU, RaisingCalculation.height_harmonic_of_formula s n _ v hv,
    RaisingCalculation.height_ne_zero_of_formula s n _ (neg_ne_zero.mpr hcoeff) v hv⟩

end DedekindZetaZeroFree.KPCplxHarmonicPropagation
