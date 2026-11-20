module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.RankOne.RightDerivedAction

@[expose] public section

noncomputable section
open scoped BigOperators Classical
namespace DedekindZetaZeroFree.RepresentationTheory.KPSmoothCoreCasimirEnergy.CompactDerivativeTransport
open InfinitesimalAction

open KPCplxIntertwinerEigenvalues MvPolynomial

def polynomialRotation (i : Fin 3) (p : MvPolynomial (Fin 3) ℂ) :=
  X (i + 1) * pderiv (i + 2) p - X (i + 2) * pderiv (i + 1) p

 section

variable (j : Fin 3)

def compactAxis : Fin 3 := ![2, 0, 1] j
 def compactCoefficient : ℂ := ![(Real.sqrt 2 : ℂ), (Real.sqrt 2 : ℂ), -(Real.sqrt 2 : ℂ)] j

def compactPolynomialDerivative (p : MvPolynomial (Fin 3) ℂ) :=
  compactCoefficient j • polynomialRotation (compactAxis j) p

end

open KPCplxPrincipalSeriesCharts KPCplxCharacterHaar

open scoped Matrix.Norms.Operator in
private theorem exp_path_components (g : ComplexGL2) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    ∀ i j, HasDerivAt (fun t : ℝ => ((g : Matrix (Fin 2) (Fin 2) ℂ) * NormedSpace.exp ((t : ℂ) • M)) i j)
      (((g : Matrix (Fin 2) (Fin 2) ℂ) * M) i j) 0 := by
  have h := ((hasDerivAt_exp_smul_const M ((0 : ℝ) : ℂ)).hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt 0 Complex.ofRealCLM.hasDerivAt
  have hmat := h.const_mul (g : Matrix (Fin 2) (Fin 2) ℂ)
  simp only [Complex.ofRealCLM_apply, Complex.ofReal_one, ContinuousLinearMap.coe_restrictScalars, ContinuousLinearMap.toSpanSingleton_apply, one_smul, zero_smul, NormedSpace.exp_zero, mul_one, one_mul] at hmat
  intro i j
  have hj := (ContinuousLinearMap.proj j : (Fin 2 → ℂ) →L[ℝ] ℂ).hasFDerivAt.comp_hasDerivAt 0 ((ContinuousLinearMap.proj i : Matrix (Fin 2) (Fin 2) ℂ →L[ℝ] Fin 2 → ℂ).hasFDerivAt.comp_hasDerivAt 0 hmat)
  change HasDerivAt (fun t : ℝ => (g * NormedSpace.exp ((t : ℂ) • M)) i j)
    ((g * (ContinuousLinearMap.restrictScalars ℝ (ContinuousLinearMap.toSpanSingleton ℂ (NormedSpace.exp (((0 : ℝ) : ℂ) • M) * M))) 1) i j) 0 at hj
  simpa using hj

open scoped Matrix.Norms.Elementwise in
private theorem curve_derivative (s : ℝ) (j : Fin 3) (f : PrincipalSeries s)
    (k : ComplexSU2) (c : ℝ → ComplexSU2) (hc : c 0 = k)
    (hd : ∀ a b, HasDerivAt (fun t => (c t : Matrix (Fin 2) (Fin 2) ℂ) a b)
      (((k : Matrix (Fin 2) (Fin 2) ℂ) * compactMatrix j) a b) 0) :
    deriv (fun t => f (complexSU2Embedding (c t))) 0 =
      localDerivative s (true, j) f (complexSU2Embedding k) := by
  have hh := ((((principalSeries_mem_iff s f.val).mp f.property).2).differentiableOn (by simp)).differentiableAt
    ((isOpen_ne.preimage (by fun_prop)).mem_nhds (Matrix.GeneralLinearGroup.det_ne_zero (complexSU2Embedding k)))
  have eq1 : (fun t => f (complexSU2Embedding (c t))) =
      matrixFunction f.val ∘ (fun t => (c t : Matrix (Fin 2) (Fin 2) ℂ)) := by
    funext t
    dsimp only [Function.comp_def]
    unfold matrixFunction
    rw [dif_pos (show (c t : Matrix (Fin 2) (Fin 2) ℂ).det ≠ 0 from by rw [(Matrix.mem_specialUnitaryGroup_iff.mp (c t).property).2]; exact one_ne_zero)]
    rfl
  have eq2 : (fun t : ℝ => f (complexSU2Embedding k * KPSmoothActualFlowData.matrixExponential ((t : ℂ) • compactMatrix j))) =
      matrixFunction f.val ∘ (fun t : ℝ => ((complexSU2Embedding k : ComplexGL2) : Matrix (Fin 2) (Fin 2) ℂ) * NormedSpace.exp ((t : ℂ) • compactMatrix j)) := by
    funext t
    have he : ((complexSU2Embedding k * KPSmoothActualFlowData.matrixExponential ((t : ℂ) • compactMatrix j)) : Matrix (Fin 2) (Fin 2) ℂ) =
        ((complexSU2Embedding k : ComplexGL2) : Matrix (Fin 2) (Fin 2) ℂ) * NormedSpace.exp ((t : ℂ) • compactMatrix j) := by congr 1
    dsimp only [Function.comp_def]
    rw [← he]
    unfold matrixFunction
    rw [dif_pos (show (((complexSU2Embedding k : ComplexGL2) : Matrix (Fin 2) (Fin 2) ℂ) *
      (KPSmoothActualFlowData.matrixExponential ((t : ℂ) • compactMatrix j) : Matrix (Fin 2) (Fin 2) ℂ)).det ≠ 0 from by
      simpa using Matrix.GeneralLinearGroup.det_ne_zero (complexSU2Embedding k * KPSmoothActualFlowData.matrixExponential ((t : ℂ) • compactMatrix j)))]
    apply congrArg f.val
    apply Units.ext
    rfl
  change _ = deriv (fun t : ℝ => f (complexSU2Embedding k * KPSmoothActualFlowData.matrixExponential ((t : ℂ) • cartanMatrix (true, j)))) 0
  simp only [cartanMatrix, Bool.true_eq, ↓reduceIte]
  rw [eq1, eq2, (hh.hasFDerivAt.comp_hasDerivAt_of_eq 0
    (hasDerivAt_pi.mpr (fun a => hasDerivAt_pi.mpr (hd a))) (by simp [hc]; rfl)).deriv, (hh.hasFDerivAt.comp_hasDerivAt_of_eq 0
    (hasDerivAt_pi.mpr (fun a => hasDerivAt_pi.mpr (exp_path_components (complexSU2Embedding k) (compactMatrix j) a))) (by simp)).deriv]
  rfl

private theorem polynomial_eval_curve (j : Fin 3) (p : MvPolynomial (Fin 3) ℂ)
    (k : ComplexSU2) (c : ℝ → ComplexSU2) (hc : c 0 = k)
    (hd : ∀ i, HasDerivAt (fun t => compactSphereCoordinate (c t) i)
      (MvPolynomial.eval (compactSphereCoordinate k) (compactPolynomialDerivative j (MvPolynomial.X i))) 0) :
    HasDerivAt (fun t => MvPolynomial.eval (compactSphereCoordinate (c t)) p)
      (MvPolynomial.eval (compactSphereCoordinate k) (compactPolynomialDerivative j p)) 0 := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa [compactPolynomialDerivative, polynomialRotation] using hasDerivAt_const (0 : ℝ) a
  | add p q hp hq =>
    convert hp.add hq using 1
    · simp only [map_add]; rfl
    · simp [compactPolynomialDerivative, polynomialRotation, mul_add, mul_sub, sub_mul, smul_add]
      ring
  | mul_X p i hp =>
    convert hp.mul (hd i) using 1
    · simp only [map_mul, MvPolynomial.eval_X]; rfl
    · simp only [hc, compactPolynomialDerivative, polynomialRotation, MvPolynomial.pderiv_mul,
        MvPolynomial.smul_eq_C_mul, map_mul, map_add, map_sub, MvPolynomial.eval_X, MvPolynomial.eval_C]
      ring

theorem compact_derivative_transport_of_curves (s : ℝ)
    (hcurve : ∀ (j : Fin 3) (k : ComplexSU2), ∃ c : ℝ → ComplexSU2,
      c 0 = k ∧
      (∀ a b, HasDerivAt (fun t => (c t : Matrix (Fin 2) (Fin 2) ℂ) a b)
        (((k : Matrix (Fin 2) (Fin 2) ℂ) * compactMatrix j) a b) 0) ∧
      (∀ i, HasDerivAt (fun t => compactSphereCoordinate (c t) i)
        (MvPolynomial.eval (compactSphereCoordinate k) (compactPolynomialDerivative j (MvPolynomial.X i))) 0))
    (j : Fin 3) (p : MvPolynomial (Fin 3) ℂ) (f : PrincipalSeries s)
    (hpf : compactRestriction s f = polynomialCompactRestriction p) :
    compactRestriction s (localDerivative s (true, j) f) =
      polynomialCompactRestriction (compactPolynomialDerivative j p) := by
  funext k
  obtain ⟨c, hc, hm, hd⟩ := hcurve j k
  have he : (fun t => f (complexSU2Embedding (c t))) =
      (fun t => MvPolynomial.eval (compactSphereCoordinate (c t)) p) := by
    funext t
    exact congrFun hpf (c t)
  change localDerivative s (true, j) f (complexSU2Embedding k) = _
  rw [← curve_derivative s j f k c hc hm, he, (polynomial_eval_curve j p k c hc hd).deriv]
  rfl

section TrigCurves
attribute [-simp] Complex.ofReal_cos Complex.ofReal_sin
 variable (j : Fin 3)

def trigMatrix (t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  let a : ℂ := Real.cos (t / Real.sqrt 2)
  let b : ℂ := Real.sin (t / Real.sqrt 2)
  ![!![a + Complex.I*b, 0; 0, a - Complex.I*b],
    !![a, Complex.I*b; Complex.I*b, a], !![a, -b; b, a]] j
 theorem trig_mem (t : ℝ) :
    trigMatrix j t ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  have hs : (Real.cos (t / Real.sqrt 2) : ℂ)^2 + (Real.sin (t / Real.sqrt 2) : ℂ)^2 = 1 := by
    exact_mod_cast Real.cos_sq_add_sin_sq (t / Real.sqrt 2)
  simp only [div_eq_mul_inv] at hs
  rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
  constructor
  · ext a b
    fin_cases j <;> fin_cases a <;> fin_cases b <;>
      simp [trigMatrix, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply,
        Complex.star_def, Matrix.one_apply] <;> ring_nf <;> (try simp) <;> linear_combination hs
  · fin_cases j <;> simp [trigMatrix, Matrix.det_fin_two] <;>
      ring_nf <;> (try simp) <;> linear_combination hs
 def trigSU2 (t : ℝ) : ComplexSU2 := ⟨trigMatrix j t, trig_mem j t⟩
private theorem trig_zero : trigSU2 j 0 = 1 := by
  apply Subtype.ext
  fin_cases j <;> ext a b <;> fin_cases a <;> fin_cases b <;> simp [trigSU2, trigMatrix, Matrix.one_apply]
private theorem trig_derivative :
    ∀ a b, HasDerivAt (fun t => (trigSU2 j t : Matrix (Fin 2) (Fin 2) ℂ) a b)
      (compactMatrix j a b) 0 := by
  have h := (hasDerivAt_id (0 : ℝ)).div_const (Real.sqrt 2)
  have hc := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 h.cos
  have hs := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 h.sin
  simp only [Function.comp_def, Complex.ofRealCLM_apply, id_eq, zero_div, Real.sin_zero, Real.cos_zero, neg_zero, zero_mul, one_mul] at hc hs
  intro a b
  fin_cases j <;> fin_cases a <;> fin_cases b
  all_goals simp only [trigSU2, trigMatrix, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    compactMatrix, noncompactMatrix, Matrix.smul_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  · convert hc.add (hs.const_mul Complex.I) using 1 <;> simp [Complex.I_sq, mul_assoc] <;> (first | rfl | (funext t; simp [mul_comm]) | (ring_nf; simp [Complex.I_sq]))
  · simpa using hasDerivAt_const (0 : ℝ) (0 : ℂ)
  · simpa using hasDerivAt_const (0 : ℝ) (0 : ℂ)
  · convert hc.sub (hs.const_mul Complex.I) using 1 <;> simp [Complex.I_sq, mul_assoc] <;> (first | rfl | (funext t; simp [mul_comm]) | (ring_nf; simp [Complex.I_sq]))
  · simpa using hc
  · convert hs.const_mul Complex.I using 1 <;> simp [Complex.I_sq, mul_assoc] <;> (first | rfl | (funext t; simp [mul_comm]) | (ring_nf; simp [Complex.I_sq]))
  · convert hs.const_mul Complex.I using 1 <;> simp [Complex.I_sq, mul_assoc] <;> (first | rfl | (funext t; simp [mul_comm]) | (ring_nf; simp [Complex.I_sq]))
  · simpa using hc
  · simpa using hc
  · convert hs.neg using 1 <;> simp [Complex.I_sq, mul_assoc] <;> (first | rfl | (funext t; simp [mul_comm]) | (ring_nf; simp [Complex.I_sq]))
  · convert hs using 1 <;> simp [Complex.I_sq, mul_assoc] <;> (first | rfl | (funext t; simp [mul_comm]) | (ring_nf; simp [Complex.I_sq]))
  · simpa using hc

theorem compact_trig_curve_exists (k : ComplexSU2) :
    ∃ c : ℝ → ComplexSU2, c 0 = k ∧
      ∀ a b, HasDerivAt (fun t => (c t : Matrix (Fin 2) (Fin 2) ℂ) a b)
        (((k : Matrix (Fin 2) (Fin 2) ℂ) * compactMatrix j) a b) 0 := by
  refine ⟨fun t => k * trigSU2 j t, by simp [trig_zero], ?_⟩
  intro a b
  let Matrix₀ := Matrix (Fin 2) (Fin 2) ℂ
  change HasDerivAt (fun t => ∑ l : Fin 2, (k : Matrix₀) a l *
    (trigSU2 j t : Matrix₀) l b) _ 0
  simpa [Matrix.mul_apply] using HasDerivAt.fun_sum (u := Finset.univ) (fun l _ => (trig_derivative j l b).const_mul ((k : Matrix₀) a l))

end TrigCurves

theorem hopf_derivative_of_matrix_tangent (j : Fin 3) (k : ComplexSU2)
    (c : ℝ → ComplexSU2) (hc : c 0 = k)
    (hd : ∀ a b, HasDerivAt (fun t => (c t : Matrix (Fin 2) (Fin 2) ℂ) a b)
      (((k : Matrix (Fin 2) (Fin 2) ℂ) * compactMatrix j) a b) 0) :
    ∀ i, HasDerivAt (fun t => compactSphereCoordinate (c t) i)
      (MvPolynomial.eval (compactSphereCoordinate k) (compactPolynomialDerivative j (MvPolynomial.X i))) 0 := by
  have ha := hd 1 0
  have hb := hd 1 1
  have hab := ha.mul hb.star
  have hnorm : ∀ z : ℂ, ‖z‖ ^ 2 = (z * star z).re := by
    intro z
    simp [Complex.mul_re, Complex.sq_norm, Complex.normSq_apply, Complex.star_def]
  intro i
  fin_cases i
  · convert Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 ((Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 hab).const_mul 2) using 1
    · funext t
      simp [compactSphereCoordinate, Function.comp_def, Complex.ofReal_mul, Complex.ofReal_add]
    · fin_cases j <;>
        simp [hc, compactPolynomialDerivative, compactCoefficient, polynomialRotation,
          compactAxis, compactMatrix, noncompactMatrix, Matrix.mul_apply, Fin.sum_univ_two,
          compactSphereCoordinate, hnorm, MvPolynomial.smul_eq_C_mul,
          Complex.star_def, Complex.mul_re, Complex.mul_im] <;>
        push_cast <;> ring
  · convert Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 ((Complex.imCLM.hasFDerivAt.comp_hasDerivAt 0 hab).const_mul 2) using 1
    · funext t
      simp [compactSphereCoordinate, Function.comp_def, Complex.ofReal_mul, Complex.ofReal_add]
    · fin_cases j <;>
        simp [hc, compactPolynomialDerivative, compactCoefficient, polynomialRotation,
          compactAxis, compactMatrix, noncompactMatrix, Matrix.mul_apply, Fin.sum_univ_two,
          compactSphereCoordinate, hnorm, MvPolynomial.smul_eq_C_mul,
          Complex.star_def, Complex.mul_re, Complex.mul_im] <;>
        push_cast <;> ring
  · convert Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 ((Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 (ha.mul ha.star)).sub (Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 (hb.mul hb.star))) using 1
    · funext t
      simp [compactSphereCoordinate, hnorm, Function.comp_def]
    · fin_cases j <;>
        simp [hc, compactPolynomialDerivative, compactCoefficient, polynomialRotation,
          compactAxis, compactMatrix, noncompactMatrix, Matrix.mul_apply, Fin.sum_univ_two,
          compactSphereCoordinate, hnorm, MvPolynomial.smul_eq_C_mul,
          Complex.star_def, Complex.mul_re, Complex.mul_im] <;>
        push_cast <;> ring

end DedekindZetaZeroFree.RepresentationTheory.KPSmoothCoreCasimirEnergy.CompactDerivativeTransport

end
