module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.RankOne.NormalizedCasimir
public import DedekindZetaZeroFree.RepresentationTheory.RankOne.Harmonics.DerivedActionBandwidth

@[expose] public section

noncomputable section

open MeasureTheory NumberField
open scoped Matrix BigOperators Classical InnerProductSpace

namespace DedekindZetaZeroFree.KPSmoothCoreCasimirEnergy

def noncompactMatrix (j : Fin 3) : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / (Real.sqrt 2 : ℂ)) •
    (![!![1, 0; 0, -1], !![0, 1; 1, 0],
      !![0, Complex.I; -Complex.I, 0]] j)

def compactMatrix (j : Fin 3) : Matrix (Fin 2) (Fin 2) ℂ :=
  Complex.I • noncompactMatrix j

abbrev LocalBasis := Bool × Fin 3

def cartanMatrix (b : LocalBasis) : Matrix (Fin 2) (Fin 2) ℂ :=
  if b.1 then compactMatrix b.2 else noncompactMatrix b.2

theorem cartan_basis_normalization :
    (∀ j, star (noncompactMatrix j) = noncompactMatrix j ∧
      Matrix.trace (noncompactMatrix j) = 0) ∧
    (∀ j, star (compactMatrix j) = -compactMatrix j ∧
      Matrix.trace (compactMatrix j) = 0) ∧
    (∀ i j, (Matrix.trace (noncompactMatrix i * noncompactMatrix j)).re =
      if i = j then 1 else 0) ∧
    (∀ i j, -(Matrix.trace (compactMatrix i * compactMatrix j)).re =
      if i = j then 1 else 0) ∧
    (∀ i j, (Matrix.trace (noncompactMatrix i * compactMatrix j)).re = 0) ∧
    ∀ M : Matrix (Fin 2) (Fin 2) ℂ, Matrix.trace M = 0 →
      ∃ x : LocalBasis → ℝ, M = ∑ b, (x b : ℂ) • cartanMatrix b := by
  have h1 : (∀ j, star (noncompactMatrix j) = noncompactMatrix j ∧
    Matrix.trace (noncompactMatrix j) = 0) ∧
    (∀ j, star (compactMatrix j) = -compactMatrix j ∧
    Matrix.trace (compactMatrix j) = 0) := by
    constructor
    · intro j
      fin_cases j <;> constructor
      all_goals first
      | (ext i k; fin_cases i <;> fin_cases k <;>
          simp [noncompactMatrix, Matrix.star_apply])
      | simp [noncompactMatrix, Matrix.trace, Fin.sum_univ_two]
    · intro j
      fin_cases j <;> constructor
      all_goals try (simp [compactMatrix, noncompactMatrix, Matrix.trace, Fin.sum_univ_two])
      all_goals ext i k; fin_cases i <;> fin_cases k
      all_goals simp [Matrix.star_apply]
  have h2 : (∀ i j, (Matrix.trace (noncompactMatrix i * noncompactMatrix j)).re =
      if i = j then 1 else 0) ∧
    (∀ i j, -(Matrix.trace (compactMatrix i * compactMatrix j)).re =
      if i = j then 1 else 0) ∧
    (∀ i j, (Matrix.trace (noncompactMatrix i * compactMatrix j)).re = 0) := by
    have hs : Real.sqrt 2 ≠ 0 := by positivity
    have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := by simp
    refine ⟨?_, ?_, ?_⟩
    all_goals intro i j; fin_cases i <;> fin_cases j
    all_goals norm_num [noncompactMatrix, compactMatrix, Matrix.trace, Matrix.mul_apply,
      Fin.sum_univ_two, Complex.mul_re, Complex.mul_im, Complex.inv_re,
      Complex.inv_im, Complex.normSq, hs]
    all_goals field_simp
    all_goals nlinarith [hs2]
  refine ⟨h1.1, h1.2, h2.1, h2.2.1, h2.2.2, ?_⟩
  intro M hM
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := by simp
  have htr : M 0 0 + M 1 1 = 0 := by simpa [Matrix.trace, Fin.sum_univ_two] using hM
  refine ⟨fun b => if b.1 then
    ![Real.sqrt 2 * (M 0 0).im,
      Real.sqrt 2 / 2 * ((M 0 1).im + (M 1 0).im),
      Real.sqrt 2 / 2 * ((M 1 0).re - (M 0 1).re)] b.2
    else ![Real.sqrt 2 * (M 0 0).re,
      Real.sqrt 2 / 2 * ((M 0 1).re + (M 1 0).re),
      Real.sqrt 2 / 2 * ((M 0 1).im - (M 1 0).im)] b.2, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j
  all_goals apply Complex.ext
  all_goals simp [Fintype.sum_prod_type, Fin.sum_univ_three, cartanMatrix, compactMatrix, noncompactMatrix, Complex.mul_re, Complex.mul_im, Complex.inv_re, Complex.inv_im, Complex.normSq]
  all_goals field_simp
  all_goals ring_nf
  all_goals simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  all_goals have hr := congrArg Complex.re htr
  all_goals have hi := congrArg Complex.im htr
  all_goals simp only [Complex.add_re, Complex.add_im, Complex.zero_re, Complex.zero_im] at hr hi
  all_goals nlinarith [hs2]

open scoped Matrix.Norms.Operator in
private theorem matrix_path_diff (g : KPCplxCharacterHaar.ComplexGL2)
    (M : Matrix (Fin 2) (Fin 2) ℂ) :
    ∀ i j, DifferentiableAt ℝ (fun t : ℝ => ((g : Matrix (Fin 2) (Fin 2) ℂ) * NormedSpace.exp ((t : ℂ) • M)) i j) 0 := by
  fun_prop
open scoped Matrix.Norms.Elementwise in
private theorem local_path_differentiable (s : ℝ) (f : KPCplxPrincipalSeriesCharts.PrincipalSeries s) (g : KPCplxCharacterHaar.ComplexGL2)
    (M : Matrix (Fin 2) (Fin 2) ℂ) :
    DifferentiableAt ℝ (fun t : ℝ => f (g * KPSmoothActualFlowData.matrixExponential ((t : ℂ) • M))) 0 := by
  have hf := ((KPCplxPrincipalSeriesCharts.principalSeries_mem_iff s f.val).mp f.property).2
  have hmat : DifferentiableAt ℝ (fun t : ℝ => (g : Matrix (Fin 2) (Fin 2) ℂ) * NormedSpace.exp ((t : ℂ) • M)) 0 :=
    differentiableAt_pi.mpr (fun i => differentiableAt_pi.mpr (matrix_path_diff g M i))
  have hdet : ((g : Matrix (Fin 2) (Fin 2) ℂ) * NormedSpace.exp (((0 : ℝ) : ℂ) • M)).det ≠ 0 := by
    simpa using Matrix.GeneralLinearGroup.det_ne_zero g
  have hcont : Continuous (fun m : Matrix (Fin 2) (Fin 2) ℂ => m.det) := by fun_prop
  have hh := (hf.differentiableOn (by simp)).differentiableAt
    ((isOpen_ne.preimage hcont).mem_nhds hdet)
  have hc := hh.comp 0 hmat
  convert hc using 1
  funext t
  have hu := Matrix.GeneralLinearGroup.det_ne_zero (g * KPSmoothActualFlowData.matrixExponential ((t : ℂ) • M))
  have he : ((g * KPSmoothActualFlowData.matrixExponential ((t : ℂ) • M)) : Matrix (Fin 2) (Fin 2) ℂ) =
      (g : Matrix (Fin 2) (Fin 2) ℂ) * NormedSpace.exp ((t : ℂ) • M) := by
    congr 1
  dsimp only [Function.comp_def]
  rw [← he]
  unfold KPCplxPrincipalSeriesCharts.matrixFunction
  rw [dif_pos (show ((g : Matrix (Fin 2) (Fin 2) ℂ) *
    (KPSmoothActualFlowData.matrixExponential ((t : ℂ) • M) : Matrix (Fin 2) (Fin 2) ℂ)).det ≠ 0 from by
      simpa only [Units.val_mul] using hu)]
  apply congrArg f.val
  apply Units.ext
  rfl

open scoped Matrix.Norms.Operator in
 theorem matrix_path_hasDeriv_components (g : KPCplxCharacterHaar.ComplexGL2)
    (M : Matrix (Fin 2) (Fin 2) ℂ) :
    ∀ i j, HasDerivAt (fun t : ℝ => ((g : Matrix (Fin 2) (Fin 2) ℂ) * NormedSpace.exp ((t : ℂ) • M)) i j) (((g : Matrix (Fin 2) (Fin 2) ℂ) * M) i j) 0 := by
  have h := ((hasDerivAt_exp_smul_const (𝕂 := ℂ) M ((0 : ℝ) : ℂ)).hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt (f := fun t : ℝ => (t : ℂ)) 0 Complex.ofRealCLM.hasDerivAt
  have hmat := h.const_mul (g : Matrix (Fin 2) (Fin 2) ℂ)
  simp only [Complex.ofRealCLM_apply, Complex.ofReal_one] at hmat
  intro i j
  have hi := (ContinuousLinearMap.proj i : Matrix (Fin 2) (Fin 2) ℂ →L[ℝ] Fin 2 → ℂ).hasFDerivAt.comp_hasDerivAt 0 hmat
  have hj := (ContinuousLinearMap.proj j : (Fin 2 → ℂ) →L[ℝ] ℂ).hasFDerivAt.comp_hasDerivAt 0 hi
  change HasDerivAt (fun t : ℝ => ((g : Matrix (Fin 2) (Fin 2) ℂ) * NormedSpace.exp ((t : ℂ) • M)) i j)
    (((g : Matrix (Fin 2) (Fin 2) ℂ) *
      (ContinuousLinearMap.restrictScalars ℝ (ContinuousLinearMap.toSpanSingleton ℂ (NormedSpace.exp (((0 : ℝ) : ℂ) • M) * M))) 1) i j) 0 at hj
  simpa using hj

open scoped Matrix.Norms.Elementwise in
private theorem raw_derivative_eq (s : ℝ) (f : KPCplxPrincipalSeriesCharts.PrincipalSeries s)
    (g : KPCplxCharacterHaar.ComplexGL2) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    deriv (fun t : ℝ => f (g * KPSmoothActualFlowData.matrixExponential ((t : ℂ) • M))) 0 =
      fderiv ℝ (KPCplxPrincipalSeriesCharts.matrixFunction f.val) (g : Matrix (Fin 2) (Fin 2) ℂ)
        ((g : Matrix (Fin 2) (Fin 2) ℂ) * M) := by
  have hf := ((KPCplxPrincipalSeriesCharts.principalSeries_mem_iff s f.val).mp f.property).2
  have hmat : HasDerivAt (fun t : ℝ => (g : Matrix (Fin 2) (Fin 2) ℂ) * NormedSpace.exp ((t : ℂ) • M))
      ((g : Matrix (Fin 2) (Fin 2) ℂ) * M) 0 :=
    hasDerivAt_pi.mpr (fun i => hasDerivAt_pi.mpr (matrix_path_hasDeriv_components g M i))
  have hcont : Continuous (fun m : Matrix (Fin 2) (Fin 2) ℂ => m.det) := by fun_prop
  have hh := (hf.differentiableOn (by simp)).differentiableAt
    ((isOpen_ne.preimage hcont).mem_nhds (Matrix.GeneralLinearGroup.det_ne_zero g))
  have hc := hh.hasFDerivAt.comp_hasDerivAt_of_eq 0 hmat (by simp)
  have heq : (fun t : ℝ => f (g * KPSmoothActualFlowData.matrixExponential ((t : ℂ) • M))) =
      KPCplxPrincipalSeriesCharts.matrixFunction f.val ∘ (fun t : ℝ => (g : Matrix (Fin 2) (Fin 2) ℂ) * NormedSpace.exp ((t : ℂ) • M)) := by
    funext t
    have hu := Matrix.GeneralLinearGroup.det_ne_zero (g * KPSmoothActualFlowData.matrixExponential ((t : ℂ) • M))
    have he : ((g * KPSmoothActualFlowData.matrixExponential ((t : ℂ) • M)) : Matrix (Fin 2) (Fin 2) ℂ) =
        (g : Matrix (Fin 2) (Fin 2) ℂ) * NormedSpace.exp ((t : ℂ) • M) := by congr 1
    dsimp only [Function.comp_def]
    rw [← he]
    unfold KPCplxPrincipalSeriesCharts.matrixFunction
    rw [dif_pos (show ((g : Matrix (Fin 2) (Fin 2) ℂ) *
      (KPSmoothActualFlowData.matrixExponential ((t : ℂ) • M) : Matrix (Fin 2) (Fin 2) ℂ)).det ≠ 0 from by
        simpa only [Units.val_mul] using hu)]
    apply congrArg f.val
    apply Units.ext
    rfl
  rw [heq]
  exact hc.deriv

open scoped Matrix.Norms.Elementwise in
 theorem local_derivative_mem (s : ℝ) (M : Matrix (Fin 2) (Fin 2) ℂ) (f : KPCplxPrincipalSeriesCharts.PrincipalSeries s) :
    (fun g => deriv (fun t : ℝ => f (g * KPSmoothActualFlowData.matrixExponential ((t : ℂ) • M))) 0) ∈ KPCplxPrincipalSeriesCharts.principalSeriesSubmodule s := by apply DedekindZetaZeroFree.RepresentationTheory.KPSmoothCoreCasimirEnergy.InfinitesimalAction.right_derivative_mem <;> assumption

def localDerivative (s : ℝ) (b : LocalBasis)
    (f : KPCplxPrincipalSeriesCharts.PrincipalSeries s) :
    KPCplxPrincipalSeriesCharts.PrincipalSeries s :=
  ⟨fun g => deriv (fun t : ℝ =>
    f (g * KPSmoothActualFlowData.matrixExponential
      ((t : ℂ) • cartanMatrix b))) 0, local_derivative_mem s (cartanMatrix b) f⟩

theorem localDerivative_raw (s : ℝ) (b : LocalBasis)
    (f : KPCplxPrincipalSeriesCharts.PrincipalSeries s) :
    localDerivative s b f = RepresentationTheory.KPSmoothCoreCasimirEnergy.InfinitesimalAction.localDerivative s b f := by
  rfl

 theorem localDerivative_add (s : ℝ) (b : LocalBasis)
    (f h : KPCplxPrincipalSeriesCharts.PrincipalSeries s) :
    localDerivative s b (f + h) = localDerivative s b f + localDerivative s b h := by
  apply Subtype.ext
  funext g
  exact deriv_add (local_path_differentiable s f g (cartanMatrix b))
    (local_path_differentiable s h g (cartanMatrix b))

def localHC (s : ℝ) : Submodule ℂ (KPCplxPrincipalSeriesCharts.PrincipalSeries s) :=
  ⨆ ℓ : ℕ, KPCplxIntertwinerEigenvalues.harmonicKType s ℓ

theorem local_derivative_harmonic_band (s : ℝ) (b : LocalBasis) (ℓ : ℕ)
    (f : KPCplxPrincipalSeriesCharts.PrincipalSeries s)
    (hf : f ∈ KPCplxIntertwinerEigenvalues.harmonicKType s ℓ) :
    localDerivative s b f ∈
      (Finset.range (ℓ + 2)).sup (KPCplxIntertwinerEigenvalues.harmonicKType s) := by
  simpa only [localDerivative_raw] using
    RepresentationTheory.KPSmoothCoreCasimirEnergy.HarmonicBandDerivatives.derivative_harmonic_band s b ℓ f hf

theorem local_derivative_preserves_HC (s : ℝ) (b : LocalBasis)
    (f : localHC s) : localDerivative s b f.val ∈ localHC s := by
  change localDerivative s b f.val ∈ ⨆ ℓ : ℕ, KPCplxIntertwinerEigenvalues.harmonicKType s ℓ
  apply Submodule.iSup_induction (KPCplxIntertwinerEigenvalues.harmonicKType s)
    (motive := fun x => localDerivative s b x ∈ localHC s) f.property
  · intro ℓ x hx
    exact (Finset.sup_le (fun j _ => le_iSup (KPCplxIntertwinerEigenvalues.harmonicKType s) j))
      (local_derivative_harmonic_band s b ℓ x hx)
  · have hz : localDerivative s b 0 = 0 := by
      apply Subtype.ext
      funext g
      exact deriv_const _ _
    rw [hz]
    simp
  · intro x y hx hy
    rw [localDerivative_add]
    exact Submodule.add_mem _ hx hy

section ActualQuotient

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (μ : KPSmoothActualFlowData.QuotientMeasureData F ζ hζ)

abbrev B := InfinitePlace F × LocalBasis
