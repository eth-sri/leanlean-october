module

meta import Batteries.Tactic.Alias
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.RankOne.NormalizedCasimir
public import DedekindZetaZeroFree.RepresentationTheory.RankOne.Harmonics.DerivedActionBandwidth

@[expose] public section

noncomputable section

open MeasureTheory NumberField
open scoped Matrix BigOperators Classical InnerProductSpace

namespace DedekindZetaZeroFree.KPSmoothCoreCasimirEnergy

export KPCplxLoweringCoordinateBoost.Geometry (noncompactMatrix compactMatrix LocalBasis cartanMatrix)

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
          simp [noncompactMatrix, Matrix.star_apply, Matrix.conjTranspose_apply])
      | simp [noncompactMatrix, Matrix.trace, Fin.sum_univ_two]
    · intro j
      fin_cases j <;> constructor
      all_goals try (simp [compactMatrix, noncompactMatrix, Matrix.trace, Fin.sum_univ_two])
      all_goals ext i k; fin_cases i <;> fin_cases k
      all_goals simp [Matrix.star_apply, Matrix.conjTranspose_apply]
  have h2 : (∀ i j, (Matrix.trace (noncompactMatrix i * noncompactMatrix j)).re =
      if i = j then 1 else 0) ∧
    (∀ i j, -(Matrix.trace (compactMatrix i * compactMatrix j)).re =
      if i = j then 1 else 0) ∧
    (∀ i j, (Matrix.trace (noncompactMatrix i * compactMatrix j)).re = 0) := by
    have hs : Real.sqrt 2 ≠ 0 := by positivity
    have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
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
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
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
  all_goals simp [Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_three,
    cartanMatrix, compactMatrix, noncompactMatrix, Complex.mul_re, Complex.mul_im,
    Complex.inv_re, Complex.inv_im, Complex.normSq, hs]
  all_goals field_simp
  all_goals ring_nf
  all_goals simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  all_goals have hr := congrArg Complex.re htr
  all_goals have hi := congrArg Complex.im htr
  all_goals simp only [Complex.add_re, Complex.add_im, Complex.zero_re, Complex.zero_im] at hr hi
  all_goals nlinarith [hs2]

export RepresentationTheory.KPSmoothCoreCasimirEnergy.InfinitesimalAction (localDerivative)
export KPCplxHarmonicExtraction.CasimirTransfer.Transfer (matrix_path_hasDeriv_components local_derivative_mem)

theorem localDerivative_add (s : ℝ) (b : LocalBasis)
    (f h : KPCplxPrincipalSeriesCharts.PrincipalSeries s) :
    localDerivative s b (f + h) = localDerivative s b f + localDerivative s b h :=
  map_add (RepresentationTheory.KPSmoothCoreCasimirEnergy.InfinitesimalAction.rightDerivativeLinear s (cartanMatrix b)) f h

def localHC (s : ℝ) : Submodule ℂ (KPCplxPrincipalSeriesCharts.PrincipalSeries s) :=
  ⨆ ℓ : ℕ, KPCplxIntertwinerEigenvalues.harmonicKType s ℓ

theorem local_derivative_harmonic_band (s : ℝ) (b : LocalBasis) (ℓ : ℕ)
    (f : KPCplxPrincipalSeriesCharts.PrincipalSeries s)
    (hf : f ∈ KPCplxIntertwinerEigenvalues.harmonicKType s ℓ) :
    localDerivative s b f ∈
      (Finset.range (ℓ + 2)).sup (KPCplxIntertwinerEigenvalues.harmonicKType s) :=
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
    exact Submodule.zero_mem _
  · intro x y hx hy
    rw [localDerivative_add]
    exact Submodule.add_mem _ hx hy










end DedekindZetaZeroFree.KPSmoothCoreCasimirEnergy

end
