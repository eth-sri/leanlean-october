module

public import PottsDiscontinuity.AnalyticTools.Implicit
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# Analytic branches of simple characteristic roots

The analytic implicit function theorem gives a local analytic branch from a jointly analytic
characteristic-polynomial evaluation and an invertible derivative in the spectral variable.
The theorem below keeps both analytic inputs explicit, so it can be applied to real symmetric
matrix families once joint analyticity of their characteristic-polynomial evaluation is supplied.
-/

public section

open Filter
open scoped Topology

namespace PottsDiscontinuity.AnalyticTools

section
variable {n : Type*} [Fintype n] [DecidableEq n] {A : ℝ → Matrix n n ℝ} {t₀ x₀ : ℝ} (hA : ∀ i j, AnalyticAt ℝ (fun t => A t i j) t₀)
include hA
/-- The determinant of an entrywise analytic matrix family after subtracting a scalar matrix is
jointly analytic in the parameter and the scalar.  The proof expands the determinant by the
Leibniz formula, so it only uses scalar real analytic operations. -/
theorem analyticAt_sub_scalar_det
     :
    AnalyticAt ℝ (fun p : ℝ × ℝ => (A p.1 - Matrix.scalar n p.2).det) (t₀, x₀) := by
  simp_rw [Matrix.det_apply']
  have hentryDiff (σ : Equiv.Perm n) (i : n) :
      AnalyticAt ℝ
        (fun p : ℝ × ℝ => A p.1 (σ i) i - if σ i = i then p.2 else 0) (t₀, x₀) := by
    have hentry : AnalyticAt ℝ (fun p : ℝ × ℝ => A p.1 (σ i) i) (t₀, x₀) := by
      have hfst : AnalyticAt ℝ (fun p : ℝ × ℝ => p.1) (t₀, x₀) := analyticAt_fst
      fun_prop
    have hdiag : AnalyticAt ℝ
        (fun p : ℝ × ℝ => if σ i = i then p.2 else 0) (t₀, x₀) := by
      by_cases h : σ i = i
      · simpa [h] using (analyticAt_snd (𝕜 := ℝ) (p := (t₀, x₀)))
      · simp [h]
        fun_prop
    exact hentry.sub hdiag
  have hprod (σ : Equiv.Perm n) (s : Finset n) :
      AnalyticAt ℝ (fun p : ℝ × ℝ =>
        ∏ i ∈ s, (A p.1 (σ i) i - if σ i = i then p.2 else 0)) (t₀, x₀) := by
    fun_prop
  fun_prop

/-- Joint analyticity of characteristic-polynomial evaluation follows from the scalar Leibniz
expansion of `det (xI - A)`. -/
theorem analyticAt_charpolyEval_of_entries
     :
    AnalyticAt ℝ (fun p : ℝ × ℝ => (A p.1).charpoly.eval p.2) (t₀, x₀) := by
  have hmul : AnalyticAt ℝ
      (fun p : ℝ × ℝ => (-1 : ℝ) ^ Fintype.card n *
        (A p.1 - Matrix.scalar n p.2).det) (t₀, x₀) :=
    analyticAt_const.mul (analyticAt_sub_scalar_det hA)
  apply hmul.congr
  filter_upwards with p
  rw [Matrix.eval_charpoly]
  have hmat : Matrix.scalar n p.2 - A p.1 = -(A p.1 - Matrix.scalar n p.2) := by
    simp
  rw [hmat, Matrix.det_neg]
end

/-- A simple real characteristic root of an entrywise analytic matrix family has a local analytic
branch, unique among nearby roots. Simplicity is expressed by root multiplicity one; its nonzero
polynomial derivative provides the invertible one-dimensional derivative required by the implicit
function theorem. -/
theorem exists_analytic_charpolyRootBranch_of_simple_with_local_uniqueness
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : ℝ → Matrix n n ℝ} {t₀ μ₀ : ℝ}
    (hA : ∀ i j, AnalyticAt ℝ (fun t => A t i j) t₀)
    (hroot : (A t₀).charpoly.eval μ₀ = 0)
    (hsimple : (A t₀).charpoly.rootMultiplicity μ₀ = 1) :
    ∃ branch : ℝ → ℝ,
      branch t₀ = μ₀ ∧ AnalyticAt ℝ branch t₀ ∧
      ∃ W : Set (ℝ × ℝ), ∃ V : Set ℝ,
        IsOpen W ∧ IsOpen V ∧ (t₀, μ₀) ∈ W ∧ t₀ ∈ V ∧
        (∀ t ∈ V, (t, branch t) ∈ W ∧ (A t).charpoly.eval (branch t) = 0) ∧
        (∀ t x, (t, x) ∈ W → (A t).charpoly.eval x = 0 → x = branch t) := by
  have hP := analyticAt_charpolyEval_of_entries (x₀ := μ₀) hA
  have hc : (A t₀).charpoly.derivative.eval μ₀ ≠ 0 := by
    intro hz
    have hdouble : 1 < (A t₀).charpoly.rootMultiplicity μ₀ := by
      apply (Polynomial.one_lt_rootMultiplicity_iff_isRoot (by aesop)).2
      simp_all
    omega
  let e : ℝ ≃L[ℝ] ℝ :=
    ContinuousLinearEquiv.smulLeft (Units.mk0 ((A t₀).charpoly.derivative.eval μ₀) hc)
  have hcurve : HasFDerivAt
      (fun x : ℝ => (A t₀).charpoly.eval x)
      ((fderiv ℝ (fun p : ℝ × ℝ => (A p.1).charpoly.eval p.2) (t₀, μ₀)).comp
        (ContinuousLinearMap.inr ℝ ℝ ℝ)) μ₀ := by
    convert ((hP.hasStrictFDerivAt).hasFDerivAt.comp μ₀
      (hasFDerivAt_prodMk_right t₀ μ₀)) using 1
    rfl
  have hderivEq := hcurve.unique (((A t₀).charpoly.hasDerivAt μ₀).hasFDerivAt)
  have he : (e : ℝ →L[ℝ] ℝ) = ContinuousLinearMap.toSpanSingleton ℝ
      ((A t₀).charpoly.derivative.eval μ₀) := by
    aesop
  obtain ⟨branch, hbranch₀, hbranchAnalytic, W, V, hWopen, hVopen, hWbase, hVbase,
      hbranch, hunique⟩ :=
    exists_analytic_implicitFunction_with_local_uniqueness hP hroot e (hderivEq.trans he.symm)
  grind

end PottsDiscontinuity.AnalyticTools
