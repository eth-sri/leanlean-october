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

variable {n : Type*}

/-- The determinant of an entrywise analytic matrix family after subtracting a scalar matrix is
jointly analytic in the parameter and the scalar.  The proof expands the determinant by the
Leibniz formula, so it only uses scalar real analytic operations. -/
theorem analyticAt_sub_scalar_det [Fintype n] [DecidableEq n]
    {A : ℝ → Matrix n n ℝ} {t₀ x₀ : ℝ}
    (hA : ∀ i j, AnalyticAt ℝ (fun t => A t i j) t₀) :
    AnalyticAt ℝ (fun p : ℝ × ℝ => (A p.1 - Matrix.scalar n p.2).det) (t₀, x₀) := by
  simp_rw [Matrix.det_apply']
  have hentryDiff (σ : Equiv.Perm n) (i : n) :
      AnalyticAt ℝ
        (fun p : ℝ × ℝ => A p.1 (σ i) i - if σ i = i then p.2 else 0) (t₀, x₀) := by
    have hentry : AnalyticAt ℝ (fun p : ℝ × ℝ => A p.1 (σ i) i) (t₀, x₀) := AnalyticAt.comp_of_eq (hA (σ i) i) analyticAt_fst rfl
    exact hentry.sub (by
      by_cases h : σ i = i
      · simpa [h] using (analyticAt_snd (𝕜 := ℝ) (p := (t₀, x₀)))
      · simp [h]
        exact analyticAt_const)
  have hprod (σ : Equiv.Perm n) (s : Finset n) :
      AnalyticAt ℝ (fun p : ℝ × ℝ =>
        ∏ i ∈ s, (A p.1 (σ i) i - if σ i = i then p.2 else 0)) (t₀, x₀) := by
    classical
    induction s using Finset.induction with
    | empty => simp [analyticAt_const]
    | @insert i s hi ih =>
      simp only [Finset.prod_insert hi]
      exact (hentryDiff σ i).mul ih
  have hterm (σ : Equiv.Perm n) :
      AnalyticAt ℝ
        (fun p : ℝ × ℝ => (Equiv.Perm.sign σ : ℤ) *
          ∏ i, (A p.1 (σ i) i - if σ i = i then p.2 else 0)) (t₀, x₀) := AnalyticAt.mul analyticAt_const (hprod σ Finset.univ)
  have hsum (s : Finset (Equiv.Perm n)) :
      AnalyticAt ℝ (fun p : ℝ × ℝ =>
        ∑ σ ∈ s, (Equiv.Perm.sign σ : ℤ) *
          ∏ i, (A p.1 (σ i) i - if σ i = i then p.2 else 0)) (t₀, x₀) := by
    classical
    induction s using Finset.induction with
    | empty => simp [analyticAt_const]
    | @insert σ s hσ ih =>
      simp only [Finset.sum_insert hσ]
      exact (hterm σ).add ih
  exact hsum Finset.univ

/-- Joint analyticity of characteristic-polynomial evaluation follows from the scalar Leibniz
expansion of `det (xI - A)`. -/
theorem analyticAt_charpolyEval_of_entries [Fintype n] [DecidableEq n]
    {A : ℝ → Matrix n n ℝ} {t₀ x₀ : ℝ}
    (hA : ∀ i j, AnalyticAt ℝ (fun t => A t i j) t₀) :
    AnalyticAt ℝ (fun p : ℝ × ℝ => (A p.1).charpoly.eval p.2) (t₀, x₀) := by
  have hmul : AnalyticAt ℝ
      (fun p : ℝ × ℝ => (-1) ^ Fintype.card n *
        (A p.1 - Matrix.scalar n p.2).det) (t₀, x₀) :=
    analyticAt_const.mul (analyticAt_sub_scalar_det (A := A) (t₀ := t₀) (x₀ := x₀) hA)
  apply hmul.congr
  filter_upwards with p
  rw [Matrix.eval_charpoly]
  have hmat : Matrix.scalar n p.2 - A p.1 = -(A p.1 - Matrix.scalar n p.2) := by
    simp
  rw [hmat, Matrix.det_neg]

/-- A simple real characteristic root of an entrywise analytic matrix family has a local analytic
branch, unique among nearby roots. Simplicity is expressed by root multiplicity one; its nonzero
polynomial derivative provides the invertible one-dimensional derivative required by the implicit
function theorem. -/
theorem exists_analytic_charpolyRootBranch_of_simple_with_local_uniqueness [Fintype n] [DecidableEq n]
    {A : ℝ → Matrix n n ℝ} {t₀ μ₀ : ℝ}
    (hA : ∀ i j, AnalyticAt ℝ (fun t => A t i j) t₀)
    (hroot : (A t₀).charpoly.eval μ₀ = 0)
    (hsimple : (A t₀).charpoly.rootMultiplicity μ₀ = 1) :
    ∃ branch,
      branch t₀ = μ₀ ∧ AnalyticAt ℝ branch t₀ ∧
      ∃ W, ∃ V,
        IsOpen W ∧ IsOpen V ∧ (t₀, μ₀) ∈ W ∧ t₀ ∈ V ∧
        (∀ t ∈ V, (t, branch t) ∈ W ∧ (A t).charpoly.eval (branch t) = 0) ∧
        (∀ t x, (t, x) ∈ W → (A t).charpoly.eval x = 0 → x = branch t) := by
  have hP := analyticAt_charpolyEval_of_entries (A := A) (t₀ := t₀) (x₀ := μ₀) hA
  have hc : (A t₀).charpoly.derivative.eval μ₀ ≠ 0 := by
    intro hz
    have hdouble : 1 < (A t₀).charpoly.rootMultiplicity μ₀ := by
      apply (Polynomial.one_lt_rootMultiplicity_iff_isRoot ((Matrix.charpoly_monic (A t₀)).ne_zero)).2
      exact ⟨hroot, hz⟩
    omega
  let e : ℝ ≃L[ℝ] ℝ :=
    ContinuousLinearEquiv.smulLeft (Units.mk0 _ hc)
  have hcurve : HasFDerivAt
      (fun x : ℝ => (A t₀).charpoly.eval x)
      ((fderiv ℝ (fun p : ℝ × ℝ => (A p.1).charpoly.eval p.2) (t₀, μ₀)).comp
        (ContinuousLinearMap.inr ℝ ℝ ℝ)) μ₀ := by
    convert (hP.hasStrictFDerivAt.hasFDerivAt.comp μ₀
      (hasFDerivAt_prodMk_right t₀ μ₀)) using 1
    rfl
  have hderivEq := hcurve.unique (((A t₀).charpoly.hasDerivAt μ₀).hasFDerivAt)
  have he : e = ContinuousLinearMap.toSpanSingleton ℝ
      ((A t₀).charpoly.derivative.eval μ₀) := by
    ext
    simp [e]
  obtain ⟨branch, hbranch₀, hbranchAnalytic, W, V, hWopen, hVopen, hWbase, hVbase,
      hbranch, hunique⟩ :=
    exists_analytic_implicitFunction_with_local_uniqueness hP hroot (hderivEq.trans he.symm)
  grind

end PottsDiscontinuity.AnalyticTools
