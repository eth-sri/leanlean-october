module

public import Mathlib
public import PottsDiscontinuity.LinearAlgebra.SymmetricSpectral
public import PottsDiscontinuity.AnalyticTools.EigenBranch

/-!
# Continuity and analyticity of the largest eigenvalue

The quantity `sSup (spectrum ℝ A)` is the largest eigenvalue for a real symmetric matrix. It is
the defining expression of the project declaration `PerronFrobenius.pfRoot`. The operator norm
controls every Rayleigh quotient, giving its one-Lipschitz estimate. A simple-root branch is then
identified with this continuous largest root by local uniqueness.
-/

public section

open Filter
open Matrix
open scoped Topology Matrix.Norms.L2Operator RealInnerProductSpace

namespace PottsDiscontinuity.AnalyticTools
 
open PerronFrobenius

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem abs_dotProduct_mulVec_le_opNorm (D : Matrix n n ℝ) (x : n → ℝ) :
    |x ⬝ᵥ (D *ᵥ x)| ≤ ‖D‖ * (x ⬝ᵥ x) := by
  let v := WithLp.toLp 2 x
  let f := Matrix.toEuclideanCLM (𝕜 := ℝ) D
  have hv : ‖v‖ ^ 2 = x ⬝ᵥ x := by
    rw [EuclideanSpace.real_norm_sq_eq]; simp [v, dotProduct, pow_two]
  calc
    _ = ‖⟪v, f v⟫‖ := by rw [Real.norm_eq_abs, Matrix.inner_toEuclideanCLM]
    _ ≤ ‖v‖ * ‖f v‖ := norm_inner_le_norm ..
    _ ≤ ‖v‖ * (‖f‖ * ‖v‖) := by gcongr; exact f.le_opNorm v
    _ = _ := by rw [← hv, Matrix.cstar_norm_def]; ring

private theorem pfRoot_sub_le_norm {A B : Matrix n n ℝ} [Nonempty n]
    (hA : A.IsHermitian) (hB : B.IsHermitian) : pfRoot A - pfRoot B ≤ ‖A - B‖ := by
  obtain ⟨i, hi⟩ := exists_eigenvalues_eq_pfRoot hA
  let x := eigvec hA i
  have hx : x ⬝ᵥ x = 1 := by simp [x, eigvec_dot]
  have ha : A *ᵥ x = pfRoot A • x := (mulVec_eigvec hA i).trans (by rw [hi])
  have hb := dotProduct_mulVec_le_pfRoot hB x
  have hd := (abs_le.mp (abs_dotProduct_mulVec_le_opNorm (A - B) x)).2
  rw [sub_mulVec, dotProduct_sub, ha, dotProduct_smul, hx] at hd
  simp only [hx, mul_one, smul_eq_mul] at hd hb
  linarith

/-- The largest eigenvalue is `1`-Lipschitz on real symmetric matrices. -/
theorem largestSpectrum_dist_le_opNorm {A B : Matrix n n ℝ} [Nonempty n]
    (hA : A.IsHermitian) (hB : B.IsHermitian) : dist (pfRoot A) (pfRoot B) ≤ ‖A - B‖ := by
  rw [Real.dist_eq, abs_le]
  have h := pfRoot_sub_le_norm hB hA
  rw [norm_sub_rev] at h
  exact ⟨by linarith, pfRoot_sub_le_norm hA hB⟩

/-- The largest eigenvalue is continuous in every continuous family of real symmetric matrices. -/
theorem continuousAt_pfRoot_of_hermitian
    {A : ℝ → Matrix n n ℝ} [Nonempty n] {t₀ : ℝ}
    (hAcont : ContinuousAt A t₀)
    (hHerm₀ : (A t₀).IsHermitian)
    (hHerm : ∀ᶠ t in 𝓝 t₀, (A t).IsHermitian) :
    ContinuousAt (fun t => pfRoot (A t)) t₀ := by
  apply Metric.tendsto_nhds.2
  intro ε hε
  filter_upwards [hAcont.eventually (Metric.ball_mem_nhds _ hε), hHerm] with t ht hHermt
  have hnorm : ‖A t - A t₀‖ < ε := by
    simpa [dist_eq_norm] using ht
  exact lt_of_le_of_lt (largestSpectrum_dist_le_opNorm hHermt hHerm₀) hnorm

/-- Entrywise real analyticity gives continuity of the matrix family and hence continuity of its
largest eigenvalue, whenever the family is real symmetric. -/
theorem continuousAt_pfRoot_of_entrywise_analytic
    {A : ℝ → Matrix n n ℝ} [Nonempty n] {t₀ : ℝ}
    (hA : ∀ i j, AnalyticAt ℝ (fun t => A t i j) t₀)
    (hHerm₀ : (A t₀).IsHermitian)
    (hHerm : ∀ᶠ t in 𝓝 t₀, (A t).IsHermitian) :
    ContinuousAt (fun t => pfRoot (A t)) t₀ := by
  have hAcont : ContinuousAt A t₀ := by
    apply continuousAt_pi.2
    intro i
    apply continuousAt_pi.2
    fun_prop
  exact continuousAt_pfRoot_of_hermitian hAcont hHerm₀ hHerm

/-- The largest eigenvalue of an entrywise analytic symmetric family is analytic at any point
where its characteristic root is simple. The largest-eigenvalue expression here is definitionally
the project declaration `PerronFrobenius.pfRoot`; irreducibility supplies the simple-root premise
through the project Perron-Frobenius theorem. -/
theorem analyticAt_pfRoot_of_simple
    {A : ℝ → Matrix n n ℝ} [Nonempty n] {t₀ : ℝ}
    (hA : ∀ i j, AnalyticAt ℝ (fun t => A t i j) t₀)
    (hHerm₀ : (A t₀).IsHermitian)
    (hHerm : ∀ᶠ t in 𝓝 t₀, (A t).IsHermitian)
    (hsimple : (A t₀).charpoly.rootMultiplicity (pfRoot (A t₀)) = 1) :
    AnalyticAt ℝ (fun t => pfRoot (A t)) t₀ := by
  have hroot {t} (h : (A t).IsHermitian) : (A t).charpoly.eval (pfRoot (A t)) = 0 :=
    (Matrix.mem_spectrum_iff_isRoot_charpoly.1 (isGreatest_pfRoot h).1).eq_zero
  obtain ⟨branch, -, hanalytic, W, V, hWopen, -, hWbase, -, -, huniq⟩ :=
    exists_analytic_charpolyRootBranch_of_simple_with_local_uniqueness hA (hroot hHerm₀) hsimple
  have hcont := continuousAt_id.prodMk (continuousAt_pfRoot_of_entrywise_analytic hA hHerm₀ hHerm)
  have hpairW := hcont.preimage_mem_nhds (hWopen.mem_nhds hWbase)
  have heq : ∀ᶠ t in 𝓝 t₀, pfRoot (A t) = branch t := by
    filter_upwards [hpairW, hHerm] with t htW hHermt
    exact huniq t _ htW (hroot hHermt)
  exact hanalytic.congr (heq.mono fun t ht => ht.symm)

end PottsDiscontinuity.AnalyticTools
