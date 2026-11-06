module

public import Mathlib
public import Mathlib.Analysis.CStarAlgebra.Matrix
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

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The eigenvector of a real symmetric matrix as an ordinary function. -/
noncomputable def eigenvector (A : Matrix n n ℝ) (hA : A.IsHermitian) (i : n) : n → ℝ :=
  ⇑(hA.eigenvectorBasis i)

private theorem eigenvector_dot (A : Matrix n n ℝ) (hA : A.IsHermitian) (i j : n) :
    eigenvector A hA i ⬝ᵥ eigenvector A hA j = if i = j then 1 else 0 := by
  have h := (orthonormal_iff_ite.mp hA.eigenvectorBasis.orthonormal) i j
  rw [EuclideanSpace.inner_eq_star_dotProduct] at h
  simpa [eigenvector, dotProduct_comm] using h

private theorem mulVec_eigenvector (A : Matrix n n ℝ) (hA : A.IsHermitian) (i : n) :
    A *ᵥ eigenvector A hA i = hA.eigenvalues i • eigenvector A hA i :=
  hA.mulVec_eigenvectorBasis i

private theorem eigenvector_expansion (A : Matrix n n ℝ) (hA : A.IsHermitian) (x : n → ℝ) :
    x = ∑ i, (eigenvector A hA i ⬝ᵥ x) • eigenvector A hA i := by
  have h' := congrArg WithLp.ofLp (hA.eigenvectorBasis.sum_repr' (WithLp.toLp 2 x))
  simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, EuclideanSpace.inner_eq_star_dotProduct,
    star_trivial] at h'
  exact h'.symm.trans (Finset.sum_congr rfl fun i _ => by rw [dotProduct_comm]; rfl)

private theorem dotProduct_self_eq_sum (A : Matrix n n ℝ) (hA : A.IsHermitian) (x : n → ℝ) :
    x ⬝ᵥ x = ∑ i, (eigenvector A hA i ⬝ᵥ x) ^ 2 := by
  conv_lhs => rhs; rw [eigenvector_expansion A hA x]
  rw [dotProduct_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [dotProduct_smul, dotProduct_comm (eigenvector A hA i) x]; simp [pow_two]

private theorem dotProduct_mulVec_eq_sum (A : Matrix n n ℝ) (hA : A.IsHermitian)
    (x : n → ℝ) :
    x ⬝ᵥ (A *ᵥ x) = ∑ i, hA.eigenvalues i * (eigenvector A hA i ⬝ᵥ x) ^ 2 := by
  conv_lhs => rhs; rw [eigenvector_expansion A hA x]
  rw [mulVec_sum, dotProduct_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mulVec_smul, mulVec_eigenvector, dotProduct_smul, dotProduct_smul,
    dotProduct_comm x (eigenvector A hA i)]
  simp only [smul_eq_mul]; ring

private theorem dotProduct_mulVec_le_of_eigenvalues
    (A : Matrix n n ℝ) (hA : A.IsHermitian) {ρ : ℝ}
    (hρ : ∀ i, hA.eigenvalues i ≤ ρ) (x : n → ℝ) :
    x ⬝ᵥ (A *ᵥ x) ≤ ρ * (x ⬝ᵥ x) := by
  rw [dotProduct_mulVec_eq_sum A hA, dotProduct_self_eq_sum A hA, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => by nlinarith [hρ i, sq_nonneg (eigenvector A hA i ⬝ᵥ x)]

/-- The quadratic form of a matrix is bounded by its L2 operator norm times the squared vector
norm. -/
theorem abs_dotProduct_mulVec_le_opNorm
    (D : Matrix n n ℝ) (x : n → ℝ) :
    |x ⬝ᵥ (D *ᵥ x)| ≤ ‖D‖ * (x ⬝ᵥ x) := by
  let v : EuclideanSpace ℝ n := WithLp.toLp 2 x
  have hvnorm : ‖v‖ ^ 2 = x ⬝ᵥ x := by
    rw [EuclideanSpace.real_norm_sq_eq]; simp [v, dotProduct, pow_two]
  have hinner : ⟪v, Matrix.toEuclideanCLM (𝕜 := ℝ) D v⟫ = x ⬝ᵥ (D *ᵥ x) := by
    simpa [v] using Matrix.inner_toEuclideanCLM (A := D) v v
  have hop : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) D v‖ ≤ ‖D‖ * ‖v‖ := by
    simpa [Matrix.cstar_norm_def] using (Matrix.toEuclideanCLM (𝕜 := ℝ) D).le_opNorm v
  rw [← hinner, ← Real.norm_eq_abs, ← hvnorm]
  exact (norm_inner_le_norm _ _).trans
    ((mul_le_mul_of_nonneg_left hop (norm_nonneg _)).trans_eq (by ring))

/-- A Hermitian matrix has its largest real eigenvalue in its spectrum. -/
theorem largestSpectrum_isGreatest
    {A : Matrix n n ℝ} [Nonempty n] (hA : A.IsHermitian) :
    IsGreatest (spectrum ℝ A) (sSup (spectrum ℝ A)) := by
  have hne : (spectrum ℝ A).Nonempty := by
    rw [hA.spectrum_real_eq_range_eigenvalues]; exact Set.range_nonempty _
  exact ⟨hne.csSup_mem A.finite_real_spectrum,
    fun _ hμ => le_csSup A.finite_real_spectrum.bddAbove hμ⟩

private theorem largestSpectrum_le_add_opNorm
    {A B : Matrix n n ℝ} [Nonempty n]
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    sSup (spectrum ℝ A) ≤ sSup (spectrum ℝ B) + ‖A - B‖ := by
  obtain ⟨iA, hiA⟩ : sSup (spectrum ℝ A) ∈ Set.range hA.eigenvalues := by
    rw [← hA.spectrum_real_eq_range_eigenvalues]; exact (largestSpectrum_isGreatest hA).1
  let xA := eigenvector A hA iA
  have hxA : xA ⬝ᵥ xA = 1 := by simpa [xA] using eigenvector_dot A hA iA iA
  have hquadA : xA ⬝ᵥ (A *ᵥ xA) = sSup (spectrum ℝ A) := by
    rw [mulVec_eigenvector, hiA, dotProduct_smul, hxA]; simp
  have hBquad := dotProduct_mulVec_le_of_eigenvalues B hB
    (fun i => le_csSup B.finite_real_spectrum.bddAbove (hB.eigenvalues_mem_spectrum_real i)) xA
  have hpert := (le_abs_self _).trans (by simpa [hxA] using abs_dotProduct_mulVec_le_opNorm (A - B) xA)
  have hdecomp : xA ⬝ᵥ (A *ᵥ xA) = xA ⬝ᵥ (B *ᵥ xA) + xA ⬝ᵥ ((A - B) *ᵥ xA) := by
    rw [sub_mulVec, dotProduct_sub]; ring
  rw [hxA, mul_one] at hBquad
  linarith

/-- The largest eigenvalue of two real symmetric matrices differs by at most their L2 operator
norm distance. This is the `1`-Lipschitz estimate for the project `pfRoot` definition. -/
theorem largestSpectrum_dist_le_opNorm
    {A B : Matrix n n ℝ} [Nonempty n]
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    dist (sSup (spectrum ℝ A)) (sSup (spectrum ℝ B)) ≤ ‖A - B‖ := by
  have hBA := largestSpectrum_le_add_opNorm hA hB
  have hAB := largestSpectrum_le_add_opNorm hB hA
  rw [norm_sub_rev] at hAB
  rw [Real.dist_eq, abs_le]
  exact ⟨by linarith, by linarith⟩

/-- The largest eigenvalue is continuous in every continuous family of real symmetric matrices. -/
theorem continuousAt_pfRoot_of_hermitian
    {A : ℝ → Matrix n n ℝ} [Nonempty n] {t₀ : ℝ}
    (hAcont : ContinuousAt A t₀)
    (hHerm₀ : (A t₀).IsHermitian)
    (hHerm : ∀ᶠ t in 𝓝 t₀, (A t).IsHermitian) :
    ContinuousAt (fun t => sSup (spectrum ℝ (A t))) t₀ := by
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  filter_upwards [hAcont.eventually (Metric.ball_mem_nhds _ hε), hHerm] with t ht hHermt
  exact (largestSpectrum_dist_le_opNorm hHermt hHerm₀).trans_lt (by simpa [dist_eq_norm] using ht)

/-- Entrywise real analyticity gives continuity of the matrix family and hence continuity of its
largest eigenvalue, whenever the family is real symmetric. -/
theorem continuousAt_pfRoot_of_entrywise_analytic
    {A : ℝ → Matrix n n ℝ} [Nonempty n] {t₀ : ℝ}
    (hA : ∀ i j, AnalyticAt ℝ (fun t => A t i j) t₀)
    (hHerm₀ : (A t₀).IsHermitian)
    (hHerm : ∀ᶠ t in 𝓝 t₀, (A t).IsHermitian) :
    ContinuousAt (fun t => sSup (spectrum ℝ (A t))) t₀ :=
  continuousAt_pfRoot_of_hermitian
    (continuousAt_pi.2 fun i => continuousAt_pi.2 fun j => (hA i j).continuousAt) hHerm₀ hHerm

/-- The largest eigenvalue of an entrywise analytic symmetric family is analytic at any point
where its characteristic root is simple. The largest-eigenvalue expression here is definitionally
the project declaration `PerronFrobenius.pfRoot`; irreducibility supplies the simple-root premise
through the project Perron-Frobenius theorem. -/
theorem analyticAt_pfRoot_of_simple
    {A : ℝ → Matrix n n ℝ} [Nonempty n] {t₀ : ℝ}
    (hA : ∀ i j, AnalyticAt ℝ (fun t => A t i j) t₀)
    (hHerm₀ : (A t₀).IsHermitian)
    (hHerm : ∀ᶠ t in 𝓝 t₀, (A t).IsHermitian)
    (hsimple : (A t₀).charpoly.rootMultiplicity (sSup (spectrum ℝ (A t₀))) = 1) :
    AnalyticAt ℝ (fun t => sSup (spectrum ℝ (A t))) t₀ := by
  have hrootAt (t : ℝ) (hHermt : (A t).IsHermitian) :
      (A t).charpoly.eval (sSup (spectrum ℝ (A t))) = 0 :=
    ((Matrix.mem_spectrum_iff_isRoot_charpoly).1 (largestSpectrum_isGreatest hHermt).1).eq_zero
  obtain ⟨branch, _, hbranchAnalytic, W, _, hWopen, _, hWbase, _, _, hbranchUnique⟩ :=
    exists_analytic_charpolyRootBranch_of_simple_with_local_uniqueness hA (hrootAt t₀ hHerm₀) hsimple
  have hpairW : ∀ᶠ t in 𝓝 t₀, (t, sSup (spectrum ℝ (A t))) ∈ W :=
    (continuousAt_id.prodMk (continuousAt_pfRoot_of_entrywise_analytic hA hHerm₀ hHerm)).preimage_mem_nhds
      (hWopen.mem_nhds hWbase)
  refine hbranchAnalytic.congr ?_
  filter_upwards [hpairW, hHerm] with t htW hHermt
  exact (hbranchUnique t (sSup (spectrum ℝ (A t))) htW (hrootAt t hHermt)).symm

end PottsDiscontinuity.AnalyticTools
