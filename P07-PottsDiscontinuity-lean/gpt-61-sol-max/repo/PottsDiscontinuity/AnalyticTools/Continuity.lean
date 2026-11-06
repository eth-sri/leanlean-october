module
public import PottsDiscontinuity.LinearAlgebra.SymmetricSpectral

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


open Matrix
open scoped Topology Matrix.Norms.L2Operator RealInnerProductSpace

namespace PottsDiscontinuity.AnalyticTools

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The quadratic form of a matrix is bounded by its L2 operator norm times the squared vector
norm. -/
theorem abs_dotProduct_mulVec_le_opNorm
    (D : Matrix n n ℝ) (x : n → ℝ) :
    |x ⬝ᵥ (D *ᵥ x)| ≤ ‖D‖ *  x ⬝ᵥ x  := by
  let v  := WithLp.toLp 2 x
  have hvnorm : ‖v‖ ^ 2 = x ⬝ᵥ x := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [v, dotProduct, pow_two]
  
  
  
  calc
    |x ⬝ᵥ (D *ᵥ x)| ≤ ‖v‖ * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) D v‖ :=  by
                                                                       calc
                                                                         |x ⬝ᵥ (D *ᵥ x)| = ‖⟪v, Matrix.toEuclideanCLM (𝕜 := ℝ) D v⟫‖ := by
                                                                           rw [ inner_toEuclideanCLM D (WithLp.toLp 2 x) (WithLp.toLp 2 x) , Real.norm_eq_abs]
                                                                         _ ≤ ‖v‖ * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) D v‖ := norm_inner_le_norm _ _ 
    _ ≤ ‖v‖ * (‖D‖ * ‖v‖) := mul_le_mul_of_nonneg_left (by
                                                          simpa [Matrix.cstar_norm_def] using
                                                            (Matrix.toEuclideanCLM (𝕜 := ℝ) D).le_opNorm v) (norm_nonneg _)
    _ = ‖D‖ *  x ⬝ᵥ x  := by rw [← hvnorm]; ring

/-- A Hermitian matrix has its largest real eigenvalue in its spectrum. -/
theorem largestSpectrum_isGreatest
    {A : Matrix n n ℝ} [Nonempty n] (hA : A.IsHermitian) :
    IsGreatest (spectrum ℝ A) (sSup (spectrum ℝ A)) := PerronFrobenius.isGreatest_pfRoot hA

private theorem largestSpectrum_le_add_norm
    {A B : Matrix n n ℝ} [Nonempty n]
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    sSup (spectrum ℝ A) ≤ sSup (spectrum ℝ B) + ‖A - B‖ := by
  obtain ⟨i, hi⟩ := PerronFrobenius.exists_eigenvalues_eq_pfRoot hA
  let x := PerronFrobenius.eigvec hA i
  have hx : x ⬝ᵥ x = 1 := by
    simpa  using PerronFrobenius.eigvec_dot hA i i
  have hq : x ⬝ᵥ  A *ᵥ x  = sSup (spectrum ℝ A) := by
    change _ = PerronFrobenius.pfRoot A
    rw [PerronFrobenius.mulVec_eigvec, dotProduct_smul, hx, smul_eq_mul, mul_one, hi]
  have hb := PerronFrobenius.dotProduct_mulVec_le_pfRoot hB x
  have hpert := abs_dotProduct_mulVec_le_opNorm (A - B) x
  rw [sub_mulVec, dotProduct_sub, hx] at hpert
  rw [hx] at hb
  dsimp [PerronFrobenius.pfRoot] at hb
  linarith [(abs_le.mp hpert).2]

/-- The largest eigenvalue of two real symmetric matrices differs by at most their L2 operator
norm distance. This is the `1`-Lipschitz estimate for the project `pfRoot` definition. -/
theorem largestSpectrum_dist_le_opNorm
    {A B : Matrix n n ℝ} [Nonempty n]
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    dist (sSup (spectrum ℝ A)) (sSup (spectrum ℝ B)) ≤ ‖A - B‖ := by
  have hAB := largestSpectrum_le_add_norm hA hB
  have hBA := largestSpectrum_le_add_norm hB hA
  rw [norm_sub_rev] at hBA
  rw [Real.dist_eq, abs_le]
  constructor <;> linarith

section

variable {A : ℝ → Matrix n n ℝ}
include A

/-- The largest eigenvalue is continuous in every continuous family of real symmetric matrices. -/
theorem continuousAt_pfRoot_of_hermitian
     [Nonempty n] {t₀ : ℝ}
    (hAcont : ContinuousAt A t₀)
    (hHerm₀ : (A t₀).IsHermitian)
    (hHerm : ∀ᶠ t in 𝓝 t₀, (A t).IsHermitian) :
    ContinuousAt (fun t => sSup (spectrum ℝ (A t))) t₀ := by
  apply Metric.tendsto_nhds.2
  intro ε hε
  filter_upwards [hAcont.eventually (Metric.ball_mem_nhds _ hε), hHerm] with t ht hHermt
  
  exact lt_of_le_of_lt (largestSpectrum_dist_le_opNorm hHermt hHerm₀) (by
                                                                         simpa [dist_eq_norm] using ht)

/-- Entrywise real analyticity gives continuity of the matrix family and hence continuity of its
largest eigenvalue, whenever the family is real symmetric. -/
theorem continuousAt_pfRoot_of_entrywise_analytic
     [Nonempty n] {t₀ : ℝ}
    (hA : ∀ i j, AnalyticAt ℝ (fun t => A t i j) t₀)
    (hHerm₀ : (A t₀).IsHermitian)
    (hHerm : ∀ᶠ t in 𝓝 t₀, (A t).IsHermitian) :
    ContinuousAt (fun t => sSup (spectrum ℝ (A t))) t₀ := continuousAt_pfRoot_of_hermitian
                                                            (continuousAt_pi.mpr fun i => continuousAt_pi.mpr fun j => AnalyticAt.continuousAt (hA i j)) hHerm₀ hHerm

/-- The largest eigenvalue of an entrywise analytic symmetric family is analytic at any point
where its characteristic root is simple. The largest-eigenvalue expression here is definitionally
the project declaration `PerronFrobenius.pfRoot`; irreducibility supplies the simple-root premise
through the project Perron-Frobenius theorem. -/
theorem analyticAt_pfRoot_of_simple
     [Nonempty n] {t₀ : ℝ}
    (hA : ∀ i j, AnalyticAt ℝ (fun t => A t i j) t₀)
    (hHerm₀ : (A t₀).IsHermitian)
    (hHerm : ∀ᶠ t in 𝓝 t₀, (A t).IsHermitian)
    (hsimple : (A t₀).charpoly.rootMultiplicity (sSup (spectrum ℝ (A t₀))) = 1) :
    AnalyticAt ℝ (fun t => sSup (spectrum ℝ (A t))) t₀ := by
  
  obtain ⟨branch, hbranch₀, hbranchAnalytic, W, V, hWopen, hVopen, hWbase, hVbase,
      hbranchLocal, hbranchUnique⟩ :=
    exists_analytic_charpolyRootBranch_of_simple_with_local_uniqueness hA (Polynomial.IsRoot.eq_zero (mem_spectrum_iff_isRoot_charpoly.mp (largestSpectrum_isGreatest hHerm₀).left)) hsimple
  
  
  have hpairW  :=
    (continuousAt_id.prodMk (continuousAt_pfRoot_of_entrywise_analytic hA hHerm₀ hHerm)).preimage_mem_nhds (hWopen.mem_nhds hWbase)
  have hrootAt (t : ℝ) (hHermt : (A t).IsHermitian) :
      (A t).charpoly.eval (sSup (spectrum ℝ (A t))) = 0 := Polynomial.IsRoot.eq_zero (mem_spectrum_iff_isRoot_charpoly.mp (largestSpectrum_isGreatest hHermt).left)
  have heq : ∀ᶠ t in 𝓝 t₀, sSup (spectrum ℝ (A t)) = branch t := by
    filter_upwards [hpairW, hHerm] with t htW hHermt
    grind
  exact hbranchAnalytic.congr (heq.mono fun t ht => ht.symm)

end

end PottsDiscontinuity.AnalyticTools
