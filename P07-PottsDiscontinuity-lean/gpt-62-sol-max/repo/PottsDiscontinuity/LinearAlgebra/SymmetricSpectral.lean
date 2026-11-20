module

public import Mathlib

/-!
# Spectral expansions for real symmetric matrices

Helper layer for the Perron-Frobenius theorems of this directory.  For a real symmetric
(`Matrix.IsHermitian`) matrix `A` over a finite index type, we use Mathlib's orthonormal eigenvector
basis `Matrix.IsHermitian.eigenvectorBasis` (viewed as plain functions `ι → ℝ`, `eigvec`) and the
eigenvalues `Matrix.IsHermitian.eigenvalues` to prove

* `expansion`: `x = ∑ i, ⟨b i, x⟩ • b i`;
* `dotProduct_pow_mulVec`: `x ⬝ᵥ A ^ M *ᵥ y = ∑ i, μ i ^ M * (⟨b i, x⟩ * ⟨b i, y⟩)`;
* `trace_pow_eq_sum`: `trace (A ^ M) = ∑ i, μ i ^ M`;
* the Rayleigh bound `x ⬝ᵥ A x ≤ ρ * (x ⬝ᵥ x)` for any upper bound `ρ` of the eigenvalues, and the
  equality case `x ⬝ᵥ A x = ρ * (x ⬝ᵥ x) → A x = ρ x`;
* the largest eigenvalue `pfRoot A = sSup (spectrum ℝ A)` and its basic properties.
-/

@[expose] public section

open Matrix

namespace PottsDiscontinuity.PerronFrobenius

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℝ}

section

variable (hA : A.IsHermitian)

/-- The orthonormal eigenvector basis of a real symmetric matrix, as plain functions `ι → ℝ`. -/
noncomputable def eigvec (i : ι) : ι → ℝ := ⇑(hA.eigenvectorBasis i)

theorem eigvec_dot (i j : ι) :
    eigvec hA i ⬝ᵥ eigvec hA j = if i = j then 1 else 0 := by
  have := hA.eigenvectorBasis.orthonormal
  simp_all [eigvec, dotProduct_comm, EuclideanSpace.inner_eq_star_dotProduct, orthonormal_iff_ite]

theorem mulVec_eigvec (i : ι) :
    A *ᵥ eigvec hA i = hA.eigenvalues i • eigvec hA i :=
  hA.mulVec_eigenvectorBasis i

theorem expansion (x : ι → ℝ) :
    x = ∑ i, (eigvec hA i ⬝ᵥ x) • eigvec hA i := by
  have h := hA.eigenvectorBasis.sum_repr' (WithLp.toLp 2 x)
  have := congrArg WithLp.ofLp h
  simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, EuclideanSpace.inner_eq_star_dotProduct] at this
  simp only [star_trivial] at this
  refine this.symm.trans ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [dotProduct_comm]
  rfl

theorem mulVec_pow_eigvec (M : ℕ) (i : ι) :
    (A ^ M) *ᵥ eigvec hA i = (hA.eigenvalues i) ^ M • eigvec hA i := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [pow_succ', ← mulVec_mulVec, ih, mulVec_smul, mulVec_eigvec, smul_smul, ← pow_succ]

/-- Spectral expansion of the bilinear form `x ⬝ᵥ A ^ M *ᵥ y`. -/
theorem dotProduct_pow_mulVec (M : ℕ) (x y : ι → ℝ) :
    x ⬝ᵥ ((A ^ M) *ᵥ y) =
      ∑ i, hA.eigenvalues i ^ M * ((eigvec hA i ⬝ᵥ x) * (eigvec hA i ⬝ᵥ y)) := by
  have hy := congrArg (fun z => x ⬝ᵥ ((A ^ M) *ᵥ z)) (expansion hA y)
  rw [hy, mulVec_sum, dotProduct_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mulVec_smul, mulVec_pow_eigvec, dotProduct_smul, dotProduct_smul, dotProduct_comm x]
  ring

/-- `trace (A ^ M)` is the sum of the `M`-th powers of the eigenvalues. -/
theorem trace_pow_eq_sum (M : ℕ) :
    (A ^ M).trace = ∑ i, hA.eigenvalues i ^ M := by
  conv_lhs =>
    rw [hA.spectral_theorem, ← map_pow, Unitary.conjStarAlgAut_apply, trace_mul_comm,
      ← mul_assoc]
  simp [diagonal_pow]

theorem dotProduct_self_eq_sum (x : ι → ℝ) :
    x ⬝ᵥ x = ∑ i, (eigvec hA i ⬝ᵥ x) ^ 2 := by
  have h := dotProduct_pow_mulVec hA 0 x x
  simpa [sq] using h

theorem dotProduct_mulVec_eq_sum (x : ι → ℝ) :
    x ⬝ᵥ (A *ᵥ x) = ∑ i, hA.eigenvalues i * (eigvec hA i ⬝ᵥ x) ^ 2 := by
  have h := dotProduct_pow_mulVec hA 1 x x
  grind

end

/-- Rayleigh bound: if `ρ` bounds the eigenvalues above then `x ⬝ᵥ A x ≤ ρ * (x ⬝ᵥ x)`. -/
theorem dotProduct_mulVec_le (hA : A.IsHermitian) {ρ : ℝ} (hρ : ∀ i, hA.eigenvalues i ≤ ρ)
    (x : ι → ℝ) : x ⬝ᵥ (A *ᵥ x) ≤ ρ * (x ⬝ᵥ x) := by
  rw [dotProduct_mulVec_eq_sum hA, dotProduct_self_eq_sum hA, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => by nlinarith [hρ i, sq_nonneg (eigvec hA i ⬝ᵥ x)]

/-- Equality case of the Rayleigh bound: a maximiser of the Rayleigh quotient is an eigenvector. -/
theorem mulVec_eq_of_dotProduct_mulVec_eq (hA : A.IsHermitian) {ρ : ℝ}
    (hρ : ∀ i, hA.eigenvalues i ≤ ρ) (x : ι → ℝ)
    (hx : x ⬝ᵥ (A *ᵥ x) = ρ * (x ⬝ᵥ x)) : A *ᵥ x = ρ • x := by
  have hP : (ρ • (1 : Matrix ι ι ℝ) - A).PosSemidef :=
    .of_dotProduct_mulVec_nonneg ((isHermitian_one.smul (IsSelfAdjoint.all ρ)).sub hA) fun y => by
      simpa [sub_mulVec, smul_mulVec] using
              dotProduct_mulVec_le hA hρ y
  have hz : (ρ • (1 : Matrix ι ι ℝ) - A) *ᵥ x = 0 :=
    hP.dotProduct_mulVec_zero_iff.mp (by simp [sub_mulVec, smul_mulVec, hx])
  simpa [sub_mulVec, smul_mulVec, sub_eq_zero, eq_comm] using hz

/-! ### The largest eigenvalue -/

/-- The largest real eigenvalue (`sSup` of the real spectrum); for a nonnegative irreducible
symmetric matrix this is the Perron-Frobenius eigenvalue. -/
noncomputable def pfRoot (A : Matrix ι ι ℝ) : ℝ := sSup (spectrum ℝ A)

theorem isGreatest_pfRoot [Nonempty ι] (hA : A.IsHermitian) :
    IsGreatest (spectrum ℝ A) (pfRoot A) := by
  have hne : (spectrum ℝ A).Nonempty := by
    rw [hA.spectrum_real_eq_range_eigenvalues]
    exact Set.range_nonempty _
  exact ⟨hne.csSup_mem A.finite_real_spectrum, fun μ hμ => le_csSup A.finite_real_spectrum.bddAbove hμ⟩

theorem eigenvalues_le_pfRoot [Nonempty ι] (hA : A.IsHermitian) (i : ι) :
    hA.eigenvalues i ≤ pfRoot A :=
  (isGreatest_pfRoot hA).2 (hA.eigenvalues_mem_spectrum_real i)

theorem exists_eigenvalues_eq_pfRoot [Nonempty ι] (hA : A.IsHermitian) :
    ∃ i, hA.eigenvalues i = pfRoot A := by
  have := (isGreatest_pfRoot hA).1
  simpa [hA.spectrum_real_eq_range_eigenvalues] using this

theorem dotProduct_mulVec_le_pfRoot [Nonempty ι] (hA : A.IsHermitian) (x : ι → ℝ) :
    x ⬝ᵥ (A *ᵥ x) ≤ pfRoot A * (x ⬝ᵥ x) :=
  dotProduct_mulVec_le hA (eigenvalues_le_pfRoot hA) x

theorem mulVec_eq_pfRoot_smul_of_dotProduct_mulVec_eq [Nonempty ι] (hA : A.IsHermitian)
    (x : ι → ℝ) (hx : x ⬝ᵥ (A *ᵥ x) = pfRoot A * (x ⬝ᵥ x)) : A *ᵥ x = pfRoot A • x :=
  mulVec_eq_of_dotProduct_mulVec_eq hA (eigenvalues_le_pfRoot hA) x hx

end PottsDiscontinuity.PerronFrobenius
