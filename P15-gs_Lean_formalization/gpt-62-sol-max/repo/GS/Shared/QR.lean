module

public import GS.Shared.Permutation

public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho

public import Mathlib.LinearAlgebra.Matrix.Block

public import Mathlib.LinearAlgebra.Matrix.Reindex

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

set_option maxHeartbeats 1000000

noncomputable section
open Matrix InnerProductSpace
open scoped BigOperators

namespace GS.Shared
variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

theorem supported_blockTriangular {block : Fin n → ℕ} {A : M 𝕜 n}
    (h : CSupported block A) : A.BlockTriangular block :=
  fun _ _ hij => h _ _ (ne_of_gt hij)

theorem upper_blockTriangular {b : ℕ} {A : M 𝕜 n} (h : A.IsUpperTriangular) :
    A.BlockTriangular (fun i : Fin n => i.val / b) :=
  fun i j hij => h (show j < i from lt_of_not_ge fun hle =>
    (not_lt_of_ge (Nat.div_le_div_right hle)) hij)

/-- A unitary matrix upper triangular in block labels is block diagonal. -/
theorem unitary_blockTriangular_supported {block : Fin n → ℕ} {U : M 𝕜 n}
    (hU : Unitary U) (htri : U.BlockTriangular block) : CSupported block U := by
  letI : Invertible U :=
    { invOf := Uᴴ, invOf_mul_self := hU.1, mul_invOf_self := hU.2 }
  have hi : U⁻¹.BlockTriangular block :=
    Matrix.blockTriangular_inv_of_blockTriangular htri
  rw [Matrix.inv_eq_left_inv hU.1] at hi
  intro i j hij
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact star_eq_zero.mp (hi hlt)
  · exact htri hgt

section Ordered
variable {ι : Type*} [Fintype ι] [LinearOrder ι] [LocallyFiniteOrderBot ι]

/-- With independent columns, Gram–Schmidt never leaves the support cell of the current column. -/
private theorem supported_qr (block : ι → ℕ) (A : Matrix ι ι 𝕜) (hA : CSupported block A)
    (hu : IsUnit A) : ∃ V R, CSupported block V ∧ Unitary V ∧ R.IsUpperTriangular ∧ A = V * R := by
  let e₀ := EuclideanSpace.basisFun (ι) 𝕜
  let f (j : ι) : EuclideanSpace 𝕜 (ι) := WithLp.toLp 2 (A.col j)
  have hi : LinearIndependent 𝕜 f :=
    (Matrix.linearIndependent_cols_iff_isUnit.mpr hu).map' ((WithLp.linearEquiv 2 𝕜 _).symm.toLinearMap)
      ((WithLp.linearEquiv 2 𝕜 (ι → 𝕜)).symm.ker)
  let e := gramSchmidtOrthonormalBasis (𝕜 := 𝕜) (by simp) f
  have hf j i (hij : block i ≠ block j) : f j i = 0 := hA i j hij
  have hs (j : ι) : ∀ i, block i ≠ block j → gramSchmidt 𝕜 f j i = 0 := by
    refine wellFounded_lt.induction (C := fun j => ∀ i, block i ≠ block j → gramSchmidt 𝕜 f j i = 0) j ?_
    intro j ih i hij
    rw [gramSchmidt_def]
    simp only [PiLp.sub_apply, WithLp.ofLp_sum, Finset.sum_apply, hf _ _ hij, zero_sub, neg_eq_zero]
    refine Finset.sum_eq_zero fun k hk => ?_
    rw [Submodule.starProjection_singleton, PiLp.smul_apply, smul_eq_mul]
    by_cases hkj : block k = block j
    · grind
    · have hw : ⟪gramSchmidt 𝕜 f k, f j⟫_𝕜 = 0 := by
        rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
        refine Finset.sum_eq_zero fun l _ => ?_
        by_cases hl : block l = block j
        · aesop
        · simp [hf j l hl]
      simp [hw]
  refine ⟨e₀.toBasis.toMatrix e, e.toBasis.toMatrix f, ?_,
    Unitary.of_conjTranspose_mul (Matrix.mem_unitaryGroup_iff'.mp
      (e₀.toMatrix_orthonormalBasis_mem_unitary e)),
    gramSchmidtOrthonormalBasis_inv_isUpperTriangular _ f, ?_⟩
  · intro i j hij
    have hn : gramSchmidtNormed 𝕜 f j ≠ 0 := by
      simp [gramSchmidtNormed, gramSchmidt_ne_zero j hi]
    simp [Module.Basis.toMatrix_apply, e₀, e, gramSchmidtOrthonormalBasis_apply _ hn,
      gramSchmidtNormed, hs _ _ hij]
  · change A = e₀.toBasis.toMatrix (e.toBasis : ι → _) * _
    rw [Module.Basis.toMatrix_mul_toMatrix (b := e₀.toBasis) (b' := e.toBasis)]
    ext i j
    simp [Module.Basis.toMatrix_apply, e₀, f]

theorem structuredQR (block : ι → ℕ) (B : Matrix ι ι 𝕜) (σ : Equiv.Perm ι)
    (hB : CSupported block B) (hBu : IsUnit B) :
    ∃ U R : Matrix ι ι 𝕜, CSupported block U ∧ Unitary U ∧ R.IsUpperTriangular ∧
      B * permMatrix (𝕜 := 𝕜) σ = U * permMatrix (𝕜 := 𝕜) σ * R := by
  let P : Matrix ι ι 𝕜 := permMatrix σ
  have hp : Unitary P := perm_unitary σ
  have hs : CSupported (block ∘ σ) (Pᴴ * B * P) := by
    intro i j hij
    simpa [P] using hB (σ i) (σ j) hij
  obtain ⟨V,R,hVs,hV,hR,he⟩ := supported_qr _ _ hs ((hp.conjTranspose.isUnit.mul hBu).mul hp.isUnit)
  refine ⟨P * V * Pᴴ, R, ?_, (hp.mul hV).mul hp.conjTranspose, hR, ?_⟩
  · intro i j hij
    aesop
  · calc
      B * P = P * (Pᴴ * B * P) := by simp [← Matrix.mul_assoc, hp.2]
      _ = P * V * Pᴴ * P * R := by rw [he]; simp [Matrix.mul_assoc, hp.1]

end Ordered

theorem structuredRQ {n : ℕ} (block : Fin n → ℕ) (B : M 𝕜 n) (σ : Equiv.Perm (Fin n))
    (hB : CSupported block B) (hBu : IsUnit B) :
    ∃ U R : M 𝕜 n, CSupported block U ∧ Unitary U ∧ R.IsUpperTriangular ∧
      permMatrix (𝕜 := 𝕜) σ * B = R * permMatrix (𝕜 := 𝕜) σ * U := by
  obtain ⟨V,T,hV,hoV,ht,he⟩ := structuredQR (ι := (Fin n)ᵒᵈ) block Bᴴ σ.symm hB.conjTranspose
    (show IsUnit Bᴴ from hBu.star)
  refine ⟨Vᴴ,Tᴴ,hV.conjTranspose,hoV.conjTranspose,?_,?_⟩
  · intro i j h
    simpa using ht (i := j) (j := i) h
  · simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, perm_conjTranspose,
      Equiv.symm_symm, ← Matrix.mul_assoc] using congrArg Matrix.conjTranspose he

end GS.Shared
