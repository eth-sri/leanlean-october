module
public import BN.Spectral.Variational
public import BN.Definition
@[expose] public section

namespace KKP
open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] [Nontrivial n]

/-- A positive two-dimensional compression is controlled by the two largest eigenvalues. -/
theorem positive_compression_le (A : Matrix n n ℝ) (hA : A.IsHermitian)
    (Q : Matrix n (Fin 2) ℝ) (hQ : Qᵀ * Q = 1)
    (hC : (Qᵀ * A * Q).PosSemidef) :
    BN.inner (Qᵀ * A * Q) (Qᵀ * A * Q) ≤
      BN.lambdaMax hA ^ 2 + BN.lambdaSecond hA ^ 2 := by
  let C := Qᵀ * A * Q
  obtain ⟨u, v, α, β, hβ, hβα, hu, hv, huv, hCeq⟩ := BN.exists_finTwo_writing hC
  change C = α • vecMulVec u u + β • vecMulVec v v at hCeq
  have hCu : u ⬝ᵥ C *ᵥ u = α := by
    rw [← BN.inner_vecMulVec, hCeq]
    simp [BN.inner_add_left, BN.inner_smul_left,
      BN.inner_vecMulVec_vecMulVec, hu, huv, dotProduct_comm]
  have hCv : v ⬝ᵥ C *ᵥ v = β := by
    rw [← BN.inner_vecMulVec, hCeq]
    simp [BN.inner_add_left, BN.inner_smul_left, BN.inner_vecMulVec_vecMulVec, hv, huv]
  have hprod (x y : Fin 2 → ℝ) : (Q *ᵥ x) ⬝ᵥ (Q *ᵥ y) = x ⬝ᵥ y := by
    rw [dotProduct_mulVec, ← vecMul_transpose, vecMul_vecMul, hQ, vecMul_one]
  have hray (x : Fin 2 → ℝ) : (Q *ᵥ x) ⬝ᵥ A *ᵥ (Q *ᵥ x) = x ⬝ᵥ C *ᵥ x := by
    rw [dotProduct_mulVec]
    nth_rewrite 1 [← vecMul_transpose]
    rw [vecMul_vecMul, ← dotProduct_mulVec]
    simp only [mulVec_mulVec]
    rfl
  have hU : (Q *ᵥ u) ⬝ᵥ (Q *ᵥ u) = 1 := by rw [hprod, hu]
  have hV : (Q *ᵥ v) ⬝ᵥ (Q *ᵥ v) = 1 := by rw [hprod, hv]
  have hUV : (Q *ᵥ u) ⬝ᵥ (Q *ᵥ v) = 0 := by rw [hprod, huv]
  have hR := BN.rayleigh_le_lambdaMax hA hU
  have h2 := BN.orthonormal_pair_le_lambdaMax_add_lambdaSecond hA hU hV hUV
  simp only [hray, hCu, hCv] at hR h2
  change BN.inner C C ≤ _
  rw [hCeq, BN.inner_self_rankTwo hu hv huv]
  nlinarith [mul_nonneg (sub_nonneg.mpr hβα) (sub_nonneg.mpr hR),
    mul_nonneg hβ (sub_nonneg.mpr h2), sq_nonneg (BN.lambdaMax hA - α),
    sq_nonneg (BN.lambdaSecond hA - β)]

end KKP
