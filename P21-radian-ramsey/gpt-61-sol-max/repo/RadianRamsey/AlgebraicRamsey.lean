module

public import OAI.Combinatorics.EuclideanRamsey.Main

public section

namespace OAI.EuclideanRamsey

theorem ramsey_of_algebraic {s d : ℕ} (a : Fin s → Space d)
    (hs : 2 ≤ s) (hd : 1 ≤ d) (ha : Function.Injective a)
    (halg : ∀ i j, IsAlgebraic ℚ (a i j))
    (hsph : ∀ i, dist (a i) 0 = 1) : Ramsey a := by
  classical
  have : FiniteDimensional ℚ (Coeff a) :=
    IntermediateField.finiteDimensional_adjoin
      (by rintro _ ⟨ij, rfl⟩; exact (halg ij.1 ij.2).isIntegral)
  have :=
    Algebra.FormallyUnramified.of_isSeparable ℚ (Coeff a)
  obtain ⟨t, ht, ht1⟩ :=
    (Algebra.FormallyUnramified.iff_exists_tensorProduct (R := ℚ) (S := Coeff a)).mp
      inferInstance
  let φ  :=
    Algebra.TensorProduct.map (coordinateField a).val (coordinateField a).val
  let u := φ t
  have hswap (x : Coeff a) : u * (1 ⊗ₜ[ℚ] (x:ℝ)) = u * ((x:ℝ) ⊗ₜ[ℚ] 1) := by
    have h := congrArg φ (ht x)
    simpa [φ, u, sub_mul, sub_eq_zero, mul_comm (φ t)] using h
  have hu : (Algebra.TensorProduct.lmul' ℚ : RealTensor →ₐ[ℚ] ℝ) u = 1 := by
    convert congrArg (coordinateField a).val ht1 using 1
    all_goals simp [u,φ]
    clear ht ht1 hswap
    induction t using TensorProduct.inductionOn <;> simp_all
  have term (x : Coeff a) :
      ((x:ℝ) ⊗ₜ[ℚ] (1:ℝ)) * u * (1 ⊗ₜ[ℚ] (x:ℝ)) = u * (((x:ℝ) ^ 2) ⊗ₜ[ℚ] 1) := by
    rw [mul_assoc,hswap,mul_left_comm,
      Algebra.TensorProduct.tmul_mul_tmul,mul_one,← pow_two]
  apply realCriterion_ramsey a hs hd ha
  refine ⟨Matrix.diagonal (fun α : Option (Fin d) => if α = none then -u else u), ?_, ?_⟩
  · intro i
    have hsum : ∑ j, (a i j)^2 = 1 := by
      have h := congrArg (fun x : ℝ => x ^ 2) (hsph i)
      rwa [dist_zero_right, EuclideanSpace.real_norm_sq_eq, one_pow] at h
    change (∑ α, ∑ β, ((realAugmented a i α) ⊗ₜ[ℚ] (1:ℝ)) * _ *
      ((1:ℝ) ⊗ₜ[ℚ] realAugmented a i β)) = 0
    simp [Matrix.diagonal, mul_ite, ite_mul, Fintype.sum_option, realAugmented,
      show ∀ j, a i j = (coordinate a i j : ℝ) from fun _ => rfl, term,
      ← Finset.mul_sum, ← TensorProduct.sum_tmul]
    simp [coordinate, hsum, ← Algebra.TensorProduct.one_def]
  · ext α β
    change Algebra.TensorProduct.lmul' ℚ ((Matrix.diagonal
      (fun α : Option (Fin d) => if α = none then -u else u)) (some α) (some β)) = _
    simp [Matrix.diagonal, apply_ite, hu, Matrix.one_apply]
end OAI.EuclideanRamsey
