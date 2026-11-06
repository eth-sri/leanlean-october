module

public import HypoellipticAleksandrov.KineticAleksandrov.Decay.SourceNotation

/-! # Euclidean frequency normalization for kinetic blocks -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Decay

variable {d : ℕ} {ξ : PDE.Vec d}

/-- A nonzero Euclidean frequency has strictly positive Euclidean norm. -/
theorem frequency_norm_pos  (hξ : ξ ≠ 0) :
    0 < PDE.vecEuclideanNorm ξ :=
  lt_of_le_of_ne (PDE.vecEuclideanNorm_nonneg ξ)
    (Ne.symm (fun h => hξ (PDE.vecEuclideanNorm_eq_zero_iff.mp h)))

/-- The source radius gives the required block duration and a unit rescaled frequency. -/
theorem frequency_radius_identities  (hξ : ξ ≠ 0) :
    let r := PDE.vecEuclideanNorm ξ ^ (-(1 / 3 : ℝ))
    0 < r ∧ r ^ 2 = PDE.vecEuclideanNorm ξ ^ (-(2 / 3 : ℝ)) ∧
      PDE.vecNormSq (r ^ 3 • ξ) = 1 := by
  let N := PDE.vecEuclideanNorm ξ
  have hN : 0 < N := frequency_norm_pos hξ
  have hr : 0 < N ^ (-(1 / 3 : ℝ)) := Real.rpow_pos_of_pos hN _
  have h2 : (N ^ (-(1 / 3 : ℝ))) ^ 2 = N ^ (-(2 / 3 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]
    norm_num
  have h3 : (N ^ (-(1 / 3 : ℝ))) ^ 3 = N⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]
    norm_num [Real.rpow_neg_one]
  refine ⟨hr, h2, ?_⟩
  rw [← PDE.vecEuclideanNorm_sq, PDE.vecEuclideanNorm_smul]
  grind

end HypoellipticAleksandrov.KineticAleksandrov.Decay
