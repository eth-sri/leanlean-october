module

public import GS.Nonmanifold.NormalizationEstimates

@[expose] public section

set_option backward.isDefEq.respectTransparency false


/-!
# Small skew logarithms for all orthogonal matrices near Q0

The older ExponentialChart exports only local injectivity. Here both inverse
identities and continuity of the inverse are obtained from the inverse function
theorem. They imply the existence of small skew logarithms for ALL orthogonal
matrices in a genuine open neighbourhood, not just for points of exp's image.

The operator norm is used only inside the inverse-function-theorem proof.
Exported statements use the original matrix topology and the explicit frobSq.

-/
noncomputable section
open Matrix Filter GS GS.Extensions GS.Continuation GS.Nonmanifold
open scoped Topology
namespace GS.NonmanifoldCompletion

/-- A local inverse of the actual matrix exponential, constructed using IFT. -/
theorem exists_continuous_local_matrix_log (q : ℕ) :
    ∃ log : Mat q → Mat q,
      log 1 = 0 ∧ ContinuousAt log 1 ∧ (∀ᶠ A in 𝓝 (1 : Mat q), matrixExp (log A) = A) := by
  let : NormedRing (Mat q) := Matrix.linftyOpNormedRing
  let : NormedAlgebra ℝ (Mat q) := Matrix.linftyOpNormedAlgebra
  have hd : HasStrictFDerivAt (NormedSpace.exp : Mat q → Mat q)
      (ContinuousLinearEquiv.refl ℝ (Mat q) : Mat q →L[ℝ] Mat q) 0 := by
    simpa only [ContinuousLinearMap.one_def, ContinuousLinearEquiv.coe_refl] using (hasStrictFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := Mat q))
  exact ⟨_, by simpa using hd.eventually_left_inverse.self_of_nhds, by simpa using hd.localInverse_continuousAt,
    by simpa [matrixExp_eq_exp] using hd.eventually_right_inverse⟩

/-- Uniform small-log existence in the exact Frobenius coordinates of K_eta.
Skewness follows from orthogonality of A and local injectivity; it is not assumed. -/
theorem exists_open_frob_small_skew_log {q : ℕ} (Q₀ : Mat q) (hQ₀ : Orthogonal Q₀) (η : ℝ) (hη : 0 < η) :
    ∃ U : Set (Mat q), IsOpen U ∧ Q₀ ∈ U ∧
      ∀ A ∈ U, Orthogonal A →
        ∃ H : Mat q, IsSkew H ∧ frobSq H < η^2 ∧ originalPsi Q₀ H = A := by
  obtain ⟨g,hg0,hgc,hright⟩ := exists_continuous_local_matrix_log q
  obtain ⟨V,hV,hV0,hdetect⟩ := exists_open_exp_skew_detection q
  have hlog : ∀ᶠ A in 𝓝 (1 : Mat q), frobSq (g A) < η^2 ∧ g A ∈ V :=
    hgc.eventually (((isOpen_lt continuous_frobSq continuous_const).inter hV).mem_nhds
      ⟨by simpa [hg0, frobSq, frobInner] using sq_pos_of_pos hη, hg0 ▸ hV0⟩)
  obtain ⟨U,hsub,hU,h1⟩ := mem_nhds_iff.mp (hright.and hlog)
  refine ⟨(Q₀ᵀ * ·) ⁻¹' U, hU.preimage (by fun_prop), by simpa [hQ₀.1] using h1, fun A hA ho => ?_⟩
  obtain ⟨he,hD',hV'⟩ := hsub hA
  refine ⟨g (Q₀ᵀ*A), hdetect _ hV' (he ▸ hQ₀.transpose.mul ho), hD', ?_⟩
  change Q₀ * matrixExp (g (Q₀ᵀ*A)) = A
  rw [he,← Matrix.mul_assoc,hQ₀.2,Matrix.one_mul]

end GS.NonmanifoldCompletion
