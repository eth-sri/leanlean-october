
import GS.Nonmanifold.NormalizationEstimates



/-!
# Small skew logarithms for all orthogonal matrices near Q0

The older ExponentialChart exports only local injectivity. Here both inverse
identities and continuity of the inverse are obtained from the inverse function
theorem. They imply the existence of small skew logarithms for ALL orthogonal
matrices in a genuine open neighbourhood, not just for points of exp's image.

The operator norm is used only inside the inverse-function-theorem proof.
Exported statements use the original matrix topology and the explicit cFrobSq.

-/
open Matrix GS.Continuation
namespace GS.NonmanifoldCompletion

/-- An arbitrary prescribed open restriction on the logarithm can be enforced.
Skewness follows from orthogonality of A and local injectivity; it is not assumed.
-/
theorem exists_open_small_skew_log {q : ℕ} (Q₀ : Mat q) (hQ₀ : Orthogonal Q₀)
    (D : Set (Mat q)) (hD : IsOpen D) (hD0 : (0 : Mat q) ∈ D) :
    ∃ U : Set (Mat q), IsOpen U ∧ Q₀ ∈ U ∧
      ∀ A ∈ U, Orthogonal A →
        ∃ H ∈ D, IsSkew H ∧ originalPsi Q₀ H = A := by
  obtain ⟨e,he,h0⟩ := exists_matrixExpChart q
  let V := D ∩ (fun H : Mat q => Hᵀ) ⁻¹' e.source ∩ (fun H : Mat q => -H) ⁻¹' e.source
  have hV : IsOpen V := (hD.inter (e.open_source.preimage (by fun_prop))).inter
    (e.open_source.preimage (by fun_prop))
  let c := e.restrOpen V hV
  have hcFun : (c : Mat q → Mat q) = NormedSpace.exp := he
  have hc0 : (0 : Mat q) ∈ c.source := ⟨h0,⟨hD0,by simpa using h0⟩,by simpa using h0⟩
  refine ⟨(fun A : Mat q => Q₀ᵀ*A) ⁻¹' c.target,
    c.open_target.preimage (by fun_prop), ?_, ?_⟩
  · change Q₀ᵀ*Q₀ ∈ c.target
    rw [hQ₀.1]
    simpa only [hcFun,NormedSpace.exp_zero] using c.map_source hc0
  · intro A hA ho
    let H := c.symm (Q₀ᵀ*A)
    have hH := c.map_target hA
    have hHA  := by
      simpa only [hcFun] using c.right_inv hA
    refine ⟨H,hH.2.1.1,?_,?_⟩
    · apply e.injOn hH.2.1.2 hH.2.2
      have hoH : Orthogonal (NormedSpace.exp H) := by rw [hHA]; exact hQ₀.transpose.mul ho
      simpa only [he,Matrix.exp_transpose,Matrix.exp_neg] using
        (Matrix.inv_eq_left_inv hoH.1).symm
    · change Q₀ * NormedSpace.exp H = A
      rw [hHA,← Matrix.mul_assoc,hQ₀.2,Matrix.one_mul]

end GS.NonmanifoldCompletion
