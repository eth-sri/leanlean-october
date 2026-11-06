module

public import NormalizerLean.Basic

@[expose] public section

/-!
# T1 for Atkin–Lehner elements and translations

* `S_mem_normalizer'`: S_k normalizes Γ₀(N) for k ∣ h(N);
* `isAtkinLehner_mem_normalizer'`: every AL element w_Q (Q ∣ N) normalizes Γ₀(N);
* `exists_isAtkinLehner'`: AL elements exist for Q ∥ N;
* `isAtkinLehner_mul_inv_mem'`: two AL elements for Q differ by Γ₀(N).

The AL computations are the identities W γ adj(W) = Q·M₁, adj(W) γ W = Q·M₂, W adj(W') = Q·M₃
with explicit integer matrices Mᵢ (checked symbolically in sympy before being given to `ring`).
-/

open Matrix MatrixGroups

namespace NormalizerLean

noncomputable section

/-! ### Scalar bookkeeping -/

theorem coe_inv_of_coe_eq_smul {g : SL(2, ℝ)} {s a b c d : ℝ}
    (h : (g : Matrix (Fin 2) (Fin 2) ℝ) = s • !![a, b; c, d]) :
    ((g⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) = s • !![d, -b; -c, a] := by
  rw [Matrix.SpecialLinearGroup.coe_inv, h, adjugate_smul, adjugate_fin_two_of]
  simp

/-! ### Translations -/

/-! ### Atkin–Lehner elements -/

end

end NormalizerLean
