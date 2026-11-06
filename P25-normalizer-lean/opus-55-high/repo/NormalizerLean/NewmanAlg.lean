module

public import NormalizerLean.T1General

@[expose] public section

/-!
# The algebra of Newman's form (8′)

For g = (ε/√e)·[[ae, b/h], [Nc/h, de]] (Newman data (a, b, c, d, e, ε)):
* `NData.e_unique`: e is determined by g (the integer matrix W = [[ae, b], [nc, de]] is primitive:
  d·(ae) − (cm)·b = 1 where n = em);
* `NData.mul`: the product of (8′)-matrices with e, e' is an (8′)-matrix with e₁f₁, where
  e = e₁q, e' = f₁q, gcd(e₁, f₁) = 1 (the Atkin–Lehner product law);
* `NData.one_of_mem`: elements of Γ₀(N) have e = 1;
* `NData.inv`.
-/

open Matrix MatrixGroups

namespace NormalizerLean

noncomputable section

/-! ### Uniqueness of e -/

theorem cross_of_prop {κ κ' : ℝ} (hκ : κ ≠ 0) {x y x' y' : ℤ}
    (h1 : κ * x = κ' * x') (h2 : κ * y = κ' * y') : x * y' = y * x' := by
  have : κ * ((x : ℝ) * y') = κ * ((y : ℝ) * x') := by
    calc κ * ((x : ℝ) * y') = (κ * x) * y' := by ring
      _ = κ' * x' * y' := by rw [h1]
      _ = (κ' * y') * x' := by ring
      _ = κ * y * x' := by rw [h2]
      _ = κ * ((y : ℝ) * x') := by ring
  exact_mod_cast mul_left_cancel₀ hκ this

/-! ### Products -/

/-! ### The invariant e(g) and the parities σ_p -/

end

end NormalizerLean
