module
public import GafniTao.WooleyPolynomialSystem

@[expose] public section

/-!
# Exact translation--dilation algebra for the Vinogradov system

This file supplies the monomial specialization of Wooley Section 4.  We keep
the variables integral and prove the full binomial expansion before extracting
the divisibility left after a common translation and prime-power dilation.
-/

open Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- Cancelling a visible prime-power factor in an integer divisibility
relation.  No coprimality is needed because this is cancellation in the
integral domain `ℤ`, not cancellation modulo a composite modulus. -/
theorem pow_dvd_of_mul_pow_dvd
    {p a j B : ℕ} (hp : p ≠ 0) (hja : j * a ≤ B) {z : ℤ}
    (h : (p : ℤ) ^ B ∣ (p : ℤ) ^ (j * a) * z) :
    (p : ℤ) ^ (B - j * a) ∣ z := by
  obtain ⟨w, hw⟩ := h
  have hpow : (p : ℤ) ^ B =
      (p : ℤ) ^ (j * a) * (p : ℤ) ^ (B - j * a) := by
    rw [← pow_add, Nat.add_sub_of_le hja]
  rw [hpow] at hw
  have hpz : ((p : ℤ) ^ (j * a)) ≠ 0 :=
    pow_ne_zero _ (by exact_mod_cast hp)
  have hz : z = (p : ℤ) ^ (B - j * a) * w := by
    apply mul_left_cancel₀ hpz
    simpa [mul_assoc] using hw
  exact ⟨w, hz⟩

end

end GafniTao
