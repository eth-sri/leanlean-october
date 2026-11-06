module

public import NormalizerDelta.NewmanDelta

@[expose] public section

/-!
# §D: the sanity statements for Γ_Δ(N), ε_Δ, h_Δ

* Γ_{(ℤ/N)ˣ}(N) = Γ₀(N) and Γ_{±1}(N) = Γ₁(N) ⊔ {±1};
* ε_⊤ = gcd(N, 24): gcd(N, 24) ∣ ε_Δ for every Δ (units modulo a divisor of 24 square to 1), and
  ε_⊤ ∣ gcd(N, 24) by the element γ_p of the T2 proof (`exists_gamma_p`), whose lower right entry is
  a unit t with v_p(t − x) = v_p(gcd(N, 24));
* ε_{±1} = N; h(N) ∣ h_Δ; h_Δ² ∣ N; h_⊤ = h(N); the form of `newman_delta` with h(N) is (8′).
-/

open Matrix MatrixGroups

namespace NormalizerLean

noncomputable section

variable {N : ℕ}

/-! ### ε_Δ -/

/-- Units modulo a divisor of 24 square to 1, so gcd(N, 24) ∣ ε_Δ. -/
theorem gcd24_dvd_epsDelta [NeZero N] (Δ : Subgroup (ZMod N)ˣ) : Nat.gcd N 24 ∣ epsDelta N Δ := by
  refine dvd_epsDelta_iff.2 ⟨Nat.gcd_dvd_left _ _, fun u _ => ?_⟩
  set k := Nat.gcd N 24
  by_cases hN : N = 1
  · subst hN; simp [k]
  have hN2 : 2 ≤ N := by have := NeZero.ne N; omega
  have h1 := one_le_val_unit hN2 u
  set a : ℤ := (((u⁻¹ : (ZMod N)ˣ) : ZMod N).val : ℤ)
  set d : ℤ := ((u : ZMod N).val : ℤ)
  have had : a * d ≡ 1 [ZMOD N] := by
    rw [← ZMod.intCast_eq_intCast_iff]
    simp [a, d]
  have hadk : a * d ≡ 1 [ZMOD k] := had.of_dvd (Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_left _ _))
  have hk : a ≡ d [ZMOD k] := modEq_of_mul_modEq_one (Nat.gcd_dvd_right _ _) hadk
  have hdd : d * d ≡ 1 [ZMOD k] := ((hk.symm.mul_right d).trans (by rw [mul_comm] at hadk ⊢; exact hadk))
  have : (k : ℤ) ∣ d ^ 2 - 1 := by
    have := (Int.ModEq.dvd hdd.symm)
    rw [pow_two]
    exact this
  have h2 : (k : ℤ) ∣ (((u : ZMod N).val ^ 2 - 1 : ℕ) : ℤ) := by
    rw [Nat.cast_sub (Nat.one_le_pow _ _ h1)]; push_cast; exact this
  exact_mod_cast h2

/-! ### h_Δ -/

theorem hDelta_ne_zero [NeZero N] (Δ : Subgroup (ZMod N)ˣ) : hDelta N Δ ≠ 0 :=
  (newmanData_delta N Δ).h_pos.ne'

theorem hDelta_sq_dvd' (N : ℕ) [NeZero N] (Δ : Subgroup (ZMod N)ˣ) : hDelta N Δ ^ 2 ∣ N :=
  (newmanData_delta N Δ).h_sq_dvd

end

end NormalizerLean
