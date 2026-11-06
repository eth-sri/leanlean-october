module

public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Nat.Factorial.NatCast
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Tactic

/-!
# Antiholomorphic transmutation: the algebraic identities (Section 5)

This file formalizes the algebraic content of Lemmas 5.4 and 5.5 of the paper: the
identities satisfied by the Vekua-type transmutation series

  `𝒱_E h = ∑_{j ≥ 0} (-E/4)^j / j! · z^j J^j h`,

where `J` is the normalized antiholomorphic primitive (`∂̄ J h = h`).

The analytic part of the paper (convergence of the series in Sobolev norms, Lemma 5.3) is not
formalized. Instead, `𝒱_E h` is treated as a *formal power series in the energy `E`*, with
coefficients in an abstract commutative `ℚ`-algebra `R` of functions, carrying two commuting
derivations `∂` (`D`) and `∂̄` (`Dbar`) with `∂ z = 1`, `∂̄ z = 0`. Antiholomorphic functions form
a submodule `A` on which `∂` vanishes and which `J` preserves. Every identity below is an
identity of coefficients of `E^j`, so it holds for any convergent realization of the series
in which termwise differentiation is justified (as in the paper).

Main results:
* `vekua_helmholtz` (Lemma 5.4, first part): `4 ∂ ∂̄ 𝒱_E h = -E 𝒱_E h`, i.e.
  `(-Δ - E) 𝒱_E h = 0`, since `Δ = 4 ∂ ∂̄`;
* `vekua_deriv` (Lemma 5.4, second part): `∂ⁿ 𝒱_E h = (-E/4)ⁿ 𝒱_E Jⁿ h`;
* `vekua_inverse` (Lemma 5.5): `∑_n (-z)ⁿ / n! · ∂ⁿ 𝒱_E h = h`, coefficientwise in `E`;
* `alternating_factorial_sum` (the combinatorial identity used in Lemma 5.5):
  `∑_{n=0}^ℓ (-1)ⁿ / (n! (ℓ-n)!) = [ℓ = 0]`.
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open PowerSeries

/-- The combinatorial identity in the proof of Lemma 5.5:
`∑_{n=0}^ℓ (-1)ⁿ / (n! (ℓ - n)!) = 1` if `ℓ = 0` and `0` otherwise. -/
theorem alternating_factorial_sum (l : ℕ) :
    ∑ n ∈ Finset.range (l + 1), ((-1 : ℚ) ^ n / (n.factorial * (l - n).factorial)) =
      if l = 0 then 1 else 0 := by
  have key : ∀ n ∈ Finset.range (l + 1), ((-1 : ℚ) ^ n / (n.factorial * (l - n).factorial)) =
      ((-1) ^ n * (l.choose n : ℚ)) / l.factorial := by
    intro n hn
    rw [Finset.mem_range] at hn
    rw [div_eq_div_iff (by positivity) (by positivity),
      ← Nat.choose_mul_factorial_mul_factorial (show n ≤ l by omega)]
    push_cast; ring
  rw [Finset.sum_congr rfl key, ← Finset.sum_div]
  have h2 : ∑ n ∈ Finset.range (l + 1), ((-1 : ℚ) ^ n * (l.choose n : ℚ)) =
      ((∑ n ∈ Finset.range (l + 1), ((-1 : ℤ) ^ n * (l.choose n : ℤ)) : ℤ) : ℚ) := by
    push_cast; rfl
  rw [h2, Int.alternating_sum_range_choose]
  split_ifs with h <;> simp [h]

variable {R : Type*} [CommRing R] [Algebra ℚ R]

variable {D Dbar : Derivation ℚ R R} {z : R} {J : R →ₗ[ℚ] R} {A : Submodule ℚ R}

end PolyaNeumann
