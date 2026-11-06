module

public import Mathlib
public import PottsDiscontinuity.Bethe.Prop21Tau

/-!
# Complex Fourier coefficients of §4 for Proposition 2.1

`hatCoef f m = (1/2π) ∫_{-π}^{π} e^{-imα} f(α) dα` is the Fourier coefficient of the source.  This
file records the coefficient computations of §4 (done here without residues, see below):

* `hatCoef_Xi`: `Ξ̂_μ(m) = e^{-μ|m|}` (the Fourier coefficients of `Ξ_μ`, Section 4);
* `hatCoef_Rsech`: `R̂(m) = 1/(2 cosh(λ m))` (eq. (4.1), `eq:Rhat`);
* `hatCoef_PsiFn_zero`, `hatCoef_PsiFn`: `Ψ̂(0) = 0` and `Ψ̂(m) = ((-1)^m/(i m)) (1 - Ξ̂_{2λ}(m))`;
* `hatCoef_TcontFn_zero`, `hatCoef_TcontFn`: `T̂(0) = 0` and `T̂(m) = ((-1)^m/(i m)) tanh(λ|m|)`;
* `rfourier_R`, `rfourier_T`: the Fourier equations (2.2) for the explicit `R` and `T`.

*Route.*  `Ξ̂_μ(m) = e^{-μ|m|}` follows from the geometric (Poisson-kernel) series of `Ξ_μ`
instead of the contour integral of §4; `R̂` from the Poisson summation formula for the hyperbolic
secant (Fourier transform of `sech` via the Beta function) instead of the residue evaluation;
`Ψ̂` from the closed series of `Ψ` obtained by differentiating (footnote 5) instead of integration
by parts; `T̂` from the splitting `T = -α + U_λ` with `U_λ` an absolutely convergent sine series.
-/

@[expose] public section



namespace PottsDiscontinuity.Bethe

/-- `Ξ_μ(α) = 1 + ∑ 2 e^{-μ(n+1)} cos((n+1)α)` as a trigonometric series. -/
theorem Xi_eq_trigSeries {μ : ℝ} (hμ : 0 < μ) :
    Xi μ = trigSeries 1 (fun n => 2 * Real.exp (-μ) ^ (n + 1))  fun _ => 0  := by
  funext α
  have h := (hasSum_Xi_cos hμ α).tsum_eq
  unfold trigSeries
  simp_all

theorem summable_two_mul_exp_pow {μ : ℝ} (hμ : 0 < μ) :
    Summable  fun n : ℕ => 2 * Real.exp (-μ) ^ (n + 1)  := by
  
  have hr1 : Real.exp (-μ) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  
  exact ((summable_geometric_of_lt_one (Real.exp_pos _).le hr1).mul_left (2 * Real.exp (-μ))).congr fun n => by ring

/-! ### The Fourier form (2.2) of (cBE') and (cOE') -/

end PottsDiscontinuity.Bethe
