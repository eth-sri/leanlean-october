module

public import PottsDiscontinuity.Bethe.RatioEvenLimit
public import PottsDiscontinuity.Bethe.RatioOddLimit

/-! # Section 4 Fourier composition for the even eigenvalue-ratio limit -/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace PottsDiscontinuity.Bethe

open BetheAnsatz

section

variable {Δ : ℝ} (hΔ : Δ < -1) (r : ℕ) (N : ℕ → ℕ) (h4 : ∀ i, 4 ∣ N i)
    (hr : ∀ i, r ≤ N i / 2) (hN : ∀ i, 0 < N i) (hn : ∀ i, 0 < N i / 2 - r)
    (p : ∀ i, Fin (N i / 2) → ℝ) (q : ∀ i, Fin (N i / 2 - r) → ℝ)
    (hp : ∀ i, p i ∈ S_n (N i / 2)) (hq : ∀ i, q i ∈ S_n (N i / 2 - r))
    (hpBE : ∀ i, DiscreteBetheEquation Δ (N i) (N i / 2) (p i))
    (hqBE : ∀ i, DiscreteBetheEquation Δ (N i) (N i / 2 - r) (q i))
    (hNlim : Tendsto (fun i => (N i : ℝ)) atTop atTop)
    (hbp : ∀ i, BddAbove (range fun α : Icc (-Real.pi) Real.pi =>
      |Xi (lamOf Δ) α *
        (rootStepDensity (N i) (p i) (half_pos_of_half_sub_pos hn i)
          (kMap (lamOf Δ) α) - rho Δ (kMap (lamOf Δ) α))|))
    (hbq : ∀ i, BddAbove (range fun α : Icc (-Real.pi) Real.pi =>
      |Xi (lamOf Δ) α *
        (rootStepDensity (N i) (q i) (hn i)
          (kMap (lamOf Δ) α) - rho Δ (kMap (lamOf Δ) α))|))
    {K : ℝ} (hK : 0 ≤ K)
    (hrate : ∀ᶠ i in atTop,
      densityNorm Δ (fun x => rootStepDensity (N i) (p i)
        (half_pos_of_half_sub_pos hn i) x - rho Δ x) ≤ K / N i ∧
      densityNorm Δ (fun x => rootStepDensity (N i) (q i)
        (hn i) x - rho Δ x) ≤ K / N i)


include hΔ h4 hr hN hp hq hpBE hqBE hNlim hbp hbq hK hrate

include h4 hN hbp hbq hn hp hpBE hq hqBE hr hΔ in
/-- The even-branch quotient limit in the explicit Section 4 Fourier form.
The same alternating-series limit `S` gives the exponent `-r(λ+2S)`. -/
theorem ratio_even_eigenvalue_limit_fourier (heven : r % 2 = 0)
    (hrpos : 1 ≤ r) {c : ℝ} (hc : 2 < c) (hcΔ : anisotropy c = Δ) :
    ∃ S : ℝ,
      Tendsto (PottsDiscontinuity.altTanhPartial (lamOf Δ)) atTop (𝓝 S) ∧
      Tendsto (fun i => eigenvalueRegular c (q i) / eigenvalueRegular c (p i)) atTop
        (𝓝 ((Real.exp (-(r : ℝ) * (lamOf Δ + 2 * S)) : ℝ) : ℂ)) := by
  have hlam := lamOf_pos hΔ
  obtain ⟨S, hS, hW15⟩ := PottsDiscontinuity.fourierRatioExponent
    (lam := lamOf Δ) (r := (r : ℝ)) hlam
  have hparam : -Real.cosh (lamOf Δ) = Δ := by simp [cosh_lamOf hΔ]
  have hlog : Real.log |Δ| = Real.log |-(Real.cosh (lamOf Δ))| := by grind
  have hIntegral := ratio_integral_eq_fourier hΔ hc hcΔ
  have hExponent : -(r : ℝ) * Real.log |Δ| +
      (r : ℝ) * ∫ x in (-Real.pi)..Real.pi, ratioEllPrime c x * tauCont Δ x =
      -(r : ℝ) * (lamOf Δ + 2 * S) := by
    grind
  have hlimit := ratio_even_eigenvalue_limit hΔ r N h4 hr hN hn p q hp hq
    hpBE hqBE hNlim hbp hbq hK hrate heven hc hcΔ
  grind

end

end PottsDiscontinuity.Bethe
