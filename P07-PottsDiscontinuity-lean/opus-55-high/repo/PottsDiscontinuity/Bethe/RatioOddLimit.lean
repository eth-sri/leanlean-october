module

public import PottsDiscontinuity.Analysis.Section4SourceIntegral
public import PottsDiscontinuity.Bethe.RatioBulk29
public import PottsDiscontinuity.Bethe.RatioOddQuotient

/-! # The complete odd-deficit eigenvalue ratio limit -/

public section

open Set Filter MeasureTheory Finset
open scoped Topology BigOperators

namespace PottsDiscontinuity.Bethe

open BetheAnsatz

/-- The fixed middle root of an odd symmetric ordered family is zero. -/
theorem ratio_odd_middle_root_zero {n t : ℕ} (hn : n = 2 * t + 1)
    (q : Fin n → ℝ) (hq : q ∈ S_n n) : q ⟨t, by omega⟩ = 0 := by
  have h := hq.2.2 ⟨t, by omega⟩
  grind

/-- The regular logarithmic derivative agrees with the source-coordinate derivative
`fourierEllPrime` of the Section 4 Fourier identities
when the anisotropy parameters agree. -/
theorem ratio_ellPrime_eq_fourierEllPrime {Δ c x : ℝ} (hΔ : Δ < -1)
    (hc : 2 < c) (hcΔ : anisotropy c = Δ)
    (hx : x ∈ Ioo (-Real.pi) Real.pi) :
    ratioEllPrime c x = PottsDiscontinuity.fourierEllPrime (lamOf Δ) x := by
  have hlam := lamOf_pos hΔ
  have hcosh := cosh_lamOf hΔ
  have hc2 : c ^ 2 = 2 + 2 * Real.cosh (lamOf Δ) := by
    grind [anisotropy]
  by_cases hx0 : x = 0
  · simp_all [ratioEllPrime, ratioNumerator, PottsDiscontinuity.fourierEllPrime]
  have hfun : ratioEll c =ᶠ[𝓝 x] PottsDiscontinuity.fourierEll (lamOf Δ) := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2, eventually_ne_nhds hx0] with y hy hy0
    have h := PottsDiscontinuity.fourierEll_eq_log_norm hlam hc2 hy hy0
    tauto
  have hR := (ratio_hasDerivAt_ell hc hx hx0).congr_of_eventuallyEq hfun.symm
  have hF := PottsDiscontinuity.fourierEll_hasDerivAt hlam hx hx0
  rw [← hR.deriv, hF.deriv]

/-- The source integral in the Bethe coordinate is the integral used in the Section 4
Fourier identities.
The representatives agree on the open interval, which suffices for the integral. -/
theorem ratio_integral_eq_fourier {Δ c : ℝ} (hΔ : Δ < -1)
    (hc : 2 < c) (hcΔ : anisotropy c = Δ) :
    (∫ x in (-Real.pi)..Real.pi, ratioEllPrime c x * tauCont Δ x) =
      (∫ x in (-Real.pi)..Real.pi,
        PottsDiscontinuity.fourierEllPrime (lamOf Δ) x *
          tau (-Real.cosh (lamOf Δ)) x) := by
  apply intervalIntegral.integral_congr_ae_restrict
  filter_upwards [ae_restrict_mem measurableSet_uIoc,
    ae_restrict_of_ae (Measure.ae_ne volume Real.pi),
    ae_restrict_of_ae (Measure.ae_ne volume (-Real.pi))] with x hx hxp hxm
  have hxIoc : x ∈ Ioc (-Real.pi) Real.pi := by
    simpa [uIoc_of_le (neg_le_self Real.pi_nonneg)] using hx
  have hxIoo : x ∈ Ioo (-Real.pi) Real.pi :=
    by grind
  have hparam : -Real.cosh (lamOf Δ) = Δ := by rw [cosh_lamOf hΔ]; ring
  rw [ratio_ellPrime_eq_fourierEllPrime hΔ hc hcΔ hxIoo, hparam,
    tau_eq_tauCont hΔ hxIoo]

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
        (rootStepDensity (N i) (N i / 2) (p i) (hp i) (half_pos_of_half_sub_pos N r hn i) (two_mul_half_le N i)
          (kMap (lamOf Δ) α) - rho Δ (kMap (lamOf Δ) α))|))
    (hbq : ∀ i, BddAbove (range fun α : Icc (-Real.pi) Real.pi =>
      |Xi (lamOf Δ) α *
        (rootStepDensity (N i) (N i / 2 - r) (q i) (hq i) (hn i) (two_mul_half_sub_le N r i)
          (kMap (lamOf Δ) α) - rho Δ (kMap (lamOf Δ) α))|))
    {K : ℝ} (hK : 0 ≤ K)
    (hrate : ∀ᶠ i in atTop,
      densityNorm Δ hΔ (fun x => rootStepDensity (N i) (N i / 2) (p i) (hp i)
        (half_pos_of_half_sub_pos N r hn i) (two_mul_half_le N i) x - rho Δ x) (hbp i) ≤ K / N i ∧
      densityNorm Δ hΔ (fun x => rootStepDensity (N i) (N i / 2 - r) (q i) (hq i)
        (hn i) (two_mul_half_sub_le N r i) x - rho Δ x) (hbq i) ≤ K / N i)


include hΔ h4 hr hN hp hq hpBE hqBE hNlim hbp hbq hK hrate

section
variable (hodd : r % 2 ≠ 0)
include hodd
/-- The requested integral-exponent eigenvalue quotient limit for every odd deficit.
The zero-root coefficient and all three odd local factors are retained. -/
theorem ratio_odd_eigenvalue_limit {c : ℝ}
    (hc : 2 < c) (hcΔ : anisotropy c = Δ) :
    Tendsto (fun i => eigenvalueZero (N i) c (q i)
    ⟨(N i / 2 - r) / 2, Nat.div_lt_self (hn i) Nat.one_lt_two⟩ /
      eigenvalueRegular c (p i)) atTop
      (𝓝 ((Real.exp (-(r : ℝ) * Real.log |Δ| +
        (r : ℝ) * ∫ x in (-Real.pi)..Real.pi, ratioEllPrime c x * tauCont Δ x) : ℝ) : ℂ)) := by
  obtain ⟨s, hrs⟩ : ∃ s : ℕ, r = 2 * s + 1 := ⟨r / 2, by omega⟩
  subst r
  let n : ℕ → ℕ := fun i => N i / 2 - (2 * s + 1)
  have hcountN (i : ℕ) : N i = 2 * (n i + (2 * s + 1)) := by
    grind
  have hnQ (i : ℕ) : 0 < n i := hn i
  have hsQ (i : ℕ) : 2 * n i ≤ N i := by simp_all
  have hnodd (i : ℕ) : n i = 2 * (N i / 4 - s - 1) + 1 := by
    grind
  let l : ∀ i, Fin (n i) := fun i => ⟨N i / 4 - s - 1, by grind⟩
  have hzero (i : ℕ) : q i (l i) = 0 := by
    grind [ratio_odd_middle_root_zero]
  have hcenter (i : ℕ) : l i =
      ⟨(N i / 2 - (2 * s + 1)) / 2, Nat.div_lt_self (hnQ i) (by omega)⟩ := by
    grind

  have hnormP :=
    ratio_densityNorm_tendsto_of_rate hΔ N hNlim _ hbp (hrate.mono (fun i hi => hi.1))
  have hnormQ : Tendsto (fun i => densityNorm Δ hΔ
      (fun x => rootStepDensity (N i) (n i) (q i) (hq i)
        (hnQ i) (hsQ i) x - rho Δ x) (hbq i)) atTop (𝓝 0) := by
    have ht := ratio_densityNorm_tendsto_of_rate hΔ N hNlim
      (fun i x => rootStepDensity (N i) (N i / 2 - (2 * s + 1)) (q i) (hq i)
        (hn i) (by omega) x - rho Δ x)
      hbq (hrate.mono (fun i hi => hi.2))
    omega

  have hA₀ := ratio_odd_A_tendsto hΔ c (2 * s + 1) N n q hq hnQ hsQ hcountN hNlim
    (fun i => hbq i) hnormQ l hzero
  have hA : Tendsto (fun i => ratioZeroCoefficient (anisotropy c) c (N i) (q i) (l i) /
      (2 * (N i : ℝ))) atTop (𝓝 (c ^ 2 * Real.pi * rho Δ 0)) := by
    simpa only [hcΔ] using hA₀

  have hfirstBound (i : ℕ) : 0 < N i / 4 := by
    grind
  let x : ℕ → ℝ := fun i => ratioPositiveRoot (N i) (h4 i) (p i)
    ⟨0, hfirstBound i⟩
  have hx (i : ℕ) :=
    ratio_positiveRoot_mem_Ioo (h4 i) (hp i) ⟨0, hfirstBound i⟩
  have hxpos (i : ℕ) := ratio_positiveRoot_pos (h4 i) (hp i) ⟨0, hfirstBound i⟩
  have hscale := ratio_full_positive_rank_scaling hΔ N h4 hN p hp hNlim hbp hnormP 0
    (fun i => by grind)
  have hxlim : Tendsto x atTop (𝓝 0) := (hscale.div_atTop hNlim).congr fun i => by
    dsimp [x]; field_simp [show (N i : ℝ) ≠ 0 by exact_mod_cast (hN i).ne']
  have hnP (i : ℕ) : 0 < N i / 2 := by grind
  have hcountP (i : ℕ) : N i = 2 * (N i / 2 + 0) := by
    grind
  let xb : ℕ → Fin s → ℝ := fun i j => p i ⟨j.val, by have := hr i; omega⟩
  let yb : ℕ → ℝ := fun i => p i ⟨s, by have := hr i; omega⟩
  have hxb (j : Fin s) : Tendsto (fun i => xb i j) atTop (𝓝 (-Real.pi)) :=
    ratio_tendsto_root_left hΔ 0 N (fun i => N i / 2) p hp hnP
      (fun i => by omega) hcountP hNlim hbp hnormP
      (fun i => ⟨j.val, by have := hr i; omega⟩) s (fun i => by simp)
  have hyb :=
    ratio_tendsto_root_left hΔ 0 N (fun i => N i / 2) p hp hnP
      (fun i => by omega) hcountP hNlim hbp hnormP
      (fun i => ⟨s, by have := hr i; omega⟩) s (fun i => le_rfl)
  have hB := ratio_odd_boundary_tendsto hc s xb yb hxb hyb

  have hBulkExp := (Real.continuous_exp.tendsto _).comp
    (ratio_bulk_log_limit hΔ (2 * s + 1) N h4 hr hN hn p q hp hq hpBE hqBE
      hNlim hbp hbq hK hrate hc)

  have hρ := rho_pos hΔ 0
  have hsmallValue : (c ^ 2 * Real.pi * rho Δ 0) *
      (((((0 : ℕ) : ℝ) + 1 / 2) / rho Δ 0) / c ^ 2) * (2 / Real.pi) = 1 := by
    field_simp
    ring
  have hsmall := (hA.mul (ratio_scaled_inverse_norm_tendsto hc (fun i => (N i : ℝ)) x hx hxpos hxlim hscale)).mul (ratio_source_midpoint_limit hΔ hc s N h4 hN p hp hNlim hbp hnormP)
  rw [hsmallValue] at hsmall

  rw [hcΔ, ← Real.exp_log (pow_pos (abs_pos.mpr (by linarith : Δ ≠ 0)) (2 * s + 1)), ← Real.exp_neg, Real.log_pow, ← neg_mul] at hB
  have hreal := hsmall.mul (hB.mul hBulkExp)
  rw [← Real.exp_add] at hreal
  have hcomplex' := by simpa only [one_mul] using (Complex.continuous_ofReal.continuousAt.tendsto.comp hreal)
  apply hcomplex'.congr
  intro i
  dsimp
  have hf := ratio_odd_quotient_factors hc s (N i) (h4 i)
    (by grind) (by tauto)
    (p i) (hp i) (q i) (hq i) (l i) (hzero i)
  rw [hcenter i] at hf
  rw [hf]
  apply congrArg (fun z : ℝ => (z : ℂ))
  rw [← hcenter i]
  linarith

/-- The odd-branch ratio limit after applying the Section 4 Fourier exponent identity.
The scalar `S` is the limit of the source alternating tanh partial sums. -/
theorem ratio_odd_eigenvalue_limit_fourier {c : ℝ} (hc : 2 < c) (hcΔ : anisotropy c = Δ) :
    ∃ S : ℝ,
      Tendsto (PottsDiscontinuity.altTanhPartial (lamOf Δ)) atTop (𝓝 S) ∧
      Tendsto (fun i => eigenvalueZero (N i) c (q i)
        ⟨(N i / 2 - r) / 2, Nat.div_lt_self (hn i) Nat.one_lt_two⟩ /
          eigenvalueRegular c (p i)) atTop
        (𝓝 ((Real.exp (-(r : ℝ) * (lamOf Δ + 2 * S)) : ℝ) : ℂ)) := by
  obtain ⟨S, hS, hW15⟩ := PottsDiscontinuity.fourierRatioExponent
    (r := (r : ℝ)) (lamOf_pos hΔ)
  have hparam : -Real.cosh (lamOf Δ) = Δ := by rw [cosh_lamOf hΔ]; ring
  have hIntegral := ratio_integral_eq_fourier hΔ hc hcΔ
  have hlimit := ratio_odd_eigenvalue_limit hΔ r N h4 hr hN hn p q hp hq
    hpBE hqBE hNlim hbp hbq hK hrate hodd hc hcΔ
  grind
end

end

end PottsDiscontinuity.Bethe
