module
public import Mathlib

public import PottsDiscontinuity.Analysis.Section4SourceIntegral
public import PottsDiscontinuity.Bethe.RatioBulk29
public import PottsDiscontinuity.Bethe.RatioOddQuotient

/-! # The complete odd-deficit eigenvalue ratio limit -/

@[expose] public section

open Set Filter MeasureTheory Finset
open scoped Topology BigOperators

namespace PottsDiscontinuity.Bethe

open BetheAnsatz

/-- The fixed middle root of an odd symmetric ordered family is zero. -/
theorem ratio_odd_middle_root_zero {n t : ℕ} (hn : n = 2 * t + 1)
    (q : Fin n → ℝ) (hq : q ∈ S_n n) : q ⟨t, by omega⟩ = 0 := by
  have hrev : Fin.rev (⟨t, by omega⟩ : Fin n) = ⟨t, by omega⟩ := by
    grind
  have h := hq.2.2 ⟨t, by omega⟩
  rw [hrev] at h
  linarith

/-- The regular logarithmic derivative agrees with the source-coordinate derivative
`fourierEllPrime` of the Section 4 Fourier identities
when the anisotropy parameters agree. -/
theorem ratio_ellPrime_eq_fourierEllPrime {Δ c x : ℝ} (hΔ : Δ < -1)
    (hc : 2 < c) (hcΔ : anisotropy c = Δ)
    (hx : x ∈ Ioo (-Real.pi) Real.pi) :
    ratioEllPrime c x = PottsDiscontinuity.fourierEllPrime (lamOf Δ) x := by
  have hlam  := lamOf_pos hΔ
  have hcosh  := cosh_lamOf hΔ
  have hc2 : c ^ 2 = 2 + 2 * Real.cosh (lamOf Δ) := by
    unfold anisotropy at hcΔ
    nlinarith
  by_cases hx0 : x = 0
  · subst x
    simp [ratioEllPrime, PottsDiscontinuity.fourierEllPrime]
  have hfun : ratioEll c =ᶠ[𝓝 x] PottsDiscontinuity.fourierEll (lamOf Δ) := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2, eventually_ne_nhds hx0] with y hy hy0
    have h := PottsDiscontinuity.fourierEll_eq_log_norm hlam hc2 hy hy0
    aesop
  
  
  rw [← ((ratio_hasDerivAt_ell hc hx hx0).congr_of_eventuallyEq hfun.symm).deriv, (PottsDiscontinuity.fourierEll_hasDerivAt hlam hx hx0).deriv]

/-- The source integral in the Bethe coordinate is the integral used in the Section 4
Fourier identities.
The representatives agree on the open interval, which suffices for the integral. -/
theorem ratio_integral_eq_fourier {Δ c : ℝ} (hΔ : Δ < -1)
    (hc : 2 < c) (hcΔ : anisotropy c = Δ) :
     ∫ x in (-Real.pi)..Real.pi, ratioEllPrime c x * tauCont Δ x  =
       ∫ x in (-Real.pi)..Real.pi,
        PottsDiscontinuity.fourierEllPrime (lamOf Δ) x *
          tau (-Real.cosh (lamOf Δ)) x  := by
  apply intervalIntegral.integral_congr_ae_restrict
  filter_upwards [ae_restrict_mem measurableSet_uIoc,
    ae_restrict_of_ae (Measure.ae_ne volume Real.pi),
    ae_restrict_of_ae (Measure.ae_ne volume (-Real.pi))] with x hx hxp hxm
  have hxIoc : x ∈ Ioc (-Real.pi) Real.pi := by
    simpa [uIoc_of_le (neg_le_self Real.pi_nonneg)] using hx
  
  
  rw [ratio_ellPrime_eq_fourierEllPrime hΔ hc hcΔ  ⟨hxIoc.1, lt_of_le_of_ne hxIoc.2 hxp⟩ , (by rw [cosh_lamOf hΔ]; ring : -Real.cosh (lamOf Δ) = Δ),
    tau_eq_tauCont hΔ  ⟨hxIoc.1, lt_of_le_of_ne hxIoc.2 hxp⟩ ]

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


include h4 hr hN hpBE hqBE hNlim hK hrate

/-- The requested integral-exponent eigenvalue quotient limit for every odd deficit.
The zero-root coefficient and all three odd local factors are retained. -/
theorem ratio_odd_eigenvalue_limit (hodd : r % 2 ≠ 0) {c : ℝ}
    (hc : 2 < c) (hcΔ : anisotropy c = Δ) :
    Tendsto (fun i => eigenvalueZero (N i) c (q i)
    ⟨(N i / 2 - r) / 2, Nat.div_lt_self (hn i) Nat.one_lt_two⟩ /
      eigenvalueRegular c (p i)) atTop
      (𝓝 ((Real.exp (-(r : ℝ) * Real.log |Δ| +
        (r : ℝ) * ∫ x in (-Real.pi)..Real.pi, ratioEllPrime c x * tauCont Δ x) : ℝ) : ℂ)) := by
  obtain ⟨s, hrs⟩ : ∃ s : ℕ, r = 2 * s + 1 := ⟨r / 2, by omega⟩
  subst r
  let n  := fun i => N i / 2 - (2 * s + 1)
  
  have hnQ (i : ℕ)  := hn i
  
  have hnodd (i : ℕ) : n i = 2 * (N i / 4 - s - 1) + 1 := by
    grind
  let l : ∀ i, Fin (n i) := fun i => ⟨N i / 4 - s - 1, by have := hnodd i; omega⟩
  have hzero (i : ℕ) : q i (l i) = 0 := by
    grind [ratio_odd_middle_root_zero]
  have hcenter (i : ℕ) : l i =
      ⟨(N i / 2 - (2 * s + 1)) / 2, Nat.div_lt_self (hnQ i) (by omega)⟩ := by
    grind

  have hnormP : Tendsto (fun i => densityNorm Δ hΔ
      (fun x => rootStepDensity (N i) (N i / 2) (p i) (hp i)
        (by have := hn i; omega) (by omega) x - rho Δ x) (hbp i)) atTop (𝓝 0) :=
    ratio_densityNorm_tendsto_of_rate hΔ N hNlim _ hbp (hrate.mono  fun i hi => hi.1 )
  

  have hA₀ := ratio_odd_A_tendsto hΔ c (2 * s + 1) N n q hq hnQ  fun (i : ℕ) => by dsimp [n]; omega   fun i => by
                                                                       grind  hNlim
     hbq  (by
                        
                        simpa  using (ratio_densityNorm_tendsto_of_rate hΔ N hNlim
                                           (fun i x => rootStepDensity (N i) (N i / 2 - (2 * s + 1)) (q i) (hq i)
                                             (hn i) (by  omega) x - rho Δ x)
                                           hbq (hrate.mono  fun i hi => hi.2 ))) l hzero
  

  have hfirstBound (i : ℕ) : 0 < N i / 4 := by
    grind
  let x  := fun i => ratioPositiveRoot (N i) (h4 i) (p i)
    ⟨0, hfirstBound i⟩
  have hx (i : ℕ)  :=
    ratio_positiveRoot_mem_Ioo (h4 i) (hp i) ⟨0, hfirstBound i⟩
  have hxpos (i : ℕ)  := ratio_positiveRoot_pos (h4 i) (hp i) ⟨0, hfirstBound i⟩
  have hscale := ratio_full_positive_rank_scaling hΔ N h4 hN p hp hNlim hbp hnormP 0
     fun i => by simp_all 
  
  have hC := ratio_scaled_inverse_norm_tendsto hc (fun i =>  N i ) x hx hxpos (by
                                                                                  
                                                                                  apply (hscale.div_atTop hNlim).congr
                                                                                  intro i
                                                                                  dsimp [x]
                                                                                  have hNi : (N i ) ≠ 0 := by simp_all <;> grind
                                                                                  field_simp) hscale

  have hnP (i : ℕ) : 0 < N i / 2 := by grind
  have hcountP (i : ℕ) : N i = 2 * (N i / 2 + 0) := by
    grind
  let xb : ℕ → Fin s → ℝ := fun i j => p i ⟨j.val, by have := hr i; omega⟩
  let yb  := fun i => p i ⟨s, by have := hr i; omega⟩
  
  
  have hB := ratio_odd_boundary_tendsto hc s xb yb (fun j => by
                                                      exact ratio_tendsto_root_left hΔ 0 N (fun i => N i / 2) p hp hnP
                                                         fun i => by omega  hcountP hNlim hbp hnormP
                                                        (fun i => ⟨j.val, by have := hr i; omega⟩) s  fun i => by change j.val ≤ s; omega ) (ratio_tendsto_root_left hΔ 0 N (fun i => N i / 2) p hp hnP
                                                             fun i => by omega  hcountP hNlim hbp hnormP
                                                            (fun i => ⟨s, by have := hr i; omega⟩) s  fun i => le_rfl )

  
  

  have hρ  := rho_pos hΔ 0
  have hc0 : c ≠ 0 := by linarith
  
  have hsmall := ((by
                     simpa only [hcΔ] using hA₀ : Tendsto (fun i => ratioZeroCoefficient (anisotropy c) c (N i) (q i) (l i) /
      (2 * (N i ))) atTop (𝓝 (c ^ 2 * Real.pi * rho Δ 0))).mul hC).mul (ratio_source_midpoint_limit hΔ hc s N h4 hN p hp hNlim hbp hnormP)
  rw [(by
         field_simp [*] <;> ring :  c ^ 2 * Real.pi * rho Δ 0  *
      ( (((0 : ℕ) ) + 1 / 2) / rho Δ 0  / c ^ 2) * (2 / Real.pi) = 1)] at hsmall

  
  have hpow : Real.exp ( (2 * s + 1 : ℕ)  * Real.log |Δ|) = |Δ| ^ (2 * s + 1) := by
    rw [Real.exp_nat_mul, Real.exp_log (abs_pos.mpr (by linarith))]
  
  rw [(by
         rw [hcΔ, ← hpow, ← Real.exp_neg]
         
         ring : (|anisotropy c| ^ (2 * s + 1))⁻¹ =
      Real.exp (-((2 * s + 1 : ℕ) ) * Real.log |Δ|))] at hB
  have hreal := hsmall.mul (hB.mul ((Real.continuous_exp.tendsto _).comp
                                      (ratio_bulk_log_limit hΔ (2 * s + 1) N h4 hr hN hn p q hp hq hpBE hqBE
                                        hNlim hbp hbq hK hrate hc)))
  have htarget : Real.exp (- (2 * s + 1 : ℕ)  * Real.log |Δ|) *
      Real.exp ( (2 * s + 1 : ℕ)  *
        ∫ x in (-Real.pi)..Real.pi, ratioEllPrime c x * tauCont Δ x) =
      Real.exp (- (2 * s + 1 : ℕ)  * Real.log |Δ| +
         (2 * s + 1 : ℕ)  *
          ∫ x in (-Real.pi)..Real.pi, ratioEllPrime c x * tauCont Δ x) := by
    rw [← Real.exp_add]
  rw [htarget] at hreal
  
  have hcomplex' := by simpa only [one_mul] using  Complex.continuous_ofReal.continuousAt.tendsto.comp hreal 
  apply hcomplex'.congr
  intro i
  dsimp only [Function.comp_def]
  have hf := ratio_odd_quotient_factors hc s (N i) (h4 i)
    (hr i) (hn i)
    (p i) (hp i) (q i) (hq i) (l i) (hzero i)
  rw [hcenter i] at hf
  rw [hf]
  apply congrArg  fun z  =>  z  
  rw [← hcenter i]
  
  
  
  
  dsimp [x, yb, xb]
  field_simp [ by exact_mod_cast  by have := hN i; omega  ,  norm_ne_zero_iff.mpr (ratio_M_ne_zero hc _) ,  norm_ne_zero_iff.mpr (ratio_M_ne_zero hc _) ,  Finset.prod_ne_zero_iff.mpr  fun j hj => norm_ne_zero_iff.mpr (ratio_M_ne_zero hc _)  ]

/-- The odd-branch ratio limit after applying the Section 4 Fourier exponent identity.
The scalar `S` is the limit of the source alternating tanh partial sums. -/
theorem ratio_odd_eigenvalue_limit_fourier (hodd : r % 2 ≠ 0)
    (hrpos : 1 ≤ r) {c : ℝ} (hc : 2 < c) (hcΔ : anisotropy c = Δ) :
    ∃ S : ℝ,
      Tendsto (PottsDiscontinuity.altTanhPartial (lamOf Δ)) atTop (𝓝 S) ∧
      Tendsto (fun i => eigenvalueZero (N i) c (q i)
        ⟨(N i / 2 - r) / 2, Nat.div_lt_self (hn i) Nat.one_lt_two⟩ /
          eigenvalueRegular c (p i)) atTop
        (𝓝 ((Real.exp (-(r : ℝ) * (lamOf Δ + 2 * S)) : ℝ) : ℂ)) := by
  
  
  obtain ⟨S, hS, hW15⟩ := PottsDiscontinuity.fourierRatioExponent
    (lam := lamOf Δ) (r := r) (lamOf_pos hΔ)
  have hparam : -Real.cosh (lamOf Δ) = Δ := by rw [cosh_lamOf hΔ]; ring
  have hlog : Real.log |Δ| = Real.log |-(Real.cosh (lamOf Δ))| := by rw [hparam]
  
  have hExponent : - r  * Real.log |Δ| +
       r  * ∫ x in (-Real.pi)..Real.pi, ratioEllPrime c x * tauCont Δ x =
      - r  * (lamOf Δ + 2 * S) := by
    simpa only [hlog,  ratio_integral_eq_fourier hΔ hc hcΔ ] using hW15
  
  
  exact ⟨S, hS,  by
                   simpa only [hExponent] using  ratio_odd_eigenvalue_limit hΔ r N h4 hr hN hn p q hp hq
                                                   hpBE hqBE hNlim hbp hbq hK hrate hodd hc hcΔ  ⟩

end

end PottsDiscontinuity.Bethe
