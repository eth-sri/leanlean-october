module

public import PottsDiscontinuity.Analysis.Section4SourceIntegral
public import PottsDiscontinuity.Bethe.RatioPositiveRoots
public import PottsDiscontinuity.Bethe.CountingDensity
public import PottsDiscontinuity.Bethe.RatioBulkLimit
public import PottsDiscontinuity.Bethe.RatioDensityLimits
public import PottsDiscontinuity.Bethe.RatioPredecessor
public import PottsDiscontinuity.Bethe.RatioProducts
public import PottsDiscontinuity.Bethe.Theorem23Bootstrap
public import PottsDiscontinuity.Bethe.RatioOddQuotient
public import PottsDiscontinuity.Bethe.RatioEvenAlgebra
public import PottsDiscontinuity.BetheAnsatz.Parity

/-! # The eigenvalue ratio limit -/

@[expose] public section

open Set Filter MeasureTheory Finset
open scoped Topology BigOperators

namespace PottsDiscontinuity.Bethe

open BetheAnsatz

/-- The regular logarithmic derivative agrees with the source-coordinate derivative
`fourierEllPrime` of the Section 4 Fourier identities
when the anisotropy parameters agree. -/
theorem ratio_ellPrime_eq_fourierEllPrime {Δ c x : ℝ} (hΔ : Δ < -1)
    (hc : 2 < c) (hcΔ : anisotropy c = Δ)
    (hx : x ∈ Ioo (-Real.pi) Real.pi) :
    ratioEllPrime c x = PottsDiscontinuity.fourierEllPrime (lamOf Δ) x := by
  have hlam : 0 < lamOf Δ := lamOf_pos hΔ
  have hcosh : Real.cosh (lamOf Δ) = -Δ := cosh_lamOf hΔ
  have hc2 : c ^ 2 = 2 + 2 * Real.cosh (lamOf Δ) := by
    unfold anisotropy at hcΔ
    nlinarith
  by_cases hx0 : x = 0
  · subst x
    simp [ratioEllPrime, PottsDiscontinuity.fourierEllPrime]
  have hfun : ratioEll c =ᶠ[𝓝 x] PottsDiscontinuity.fourierEll (lamOf Δ) := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2, eventually_ne_nhds hx0] with y hy hy0
    have h := PottsDiscontinuity.fourierEll_eq_log_norm hlam hc2 hy hy0
    simpa [ratioEll, BetheAnsatz.z] using h.symm
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
  apply intervalIntegral.integral_congr_Ioo_of_le (neg_le_self Real.pi_nonneg)
  intro x hx
  dsimp only
  simp [ratio_ellPrime_eq_fourierEllPrime hΔ hc hcΔ hx, cosh_lamOf hΔ, tau_eq_tauCont hΔ hx]

theorem even_sector_iff {N r : ℕ} (h4 : 4 ∣ N) (hr : r ≤ N / 2) :
    Even (N / 2 - r) ↔ r % 2 = 0 := by
  obtain ⟨k, rfl⟩ := h4
  rw [Nat.even_iff]
  omega

local notation "J" => Icc (-Real.pi) Real.pi

private theorem tendsto_of_rate {ι : Type*} {l : Filter ι} {a C : ℝ} {N f g : ι → ℝ}
    (hN : Tendsto N l atTop) (hg : Tendsto g l (𝓝 a))
    (h : ∀ᶠ i in l, |f i - g i| ≤ C / N i) : Tendsto f l (𝓝 a) := by
  have hd : Tendsto (fun i => f i - g i) l (𝓝 0) := squeeze_zero_norm'
    (h.mono fun i hi => by assumption) (tendsto_const_nhds.div_atTop hN)
  simpa using hd.add hg

private theorem large_interval {x : ℝ} (hx : x ∈ J) : x ∈ Icc (-(3 * Real.pi)) (3 * Real.pi) := by
  grind

section

variable {Δ : ℝ} (hΔ : Δ < -1) (r : ℕ) (N : ℕ → ℕ) (h4 : ∀ i, 4 ∣ N i)
    (hr : ∀ i, r ≤ N i / 2) (hN : ∀ i, 0 < N i) (hn : ∀ i, 0 < N i / 2 - r)
    (p : ∀ i, Fin (N i / 2) → ℝ) (q : ∀ i, Fin (N i / 2 - r) → ℝ)
    (hp : ∀ i, p i ∈ S_n (N i / 2)) (hq : ∀ i, q i ∈ S_n (N i / 2 - r))
    (hpBE : ∀ i, DiscreteBetheEquation Δ (N i) (N i / 2) (p i))
    (hqBE : ∀ i, DiscreteBetheEquation Δ (N i) (N i / 2 - r) (q i))
    (hNlim : Tendsto (fun i => (N i : ℝ)) atTop atTop)
    {K : ℝ}
    (hrate : ∀ᶠ i in atTop,
      densityNorm Δ (rootStepError Δ (N i) (p i) (half_pos_of_half_sub_pos N r hn i)) ≤ K / N i ∧
      densityNorm Δ (rootStepError Δ (N i) (q i) (hn i)) ≤ K / N i)


include hΔ h4 hr hN hp hq hpBE hqBE hNlim hrate

/-- The logarithm of the source bulk factor, for both parity clauses of
the aligned roots. All density/Bethe premises are exactly those of Theorem 2.9. -/
private theorem ratio_bulk_limits {c : ℝ} (hc : 2 < c) :
    Tendsto (fun i => ∑ j, (ratioEll c (q i j) -
      ratioEll c (alignedRoot (N i) r (hr i) (p i) j))) atTop
      (𝓝 ((r : ℝ) * ∫ x in (-Real.pi)..Real.pi, ratioEllPrime c x * tauCont Δ x)) ∧
      Tendsto (fun i => betheCountingDerivative Δ (N i) (N i / 2 - r) (q i) 0) atTop (𝓝 (rho Δ 0)) ∧
      Nonempty (FullRoots Δ N p) := by
  have heP := ratio_density_error_of_rate hΔ N _
    (fun i => rootStepDensity_error_bddAbove hΔ (N := N i) (p i) (half_pos_of_half_sub_pos N r hn i))
    (hrate.mono fun _ h => h.1)
  have heQ := ratio_density_error_of_rate hΔ N _
    (fun i => rootStepDensity_error_bddAbove hΔ (N := N i) (q i) (hn i))
    (hrate.mono fun _ h => h.2)
  have hcount (i : ℕ) : N i = 2 * (N i / 2) := by obtain ⟨z, hz⟩ := h4 i; omega
  have hcountq (i : ℕ) : N i = 2 * (N i / 2 - r + r) := by have := hr i; have := hcount i; omega
  obtain ⟨L, hL, hLip⟩ := exists_uniform_countingDerivative_lipschitz hΔ
  let Dp (i : ℕ) := betheCountingDerivative Δ (N i) (N i / 2) (p i)
  let Dq (i : ℕ) := betheCountingDerivative Δ (N i) (N i / 2 - r) (q i)
  have hLp (i : ℕ) := hLip Δ le_rfl (N i) _ (hN i) (p i) (hp i) (two_mul_half_le N i)
  have hLq (i : ℕ) := hLip Δ le_rfl (N i) _ (hN i) (q i) (hq i) (two_mul_half_sub_le N r i)
  obtain ⟨_, EP, _, happroxP⟩ := eventually_countingDerivative_approx hΔ 0 N _ p hp
    (half_pos_of_half_sub_pos N r hn) (by simpa using hcount) hpBE hNlim hL.le hLp heP
  obtain ⟨DQ, EQ, hDQ, happroxQ⟩ := eventually_countingDerivative_approx hΔ r N _ q hq hn hcountq hqBE hNlim hL.le hLq heQ
  obtain ⟨m₀, hm₀, hrho⟩ := rho_uniform_lower_bound hΔ
  let m := m₀ / 2
  have hm : 0 < m := by positivity
  obtain ⟨U₀, hU₀⟩ := rho_uniform_upper_bound hΔ
  let U := U₀ + 1
  have hU : 0 ≤ U := by linarith [(rho_pos hΔ 0).trans_le (hU₀ Δ le_rfl 0)]
  have hbounds {d : ℕ → ℝ → ℝ} {A : ℝ} (hd : ∀ᶠ i in atTop, ∀ x ∈ J, |d i x - rho Δ x| ≤ A / N i) :
      ∀ᶠ i in atTop, ∀ x ∈ J, m ≤ d i x ∧ d i x ≤ U := by
    filter_upwards [hd, (tendsto_const_nhds.div_atTop hNlim : Tendsto (fun i => A / (N i : ℝ)) atTop (𝓝 0)).eventually
      (gt_mem_nhds (lt_min hm zero_lt_one))] with i hi he x hx
    obtain ⟨h₁,h₂⟩ := abs_le.mp (hi x hx)
    have he₁ : A / (N i : ℝ) < m₀ / 2 := he.trans_le (min_le_left m 1)
    dsimp [m, U]
    constructor <;> linarith [hrho Δ le_rfl x hx, hU₀ Δ le_rfl x, he₁,
      he.trans_le (min_le_right m 1)]
  have hP := happroxP.mono fun _ h => h.2
  have hQ := happroxQ.mono fun _ h => h.2
  have hlowP := hbounds hP
  have hlowQ := hbounds hQ
  have hρpoint (x : ℝ) (hx : x ∈ J) : Tendsto (fun i => Dq i x) atTop (𝓝 (rho Δ x)) :=
    tendsto_of_rate hNlim tendsto_const_nhds (hQ.mono fun _ h => h x hx)
  refine ⟨?_, hρpoint 0 (by simp [Real.pi_nonneg]),
    ⟨⟨hΔ, h4, hN, hp, hpBE, hNlim, m, U, EP, hm, hlowP, hP⟩⟩⟩
  obtain ⟨C, hC, hcountShift⟩ := countingShift_estimates hΔ r hm hL.le
  obtain ⟨T, hT, hτ⟩ := exists_tauCont_abs_le_mul hΔ
  let H (i : ℕ) := countingShift Δ (N i) (p i) (q i)
  have hH : ∀ᶠ i in atTop, ∀ x ∈ J, |H i x + (r : ℝ) * tauCont Δ x| ≤ C / N i := by
    filter_upwards [hlowP, hlowQ] with i hp' hq'
    exact hcountShift (hn i) (hcount i) (by have := hr i; omega) (hp i) (hq i) (hpBE i) (hqBE i)
      (fun x hx => ⟨(hp' x hx).1, (hq' x hx).1⟩)
      (fun x hx y hy => ⟨hLp i x (large_interval hx) y (large_interval hy), hLq i x (large_interval hx) y (large_interval hy)⟩)
  let G := ((r : ℝ) * T + 2 * (C + L / m ^ 2) * U) / m
  have hG : 0 ≤ G := by positivity
  let k : ℕ → ℕ := fun i => N i / 2 - r
  let a (i : ℕ) := alignedRoot (N i) r (hr i) (p i)
  let d : ℕ → ℝ := fun i => DQ / N i
  have hpoint (x : ℝ) (hx : x ∈ Ioo (-Real.pi) Real.pi) :=
    ratio_rootIndex_tendsto k hn q hq d (tendsto_const_nhds.div_atTop hNlim)
      (fun i => div_nonneg hDQ (Nat.cast_nonneg _)) (happroxQ.mono fun _ h => h.1) hx
  have hfinite : ∀ᶠ i in atTop, ∀ j,
      let S := (N i : ℝ) * (q i j - a i j)
      |S| ≤ G * |q i j| ∧
        ∃ t ∈ uIcc (q i j) (a i j), |Dp i t * S + H i (q i j)| ≤ (L / m ^ 2) / N i := by
    filter_upwards [hlowP, hlowQ, hH] with i hp' hq' hh j
    exact bethe_alignedShift_control hΔ (hN i) (hr i) (hp i) (hq i) (hpBE i) (hqBE i) hm hL.le hC
      (fun x hx => ⟨(hp' x hx).1, (hq' x hx).1⟩) (fun x hx => (hq' x hx).2)
      (fun x hx y hy => hLp i x (large_interval hx) y (large_interval hy))
      hh hτ j
  have hshift := hfinite.mono fun i hi j => (hi j).1
  have hupper : ∀ᶠ i in atTop, ∀ x ∈ J, |Dq i x| ≤ U := hlowQ.mono fun _ h x hx =>
    (abs_of_pos (hm.trans_le (h x hx).1)).trans_le (h x hx).2
  have hpred (x : ℝ) (hx : x ∈ Ioo (-Real.pi) Real.pi) (_hx0 : x ≠ 0) :
      Tendsto (fun i => (N i : ℝ) *
        (q i (ratioRootIndex (hn i) (q i) x) - a i (ratioRootIndex (hn i) (q i) x)))
        atTop (𝓝 ((r : ℝ) * tauCont Δ x / rho Δ x)) := by
    classical
    let j (i : ℕ) := ratioRootIndex (hn i) (q i) x
    let X (i : ℕ) := q i (j i)
    let Y (i : ℕ) := a i (j i)
    let S (i : ℕ) := (N i : ℝ) * (X i - Y i)
    have hX (i : ℕ) : X i ∈ J := Ioo_subset_Icc_self ((hq i).1 (j i))
    have hY (i : ℕ) : Y i ∈ J := Ioo_subset_Icc_self (ratio_alignedRoot_mem_Ioo (hr i) (hp i) _)
    have hxlim : Tendsto X atTop (𝓝 x) := (hpoint x hx).1
    have hylim : Tendsto Y atTop (𝓝 x) := by
      apply tendsto_of_rate hNlim hxlim (C := G * Real.pi)
      filter_upwards [hshift] with i hi
      have hn' : (0 : ℝ) < N i := by exact_mod_cast hN i
      have hs' := (hi (j i)).trans (mul_le_mul_of_nonneg_left (abs_le.mpr (hX i)) hG)
      change |S i| ≤ _ at hs'
      dsimp only [S] at hs'
      rw [abs_mul, abs_of_pos hn', abs_sub_comm] at hs'
      exact (le_div_iff₀' hn').mpr hs'
    obtain ⟨t, ht⟩ := (hfinite.mono fun i hi => (hi (j i)).2).choice
    have htJ := ht.mono fun i hi => ordConnected_Icc.uIcc_subset (hX i) (hY i) hi.1
    have htlim := (hxlim.uIcc hylim).of_smallSets (ht.mono fun _ hi => hi.1)
    have hDlim : Tendsto (fun i => Dp i (t i)) atTop (𝓝 (rho Δ x)) := by
      apply tendsto_of_rate hNlim ((continuous_rho hΔ).continuousAt.tendsto.comp htlim)
      filter_upwards [hP, htJ] with i hi hj
      exact hi (t i) hj
    have hP : Tendsto (fun i => Dp i (t i) * S i) atTop (𝓝 ((r : ℝ) * tauCont Δ x)) := by
      apply tendsto_of_rate hNlim ((tendsto_const_nhds (x := (r : ℝ))).mul
        ((continuous_tauCont hΔ).continuousAt.tendsto.comp hxlim)) (C := L / m ^ 2 + C)
      filter_upwards [ht, hH] with i hi hh
      rw [add_div]
      simpa using
              (abs_sub (Dp i (t i) * S i + H i (X i)) ((r : ℝ) * tauCont Δ (X i) + H i (X i))).trans
                (add_le_add hi.2 (by simpa only [add_comm] using hh (X i) (hX i)))
    apply (hP.div hDlim (rho_pos hΔ x).ne').congr'
    filter_upwards [hlowP, htJ] with i hi ht'
    exact mul_div_cancel_left₀ (S i) (hm.trans_le (hi (t i) ht').1).ne'
  have ht := ratio_logsum_tendsto_of_geometry hΔ hc hG hU N k hN hn q a hq
    (fun i j => ratio_alignedRoot_mem_Ioo (hr i) (hp i) j) hqBE hNlim hshift hupper
    (rho Δ) (fun x => (r : ℝ) * tauCont Δ x / rho Δ x) (fun x hx => hρpoint x (Ioo_subset_Icc_self hx))
    (fun x hx => (hpoint x hx).2) (fun x hx => (hpoint x hx).1) hpred
  have hInt : (∫ x in Icc (-Real.pi) Real.pi,
      ratioEllPrime c x * ((r : ℝ) * tauCont Δ x / rho Δ x) * rho Δ x) =
      (r : ℝ) * ∫ x in (-Real.pi)..Real.pi, ratioEllPrime c x * tauCont Δ x := by
    rw [intervalIntegral.integral_of_le (neg_le_self Real.pi_nonneg), ← integral_Icc_eq_integral_Ioc,
      ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Icc fun x _ => ?_
    field_simp [(rho_pos hΔ x).ne']
  simpa only [a, hInt] using ht

/-- Both parity limits share the bulk term and the Fourier exponent. -/
theorem ratio_eigenvalue_limit_fourier {c : ℝ} (hc : 2 < c) (hcΔ : anisotropy c = Δ) :
    ∃ S : ℝ, Tendsto (PottsDiscontinuity.altTanhPartial (lamOf Δ)) atTop (𝓝 S) ∧
      Tendsto (fun i => parityEigenvalue (N i) c (q i) / eigenvalueRegular c (p i)) atTop
        (𝓝 ((Real.exp (-(r : ℝ) * (lamOf Δ + 2 * S)) : ℝ) : ℂ)) := by
  obtain ⟨S, hS, hExp⟩ := PottsDiscontinuity.fourierRatioExponent
    (r := (r : ℝ)) (lamOf_pos hΔ)
  rw [← ratio_integral_eq_fourier hΔ hc hcΔ, neg_eq_iff_eq_neg.mpr (cosh_lamOf hΔ)] at hExp
  refine ⟨S, hS, ?_⟩
  rw [← hExp]
  obtain ⟨hbulk₀, hD, ⟨R⟩⟩ := ratio_bulk_limits hΔ r N h4 hr hN hn p q hp hq hpBE hqBE hNlim hrate hc
  have hbulk := (Real.continuous_exp.tendsto _).comp hbulk₀
  have hnormP := ratio_densityNorm_tendsto_of_rate N hNlim _ (hrate.mono fun i hi => hi.1)
  have hnP (i : ℕ) : 0 < N i / 2 := half_pos_of_half_sub_pos N r hn i
  have hcountP (i : ℕ) : N i = 2 * (N i / 2 + 0) := by obtain ⟨k, hk⟩ := h4 i; omega
  have hleft (j : ℕ) (hj : j ≤ r) : Tendsto
      (fun i => p i ⟨j, by have := hr i; have := hn i; omega⟩) atTop (𝓝 (-Real.pi)) :=
    ratio_tendsto_root_left hΔ 0 N (fun i => N i / 2) p hp hnP (two_mul_half_le N)
      hcountP hNlim (fun i => rootStepDensity_error_bddAbove hΔ _ (hnP i)) hnormP _ r (fun _ => hj)
  have hBexp : (|anisotropy c| ^ r)⁻¹ = Real.exp (-(r : ℝ) * Real.log |Δ|) := by
    rw [hcΔ, neg_mul, Real.exp_neg, Real.exp_nat_mul, Real.exp_log (abs_pos.mpr (by linarith))]
  have hexp : Real.exp (-(r : ℝ) * Real.log |Δ|) *
      Real.exp ((r : ℝ) * ∫ x in (-Real.pi)..Real.pi, ratioEllPrime c x * tauCont Δ x) =
      Real.exp (-(r : ℝ) * Real.log |Δ| +
        (r : ℝ) * ∫ x in (-Real.pi)..Real.pi, ratioEllPrime c x * tauCont Δ x) :=
    (Real.exp_add _ _).symm
  by_cases hpar : r % 2 = 0
  · let s := r / 2
    have hcount (i : ℕ) : s + (N i / 2 - r) + s = N i / 2 := by
      dsimp [s]
      have := hr i
      omega
    have halign (i : ℕ) (j : Fin (N i / 2 - r)) :
        alignedRoot (N i) r (hr i) (p i) j = p i ⟨j.val + s, by omega⟩ := by
      simp [alignedRoot, hpar, s]
    simp only [Function.comp_def, Finset.sum_sub_distrib, Real.exp_sub, ratio_exp_sum_ell hc,
      ← Finset.prod_div_distrib, halign] at hbulk
    have hboundary := ratio_even_boundary_tendsto hc s
      (fun i j => p i ⟨j.val, by have := hcount i; omega⟩)
      (fun j => hleft j.val (by omega))
    have hs2 : s * 2 = r := by omega
    rw [← pow_mul, hs2, hBexp] at hboundary
    have hreal := hboundary.mul hbulk
    rw [hexp] at hreal
    refine (Complex.continuous_ofReal.continuousAt.tendsto.comp hreal).congr fun i => ?_
    rw [parityEigenvalue, dite_eq_left ((even_sector_iff (h4 i) (hr i)).mpr hpar)]
    rw [ratio_even_quotient_split (hcount i) hc (hp i) (hq i)]
    exact congrArg (fun x : ℝ => (x : ℂ)) (mul_comm _ _)
  · obtain ⟨s, hrs⟩ : ∃ s : ℕ, r = 2 * s + 1 := ⟨r / 2, by omega⟩
    subst r
    let n : ℕ → ℕ := fun i => N i / 2 - (2 * s + 1)
    have hnQ (i : ℕ) : 0 < n i := hn i
    let l (i : ℕ) : Fin (n i) := ⟨n i / 2, Nat.div_lt_self (hnQ i) Nat.one_lt_two⟩
    have hzero (i : ℕ) : q i (l i) = 0 := by
      have hnodd : n i = 2 * (n i / 2) + 1 := by
        dsimp [n]
        obtain ⟨k, hk⟩ := h4 i
        have := hr i
        omega
      exact odd_middle_root_zero hnodd (q i) (hq i).2.2

    have hA₀ := ratio_odd_A_tendsto c N n q hN hNlim hD l hzero
    have hA : Tendsto (fun i => ratioZeroCoefficient (anisotropy c) c (N i) (q i) (l i) /
        (2 * (N i : ℝ))) atTop (𝓝 (c ^ 2 * Real.pi * rho Δ 0)) := by
      simpa [hcΔ] using hA₀

    have hfirstBound (i : ℕ) : 0 < N i / 4 := by
      obtain ⟨m, hm⟩ := h4 i
      have := hN i
      omega
    have hC₀ := ratio_scaled_inverse_norm_tendsto hc (fun i => (N i : ℝ)) (R.rank 0)
      (R.rank_mem 0) (R.rank_pos 0) (R.rank_limits 0).1 (R.rank_limits 0).2
    have hC := hC₀.congr fun i => by rw [R.rank_eq (hfirstBound i)]

    have hB := ratio_odd_boundary_tendsto hc s
      (fun i j => p i ⟨j.val, by have := hr i; omega⟩) (fun i => p i ⟨s, by have := hr i; omega⟩)
      (fun j => hleft j.val (by omega)) (hleft s (by omega))
    have hW := ratio_source_midpoint_limit hc s R
    have hρ : 0 < rho Δ 0 := rho_pos hΔ 0
    have hc0 : c ≠ 0 := by linarith
    have hsmallValue : (c ^ 2 * Real.pi * rho Δ 0) *
        (((((0 : ℕ) : ℝ) + 1 / 2) / rho Δ 0) / c ^ 2) * (2 / Real.pi) = 1 := by
      field_simp [hρ.ne', hc0, Real.pi_ne_zero]
      ring
    have hsmall := (hA.mul hC).mul hW
    rw [hsmallValue] at hsmall

    rw [hBexp] at hB
    have hreal := hsmall.mul (hB.mul hbulk)
    rw [hexp, one_mul] at hreal
    refine (Complex.continuous_ofReal.continuousAt.tendsto.comp hreal).congr fun i => ?_
    rw [parityEigenvalue, dite_eq_right (fun h => hpar ((even_sector_iff (h4 i) (hr i)).mp h))]
    simp only [oddCenter]
    rw [show (⟨(N i / 2 - (2 * s + 1)) / 2, _⟩ : Fin (n i)) = l i from rfl,
      ratio_odd_quotient_factors hc s (N i) (h4 i) (hr i) (hn i) (p i) (hp i) (q i) (hq i) (l i) (hzero i)]
    dsimp only [Function.comp_def]
    exact congrArg (fun x : ℝ => (x : ℂ)) (by ring)

end

end PottsDiscontinuity.Bethe
