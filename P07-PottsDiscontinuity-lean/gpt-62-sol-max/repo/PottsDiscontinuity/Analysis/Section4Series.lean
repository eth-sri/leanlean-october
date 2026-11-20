module

public import Mathlib
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import PottsDiscontinuity.Analysis.Identity44
public import PottsDiscontinuity.Bethe.Prop21Tau
public import PottsDiscontinuity.Bethe.RatioProducts

/-! The punctured logarithmic profile and the expansion of `log (cosh λ)`. -/

@[expose] public section

open Complex Filter MeasureTheory Real Topology Set intervalIntegral

namespace PottsDiscontinuity

/-- The real logarithmic profile in (4.2), with its value at the single singular point
chosen as an `L¹` representative.  Every theorem identifying it with the source profile is
stated away from `α = 0`; its value there does not encode a finite value for the logarithmic
singularity. -/
noncomputable def fourierP (lam α : ℝ) : ℝ :=
  if α = 0 then 0 else
    (1 / 2 : ℝ) * Real.log
      ((Real.cosh (2 * lam) - Real.cos α) / (1 - Real.cos α))

/-- The Möbius expression for `e^{ik(α)}` in unit-circle coordinates. -/
private theorem exp_I_mul_kMap_fraction {lam α : ℝ} (hlam : 0 < lam) :
    Complex.exp (I * (Bethe.kMap lam α : ℂ)) =
      (Complex.exp (I * (α : ℂ)) * (Real.exp lam : ℂ) - 1) /
        ((Real.exp lam : ℂ) - Complex.exp (I * (α : ℂ))) := by
  grind only [Complex.exp_neg, Complex.exp_ne_zero, Bethe.exp_I_mul_kMap_aux]

/-- With `c² = 2 - 2Δ = 2 + 2 cosh λ`, the Bethe factor satisfies the source modulus formula.
This is the explicit algebraic step omitted in the source's phrase “some elementary algebraic
manipulations.” -/
theorem normSq_M_kMap_eq_ratio {lam c α : ℝ} (hlam : 0 < lam)
    (hc : c ^ 2 = 2 + 2 * Real.cosh lam) (hcos : Real.cos α < 1) :
    Complex.normSq (BetheAnsatz.M c (Complex.exp (I * (Bethe.kMap lam α : ℂ)))) =
      (Real.cosh (2 * lam) - Real.cos α) / (1 - Real.cos α) := by
  let e := Real.exp lam
  let E : ℂ := e
  let w := Complex.exp (I * (α : ℂ))
  let z := Complex.exp (I * (Bethe.kMap lam α : ℂ))
  have he : 0 < e := Real.exp_pos _
  have hEc : E ≠ 0 := Complex.ofReal_ne_zero.mpr he.ne'
  have hw : ‖w‖ = 1 := by simp [w]
  have hwR : w.re = Real.cos α := by simp [w, Bethe.exp_I_mul_ofReal, Complex.cos_ofReal_re]
  have hEw : E - w ≠ 0 := Bethe.ofReal_sub_ne_zero (Real.one_lt_exp_iff.2 hlam) hw
  have hnorm (x : ℝ) : Complex.normSq ((x : ℂ) - w) = x ^ 2 + 1 - 2 * x * Real.cos α := by
    rw [Complex.normSq_sub, Complex.normSq_ofReal, Complex.normSq_eq_norm_sq, hw]
    simp [Complex.mul_re, hwR]
    ring
  have h1w : (1 : ℂ) - w ≠ 0 := by
    apply Complex.normSq_pos.mp
    rw [← Complex.ofReal_one, hnorm]
    linarith
  have hcs : (c : ℂ) ^ 2 = (E + 1) ^ 2 / E := by
    have hcs : c ^ 2 = (e + 1) ^ 2 / e := by
      grind only [Real.cosh_eq, Real.exp_neg]
    simpa using congrArg Complex.ofReal hcs
  have hden : 1 - z = (E + 1) * (1 - w) / (E - w) := by
    rw [show z = (w * E - 1) / (E - w) from exp_I_mul_kMap_fraction hlam]
    field_simp
    ring
  have hm : BetheAnsatz.M c z = -((E ^ 2 - w) / (E * (1 - w))) := by
    have hs : E + 1 ≠ 0 := by
      simpa using Complex.ofReal_ne_zero.mpr (show e + 1 ≠ 0 by positivity)
    rw [BetheAnsatz.M, hden, hcs]
    field_simp
    ring
  change Complex.normSq (BetheAnsatz.M c z) = _
  rw [hm, Complex.normSq_neg, Complex.normSq_div, Complex.normSq_mul,
    ← Complex.ofReal_pow, hnorm, Complex.normSq_ofReal, ← Complex.ofReal_one, hnorm]
  rw [Real.cosh_eq, Real.exp_neg, show 2 * lam = lam + lam by ring, Real.exp_add, ← pow_two]
  have hh : 1 - Real.cos α ≠ 0 := (sub_pos.mpr hcos).ne'
  have hh' : 2 - Real.cos α * 2 ≠ 0 := by linarith
  ring_nf
  field_simp
  ring

/-- On the punctured circle, the real profile is exactly the logarithm of the modulus of the
Bethe factor `M(e^{ik(α)})`. -/
theorem fourierP_eq_log_norm {lam c α : ℝ} (hlam : 0 < lam)
    (hc : c ^ 2 = 2 + 2 * Real.cosh lam) (hcos : Real.cos α < 1) :
    fourierP lam α = Real.log
      ‖BetheAnsatz.M c (Complex.exp (I * (Bethe.kMap lam α : ℂ)))‖ := by
  let z : ℂ := BetheAnsatz.M c (Complex.exp (I * (Bethe.kMap lam α : ℂ)))
  have hα : α ≠ 0 := by
    aesop
  have htop : 0 < Real.cosh (2 * lam) - Real.cos α := by
    have h := Real.one_le_cosh (2 * lam)
    linarith
  have hbottom : 0 < 1 - Real.cos α := by linarith
  have hnormSq : ‖z‖ ^ 2 =
      (Real.cosh (2 * lam) - Real.cos α) / (1 - Real.cos α) := by
    rw [← Complex.normSq_eq_norm_sq]
    exact normSq_M_kMap_eq_ratio hlam hc hcos
  unfold fourierP
  rw [ite_eq_right hα]
  change (1 / 2 : ℝ) * Real.log
      ((Real.cosh (2 * lam) - Real.cos α) / (1 - Real.cos α)) = Real.log ‖z‖
  rw [← hnormSq, Real.log_pow]
  ring

/-- Jordan's sine inequality gives a quadratic lower bound for the denominator of `P` on the
fundamental interval. -/
theorem fourier_one_sub_cos_lower {α : ℝ} (hα : α ∈ Icc (-π) π) :
    2 * α ^ 2 / π ^ 2 ≤ 1 - Real.cos α := by
  have hx : |α / 2| ≤ π / 2 := by
    grind
  have hj := Real.mul_abs_le_abs_sin hx
  have hjSq :=
    (sq_le_sq₀ (by positivity) (abs_nonneg _)).2 hj
  have habshalf : |α / 2| = |α| / 2 := by
    simp [abs_div]
  rw [habshalf] at hjSq
  have hsimpl : (2 / π * (|α| / 2)) ^ 2 = α ^ 2 / π ^ 2 := by
    field_simp [Real.pi_ne_zero]
    simp
  rw [hsimpl, sq_abs] at hjSq
  grind only [Real.sin_sq_eq_half_sub]

/-- The punctured derivative of the logarithmic profile, assigned an irrelevant finite value at
the singular point so that it can be used as an interval-integral representative. -/
noncomputable def fourierPPrime (lam α : ℝ) : ℝ :=
  if α = 0 then 0 else
    (1 / 2 : ℝ) *
      (Real.sin α / (Real.cosh (2 * lam) - Real.cos α) -
        Real.sin α / (1 - Real.cos α))

/-- Away from zero, `fourierPPrime` is the classical derivative of `P`. -/
theorem fourierP_hasDerivAt {lam α : ℝ} (hlam : 0 < lam)
    (hα : α ∈ Ioo (-π) π) (hα0 : α ≠ 0) :
    HasDerivAt (fourierP lam) (fourierPPrime lam α) α := by
  have hαcc := Ioo_subset_Icc_self hα
  have hcosLower := fourier_one_sub_cos_lower hαcc
  have hden : 0 < 1 - Real.cos α := by
    have hbound : 0 < 2 * α ^ 2 / π ^ 2 := by positivity
    exact lt_of_lt_of_le hbound hcosLower
  have hcosh : 1 < Real.cosh (2 * lam) :=
    Real.one_lt_cosh.mpr (by positivity)
  have hnum : 0 < Real.cosh (2 * lam) - Real.cos α := by
    linarith [Real.cos_le_one α]
  let u : ℝ → ℝ := fun x => Real.cosh (2 * lam) - Real.cos x
  let v : ℝ → ℝ := fun x => 1 - Real.cos x
  have hu : HasDerivAt u (Real.sin α) α := by
    simpa using (Real.hasDerivAt_cos α).const_sub (Real.cosh (2 * lam))
  have hv : HasDerivAt v (Real.sin α) α := by
    simpa using (Real.hasDerivAt_cos α).const_sub (1 : ℝ)
  have hraw := (hu.div hv hden.ne').log (div_ne_zero hnum.ne' hden.ne')
  have hraw' := hraw.const_mul (1 / 2 : ℝ)
  have hderiv :
      (1 / 2 : ℝ) *
          (((Real.sin α * v α - u α * Real.sin α) / v α ^ 2) / ((u / v) α)) =
        fourierPPrime lam α := by
    simp [fourierPPrime, hα0, u, v]
    field_simp [hden.ne', hnum.ne']
  have hraw'' := hraw'.congr_deriv hderiv
  apply hraw''.congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds hα0] with x hx
  simp [fourierP, u, v, hx]

noncomputable def logCoshExpTerm (lam : ℝ) (m : ℕ) : ℝ :=
  (-1 : ℝ) ^ m / (m : ℝ) * (Real.exp (-2 * lam * m) - 1)

/-- The ordered partial sum of the expansion of `log (cosh λ)`, indexed from `m = 1`. -/
noncomputable def logCoshExpPartial (lam : ℝ) (N : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 N, logCoshExpTerm lam m

/-- Abel's theorem with the power index starting at one. -/
theorem tendsto_abel_succ {f : ℕ → ℝ} {L : ℝ}
    (h : Tendsto (fun N => ∑ n ∈ Finset.range N, f n) atTop (𝓝 L)) :
    Tendsto (fun r => ∑' n, f n * r ^ (n + 1)) (𝓝[<] (1 : ℝ)) (𝓝 L) := by
  have hr : Tendsto (fun r : ℝ => r) (𝓝[<] (1 : ℝ)) (𝓝 1) :=
    tendsto_id.mono_right nhdsWithin_le_nhds
  simpa [← tsum_mul_right, mul_assoc, ← pow_succ] using
      (Real.tendsto_tsum_powerSeries_nhdsWithin_lt h).mul hr

private noncomputable def altHarmonicTerm (n : ℕ) : ℝ := (-1 : ℝ) ^ (n + 1) / ((n : ℝ) + 1)

private theorem hasSum_altLog {x : ℝ} (hx : |x| < 1) :
    HasSum (fun n => altHarmonicTerm n * x ^ (n + 1)) (-Real.log (1 + x)) := by
  have h := Real.hasSum_pow_div_log_of_abs_lt_one (x := -x) (by simpa using hx)
  simp only [sub_neg_eq_add] at h
  exact h.congr_fun fun n => by
    simp [altHarmonicTerm, div_mul_eq_mul_div, ← mul_pow]

private theorem tendsto_altHarmonic :
    Tendsto (fun N => ∑ n ∈ Finset.range N, altHarmonicTerm n) atTop (𝓝 (-Real.log 2)) := by
  have hanti : Antitone (fun n : ℕ => 1 / ((n : ℝ) + 1)) := by
    intro a b hab
    exact one_div_le_one_div_of_le (by positivity) (by gcongr)
  obtain ⟨L, hL⟩ := hanti.tendsto_alternating_series_of_tendsto_zero
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have h : Tendsto (fun N => ∑ n ∈ Finset.range N, altHarmonicTerm n) atTop (𝓝 (-L)) := by
    simpa [altHarmonicTerm, pow_succ, div_eq_mul_inv] using hL.neg
  have hlog : ContinuousAt (fun x : ℝ => -Real.log (1 + x)) 1 := by fun_prop (disch := norm_num)
  have heq : (fun x => ∑' n, altHarmonicTerm n * x ^ (n + 1)) =ᶠ[𝓝[<] (1 : ℝ)]
      (fun x => -Real.log (1 + x)) := by
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with x hx
    exact (hasSum_altLog ((abs_of_pos hx.1).trans_lt hx.2)).tsum_eq
  have hc : Tendsto (fun x : ℝ => -Real.log (1 + x)) (𝓝[<] (1 : ℝ)) (𝓝 (-Real.log 2)) := by
    simpa [ContinuousWithinAt, one_add_one_eq_two] using hlog.continuousWithinAt (s := Iio 1)
  rwa [tendsto_nhds_unique ((tendsto_abel_succ h).congr' heq) hc] at h

/-- The logarithmic expansion is the difference of the log series at
`-exp(-2λ)` and at the alternating harmonic endpoint `-1`. -/
theorem tendsto_logCoshExpPartial {lam : ℝ} (hlam : 0 < lam) :
    Tendsto (logCoshExpPartial lam) atTop (𝓝 (lam - Real.log (Real.cosh lam))) := by
  let x := Real.exp (-2 * lam)
  have hx : |x| < 1 := by simp [x, hlam]
  have h := (hasSum_altLog hx).tendsto_sum_nat.sub tendsto_altHarmonic
  have hc : Real.cosh lam = Real.exp lam * ((1 + x) / 2) := by
    rw [Real.cosh_eq, show Real.exp (-lam) = Real.exp lam * x by
      rw [← Real.exp_add]; congr 1; ring]
    ring
  have hval : -Real.log (1 + x) - -Real.log 2 = lam - Real.log (Real.cosh lam) := by
    rw [hc, Real.log_mul (Real.exp_ne_zero _) (by positivity),
      Real.log_div (by positivity) (by norm_num), Real.log_exp]
    ring
  rw [hval] at h
  apply h.congr
  intro N
  rw [logCoshExpPartial, sum_Icc_one_eq_sum_range, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  simp only [logCoshExpTerm, altHarmonicTerm, Nat.cast_succ]
  rw [show x ^ (n + 1) = Real.exp (-2 * lam * ((n : ℝ) + 1)) by
    dsimp [x]; rw [← Real.exp_nat_mul]; push_cast; congr 1; ring]
  ring

/-! ### The algebra of (4.3) and its ordered partial sums -/

/-- The ordered partial sums of `∑ (-1)^m tanh(λm)/m`. -/
noncomputable def altTanhPartial (lam : ℝ) (N : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 N, (-1 : ℝ) ^ m / (m : ℝ) * Real.tanh ((m : ℝ) * lam)

theorem tanh_exp_identity (x : ℝ) :
    (1 + Real.tanh x) * (Real.exp (-2 * x) - 1) = -2 * Real.tanh x := by
  rw [Real.tanh_eq]
  have he := (Real.exp_pos x).ne'
  have he' := (Real.exp_pos (-x)).ne'
  have hexp : Real.exp (-2 * x) = Real.exp (-x) / Real.exp x := by
    rw [← Real.exp_sub]
    congr 1
    ring
  rw [hexp]
  field_simp [he, he']
  ring

end PottsDiscontinuity
