/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ODE.ConnectionEulerEndpoint
public import DOZZ.Hypergeom.Series
public import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric
public import Mathlib.RingTheory.Binomial
import Mathlib.Analysis.Analytic.Binomial

/-! Coefficient identities for matching Euler's binomial expansion with the Gauss series. -/

@[expose] public section

namespace DOZZ.Proofs

open Set MeasureTheory

/-- Evaluating the rising factorial commutes with the real-to-complex cast. -/
theorem ofReal_ascPochhammer_eval (x : ℝ) (n : ℕ) :
    Complex.ofReal ((ascPochhammer ℝ n).eval x) =
      (ascPochhammer ℂ n).eval (x : ℂ) := by
  calc
    Complex.ofReal ((ascPochhammer ℝ n).eval x) =
        ((ascPochhammer ℝ n).map Complex.ofRealHom).eval (x : ℂ) := by
          exact Eq.symm (Polynomial.eval_map_apply Complex.ofRealHom x)
    _ = (ascPochhammer ℂ n).eval (x : ℂ) := by
      rw [ascPochhammer_map]

/-- Gamma's natural shift formula, stated over positive real arguments. -/
theorem realGamma_add_nat_div_Gamma_eq (x : ℝ) (n : ℕ) (hx : 0 < x) :
    Real.Gamma (x + n) / Real.Gamma x = (ascPochhammer ℝ n).eval x := by
  have hcx : ∀ k : ℕ, (x : ℂ) ≠ -(k : ℂ) := by
    intro k hk
    have hxk : x = -(k : ℝ) := by exact_mod_cast hk
    linarith
  have h := Complex.Gamma_add_nat_div_Gamma_eq (n := n) (x : ℂ) hcx
  rw [show (x : ℂ) + (n : ℂ) = ((x + n : ℝ) : ℂ) by push_cast; ring,
    Complex.Gamma_ofReal, Complex.Gamma_ofReal,
    ← ofReal_ascPochhammer_eval x n] at h
  assumption_mod_cast

/-- Scaling the beta moment with its Euler normalization gives the ratio of rising factorials. -/
theorem realEulerBetaMoment_scaled (b c : ℝ) (n : ℕ)
    (hb : 0 < b) (hcb : 0 < c - b) :
    (Real.Gamma c / (Real.Gamma b * Real.Gamma (c - b))) *
        (∫ t : ℝ in Ioc 0 1,
          t ^ (b + n - 1) * (1 - t) ^ (c - b - 1)) =
      (ascPochhammer ℝ n).eval b / (ascPochhammer ℝ n).eval c := by
  have hc : 0 < c := by linarith
  have hbn : 0 < b + (n : ℝ) := by positivity
  
  have hbeta := realEulerBetaIntegral_eq_gamma_ratio (b + n) (c - b) hbn hcb
  have hbeta' :
      (∫ t : ℝ in Ioc 0 1,
        t ^ (b + n - 1) * (1 - t) ^ (c - b - 1)) =
        Real.Gamma (b + n) * Real.Gamma (c - b) / Real.Gamma (c + n) := by
    grind
  have hshiftB := realGamma_add_nat_div_Gamma_eq b n hb
  have hshiftC := realGamma_add_nat_div_Gamma_eq c n hc
  have hΓb  := Real.Gamma_pos_of_pos hb
  have hΓq  := Real.Gamma_pos_of_pos hcb
  grind

/-- A positive argument gives positive rising factorials. -/
theorem realAscPochhammer_eval_pos {x : ℝ} (hx : 0 < x) (n : ℕ) :
    0 < (ascPochhammer ℝ n).eval x := by
  exact ascPochhammer_pos n x hx

/-- The real form of Mathlib's ordinary Gauss-series coefficient. -/
noncomputable def realOrdinaryHypergeometricCoefficient (a b c : ℝ) (n : ℕ) : ℝ :=
  ((n.factorial : ℝ)⁻¹) * (ascPochhammer ℝ n).eval a *
    (ascPochhammer ℝ n).eval b * ((ascPochhammer ℝ n).eval c)⁻¹

/-- The binomial coefficient in `(1-x)^{-a}` is the rising-Pochhammer coefficient. -/
theorem realBinomialCoefficient_eq_ascPochhammer (a : ℝ) (n : ℕ) :
    Ring.choose (a + n - 1) n =
      (ascPochhammer ℝ n).eval a / (n.factorial : ℝ) := by
  rw [Ring.choose_eq_smul, Polynomial.descPochhammer_smeval_eq_ascPochhammer,
    Polynomial.ascPochhammer_smeval_eq_eval]
  ring

variable (a b c x : ℝ) (n : ℕ)

include a b c x n in
/-- The real binomial terms after multiplication by the Euler beta weight. -/
noncomputable def realGaussEulerBinomialTerm  (t : ℝ) : ℝ :=
  Ring.choose (a + n - 1) n * (x * t) ^ n *
    t ^ (b - 1) * (1 - t) ^ (c - b - 1)

include a b c x n in
/-- Each integrated binomial term equals the corresponding normalized ordinary Gauss-series term. -/
theorem realGaussEulerBinomialTerm_integral 
    (ha : 0 < a) (hb : 0 < b) (hcb : 0 < c - b) (hx : 0 < x) :
    (Real.Gamma c / (Real.Gamma b * Real.Gamma (c - b))) *
        (∫ t : ℝ in Ioc 0 1, realGaussEulerBinomialTerm a b c x n t) =
      realOrdinaryHypergeometricCoefficient a b c n * x ^ n := by
  let s : Set ℝ := Ioc 0 1
  let w : ℝ → ℝ := fun t => t ^ (b + n - 1) * (1 - t) ^ (c - b - 1)
  let C  := Ring.choose (a + n - 1) n * x ^ n
  have hchoose : 0 < Ring.choose (a + n - 1) n := by
    rw [realBinomialCoefficient_eq_ascPochhammer]
    exact div_pos (realAscPochhammer_eval_pos ha n) (by positivity)
  have hweight : IntegrableOn w s := by
    exact (realEulerBetaWeight_integrable (b + n) (c - b) (by positivity) hcb)
  have hpowEq :
      realGaussEulerBinomialTerm a b c x n =ᵐ[volume.restrict s]
        fun t => C * w t := by
    filter_upwards [ae_restrict_mem (by simp [s]),
      ae_restrict_of_ae (volume.ae_ne (0 : ℝ))] with t ht ht0
    have htpos  := ht.1
    have hpow  := mul_pow x t n
    have hrpowNat  := (Real.rpow_natCast t n).symm
    have hrpowAdd : t ^ (b - 1) * t ^ (n : ℝ) = t ^ (b + n - 1) := by
      rw [← Real.rpow_add htpos]
      congr 1
      ring
    dsimp [realGaussEulerBinomialTerm, C, w]
    grind
  have hterm_int : IntegrableOn
      (realGaussEulerBinomialTerm a b c x n) s := by
    have hC : IntegrableOn (fun t => C * w t) s := hweight.const_mul C
    exact hC.congr_fun_ae hpowEq.symm
  have hterm_integral :
      (∫ t : ℝ in s, realGaussEulerBinomialTerm a b c x n t) =
        C * (∫ t : ℝ in s, w t) := by
    calc
      _ = ∫ t : ℝ in s, C * w t := integral_congr_ae hpowEq
      _ = C * (∫ t : ℝ in s, w t) := integral_const_mul _ _
  have hscaled := realEulerBetaMoment_scaled b c n hb hcb
  have hPochC  :=
    (realAscPochhammer_eval_pos (by linarith : 0 < c) n).ne'
  rw [hterm_integral]
  dsimp [C]
  calc
    _ = Ring.choose (a + n - 1) n * x ^ n *
        ((Real.Gamma c / (Real.Gamma b * Real.Gamma (c - b))) *
          (∫ t : ℝ in Ioc 0 1, w t)) := by ring
    _ = Ring.choose (a + n - 1) n * x ^ n *
        ((ascPochhammer ℝ n).eval b / (ascPochhammer ℝ n).eval c) := by
          rw [hscaled]
    _ = realOrdinaryHypergeometricCoefficient a b c n * x ^ n := by
          rw [realBinomialCoefficient_eq_ascPochhammer]
          dsimp [realOrdinaryHypergeometricCoefficient]
          field_simp [hPochC]

include a b c x n in
/-- Every real Euler binomial term is integrable against the beta density. -/
theorem realGaussEulerBinomialTerm_integrableOn 
    (hb : 0 < b) (hcb : 0 < c - b) :
    IntegrableOn (realGaussEulerBinomialTerm a b c x n) (Ioc 0 1) := by
  let s : Set ℝ := Ioc 0 1
  let w : ℝ → ℝ := fun t => t ^ (b + n - 1) * (1 - t) ^ (c - b - 1)
  let C  := Ring.choose (a + n - 1) n * x ^ n
  have hweight : IntegrableOn w s := by
    exact (realEulerBetaWeight_integrable (b + n) (c - b) (by positivity) hcb)
  have hpowEq :
      realGaussEulerBinomialTerm a b c x n =ᵐ[volume.restrict s]
        fun t => C * w t := by
    filter_upwards [ae_restrict_mem (by simp [s]),
      ae_restrict_of_ae (volume.ae_ne (0 : ℝ))] with t ht ht0
    have htpos  := ht.1
    have hpow  := mul_pow x t n
    have hrpowNat  := (Real.rpow_natCast t n).symm
    have hrpowAdd : t ^ (b - 1) * t ^ (n : ℝ) = t ^ (b + n - 1) := by
      rw [← Real.rpow_add htpos]
      congr 1
      ring
    dsimp [realGaussEulerBinomialTerm, C, w]
    grind
  have hCw : IntegrableOn (fun t => C * w t) s := hweight.const_mul C
  exact hCw.congr_fun_ae hpowEq.symm

include a b c x n in
/-- Under positive parameters, each real Euler binomial term is nonnegative on the beta interval. -/
theorem realGaussEulerBinomialTerm_nonneg  (t : ℝ)
    (ha : 0 < a) (hx : 0 < x) (ht : t ∈ Ioc 0 1) :
    0 ≤ realGaussEulerBinomialTerm a b c x n t := by
  have hchoose : 0 ≤ Ring.choose (a + n - 1) n := by
    rw [realBinomialCoefficient_eq_ascPochhammer]
    exact le_of_lt (div_pos (realAscPochhammer_eval_pos ha n) (by positivity))
  have hxt  := mul_nonneg hx.le ht.1.le
  have htPow : 0 ≤ t ^ (b - 1) := Real.rpow_nonneg ht.1.le _
  have h1t  := sub_nonneg.mpr ht.2
  
  dsimp [realGaussEulerBinomialTerm]
  positivity

/-- Pointwise, the real Euler kernel is the integral of the binomial expansion against its beta
weight. -/
theorem realGaussEulerBinomialTerm_hasSum (a b c x t : ℝ)
    (hx : 0 < x) (hx1 : x < 1) (ht : t ∈ Ioc 0 1) :
    HasSum (fun n => realGaussEulerBinomialTerm a b c x n t)
      (t ^ (b - 1) * (1 - t) ^ (c - b - 1) * (1 - x * t) ^ (-a)) := by
  have ht0  := ht.1
  have ht1  := ht.2
  have hu0  := mul_nonneg hx.le ht0.le
  have hu1 : x * t < 1 := by nlinarith
  have huNorm : ‖x * t‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hu0]
    exact hu1
  have huBall : (x * t : ℝ) ∈ Metric.eball (0 : ℝ) 1 := by
    have hnn : ‖(x * t : ℝ)‖₊ < 1 := by exact_mod_cast huNorm
    simpa [Metric.mem_eball, edist_eq_enorm_sub, enorm_eq_nnnorm, dist_zero_right] using
      (ENNReal.coe_lt_coe.mpr hnn)
  have hbin :=
    (Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero a).hasSum huBall
  have hbin' : HasSum
      (fun n : ℕ => Ring.choose (a + n - 1) n * (x * t) ^ n)
      (1 / (1 - x * t) ^ a) := by
    convert hbin using 1
    · funext (n : ℕ)
      simp [smul_eq_mul]; ring
    · simp
  let W  := t ^ (b - 1) * (1 - t) ^ (c - b - 1)
  have hweighted := hbin'.mul_left W
  have hterms : HasSum (fun n => realGaussEulerBinomialTerm a b c x n t)
      (W * (1 / (1 - x * t) ^ a)) := by
    apply HasSum.congr_fun hweighted
    intro n
    dsimp [realGaussEulerBinomialTerm, W]
    ring
  have hbase : 0 ≤ 1 - x * t := by linarith
  have hpow := Real.rpow_neg hbase a
  aesop

/-- Casting the real coefficient gives Mathlib's complex ordinary Gauss coefficient. -/
theorem ofReal_realOrdinaryHypergeometricCoefficient (a b c : ℝ) (n : ℕ) :
    (realOrdinaryHypergeometricCoefficient a b c n : ℂ) =
      ordinaryHypergeometricCoefficient (a : ℂ) (b : ℂ) (c : ℂ) n := by
  simp only [realOrdinaryHypergeometricCoefficient, ordinaryHypergeometricCoefficient]
  push_cast
  rw [ofReal_ascPochhammer_eval a n, ofReal_ascPochhammer_eval b n,
    ofReal_ascPochhammer_eval c n]

/-- The real ordinary Gauss-series terms are summable on the positive part of the unit interval. -/
theorem realOrdinaryHypergeometricTerm_summable (a b c x : ℝ)
    (hc : 0 < c) (hx : 0 < x) (hx1 : x < 1) :
    Summable (fun n : ℕ => realOrdinaryHypergeometricCoefficient a b c n * x ^ n) := by
  let P : FormalMultilinearSeries ℂ ℂ ℂ :=
    ordinaryHypergeometricSeries ℂ (a : ℂ) (b : ℂ) (c : ℂ)
  have hcC : ∀ n : ℕ, (c : ℂ) ≠ -(n : ℂ) := by
    intro n hn
    have hreal : c = -(n : ℝ) := by exact_mod_cast hn
    linarith
  have hrad  := ordinaryHypergeometricSeries_one_le_radius (a : ℂ) (b : ℂ) (c : ℂ) hcC
  have hxnorm : ‖(x : ℂ)‖ < 1 := by
    calc
      ‖(x : ℂ)‖ = |x| := Complex.norm_real x
      _ = x := abs_of_pos hx
      _ < 1 := hx1
  have hxnn : ‖(x : ℂ)‖₊ < 1 := by exact_mod_cast hxnorm
  have hxball : (x : ℂ) ∈ Metric.eball (0 : ℂ) 1 := by
    simpa [Metric.mem_eball, edist_eq_enorm_sub, enorm_eq_nnnorm, dist_zero_right] using
      (ENNReal.coe_lt_coe.mpr hxnn)
  have hsum := P.hasSum (Metric.eball_subset_eball hrad hxball)
  have hsum' : HasSum
      (fun n : ℕ => ((realOrdinaryHypergeometricCoefficient a b c n * x ^ n : ℝ) : ℂ))
      (P.sum (x : ℂ)) := by
    apply HasSum.congr_fun hsum
    intro n
    calc
      ((realOrdinaryHypergeometricCoefficient a b c n * x ^ n : ℝ) : ℂ) =
          (realOrdinaryHypergeometricCoefficient a b c n : ℂ) * (x : ℂ) ^ n := by
            push_cast
            rfl
      _ = ordinaryHypergeometricCoefficient (a : ℂ) (b : ℂ) (c : ℂ) n * (x : ℂ) ^ n := by
            rw [ofReal_realOrdinaryHypergeometricCoefficient]
      _ = (P n) (fun _ => (x : ℂ)) := by
            dsimp [P]
            rw [ordinaryHypergeometricSeries_apply_eq, smul_eq_mul]
  exact Complex.summable_ofReal.mp hsum'.summable

/-- Euler's real integral on `(0,1)` equals the ordinary Gauss series for `0 < x < 1` and
positive real Euler parameters. -/
theorem realGaussEulerIntegral_eq_tsum (a b c x : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hcb : 0 < c - b)
    (hx : 0 < x) (hx1 : x < 1) :
    (Real.Gamma c / (Real.Gamma b * Real.Gamma (c - b))) *
        (∫ t : ℝ in Ioc 0 1,
          t ^ (b - 1) * (1 - t) ^ (c - b - 1) * (1 - x * t) ^ (-a)) =
      ∑' n : ℕ, realOrdinaryHypergeometricCoefficient a b c n * x ^ n := by
  let N  := Real.Gamma c / (Real.Gamma b * Real.Gamma (c - b))
  let F  := fun n t => N * realGaussEulerBinomialTerm a b c x n t
  have hc : 0 < c := by linarith
  have hN : 0 < N := by
    positivity
  have hcoeff := realOrdinaryHypergeometricTerm_summable a b c x hc hx hx1
  have hFint : ∀ n : ℕ, IntegrableOn (F n) (Ioc 0 1) := by
    intro n
    exact (realGaussEulerBinomialTerm_integrableOn a b c x n hb hcb).const_mul N
  have hFval (n : ℕ) :
      (∫ t : ℝ in Ioc 0 1, F n t) =
        realOrdinaryHypergeometricCoefficient a b c n * x ^ n := by
    simpa [F, N, MeasureTheory.integral_const_mul] using
      realGaussEulerBinomialTerm_integral a b c x n ha hb hcb hx
  have hFnorm (n : ℕ) :
      (∫ t : ℝ in Ioc 0 1, ‖F n t‖) =
        realOrdinaryHypergeometricCoefficient a b c n * x ^ n := by
    have hnonneg : ∀ᵐ t ∂volume.restrict (Ioc 0 1), 0 ≤ F n t := by
      filter_upwards [ae_restrict_mem (by simp)] with t ht
      exact mul_nonneg hN.le
        (realGaussEulerBinomialTerm_nonneg a b c x n t ha hx ht)
    have hnorm : (fun t : ℝ => ‖F n t‖) =ᵐ[volume.restrict (Ioc 0 1)] F n := by
      filter_upwards [hnonneg] with t ht
      rw [Real.norm_eq_abs, abs_of_nonneg ht]
    rw [integral_congr_ae hnorm]
    exact hFval n
  have hFsum  := hcoeff.congr fun n => (hFnorm n).symm
  have hpoint : ∀ᵐ t ∂volume.restrict (Ioc 0 1),
      (∑' n : ℕ, F n t) =
        N * (t ^ (b - 1) * (1 - t) ^ (c - b - 1) * (1 - x * t) ^ (-a)) := by
    filter_upwards [ae_restrict_mem (by simp)] with t ht
    have hs := realGaussEulerBinomialTerm_hasSum a b c x t hx hx1 ht
    exact (hs.mul_left N).tsum_eq
  have hswap := MeasureTheory.hasSum_integral_of_summable_integral_norm
    (μ := volume.restrict (Ioc 0 1)) hFint hFsum
  rw [integral_congr_ae hpoint, MeasureTheory.integral_const_mul] at hswap
  have hfinal : HasSum
      (fun n : ℕ => realOrdinaryHypergeometricCoefficient a b c n * x ^ n)
      (N * ∫ t : ℝ in Ioc 0 1,
        t ^ (b - 1) * (1 - t) ^ (c - b - 1) * (1 - x * t) ^ (-a)) := by
    simp_all
  exact hfinal.tsum_eq.symm

/-- For a characterized Gauss family, the normalized real Euler integral agrees with its value
on the open unit interval. -/
theorem realGaussEulerIntegral_eq_family
    {H : ℂ → ℂ → ℂ → ℂ → ℂ} (hH : IsGaussHypergeometricFamily H)
    (a b c x : ℝ) (ha : 0 < a) (hb : 0 < b) (hcb : 0 < c - b)
    (hx : 0 < x) (hx1 : x < 1) :
    ((Real.Gamma c / (Real.Gamma b * Real.Gamma (c - b)) : ℝ) : ℂ) *
        (∫ t : ℝ in Ioc 0 1,
          t ^ (b - 1) * (1 - t) ^ (c - b - 1) * (1 - x * t) ^ (-a)) =
      H (a : ℂ) (b : ℂ) (c : ℂ) (x : ℂ) := by
  let N  := Real.Gamma c / (Real.Gamma b * Real.Gamma (c - b))
  
  have hcC : ∀ n : ℕ, (c : ℂ) ≠ -(n : ℂ) := by
    intro n hn
    have hreal : c = -(n : ℝ) := by exact_mod_cast hn
    linarith
  have hxnorm : ‖(x : ℂ)‖ < 1 := by
    calc
      ‖(x : ℂ)‖ = |x| := Complex.norm_real x
      _ = x := abs_of_pos hx
      _ < 1 := hx1
  have hEuler := realGaussEulerIntegral_eq_tsum a b c x ha hb hcb hx hx1
  have hcast := congrArg (fun y : ℝ => (y : ℂ)) hEuler
  have hsum :
      (∑' n : ℕ,
        ((realOrdinaryHypergeometricCoefficient a b c n * x ^ n : ℝ) : ℂ)) =
        ordinaryHypergeometric (a : ℂ) (b : ℂ) (c : ℂ) (x : ℂ) := by
    rw [ordinaryHypergeometric_eq_tsum]
    apply tsum_congr
    intro n
    simp only [Complex.ofReal_mul, Complex.ofReal_pow,
      ofReal_realOrdinaryHypergeometricCoefficient, smul_eq_mul]
  have hchar := hH (a : ℂ) (b : ℂ) (c : ℂ) hcC
  have hseriesValue := hchar.2 (x : ℂ) hxnorm
  have hcast' :
      (N : ℂ) *
          (∫ t : ℝ in Ioc 0 1,
            t ^ (b - 1) * (1 - t) ^ (c - b - 1) * (1 - x * t) ^ (-a)) =
        ordinaryHypergeometric (a : ℂ) (b : ℂ) (c : ℂ) (x : ℂ) := by
    have h := hcast
    rw [Complex.ofReal_mul, Complex.ofReal_tsum] at h
    aesop
  aesop

end DOZZ.Proofs
