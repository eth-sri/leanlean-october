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
theorem ofReal_ascPochhammer_eval (x : ℝ) n :
    Complex.ofReal ((ascPochhammer ℝ n).eval x) =
      (ascPochhammer ℂ n).eval (x : ℂ) := by
  calc
    Complex.ofReal ((ascPochhammer ℝ n).eval x) =
        ((ascPochhammer ℝ n).map Complex.ofRealHom).eval (x : ℂ) := by
          symm
          exact Polynomial.eval_map_apply (p := ascPochhammer ℝ n)
            (f := Complex.ofRealHom) x
    _ = (ascPochhammer ℂ n).eval (x : ℂ) := by
      rw [ascPochhammer_map]

/-- Gamma's natural shift formula, stated over positive real arguments. -/
theorem realGamma_add_nat_div_Gamma_eq x (n : ℕ) (hx : 0 < x) :
    Real.Gamma (x + n) / Real.Gamma x = (ascPochhammer ℝ n).eval x := by
  have hcx : ∀ k : ℕ, (x : ℂ) ≠ -(k : ℂ) := by
    intro k hk
    have : x = -(k : ℝ) := by exact_mod_cast hk
    linarith
  have h := Complex.Gamma_add_nat_div_Gamma_eq (n := n) (x : ℂ) hcx
  rw [show (x : ℂ) + (n : ℂ) = ((x + n : ℝ) : ℂ) by push_cast; ring,
    Complex.Gamma_ofReal, Complex.Gamma_ofReal,
    ← ofReal_ascPochhammer_eval x n] at h
  apply Complex.ofReal_injective
  simpa only [Complex.ofReal_div] using h


/-- A positive argument gives positive rising factorials. -/
theorem realAscPochhammer_eval_pos {x} (hx : 0 < x) n :
    0 < (ascPochhammer ℝ n).eval x := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [ascPochhammer_succ_eval]
      exact mul_pos ih (by positivity)

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
  rw [(show a + (n : ℝ) - 1 - (n : ℝ) + 1 = a by ring)]
  simp [div_eq_mul_inv, mul_comm]

/-- The real binomial terms after multiplication by the Euler beta weight. -/
noncomputable def realGaussEulerBinomialTerm (a b c x : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  Ring.choose (a + n - 1) n * (x * t) ^ n *
    t ^ (b - 1) * (1 - t) ^ (c - b - 1)





/-- Casting the real coefficient gives Mathlib's complex ordinary Gauss coefficient. -/
theorem ofReal_realOrdinaryHypergeometricCoefficient (a b c : ℝ) (n : ℕ) :
    (realOrdinaryHypergeometricCoefficient a b c n : ℂ) =
      ordinaryHypergeometricCoefficient (a : ℂ) (b : ℂ) (c : ℂ) n := by
  simp only [realOrdinaryHypergeometricCoefficient, ordinaryHypergeometricCoefficient]
  push_cast
  rw [ofReal_ascPochhammer_eval a n, ofReal_ascPochhammer_eval b n,
    ofReal_ascPochhammer_eval c n]



/-- For a characterized Gauss family, the normalized real Euler integral agrees with its value
on the open unit interval. -/
theorem realGaussEulerIntegral_eq_family
    {H} (hH : IsGaussHypergeometricFamily H)
    (a b c x : ℝ) (ha : 0 < a) (hb : 0 < b) (hcb : 0 < c - b)
    (hx : 0 < x) (hx1 : x < 1) :
    ((Real.Gamma c / (Real.Gamma b * Real.Gamma (c - b)) : ℝ) : ℂ) *
        (∫ t : ℝ in Ioc 0 1,
          t ^ (b - 1) * (1 - t) ^ (c - b - 1) * (1 - x * t) ^ (-a)) =
      H (a : ℂ) (b : ℂ) (c : ℂ) (x : ℂ) := by
  have realGaussEulerIntegral_eq_tsum : (Real.Gamma c / (Real.Gamma b * Real.Gamma (c - b))) * (∫ t : ℝ in Ioc 0 1, t ^ (b - 1) * (1 - t) ^ (c - b - 1) * (1 - x * t) ^ (-a)) = ∑' n : ℕ, realOrdinaryHypergeometricCoefficient a b c n * x ^ n := by
    have realOrdinaryHypergeometricTerm_summable (hc : 0 < c) (hx : 0 < x) (hx1 : x < 1) : Summable (fun n : ℕ => realOrdinaryHypergeometricCoefficient a b c n * x ^ n) := by
      let P : FormalMultilinearSeries ℂ ℂ ℂ :=
        ordinaryHypergeometricSeries ℂ (a : ℂ) (b : ℂ) (c : ℂ)
      have hcC : ∀ n : ℕ, (c : ℂ) ≠ -(n : ℂ) := by
        intro n hn
        have : c = -(n : ℝ) := by exact_mod_cast hn
        linarith
      have hxnorm : ‖(x : ℂ)‖ < 1 := by
        calc
          ‖(x : ℂ)‖ = |x| := Complex.norm_real x
          _ = x := abs_of_pos hx
          _ < 1 := hx1
      have hsum' : HasSum
          (fun n : ℕ => ((realOrdinaryHypergeometricCoefficient a b c n * x ^ n : ℝ) : ℂ))
          (P.sum (x : ℂ)) := by
        apply HasSum.congr_fun (P.hasSum (Metric.eball_subset_eball (ordinaryHypergeometricSeries_one_le_radius (a : ℂ) (b : ℂ) (c : ℂ) hcC) (by simpa [Metric.mem_eball, edist_eq_enorm_sub, enorm_eq_nnnorm, dist_zero_right] using (ENNReal.coe_lt_coe.mpr (by exact_mod_cast hxnorm)))))
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
    have realGaussEulerBinomialTerm_hasSum t (hx : 0 < x) (hx1 : x < 1) (ht : t ∈ Ioc 0 1) : HasSum (fun n => realGaussEulerBinomialTerm a b c x n t) (t ^ (b - 1) * (1 - t) ^ (c - b - 1) * (1 - x * t) ^ (-a)) := by
      have hu0 := mul_nonneg hx.le ht.1.le
      have hu1 : x * t < 1 := by nlinarith [mul_le_mul_of_nonneg_left ht.2 hx.le]
      have hbin' : HasSum
          (fun n : ℕ => Ring.choose (a + n - 1) n * (x * t) ^ n)
          (1 / (1 - x * t) ^ a) := by
        convert ((Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero a).hasSum (show (x * t : ℝ) ∈ Metric.eball (0 : ℝ) 1 by simpa [Metric.mem_eball, edist_eq_enorm_sub, enorm_eq_nnnorm, dist_zero_right] using (ENNReal.coe_lt_coe.mpr (show ‖(x * t : ℝ)‖₊ < 1 by exact_mod_cast (show ‖x * t‖ < 1 by rw [Real.norm_eq_abs, abs_of_nonneg hu0]; exact hu1))))) using 1
        · funext (n : ℕ)
          simp [smul_eq_mul]; ring
        · simp
      let W := t ^ (b - 1) * (1 - t) ^ (c - b - 1)
      have hterms : HasSum (fun n => realGaussEulerBinomialTerm a b c x n t)
          (W * (1 / (1 - x * t) ^ a)) := by
        apply HasSum.congr_fun (hbin'.mul_left W)
        intro n
        dsimp [realGaussEulerBinomialTerm, W]
        ring
      have hrewrite : W * (1 / (1 - x * t) ^ a) =
          t ^ (b - 1) * (1 - t) ^ (c - b - 1) * (1 - x * t) ^ (-a) := by
        dsimp [W]
        rw [(Real.rpow_neg (show 0 ≤ 1 - x * t by linarith) a)]
        ring
      rw [hrewrite] at hterms
      exact hterms
    have realGaussEulerBinomialTerm_nonneg n t (ha : 0 < a) (hx : 0 < x) (ht : t ∈ Ioc 0 1) : 0 ≤ realGaussEulerBinomialTerm a b c x n t := by
      dsimp [realGaussEulerBinomialTerm]
      exact mul_nonneg (mul_nonneg (mul_nonneg (by rw [realBinomialCoefficient_eq_ascPochhammer]; exact le_of_lt (div_pos (realAscPochhammer_eval_pos ha n) (by positivity))) (pow_nonneg (mul_nonneg hx.le ht.1.le) _)) (Real.rpow_nonneg ht.1.le _)) (Real.rpow_nonneg (sub_nonneg.mpr ht.2) _)
    have realGaussEulerBinomialTerm_integrableOn n (hb : 0 < b) (hcb : 0 < c - b) : IntegrableOn (realGaussEulerBinomialTerm a b c x n) (Ioc 0 1) := by
      let s : Set ℝ := Ioc 0 1
      let w : ℝ → ℝ := fun t => t ^ (b + n - 1) * (1 - t) ^ (c - b - 1)
      let C : ℝ := Ring.choose (a + n - 1) n * x ^ n
      have hweight : IntegrableOn w s := by
        simpa [w, s] using
          (realEulerBetaWeight_integrable (b + n) (c - b) (by positivity) hcb)
      have hpowEq :
          realGaussEulerBinomialTerm a b c x n =ᵐ[volume.restrict s]
            fun t => C * w t := by
        filter_upwards [ae_restrict_mem (by simp [s]),
          ae_restrict_of_ae (volume.ae_ne (0 : ℝ))] with t ht ht0
        have hrpowAdd : t ^ (b - 1) * t ^ (n : ℝ) = t ^ (b + n - 1) := by
          rw [← Real.rpow_add ht.1]
          congr 1
          ring
        dsimp [realGaussEulerBinomialTerm, C, w]
        calc
          Ring.choose (a + n - 1) n * (x * t) ^ n *
              t ^ (b - 1) * (1 - t) ^ (c - b - 1) =
              Ring.choose (a + n - 1) n * x ^ n *
                ((t ^ (b - 1) * t ^ (n : ℝ)) * (1 - t) ^ (c - b - 1)) := by
                  rw [(mul_pow x t n), ((Real.rpow_natCast t n).symm)]
                  ring
          _ = Ring.choose (a + n - 1) n * x ^ n *
                (t ^ (b + n - 1) * (1 - t) ^ (c - b - 1)) := by rw [hrpowAdd]
      have hCw : IntegrableOn (fun t => C * w t) s := hweight.const_mul C
      exact hCw.congr_fun_ae hpowEq.symm
    have realGaussEulerBinomialTerm_integral (n : ℕ) (ha : 0 < a) (hb : 0 < b) (hcb : 0 < c - b) (hx : 0 < x) : (Real.Gamma c / (Real.Gamma b * Real.Gamma (c - b))) * (∫ t : ℝ in Ioc 0 1, realGaussEulerBinomialTerm a b c x n t) = realOrdinaryHypergeometricCoefficient a b c n * x ^ n := by
      have realEulerBetaMoment_scaled : (Real.Gamma c / (Real.Gamma b * Real.Gamma (c - b))) * (∫ t : ℝ in Ioc 0 1, t ^ (b + n - 1) * (1 - t) ^ (c - b - 1)) = (ascPochhammer ℝ n).eval b / (ascPochhammer ℝ n).eval c := by
        have hc : 0 < c := by linarith
        have hshiftB := realGamma_add_nat_div_Gamma_eq b n hb
        have hshiftC := realGamma_add_nat_div_Gamma_eq c n hc
        have hΓb := Real.Gamma_pos_of_pos hb
        have hΓc := Real.Gamma_pos_of_pos hc
        rw [(show (∫ t : ℝ in Ioc 0 1, t ^ (b + n - 1) * (1 - t) ^ (c - b - 1)) = Real.Gamma (b + n) * Real.Gamma (c - b) / Real.Gamma (c + n) by simpa only [show b + (n : ℝ) + (c - b) = c + n by ring] using (realEulerBetaIntegral_eq_gamma_ratio (b + n) (c - b) (by positivity) hcb)), (show Real.Gamma (b + n) = (ascPochhammer ℝ n).eval b * Real.Gamma b by field_simp [hΓb.ne'] at hshiftB; nlinarith), (show Real.Gamma (c + n) = (ascPochhammer ℝ n).eval c * Real.Gamma c by field_simp [hΓc.ne'] at hshiftC; nlinarith)]
        field_simp [hΓb.ne', (Real.Gamma_pos_of_pos hcb).ne', hΓc.ne', (show 0 < (ascPochhammer ℝ n).eval c by rw [← hshiftC]; exact div_pos (Real.Gamma_pos_of_pos (by positivity)) hΓc).ne']
      let s : Set ℝ := Ioc 0 1
      let w : ℝ → ℝ := fun t => t ^ (b + n - 1) * (1 - t) ^ (c - b - 1)
      let C : ℝ := Ring.choose (a + n - 1) n * x ^ n
      have hpowEq :
          realGaussEulerBinomialTerm a b c x n =ᵐ[volume.restrict s]
            fun t => C * w t := by
        filter_upwards [ae_restrict_mem (by simp [s]),
          ae_restrict_of_ae (volume.ae_ne (0 : ℝ))] with t ht ht0
        have hrpowAdd : t ^ (b - 1) * t ^ (n : ℝ) = t ^ (b + n - 1) := by
          rw [← Real.rpow_add ht.1]
          congr 1
          ring
        dsimp [realGaussEulerBinomialTerm, C, w]
        calc
          Ring.choose (a + n - 1) n * (x * t) ^ n *
              t ^ (b - 1) * (1 - t) ^ (c - b - 1) =
              Ring.choose (a + n - 1) n * x ^ n *
                ((t ^ (b - 1) * t ^ (n : ℝ)) * (1 - t) ^ (c - b - 1)) := by
                  rw [(mul_pow x t n), ((Real.rpow_natCast t n).symm)]
                  ring
          _ = Ring.choose (a + n - 1) n * x ^ n *
                (t ^ (b + n - 1) * (1 - t) ^ (c - b - 1)) := by rw [hrpowAdd]
      have hterm_integral :
          (∫ t : ℝ in s, realGaussEulerBinomialTerm a b c x n t) =
            C * (∫ t : ℝ in s, w t) := by
        calc
          _ = ∫ t : ℝ in s, C * w t := integral_congr_ae hpowEq
          _ = C * (∫ t : ℝ in s, w t) := integral_const_mul _ _
      rw [hterm_integral]
      dsimp [C]
      calc
        _ = Ring.choose (a + n - 1) n * x ^ n *
            ((Real.Gamma c / (Real.Gamma b * Real.Gamma (c - b))) *
              (∫ t : ℝ in Ioc 0 1, w t)) := by ring
        _ = Ring.choose (a + n - 1) n * x ^ n *
            ((ascPochhammer ℝ n).eval b / (ascPochhammer ℝ n).eval c) := by
              rw [(realEulerBetaMoment_scaled)]
        _ = realOrdinaryHypergeometricCoefficient a b c n * x ^ n := by
              rw [realBinomialCoefficient_eq_ascPochhammer]
              dsimp [realOrdinaryHypergeometricCoefficient]
              field_simp [((realAscPochhammer_eval_pos (by linarith : 0 < c) n).ne')]
    let N := Real.Gamma c / (Real.Gamma b * Real.Gamma (c - b))
    let F : ℕ → ℝ → ℝ := fun n t => N * realGaussEulerBinomialTerm a b c x n t
    have hc : 0 < c := by linarith
    have hFval n :
        (∫ t : ℝ in Ioc 0 1, F n t) =
          realOrdinaryHypergeometricCoefficient a b c n * x ^ n := by
      simpa [F, N, MeasureTheory.integral_const_mul] using
        realGaussEulerBinomialTerm_integral n ha hb hcb hx
    have hFnorm n :
        (∫ t : ℝ in Ioc 0 1, ‖F n t‖) =
          realOrdinaryHypergeometricCoefficient a b c n * x ^ n := by
      have hnonneg : ∀ᵐ t ∂volume.restrict (Ioc 0 1), 0 ≤ F n t := by
        filter_upwards [ae_restrict_mem (by simp)] with t ht
        dsimp [F]
        exact mul_nonneg (show 0 < N by dsimp [N]; exact div_pos (Real.Gamma_pos_of_pos hc) (mul_pos (Real.Gamma_pos_of_pos hb) (Real.Gamma_pos_of_pos hcb))).le
          (realGaussEulerBinomialTerm_nonneg n t ha hx ht)
      rw [integral_congr_ae (show (fun t => ‖F n t‖) =ᵐ[volume.restrict (Ioc 0 1)] F n by filter_upwards [hnonneg] with t ht; rw [Real.norm_eq_abs, abs_of_nonneg ht])]
      exact hFval n
    have hswap := MeasureTheory.hasSum_integral_of_summable_integral_norm
      (μ := volume.restrict (Ioc 0 1)) (by intro n; exact (realGaussEulerBinomialTerm_integrableOn n hb hcb).const_mul N) ((realOrdinaryHypergeometricTerm_summable hc hx hx1).congr fun n => (hFnorm n).symm)
    rw [integral_congr_ae (show ∀ᵐ t ∂volume.restrict (Ioc 0 1), (∑' n : ℕ, F n t) = N * (t ^ (b - 1) * (1 - t) ^ (c - b - 1) * (1 - x * t) ^ (-a)) by filter_upwards [ae_restrict_mem (by simp)] with t ht; simpa [F] using ((realGaussEulerBinomialTerm_hasSum t hx hx1 ht).mul_left N).tsum_eq), MeasureTheory.integral_const_mul] at hswap
    have hfinal : HasSum
        (fun n => realOrdinaryHypergeometricCoefficient a b c n * x ^ n)
        (N * ∫ t : ℝ in Ioc 0 1,
          t ^ (b - 1) * (1 - t) ^ (c - b - 1) * (1 - x * t) ^ (-a)) := by
      apply HasSum.congr_fun hswap
      intro n
      exact (hFval n).symm
    simpa [N] using hfinal.tsum_eq.symm
  let N := Real.Gamma c / (Real.Gamma b * Real.Gamma (c - b))
  have hcC : ∀ n : ℕ, (c : ℂ) ≠ -(n : ℂ) := by
    intro n hn
    have : c = -(n : ℝ) := by exact_mod_cast hn
    linarith
  have hxnorm : ‖(x : ℂ)‖ < 1 := by
    calc
      ‖(x : ℂ)‖ = |x| := Complex.norm_real x
      _ = x := abs_of_pos hx
      _ < 1 := hx1
  have hcast' :
      (N : ℂ) *
          (∫ t : ℝ in Ioc 0 1,
            t ^ (b - 1) * (1 - t) ^ (c - b - 1) * (1 - x * t) ^ (-a)) =
        ordinaryHypergeometric (a : ℂ) (b : ℂ) (c : ℂ) (x : ℂ) := by
    have h := (congrArg (fun y : ℝ => (y : ℂ)) (realGaussEulerIntegral_eq_tsum))
    rw [Complex.ofReal_mul, Complex.ofReal_tsum] at h
    calc
      (N : ℂ) *
          (∫ t : ℝ in Ioc 0 1,
            t ^ (b - 1) * (1 - t) ^ (c - b - 1) * (1 - x * t) ^ (-a)) =
        ∑' n : ℕ,
          ((realOrdinaryHypergeometricCoefficient a b c n * x ^ n : ℝ) : ℂ) := by
            simpa [N] using h
      _ = ordinaryHypergeometric (a : ℂ) (b : ℂ) (c : ℂ) (x : ℂ) := (by rw [ordinaryHypergeometric_eq_tsum]; apply tsum_congr; intro n; simp only [Complex.ofReal_mul, Complex.ofReal_pow, ofReal_realOrdinaryHypergeometricCoefficient, smul_eq_mul])
  calc
    ((Real.Gamma c / (Real.Gamma b * Real.Gamma (c - b)) : ℝ) : ℂ) *
          (∫ t : ℝ in Ioc 0 1,
            t ^ (b - 1) * (1 - t) ^ (c - b - 1) * (1 - x * t) ^ (-a)) =
      (N : ℂ) *
          (∫ t : ℝ in Ioc 0 1,
            t ^ (b - 1) * (1 - t) ^ (c - b - 1) * (1 - x * t) ^ (-a)) := by
              rfl
    _ = ordinaryHypergeometric (a : ℂ) (b : ℂ) (c : ℂ) (x : ℂ) := hcast'
    _ = H (a : ℂ) (b : ℂ) (c : ℂ) (x : ℂ) := ((hH (a : ℂ) (b : ℂ) (c : ℂ) hcC).2 (x : ℂ) hxnorm).symm

end DOZZ.Proofs
