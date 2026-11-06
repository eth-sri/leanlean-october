/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.BasisEquationTransforms
public import DOZZ.Hypergeom.Germs
import Mathlib.Tactic
import Batteries.Tactic.Alias

/-! Abel's identity and the endpoint normalization of the zero-basis Wronskian. -/

public section

namespace DOZZ.Proofs

open Filter

private theorem gaussSlitPlane_isOpen_for_wronskians : IsOpen gaussSlitPlane := (isOpen_compl_singleton.preimage Complex.continuous_im).union
    (isOpen_Iio.preimage Complex.continuous_re)

private alias gaussCutPlane_isOpen_for_wronskians := DOZZ.Proofs.gaussCutPlane_isOpen

variable {H : ℂ → ℂ → ℂ → ℂ → ℂ} (hH : IsGaussHypergeometricFamily H) (a b c : ℂ)

include H hH a b c in
/-- The zero-basis Wronskian has its explicit value on the principal cut plane. -/
theorem gaussFPlus_wronskian_identity
     (hc : ∀ n : ℤ, c ≠ (n : ℂ)) :
    ∀ z ∈ gaussCutPlane,
      gaussFMinus H a b c z * deriv (gaussFPlus H a b c) z -
        deriv (gaussFMinus H a b c) z * gaussFPlus H a b c z =
          (1 - c) * z ^ (-c) * (1 - z) ^ (c - a - b - 1) := by
  let A  := a - c + 1
  let B  := b - c + 1
  let C  := 2 - c
  let e  := a + b - c + 1
  let f  := H a b c
  let v  := H A B C
  let p : ℂ → ℂ := fun z => z ^ (1 - c)
  let q : ℂ → ℂ := fun z => (1 - z) ^ e
  let g  := gaussFPlus H a b c
  let W  := fun z => f z * deriv g z - deriv f z * g z
  let T  := fun z => z ^ c * q z
  let S  := fun z => T z * W z
  have hcNat : ∀ n : ℕ, c ≠ -(n : ℂ) := by
    intro n heq
    apply hc (-(n : ℤ))
    exact heq.trans (by simp)
  have hCfree : ∀ n : ℕ, C ≠ -(n : ℂ) := two_sub_parameter_ne_nat_neg hc
  have hfchar := hH a b c hcNat
  have hvchar := hH A B C hCfree
  have hFanalyticSlit  :=
    hfchar.1.analyticOnNhd gaussSlitPlane_isOpen_for_wronskians
  have hVanalyticSlit  :=
    hvchar.1.analyticOnNhd gaussSlitPlane_isOpen_for_wronskians
  have hFanalytic  := hFanalyticSlit.mono gaussCutPlane_subset_gaussSlitPlane
  have hVanalytic  := hVanalyticSlit.mono gaussCutPlane_subset_gaussSlitPlane
  have hPanalytic : AnalyticOnNhd ℂ p gaussCutPlane := analyticOnNhd_id.cpow analyticOnNhd_const
      (fun z hz => gaussCutPlane_subset_Complex_slitPlane hz)
  have hGanalytic : AnalyticOnNhd ℂ g gaussCutPlane := hPanalytic.mul hVanalytic
  have hQanalytic : AnalyticOnNhd ℂ q gaussCutPlane := (analyticOnNhd_const.sub analyticOnNhd_id).cpow analyticOnNhd_const
      (fun z hz => gaussCutPlane_subset_Complex_slitPlane
        (one_sub_gaussCutPlane_subset_gaussCutPlane hz))
  have hZanalytic : AnalyticOnNhd ℂ (fun z : ℂ => z ^ c) gaussCutPlane := analyticOnNhd_id.cpow analyticOnNhd_const
      (fun z hz => gaussCutPlane_subset_Complex_slitPlane hz)
  have hTanalytic : AnalyticOnNhd ℂ T gaussCutPlane := by
    fun_prop (disch := positivity)
  have hFanalytic₁  := hFanalytic.deriv

  have hGanalytic₁  := hGanalytic.deriv
  have hWanalytic : AnalyticOnNhd ℂ W gaussCutPlane := by
    fun_prop
  have hSanalytic : AnalyticOnNhd ℂ S gaussCutPlane := by
    fun_prop (disch := positivity)
  have hPderiv : gaussCutPlane.EqOn (deriv p)
      (fun z => (1 - c) * z ^ (-c)) := by
    intro z hz
    simpa [p] using (Complex.deriv_cpow_const (c := 1 - c)
      (gaussCutPlane_subset_Complex_slitPlane hz))
  have hQderiv : gaussCutPlane.EqOn (deriv q)
      (fun z => -e * (1 - z) ^ (e - 1)) := by
    intro z hz
    have hw  := one_sub_gaussCutPlane_subset_gaussCutPlane hz
    have hws := gaussCutPlane_subset_Complex_slitPlane hw
    have hmap : HasDerivAt (fun w : ℂ => 1 - w) (-1) z := (hasDerivAt_id z).const_sub (1 : ℂ)
    have hpow := Complex.deriv_cpow_const (c := e) hws
    have hcomp := (differentiableAt_id.cpow_const (c := e) hws).hasDerivAt.comp z hmap
    change deriv (fun w => (1 - w) ^ e) z = -e * (1 - z) ^ (e - 1)
    simpa [Function.comp_def, hpow, mul_comm] using hcomp.deriv
  have hGderiv : gaussCutPlane.EqOn (deriv g)
      (fun z => (1 - c) * z ^ (-c) * v z + p z * deriv v z) := by
    intro z hz
    have hPAt := (hPanalytic z hz).differentiableAt
    have hVAt := (hVanalytic z hz).differentiableAt
    have hmul := hPAt.hasDerivAt.mul hVAt.hasDerivAt
    change deriv (p * v) z = (1 - c) * z ^ (-c) * v z + p z * deriv v z
    rw [hmul.deriv, hPderiv hz]
  have hWderiv : ∀ z ∈ gaussCutPlane,
      deriv W z = f z * deriv (deriv g) z - deriv (deriv f) z * g z := by
    intro z hz
    have hleft := (hFanalytic z hz).differentiableAt.hasDerivAt.mul
      (hGanalytic₁ z hz).differentiableAt.hasDerivAt
    have hright := (hFanalytic₁ z hz).differentiableAt.hasDerivAt.mul
      (hGanalytic z hz).differentiableAt.hasDerivAt
    have hsub := hleft.sub hright
    change deriv (fun w => f w * deriv g w - deriv f w * g w) z = _
    have hfun : (fun w => f w * deriv g w - deriv f w * g w) =
        f * deriv g - deriv f * g := by
      funext w
      rfl
    rw [hfun]
    rw [hsub.deriv]
    ring
  have hTderiv : ∀ z ∈ gaussCutPlane,
      deriv T z = c * z ^ (c - 1) * q z - e * z ^ c * (1 - z) ^ (e - 1) := by
    intro z hz
    have hZAt := (hZanalytic z hz).differentiableAt
    have hQAt := (hQanalytic z hz).differentiableAt
    have hmul := hZAt.hasDerivAt.mul hQAt.hasDerivAt
    have hZderiv : deriv (fun w : ℂ => w ^ c) z = c * z ^ (c - 1) :=
      Complex.deriv_cpow_const (gaussCutPlane_subset_Complex_slitPlane hz)
    change deriv (fun w => w ^ c * q w) z = _
    have hfun : (fun w => w ^ c * q w) = (fun w => w ^ c) * q := by
      funext w
      rfl
    rw [hfun]
    rw [hmul.deriv, hZderiv, hQderiv hz]
    ring
  have hFop : ∀ z ∈ gaussCutPlane,
      gaussHolomorphicOperator a b c f z = 0 := gauss_family_holomorphicOperator_eq_zero hH a b c hcNat
  have hGop : ∀ z ∈ gaussCutPlane,
      gaussHolomorphicOperator a b c g z = 0 := gaussFPlus_holomorphicOperator_eq_zero hH a b c hc
  have hAbel : ∀ z ∈ gaussCutPlane,
      z * (1 - z) * deriv W z + (c - (a + b + 1) * z) * W z = 0 := by
    intro z hz
    rw [hWderiv z hz]
    dsimp [W]
    have hFeq := hFop z hz
    have hGeq := hGop z hz
    dsimp [gaussHolomorphicOperator] at hFeq hGeq
    grind
  have hTscaled : ∀ z ∈ gaussCutPlane,
      z * (1 - z) * deriv T z = (c - (a + b + 1) * z) * T z := by
    intro z hz
    have hz0 := (gaussCutPlane_subset_regularPlane hz).1
    have hz1 := (gaussCutPlane_subset_regularPlane hz).2
    have hw0 : 1 - z ≠ 0 := by
      positivity
    have hpowz : z ^ (c - 1) = z ^ c / z := by
      simpa using Complex.cpow_sub c 1 hz0
    have hpoww : (1 - z) ^ (e - 1) = (1 - z) ^ e / (1 - z) := by
      simpa using Complex.cpow_sub e 1 hw0
    grind
  have hSderivZero : gaussCutPlane.EqOn (deriv S) (fun _ => 0) := by
    intro z hz
    have hTAt := (hTanalytic z hz).differentiableAt
    have hWAt := (hWanalytic z hz).differentiableAt
    have hmul := hTAt.hasDerivAt.mul hWAt.hasDerivAt
    have hSderiv : deriv S z = deriv T z * W z + T z * deriv W z := hmul.deriv
    have hz0 := (gaussCutPlane_subset_regularPlane hz).1
    have hz1 := (gaussCutPlane_subset_regularPlane hz).2
    grind
  have hSdiff  := hSanalytic.differentiableOn
  have hcutPre : IsPreconnected gaussCutPlane := by
    rw [isPreconnected_iff_preconnectedSpace]
    infer_instance
  have hmid : (1 / 2 : ℂ) ∈ gaussCutPlane := by norm_num [gaussCutPlane]
  have hconst : ∀ z ∈ gaussCutPlane, S z = S (1 / 2) := by
    intro z hz
    exact gaussCutPlane_isOpen.is_const_of_deriv_eq_zero
      hcutPre hSdiff hSderivZero hz hmid
  have hfzero : f 0 = 1 := by
    simpa [f] using (hfchar.2 0 (by norm_num : ‖(0 : ℂ)‖ < 1))
  have hvzero : v 0 = 1 := by
    simpa [v] using (hvchar.2 0 (by norm_num : ‖(0 : ℂ)‖ < 1))
  have h0slit : (0 : ℂ) ∈ gaussSlitPlane := by
    change (0 : ℂ).im ≠ 0 ∨ (0 : ℂ).re < 1
    simp
  have hfcont  := (hFanalyticSlit 0 h0slit).continuousAt
  have hvcont  := (hVanalyticSlit 0 h0slit).continuousAt
  have hf'cont  :=
    (hFanalyticSlit.deriv 0 h0slit).continuousAt
  have hv'cont  :=
    (hVanalyticSlit.deriv 0 h0slit).continuousAt
  have hqcont : ContinuousAt q 0 := (by fun_prop : ContinuousAt (fun z : ℂ => 1 - z) 0).cpow
      continuousAt_const (by simp [Complex.mem_slitPlane_iff])
  have hRcont : ContinuousAt
      (fun z => q z * ((1 - c) * f z * v z +
        z * (f z * deriv v z - deriv f z * v z))) 0 := by
    fun_prop
  have hRzero : (fun z => q z * ((1 - c) * f z * v z +
      z * (f z * deriv v z - deriv f z * v z))) 0 = 1 - c := by
    simp [q, hfzero, hvzero]
  have hRlim : Tendsto
      (fun z => q z * ((1 - c) * f z * v z +
        z * (f z * deriv v z - deriv f z * v z)))
      (nhdsWithin 0 gaussCutPlane) (nhds (1 - c)) := by
    have h := hRcont.tendsto.mono_left
      (nhdsWithin_le_nhds : nhdsWithin 0 gaussCutPlane ≤ nhds 0)
    simp_all
  have hscaled : ∀ z ∈ gaussCutPlane,
      S z = q z * ((1 - c) * f z * v z +
        z * (f z * deriv v z - deriv f z * v z)) := by
    intro z hz
    have hz0 := (gaussCutPlane_subset_regularPlane hz).1
    have hGderivAt : deriv g z =
        (1 - c) * z ^ (-c) * v z + p z * deriv v z := hGderiv hz
    have hpow₀ : z ^ c * z ^ (-c) = 1 := by
      rw [← Complex.cpow_add c (-c) hz0]
      simp
    have hpow₁ : z ^ c * z ^ (1 - c) = z := by
      rw [← Complex.cpow_add c (1 - c) hz0]
      simp_all
    have hgval : g z = z ^ (1 - c) * v z := rfl
    grind
  have hlimS : Tendsto S (nhdsWithin 0 gaussCutPlane) (nhds (1 - c)) := by
    have hEq : S =ᶠ[nhdsWithin 0 gaussCutPlane]
        (fun z => q z * ((1 - c) * f z * v z +
          z * (f z * deriv v z - deriv f z * v z))) := by
      filter_upwards [self_mem_nhdsWithin] with z hz
      exact hscaled z hz
    exact hRlim.congr' hEq.symm
  have hSvalue : S (1 / 2) = 1 - c := by
    have hzeroClosure : (0 : ℂ) ∈ closure gaussCutPlane := by
      apply Metric.mem_closure_iff.2
      intro ε hε
      let r  := min ε 1 / 2
      have hrpos : 0 < r := by
        dsimp [r]
        positivity
      have hrε : r < ε := by
        dsimp [r]
        have hmin : min ε 1 ≤ ε := min_le_left _ _
        linarith
      have hrone : r < 1 := by
        bound
      refine ⟨(r : ℂ), ?_, ?_⟩
      · change (r : ℂ).im ≠ 0 ∨ (0 < (r : ℂ).re ∧ (r : ℂ).re < 1)
        simp [hrpos, hrone]
      · simpa [dist_eq_norm, Real.norm_eq_abs, abs_of_pos hrpos] using hrε
    have hconstlim : Tendsto (fun _ : ℂ => S (1 / 2))
        (nhdsWithin 0 gaussCutPlane) (nhds (1 - c)) := by
      have hEq : S =ᶠ[nhdsWithin 0 gaussCutPlane] (fun _ => S (1 / 2)) := by
        filter_upwards [self_mem_nhdsWithin] with z hz
        exact hconst z hz
      exact hlimS.congr' hEq
    have hconstant : Tendsto (fun _ : ℂ => S (1 / 2))
        (nhdsWithin 0 gaussCutPlane) (nhds (S (1 / 2))) := tendsto_const_nhds
    exact (tendsto_nhds_unique'
      (mem_closure_iff_nhdsWithin_neBot.mp hzeroClosure) hconstlim hconstant).symm
  intro z hz
  have hz0 := (gaussCutPlane_subset_regularPlane hz).1
  have hz1 := (gaussCutPlane_subset_regularPlane hz).2
  have hw0 : 1 - z ≠ 0 := by
    positivity
  have hSval := hconst z hz
  rw [hSvalue] at hSval
  have hpowe : -(e) = c - a - b - 1 := by dsimp [e]; ring
  have hcpowz : (z ^ c)⁻¹ = z ^ (-c) := by rw [Complex.cpow_neg]
  have hcpoww : (q z)⁻¹ = (1 - z) ^ (c - a - b - 1) := by
    dsimp [q]
    rw [← hpowe, Complex.cpow_neg]
  dsimp [S, T, W, q, f, g] at hSval ⊢
  have hzPowNe : z ^ c ≠ 0 :=
    (Complex.cpow_ne_zero_iff.mpr (Or.inl hz0))
  have hwPowNe : (1 - z) ^ e ≠ 0 :=
    (Complex.cpow_ne_zero_iff.mpr (Or.inl hw0))
  have hprod  := mul_ne_zero hzPowNe hwPowNe
  have hratio : W z = (1 - c) / (z ^ c * (1 - z) ^ e) := by
    grind
  calc
    W z = (1 - c) / (z ^ c * (1 - z) ^ e) := hratio
    _ = (1 - c) * (z ^ c)⁻¹ * ((1 - z) ^ e)⁻¹ := by
      rw [div_eq_mul_inv, mul_inv]
      ring
    _ = (1 - c) * z ^ (-c) * (1 - z) ^ (c - a - b - 1) := by
      rw [hcpowz, hcpoww]

include H hH a b c in
/-- The one-basis Wronskian follows from the zero-basis identity by reflection. -/
theorem gaussGPlus_wronskian_identity
     (hδ : ∀ n : ℤ, c - a - b ≠ (n : ℂ)) :
    ∀ z ∈ gaussCutPlane,
      gaussGMinus H a b c z * deriv (gaussGPlus H a b c) z -
        deriv (gaussGMinus H a b c) z * gaussGPlus H a b c z =
          -(c - a - b) * z ^ (-c) * (1 - z) ^ (c - a - b - 1) := by
  let c₀  := 1 + a + b - c
  let F  := gaussFMinus H a b c₀
  let G  := gaussFPlus H a b c₀
  let f  := gaussGMinus H a b c
  let g  := gaussGPlus H a b c
  have hc₀ : ∀ n : ℤ, c₀ ≠ (n : ℂ) := by
    intro n heq
    apply hδ (1 - n)
    grind
  have hFdiff : DifferentiableOn ℂ F gaussCutPlane := gaussFMinus_differentiableOn_cutPlane hH a b c₀ hc₀
  have hGdiff : DifferentiableOn ℂ G gaussCutPlane := gaussFPlus_differentiableOn_cutPlane hH a b c₀ hc₀
  have hFident : f = (fun z => F (1 - z)) := by
    funext z
    rfl
  have hGident : g = (fun z => G (1 - z)) := by
    funext z
    change (1 - z) ^ (c - a - b) *
        H (c - b) (c - a) (1 + c - a - b) (1 - z) =
      (1 - z) ^ (1 - c₀) *
        H (a - c₀ + 1) (b - c₀ + 1) (2 - c₀) (1 - z)
    grind
  have hmap (z : ℂ) : HasDerivAt (fun w : ℂ => 1 - w) (-1) z := (hasDerivAt_id z).const_sub (1 : ℂ)
  have hFderiv : gaussCutPlane.EqOn (deriv f)
      (fun z => -deriv F (1 - z)) := by
    intro z hz
    have hw  := one_sub_gaussCutPlane_subset_gaussCutPlane hz
    have hAt := (hFdiff (1 - z) hw).differentiableAt
      (gaussCutPlane_isOpen_for_wronskians.mem_nhds hw)
    have hcomp := hAt.hasDerivAt.comp z (hmap z)
    calc
      deriv f z = deriv (fun w => F (1 - w)) z := by rw [hFident]
      _ = -deriv F (1 - z) := by
        simpa [Function.comp_def, mul_comm] using hcomp.deriv
  have hGderiv : gaussCutPlane.EqOn (deriv g)
      (fun z => -deriv G (1 - z)) := by
    intro z hz
    have hw  := one_sub_gaussCutPlane_subset_gaussCutPlane hz
    have hAt := (hGdiff (1 - z) hw).differentiableAt
      (gaussCutPlane_isOpen_for_wronskians.mem_nhds hw)
    have hcomp := hAt.hasDerivAt.comp z (hmap z)
    calc
      deriv g z = deriv (fun w => G (1 - w)) z := by rw [hGident]
      _ = -deriv G (1 - z) := by
        simpa [Function.comp_def, mul_comm] using hcomp.deriv
  intro z hz
  let w  := 1 - z
  have hw : w ∈ gaussCutPlane := one_sub_gaussCutPlane_subset_gaussCutPlane hz
  have hW := gaussFPlus_wronskian_identity hH a b c₀ hc₀ w hw
  grind

end DOZZ.Proofs
