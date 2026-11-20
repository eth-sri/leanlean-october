/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.BasisEquationTransforms
public import DOZZ.Hypergeom.Germs

/-! Abel's identity and the endpoint normalization of the zero-basis Wronskian. -/

@[expose] public section

namespace DOZZ.Proofs

open Filter Topology

theorem analyticOnNhd_wronskian {s : Set ℂ} {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f s) (hg : AnalyticOnNhd ℂ g s) :
    AnalyticOnNhd ℂ (fun z => f z * deriv g z - deriv f z * g z) s :=
  (hf.mul hg.deriv).sub (hf.deriv.mul hg)

/-- The Wronskian of two holomorphic Gauss solutions satisfies Abel's identity. -/
theorem gauss_pair_wronskian_abel
    (a b c : ℂ) (f g : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f gaussCutPlane)
    (hg : AnalyticOnNhd ℂ g gaussCutPlane)
    (hfeq : ∀ z ∈ gaussCutPlane,
      gaussHolomorphicOperator a b c f z = 0)
    (hgeq : ∀ z ∈ gaussCutPlane,
      gaussHolomorphicOperator a b c g z = 0) :
    ∀ z ∈ gaussCutPlane,
      z * (1 - z) * deriv (fun w => f w * deriv g w - deriv f w * g w) z +
        (c - (a + b + 1) * z) *
          (f z * deriv g z - deriv f z * g z) = 0 := by
  intro z hz
  have hd := (((hf z hz).differentiableAt.hasDerivAt.mul (hg.deriv z hz).differentiableAt.hasDerivAt).sub
    ((hf.deriv z hz).differentiableAt.hasDerivAt.mul (hg z hz).differentiableAt.hasDerivAt)).deriv
  change z * (1 - z) * deriv (f * deriv g - deriv f * g) z + _ = 0
  rw [hd]
  have hfz := hfeq z hz
  have hgz := hgeq z hz
  dsimp [gaussHolomorphicOperator] at hfz hgz
  linear_combination f z * hgz - g z * hfz

section
variable {H : ℂ → ℂ → ℂ → ℂ → ℂ} (hH : IsGaussHypergeometricFamily H) (a b c : ℂ)
include hH

/-- The zero-basis Wronskian has its explicit value on the principal cut plane. -/
theorem gaussFPlus_wronskian_identity (hc : ∀ n : ℤ, c ≠ (n : ℂ)) :
    ∀ z ∈ gaussCutPlane,
      gaussFMinus H a b c z * deriv (gaussFPlus H a b c) z -
        deriv (gaussFMinus H a b c) z * gaussFPlus H a b c z =
          (1 - c) * z ^ (-c) * (1 - z) ^ (c - a - b - 1) := by
  let f := gaussFMinus H a b c
  let v := H (a - c + 1) (b - c + 1) (2 - c)
  let g := gaussFPlus H a b c
  let e := a + b - c + 1
  let q : ℂ → ℂ := fun z => (1 - z) ^ e
  let p : ℂ → ℂ := fun z => z ^ c
  let W : ℂ → ℂ := fun z => f z * deriv g z - deriv f z * g z
  let S := p * q * W
  have hf := hH a b c (parameter_ne_nat_neg_of_ne_int hc)
  have hv := hH (a - c + 1) (b - c + 1) (2 - c) (two_sub_parameter_ne_nat_neg hc)
  have hF : AnalyticOnNhd ℂ f gaussSlitPlane := hf.1.analyticOnNhd gaussSlitPlane_isOpen
  have hV : AnalyticOnNhd ℂ v gaussSlitPlane := hv.1.analyticOnNhd gaussSlitPlane_isOpen
  have hFcut := hF.mono gaussCutPlane_subset_gaussSlitPlane
  have hG := (gaussFPlus_differentiableOn_cutPlane hH a b c hc).analyticOnNhd gaussCutPlane_isOpen
  have hW : AnalyticOnNhd ℂ W gaussCutPlane := analyticOnNhd_wronskian hFcut hG
  have hAbel := gauss_pair_wronskian_abel a b c f g hFcut hG
    (gaussFMinus_holomorphicOperator_eq_zero hH a b c hc) (gaussFPlus_holomorphicOperator_eq_zero hH a b c hc)
  have hP (z) (hz : z ∈ gaussCutPlane) : HasDerivAt p (c * (p z / z)) z := by
    have h := (Complex.hasStrictDerivAt_cpow_const (c := c)
      (gaussCutPlane_subset_Complex_slitPlane hz)).hasDerivAt
    simpa [p, Complex.cpow_sub c 1 (gaussCutPlane_subset_regularPlane hz).1] using h
  have hQ (z) (hz : z ∈ gaussCutPlane) : HasDerivAt q (e * (q z / (1 - z)) * (-1)) z := by
    have hw := one_sub_gaussCutPlane_subset_gaussCutPlane hz
    have h := ((hasDerivAt_id z).const_sub (1 : ℂ)).cpow_const (c := e)
      (gaussCutPlane_subset_Complex_slitPlane hw)
    simpa [q, Complex.cpow_sub e 1 (gaussCutPlane_subset_regularPlane hw).1] using h
  have hD : DifferentiableOn ℂ S gaussCutPlane := fun z hz =>
    (((hP z hz).mul (hQ z hz)).mul (hW z hz).differentiableAt.hasDerivAt).differentiableAt.differentiableWithinAt
  have hS : gaussCutPlane.EqOn (deriv S) (fun _ => 0) := by
    intro z hz
    have hz0 := (gaussCutPlane_subset_regularPlane hz).1
    have hw0 := (gaussCutPlane_subset_regularPlane (one_sub_gaussCutPlane_subset_gaussCutPlane hz)).1
    have hd := (((hP z hz).mul (hQ z hz)).mul (hW z hz).differentiableAt.hasDerivAt).deriv
    change deriv S z = 0
    rw [show deriv S z = _ from hd]
    have eqn := hAbel z hz
    change z * (1 - z) * deriv W z + _ * W z = 0 at eqn
    dsimp only [Pi.mul_apply]
    field_simp [hz0, hw0]
    dsimp only [e]
    linear_combination p z * q z * eqn
  have hmid : (1 / 2 : ℂ) ∈ gaussCutPlane := by norm_num [gaussCutPlane]
  have hconst z (hz : z ∈ gaussCutPlane) : S z = S (1 / 2) :=
    gaussCutPlane_isOpen.is_const_of_deriv_eq_zero gaussCutPlane_isPreconnected hD hS hz hmid
  let R := fun z => q z * ((1 - c) * f z * v z + z * (f z * deriv v z - deriv f z * v z))
  have hSR : gaussCutPlane.EqOn S R := by
    intro z hz
    have hs := gaussCutPlane_subset_Complex_slitPlane hz
    have hz0 := Complex.slitPlane_ne_zero hs
    have hd : deriv g z = (1 - c) * z ^ (-c) * v z + z ^ (1 - c) * deriv v z := by
      have hp := (Complex.hasStrictDerivAt_cpow_const (c := 1 - c) hs).hasDerivAt
      change deriv ((fun w : ℂ => w ^ (1 - c)) * v) z = _
      simpa using (hp.mul (hV z (gaussCutPlane_subset_gaussSlitPlane hz)).differentiableAt.hasDerivAt).deriv
    have hp₀ : p z * z ^ (-c) = 1 := by dsimp [p]; rw [← Complex.cpow_add _ _ hz0]; simp
    have hp₁ : p z * z ^ (1 - c) = z := by dsimp [p]; rw [← Complex.cpow_add _ _ hz0]; simp
    change p z * q z * (f z * deriv g z - deriv f z * (z ^ (1 - c) * v z)) = R z
    rw [hd]
    dsimp only [R]
    linear_combination (1 - c) * q z * f z * v z * hp₀ + q z * (f z * deriv v z - deriv f z * v z) * hp₁
  have hzero : (0 : ℂ) ∈ gaussSlitPlane := by simp [gaussSlitPlane]
  have hR : ContinuousAt R 0 := by
    have hf₀ := (hF 0 hzero).continuousAt
    have hv₀ := (hV 0 hzero).continuousAt
    have hf₁ := (hF.deriv 0 hzero).continuousAt
    have hv₁ := (hV.deriv 0 hzero).continuousAt
    have hq : ContinuousAt q 0 :=
      (by fun_prop : ContinuousAt (fun z : ℂ => 1 - z) 0).cpow continuousAt_const (by simp)
    dsimp only [R]
    fun_prop
  have hF₀ : f 0 = 1 := by simpa [f, gaussFMinus] using hf.2 0 (by norm_num : ‖(0 : ℂ)‖ < 1)
  have hV₀ : v 0 = 1 := by simpa [v] using hv.2 0 (by norm_num : ‖(0 : ℂ)‖ < 1)
  have hR₀ : R 0 = 1 - c := by simp [R, q, hF₀, hV₀]
  have hcl : (0 : ℂ) ∈ closure gaussCutPlane := by
    have hr : (0 : ℝ) ∈ closure (Set.Ioo 0 1) := by rw [closure_Ioo (by norm_num)]; simp
    simpa using closure_mono (by
      rintro _ ⟨x, hx, rfl⟩
      simpa [gaussCutPlane] using hx) (mem_closure_image Complex.continuous_ofReal.continuousAt hr)
  have := mem_closure_iff_nhdsWithin_neBot.mp hcl
  have hval : S (1 / 2) = R 0 := by
    refine tendsto_nhds_unique_of_eventuallyEq (l := nhdsWithin 0 gaussCutPlane) tendsto_const_nhds hR.continuousWithinAt ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (hconst z hz).symm.trans (hSR hz)
  intro z hz
  have he := (hconst z hz).trans (hval.trans hR₀)
  have hz0 := (gaussCutPlane_subset_regularPlane hz).1
  have hw0 := (gaussCutPlane_subset_regularPlane (one_sub_gaussCutPlane_subset_gaussCutPlane hz)).1
  have hden : p z * q z ≠ 0 := mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl hz0))
    (Complex.cpow_ne_zero_iff.mpr (Or.inl hw0))
  have hw : W z = (1 - c) / (p z * q z) := (eq_div_iff hden).mpr (by simpa [S, mul_comm] using he)
  change W z = _
  rw [hw, div_eq_mul_inv, mul_inv_rev, ← mul_assoc, mul_right_comm (1 - c)]
  simp [p, q, ← Complex.cpow_neg, show -e = c - a - b - 1 by dsimp [e]; ring]

/-- The one-basis Wronskian follows from the zero-basis identity by reflection. -/
theorem gaussGPlus_wronskian_identity (hδ : ∀ n : ℤ, c - a - b ≠ (n : ℂ)) :
    ∀ z ∈ gaussCutPlane,
      gaussGMinus H a b c z * deriv (gaussGPlus H a b c) z -
        deriv (gaussGMinus H a b c) z * gaussGPlus H a b c z =
          -(c - a - b) * z ^ (-c) * (1 - z) ^ (c - a - b - 1) := by
  let c₀ := 1 + a + b - c
  have hc₀ := one_add_a_add_b_sub_c_ne_int hδ
  intro z hz
  have hw := one_sub_gaussCutPlane_subset_gaussCutPlane hz
  rw [gaussGMinus_eq_reflect, gaussGPlus_eq_reflect,
    (hasDerivAt_gaussReflect ((gaussFMinus_differentiableOn_cutPlane hH a b c₀ hc₀ _ hw).differentiableAt
      (gaussCutPlane_isOpen.mem_nhds hw))).deriv,
    (hasDerivAt_gaussReflect ((gaussFPlus_differentiableOn_cutPlane hH a b c₀ hc₀ _ hw).differentiableAt
      (gaussCutPlane_isOpen.mem_nhds hw))).deriv]
  have he := gaussFPlus_wronskian_identity hH a b c₀ hc₀ _ hw
  grind (splits := 0)

end

end DOZZ.Proofs
