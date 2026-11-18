/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.BasisWronskians
public import DOZZ.Hypergeom.ODE.CutPlaneTopology

/-! A nonvanishing Wronskian gives a global basis of Gauss solutions. -/

@[expose] public section

namespace DOZZ.Proofs

section
variable (a b c : ℂ) (f g : ℂ → ℂ)
include a b c f g

/-- The Wronskian of two holomorphic Gauss solutions satisfies Abel's identity. -/
theorem gauss_pair_wronskian_abel

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
  let W : ℂ → ℂ := fun z => f z * deriv g z - deriv f z * g z
  have hWderiv : ∀ z ∈ gaussCutPlane,
      deriv W z = f z * deriv (deriv g) z - deriv (deriv f) z * g z := by
    intro z hz
    have hleft := (hf z hz).differentiableAt.hasDerivAt.mul
      ((hg.deriv) z hz).differentiableAt.hasDerivAt
    have hright := ((hf.deriv) z hz).differentiableAt.hasDerivAt.mul
      (hg z hz).differentiableAt.hasDerivAt
    change deriv (fun w => f w * deriv g w - deriv f w * g w) z = _
    have hfun : (fun w => f w * deriv g w - deriv f w * g w) =
        f * deriv g - deriv f * g := by
      funext w
      rfl
    rw [hfun, (hleft.sub hright).deriv]
    ring
  intro z hz
  rw [hWderiv z hz]
  have hfeq := hfeq z hz
  have hgeq := hgeq z hz
  dsimp [gaussHolomorphicOperator] at hfeq hgeq
  linear_combination (f z) * hgeq - (g z) * hfeq

/-- On the principal cut plane, any solution is the unique constant linear combination of two
holomorphic solutions whose Wronskian never vanishes. -/
theorem gauss_two_solution_span_unique

    (hfDiff : DifferentiableOn ℂ f gaussCutPlane)
    (hgDiff : DifferentiableOn ℂ g gaussCutPlane)
    (hfeq : ∀ z ∈ gaussCutPlane,
      gaussHolomorphicOperator a b c f z = 0)
    (hgeq : ∀ z ∈ gaussCutPlane,
      gaussHolomorphicOperator a b c g z = 0)
    (hWne : ∀ z ∈ gaussCutPlane,
      f z * deriv g z - deriv f z * g z ≠ 0)
    (y : ℂ → ℂ) (hyDiff : DifferentiableOn ℂ y gaussCutPlane)
    (hyeq : ∀ z ∈ gaussCutPlane,
      gaussHolomorphicOperator a b c y z = 0) :
    ∃! v : ℂ × ℂ, ∀ z ∈ gaussCutPlane,
      y z = v.1 * f z + v.2 * g z := by
  let W : ℂ → ℂ := fun z => f z * deriv g z - deriv f z * g z
  let A : ℂ → ℂ := fun z => y z * deriv g z - deriv y z * g z
  let B : ℂ → ℂ := fun z => f z * deriv y z - deriv f z * y z
  let α : ℂ → ℂ := fun z => A z / W z
  let β : ℂ → ℂ := fun z => B z / W z
  have hfAnalytic :=
    hfDiff.analyticOnNhd gaussCutPlane_isOpen
  have hgAnalytic :=
    hgDiff.analyticOnNhd gaussCutPlane_isOpen
  have hyAnalytic :=
    hyDiff.analyticOnNhd gaussCutPlane_isOpen
  have := hfAnalytic.deriv
  have := hgAnalytic.deriv
  have := hyAnalytic.deriv
  have hWanalytic : AnalyticOnNhd ℂ W gaussCutPlane := by fun_prop
  have hAanalytic : AnalyticOnNhd ℂ A gaussCutPlane := by fun_prop
  have hBanalytic : AnalyticOnNhd ℂ B gaussCutPlane := by fun_prop
  have hWabel : ∀ z ∈ gaussCutPlane,
      z * (1 - z) * deriv W z +
        (c - (a + b + 1) * z) * W z = 0 := by
    intro z hz
    simpa [W] using gauss_pair_wronskian_abel a b c f g
      hfAnalytic hgAnalytic hfeq hgeq z hz
  have hAabel : ∀ z ∈ gaussCutPlane,
      z * (1 - z) * deriv A z +
        (c - (a + b + 1) * z) * A z = 0 := by
    intro z hz
    simpa [A] using gauss_pair_wronskian_abel a b c y g
      hyAnalytic hgAnalytic hyeq hgeq z hz
  have hBabel : ∀ z ∈ gaussCutPlane,
      z * (1 - z) * deriv B z +
        (c - (a + b + 1) * z) * B z = 0 := by
    intro z hz
    simpa [B] using gauss_pair_wronskian_abel a b c f y
      hfAnalytic hyAnalytic hfeq hyeq z hz
  have := hWanalytic.differentiableOn
  have := hAanalytic.differentiableOn
  have := hBanalytic.differentiableOn
  have hαdiff : DifferentiableOn ℂ α gaussCutPlane := by fun_prop
  have hβdiff : DifferentiableOn ℂ β gaussCutPlane := by fun_prop
  have hαderivZero : gaussCutPlane.EqOn (deriv α) (fun _ => 0) := by
    intro z hz
    have hreg := gaussCutPlane_subset_regularPlane hz
    have hnum : deriv A z * W z - A z * deriv W z = 0 := by
      have hmul : z * (1 - z) *
          (deriv A z * W z - A z * deriv W z) = 0 := by
        linear_combination (W z) * hAabel z hz - (A z) * hWabel z hz
      exact (mul_eq_zero.mp hmul).resolve_left (mul_ne_zero hreg.1 (sub_ne_zero.mpr (Ne.symm hreg.2)))
    change deriv (A / W) z = 0
    rw [(((hAanalytic z hz).differentiableAt).hasDerivAt.div ((hWanalytic z hz).differentiableAt).hasDerivAt (hWne z hz)).deriv, hnum]
    simp
  have hβderivZero : gaussCutPlane.EqOn (deriv β) (fun _ => 0) := by
    intro z hz
    have hreg := gaussCutPlane_subset_regularPlane hz
    have hnum : deriv B z * W z - B z * deriv W z = 0 := by
      have hmul : z * (1 - z) *
          (deriv B z * W z - B z * deriv W z) = 0 := by
        linear_combination (W z) * hBabel z hz - (B z) * hWabel z hz
      exact (mul_eq_zero.mp hmul).resolve_left (mul_ne_zero hreg.1 (sub_ne_zero.mpr (Ne.symm hreg.2)))
    change deriv (B / W) z = 0
    rw [(((hBanalytic z hz).differentiableAt).hasDerivAt.div ((hWanalytic z hz).differentiableAt).hasDerivAt (hWne z hz)).deriv, hnum]
    simp
  have hcutPre : IsPreconnected gaussCutPlane := by
    rw [isPreconnected_iff_preconnectedSpace]
    infer_instance
  have hmid : (1 / 2 : ℂ) ∈ gaussCutPlane := by norm_num [gaussCutPlane]
  have : ∀ z ∈ gaussCutPlane, α z = α (1 / 2) := by
    intro z hz
    exact gaussCutPlane_isOpen.is_const_of_deriv_eq_zero
      hcutPre hαdiff hαderivZero hz hmid
  have : ∀ z ∈ gaussCutPlane, β z = β (1 / 2) := by
    intro z hz
    exact gaussCutPlane_isOpen.is_const_of_deriv_eq_zero
      hcutPre hβdiff hβderivZero hz hmid
  let v := (α (1 / 2), β (1 / 2))
  have hv : ∀ z ∈ gaussCutPlane, y z = v.1 * f z + v.2 * g z := by grind
  refine ⟨v, hv, ?_⟩
  intro v' hv'
  have hlinearDeriv (r s : ℂ) :
      deriv (fun z => r * f z + s * g z) (1 / 2) =
        r * deriv f (1 / 2) + s * deriv g (1 / 2) := by
    exact ((((hfAnalytic (1 / 2) hmid).differentiableAt).hasDerivAt.const_mul r).add (((hgAnalytic (1 / 2) hmid).differentiableAt).hasDerivAt.const_mul s)).deriv
  have hmidDeriv (r s : ℂ)
      (hvalues : ∀ z ∈ gaussCutPlane, y z = r * f z + s * g z) :
      deriv y (1 / 2) = r * deriv f (1 / 2) + s * deriv g (1 / 2) := by
    have hEqOn : gaussCutPlane.EqOn y (fun z => r * f z + s * g z) := hvalues
    exact (hEqOn.deriv gaussCutPlane_isOpen hmid).trans (hlinearDeriv r s)
  have hE0 : (v'.1 - v.1) * f (1 / 2) + (v'.2 - v.2) * g (1 / 2) = 0 := by
    calc
      _ = (v'.1 * f (1 / 2) + v'.2 * g (1 / 2)) -
          (v.1 * f (1 / 2) + v.2 * g (1 / 2)) := by ring
      _ = y (1 / 2) - y (1 / 2) := by rw [← (hv' (1 / 2) hmid), ← (hv (1 / 2) hmid)]
      _ = 0 := by ring
  have hE1 : (v'.1 - v.1) * deriv f (1 / 2) +
      (v'.2 - v.2) * deriv g (1 / 2) = 0 := by
    calc
      _ = (v'.1 * deriv f (1 / 2) + v'.2 * deriv g (1 / 2)) -
          (v.1 * deriv f (1 / 2) + v.2 * deriv g (1 / 2)) := by ring
      _ = deriv y (1 / 2) - deriv y (1 / 2) := by
        rw [← hmidDeriv v'.1 v'.2 hv', ← hmidDeriv v.1 v.2 hv]
      _ = 0 := by ring
  have hWmid : W (1 / 2) ≠ 0 := by
    simpa [W] using hWne (1 / 2) hmid
  apply Prod.ext
  · have hprod : (v'.1 - v.1) * W (1 / 2) = 0 := by
      dsimp [W]
      linear_combination (deriv g (1 / 2)) * hE0 - g (1 / 2) * hE1
    exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right hWmid)
  · have hprod : (v'.2 - v.2) * W (1 / 2) = 0 := by
      dsimp [W]
      linear_combination f (1 / 2) * hE1 - deriv f (1 / 2) * hE0
    exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right hWmid)


end
section
variable {H : ℂ → ℂ → ℂ → ℂ → ℂ} (hH : IsGaussHypergeometricFamily H) (a b c : ℂ)
include hH a b c

/-- The zero-end local basis, including its Wronskian and global spanning property. -/
theorem gauss_local_basis_zero
    (hc : ∀ n : ℤ, c ≠ (n : ℂ)) :
    DifferentiableOn ℂ (gaussFMinus H a b c) gaussCutPlane ∧
    DifferentiableOn ℂ (gaussFPlus H a b c) gaussCutPlane ∧
    (∀ z ∈ gaussCutPlane,
      gaussHolomorphicOperator a b c (gaussFMinus H a b c) z = 0 ∧
      gaussHolomorphicOperator a b c (gaussFPlus H a b c) z = 0 ∧
      gaussFMinus H a b c z * deriv (gaussFPlus H a b c) z -
        deriv (gaussFMinus H a b c) z * gaussFPlus H a b c z =
          (1 - c) * z ^ (-c) * (1 - z) ^ (c - a - b - 1)) ∧
    (∀ y : ℂ → ℂ, DifferentiableOn ℂ y gaussCutPlane →
      (∀ z ∈ gaussCutPlane, gaussHolomorphicOperator a b c y z = 0) →
      ∃! v : ℂ × ℂ, ∀ z ∈ gaussCutPlane,
        y z = v.1 * gaussFMinus H a b c z + v.2 * gaussFPlus H a b c z) := by
  have hFminusDiff := gaussFMinus_differentiableOn_cutPlane hH a b c hc
  have hFplusDiff := gaussFPlus_differentiableOn_cutPlane hH a b c hc
  have hFminusEq := gaussFMinus_holomorphicOperator_eq_zero hH a b c hc
  have hFplusEq := gaussFPlus_holomorphicOperator_eq_zero hH a b c hc
  have hW := gaussFPlus_wronskian_identity hH a b c hc
  refine ⟨hFminusDiff, hFplusDiff, ?_, ?_⟩
  · intro z hz
    exact ⟨hFminusEq z hz, hFplusEq z hz, hW z hz⟩
  · intro y hyDiff hyEq
    refine gauss_two_solution_span_unique a b c
      (gaussFMinus H a b c) (gaussFPlus H a b c)
      hFminusDiff hFplusDiff hFminusEq hFplusEq ?_ y hyDiff hyEq
    intro z hz
    have hzreg := gaussCutPlane_subset_regularPlane hz
    have hw0 : 1 - z ≠ 0 := by
      intro he
      apply hzreg.2
      exact (sub_eq_zero.mp he).symm
    have hpowz : z ^ (-c) ≠ 0 :=
      Complex.cpow_ne_zero_iff.mpr (Or.inl hzreg.1)
    have hpoww : (1 - z) ^ (c - a - b - 1) ≠ 0 :=
      Complex.cpow_ne_zero_iff.mpr (Or.inl hw0)
    have hcoeff : (1 - c) ≠ 0 := by
      intro he
      apply hc 1
      exact_mod_cast (sub_eq_zero.mp he).symm
    rw [hW z hz]
    exact mul_ne_zero (mul_ne_zero hcoeff hpowz) hpoww

/-- The one-end local basis, including its Wronskian and global spanning property. -/
theorem gauss_local_basis_one
    (hδ : ∀ n : ℤ, c - a - b ≠ (n : ℂ)) :
    DifferentiableOn ℂ (gaussGMinus H a b c) gaussCutPlane ∧
    DifferentiableOn ℂ (gaussGPlus H a b c) gaussCutPlane ∧
    (∀ z ∈ gaussCutPlane,
      gaussHolomorphicOperator a b c (gaussGMinus H a b c) z = 0 ∧
      gaussHolomorphicOperator a b c (gaussGPlus H a b c) z = 0 ∧
      gaussGMinus H a b c z * deriv (gaussGPlus H a b c) z -
        deriv (gaussGMinus H a b c) z * gaussGPlus H a b c z =
          -(c - a - b) * z ^ (-c) * (1 - z) ^ (c - a - b - 1)) ∧
    (∀ y : ℂ → ℂ, DifferentiableOn ℂ y gaussCutPlane →
      (∀ z ∈ gaussCutPlane, gaussHolomorphicOperator a b c y z = 0) →
      ∃! v : ℂ × ℂ, ∀ z ∈ gaussCutPlane,
        y z = v.1 * gaussGMinus H a b c z + v.2 * gaussGPlus H a b c z) := by
  have hGminusDiff := gaussGMinus_differentiableOn_cutPlane hH a b c hδ
  have hGplusDiff := gaussGPlus_differentiableOn_cutPlane hH a b c hδ
  have hGminusEq := gaussGMinus_holomorphicOperator_eq_zero hH a b c hδ
  have hGplusEq := gaussGPlus_holomorphicOperator_eq_zero hH a b c hδ
  have hW := gaussGPlus_wronskian_identity hH a b c hδ
  refine ⟨hGminusDiff, hGplusDiff, ?_, ?_⟩
  · intro z hz
    exact ⟨hGminusEq z hz, hGplusEq z hz, hW z hz⟩
  · intro y hyDiff hyEq
    refine gauss_two_solution_span_unique a b c
      (gaussGMinus H a b c) (gaussGPlus H a b c)
      hGminusDiff hGplusDiff hGminusEq hGplusEq ?_ y hyDiff hyEq
    intro z hz
    have hzreg := gaussCutPlane_subset_regularPlane hz
    have hw0 : 1 - z ≠ 0 := by
      intro he
      apply hzreg.2
      exact (sub_eq_zero.mp he).symm
    have hpowz : z ^ (-c) ≠ 0 :=
      Complex.cpow_ne_zero_iff.mpr (Or.inl hzreg.1)
    have hpoww : (1 - z) ^ (c - a - b - 1) ≠ 0 :=
      Complex.cpow_ne_zero_iff.mpr (Or.inl hw0)
    have hcoeff : -(c - a - b) ≠ 0 := by
      intro he
      apply hδ 0
      exact_mod_cast (neg_eq_zero.mp he)
    rw [hW z hz]
    exact mul_ne_zero (mul_ne_zero hcoeff hpowz) hpoww


end
end DOZZ.Proofs
