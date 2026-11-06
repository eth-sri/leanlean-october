/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.BasisWronskians
public import DOZZ.Hypergeom.ODE.CutPlaneTopology
import Mathlib.Tactic

/-! A nonvanishing Wronskian gives a global basis of Gauss solutions. -/

public section

namespace DOZZ.Proofs

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
  let W  := fun z => f z * deriv g z - deriv f z * g z
  have hf₁  := hf.deriv
  have hg₁  := hg.deriv
  
  have hWderiv : ∀ z ∈ gaussCutPlane,
      deriv W z = f z * deriv (deriv g) z - deriv (deriv f) z * g z := by
    intro z hz
    have hleft := (hf z hz).differentiableAt.hasDerivAt.mul
      (hg₁ z hz).differentiableAt.hasDerivAt
    have hright := (hf₁ z hz).differentiableAt.hasDerivAt.mul
      (hg z hz).differentiableAt.hasDerivAt
    have hsub := hleft.sub hright
    change deriv (fun w => f w * deriv g w - deriv f w * g w) z = _
    have hfun : (fun w => f w * deriv g w - deriv f w * g w) =
        f * deriv g - deriv f * g := by
      funext w
      rfl
    rw [hfun, hsub.deriv]
    ring
  intro z hz
  rw [hWderiv z hz]
  have hfeq := hfeq z hz
  have hgeq := hgeq z hz
  dsimp [gaussHolomorphicOperator] at hfeq hgeq
  grind

/-- On the principal cut plane, any solution is the unique constant linear combination of two
holomorphic solutions whose Wronskian never vanishes. -/
theorem gauss_two_solution_span_unique
    (a b c : ℂ) (f g : ℂ → ℂ)
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
  let W  := fun z => f z * deriv g z - deriv f z * g z
  let A  := fun z => y z * deriv g z - deriv y z * g z
  let B  := fun z => f z * deriv y z - deriv f z * y z
  let α  := fun z => A z / W z
  let β  := fun z => B z / W z
  have hfAnalytic  :=
    hfDiff.analyticOnNhd gaussCutPlane_isOpen
  have hgAnalytic  :=
    hgDiff.analyticOnNhd gaussCutPlane_isOpen
  have hyAnalytic  :=
    hyDiff.analyticOnNhd gaussCutPlane_isOpen
  have hf₁  := hfAnalytic.deriv
  have hg₁  := hgAnalytic.deriv
  have hy₁  := hyAnalytic.deriv
  have hWanalytic : AnalyticOnNhd ℂ W gaussCutPlane := by
    fun_prop
  have hAanalytic : AnalyticOnNhd ℂ A gaussCutPlane := by
    fun_prop
  have hBanalytic : AnalyticOnNhd ℂ B gaussCutPlane := by
    fun_prop
  have hWabel : ∀ z ∈ gaussCutPlane,
      z * (1 - z) * deriv W z +
        (c - (a + b + 1) * z) * W z = 0 := by
    intro z hz
    exact gauss_pair_wronskian_abel a b c f g
      hfAnalytic hgAnalytic hfeq hgeq z hz
  have hAabel : ∀ z ∈ gaussCutPlane,
      z * (1 - z) * deriv A z +
        (c - (a + b + 1) * z) * A z = 0 := by
    intro z hz
    exact gauss_pair_wronskian_abel a b c y g
      hyAnalytic hgAnalytic hyeq hgeq z hz
  have hBabel : ∀ z ∈ gaussCutPlane,
      z * (1 - z) * deriv B z +
        (c - (a + b + 1) * z) * B z = 0 := by
    intro z hz
    exact gauss_pair_wronskian_abel a b c f y
      hfAnalytic hyAnalytic hfeq hyeq z hz
  have hWdiff  := hWanalytic.differentiableOn
  have hAdiff  := hAanalytic.differentiableOn
  have hBdiff  := hBanalytic.differentiableOn
  have hαdiff  := hAdiff.div hWdiff hWne
  have hβdiff  := hBdiff.div hWdiff hWne
  have hαderivZero : gaussCutPlane.EqOn (deriv α) (fun _ => 0) := by
    intro z hz
    have hAAt := (hAanalytic z hz).differentiableAt
    have hWAt := (hWanalytic z hz).differentiableAt
    have hquot := (hAAt.hasDerivAt.div hWAt.hasDerivAt (hWne z hz)).deriv
    have hreg := gaussCutPlane_subset_regularPlane hz
    have hden  :=
      mul_ne_zero hreg.1 (sub_ne_zero.mpr (Ne.symm hreg.2))
    have hnum : deriv A z * W z - A z * deriv W z = 0 := by
      grind
    change deriv (A / W) z = 0
    rw [hquot, hnum]
    simp
  have hβderivZero : gaussCutPlane.EqOn (deriv β) (fun _ => 0) := by
    intro z hz
    have hBAt := (hBanalytic z hz).differentiableAt
    have hWAt := (hWanalytic z hz).differentiableAt
    have hquot := (hBAt.hasDerivAt.div hWAt.hasDerivAt (hWne z hz)).deriv
    have hreg := gaussCutPlane_subset_regularPlane hz
    have hden  :=
      mul_ne_zero hreg.1 (sub_ne_zero.mpr (Ne.symm hreg.2))
    have hnum : deriv B z * W z - B z * deriv W z = 0 := by
      grind
    change deriv (B / W) z = 0
    rw [hquot, hnum]
    simp
  have hcutPre : IsPreconnected gaussCutPlane := by
    rw [isPreconnected_iff_preconnectedSpace]
    infer_instance
  have hmid : (1 / 2 : ℂ) ∈ gaussCutPlane := by norm_num [gaussCutPlane]
  have hαconst : ∀ z ∈ gaussCutPlane, α z = α (1 / 2) := by
    intro z hz
    exact gaussCutPlane_isOpen.is_const_of_deriv_eq_zero
      hcutPre hαdiff hαderivZero hz hmid
  have hβconst : ∀ z ∈ gaussCutPlane, β z = β (1 / 2) := by
    intro z hz
    exact gaussCutPlane_isOpen.is_const_of_deriv_eq_zero
      hcutPre hβdiff hβderivZero hz hmid
  have hdecompose : ∀ z ∈ gaussCutPlane,
      y z = α z * f z + β z * g z := by
    grind
  let v  := (α (1 / 2), β (1 / 2))
  have hv : ∀ z ∈ gaussCutPlane, y z = v.1 * f z + v.2 * g z := by
    grind
  refine ⟨v, hv, ?_⟩
  intro v' hv'
  have hmidValue  := hv' (1 / 2) hmid
  
  have hFAt  := (hfAnalytic (1 / 2) hmid).differentiableAt
  have hGAt  := (hgAnalytic (1 / 2) hmid).differentiableAt
  have hlinearDeriv (r s : ℂ) :
      deriv (fun z => r * f z + s * g z) (1 / 2) =
        r * deriv f (1 / 2) + s * deriv g (1 / 2) := by
    have hsum := (hFAt.hasDerivAt.const_mul r).add (hGAt.hasDerivAt.const_mul s)
    exact hsum.deriv
  have hmidDeriv (r s : ℂ)
      (hvalues : ∀ z ∈ gaussCutPlane, y z = r * f z + s * g z) :
      deriv y (1 / 2) = r * deriv f (1 / 2) + s * deriv g (1 / 2) := by
    have hEqOn : gaussCutPlane.EqOn y (fun z => r * f z + s * g z) := hvalues
    have hderiv := hEqOn.deriv gaussCutPlane_isOpen hmid
    grind
  
  have hE1 : (v'.1 - v.1) * deriv f (1 / 2) +
      (v'.2 - v.2) * deriv g (1 / 2) = 0 := by
    calc
      _ = (v'.1 * deriv f (1 / 2) + v'.2 * deriv g (1 / 2)) -
          (v.1 * deriv f (1 / 2) + v.2 * deriv g (1 / 2)) := by ring
      _ = deriv y (1 / 2) - deriv y (1 / 2) := by
        rw [← hmidDeriv v'.1 v'.2 hv', ← hmidDeriv v.1 v.2 hv]
      _ = 0 := by ring
  grind

variable {H : ℂ → ℂ → ℂ → ℂ → ℂ} (hH : IsGaussHypergeometricFamily H) (a b c : ℂ)

include H hH a b c in
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
  · simp_all
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
    
    have hcoeff : (1 - c) ≠ 0 := by
      intro he
      apply hc 1
      exact_mod_cast (sub_eq_zero.mp he).symm
    simp_all

include H hH a b c in
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
  · simp_all
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
    
    have hcoeff : -(c - a - b) ≠ 0 := by
      intro he
      apply hδ 0
      exact_mod_cast (neg_eq_zero.mp he)
    simp_all

end DOZZ.Proofs
