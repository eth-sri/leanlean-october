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
  let W : ℂ → ℂ := fun z => f z * deriv g z - deriv f z * g z
  let A : ℂ → ℂ := fun z => y z * deriv g z - deriv y z * g z
  let B : ℂ → ℂ := fun z => f z * deriv y z - deriv f z * y z
  let m : ℂ := 1 / 2
  have hm : m ∈ gaussCutPlane := by norm_num [m, gaussCutPlane]
  have hf := hfDiff.analyticOnNhd gaussCutPlane_isOpen
  have hg := hgDiff.analyticOnNhd gaussCutPlane_isOpen
  have hy := hyDiff.analyticOnNhd gaussCutPlane_isOpen
  have hW : AnalyticOnNhd ℂ W gaussCutPlane := analyticOnNhd_wronskian hf hg
  have habel := gauss_pair_wronskian_abel a b c f g hf hg hfeq hgeq
  have hconst (V : ℂ → ℂ) (hV : AnalyticOnNhd ℂ V gaussCutPlane)
      (hVabel : ∀ z ∈ gaussCutPlane,
        z * (1 - z) * deriv V z + (c - (a + b + 1) * z) * V z = 0) :
      ∀ z ∈ gaussCutPlane, V z / W z = V m / W m := by
    refine fun z hz => gaussCutPlane_isOpen.is_const_of_deriv_eq_zero (f := V / W)
      gaussCutPlane_isPreconnected (hV.differentiableOn.div hW.differentiableOn hWne) ?_ hz hm
    intro w hw
    change deriv (V / W) w = 0
    rw [((hV w hw).differentiableAt.hasDerivAt.div (hW w hw).differentiableAt.hasDerivAt (hWne w hw)).deriv]
    have hd : w * (1 - w) ≠ 0 := mul_ne_zero (gaussCutPlane_subset_regularPlane hw).1
      (gaussCutPlane_subset_regularPlane (one_sub_gaussCutPlane_subset_gaussCutPlane hw)).1
    suffices deriv V w * W w - V w * deriv W w = 0 by rw [this, zero_div]
    apply (mul_eq_zero.mp (show w * (1 - w) * (deriv V w * W w - V w * deriv W w) = 0 from ?_)).resolve_left hd
    have h := habel w hw
    change w * (1 - w) * deriv W w + _ * W w = 0 at h
    linear_combination W w * hVabel w hw - V w * h
  have hA := hconst A (analyticOnNhd_wronskian hy hg) (gauss_pair_wronskian_abel a b c y g hy hg hyeq hgeq)
  have hB := hconst B (analyticOnNhd_wronskian hf hy) (gauss_pair_wronskian_abel a b c f y hf hy hfeq hyeq)
  let v := (A m / W m, B m / W m)
  have hv : ∀ z ∈ gaussCutPlane, y z = v.1 * f z + v.2 * g z := by
    intro z hz
    dsimp only [v]
    rw [← hA z hz, ← hB z hz]
    have hne : W z ≠ 0 := hWne z hz
    field_simp [hne]
    dsimp [W, A, B]
    ring
  refine ⟨v, hv, fun u hu => ?_⟩
  have hD (u : ℂ × ℂ) (h : ∀ z ∈ gaussCutPlane, y z = u.1 * f z + u.2 * g z) :
      deriv y m = u.1 * deriv f m + u.2 * deriv g m :=
    (Set.EqOn.deriv h gaussCutPlane_isOpen hm).trans
      (((hf m hm).differentiableAt.hasDerivAt.const_mul u.1).add
        ((hg m hm).differentiableAt.hasDerivAt.const_mul u.2)).deriv
  have h0 := (hv m hm).symm.trans (hu m hm)
  have h1 := (hD v hv).symm.trans (hD u hu)
  apply Prod.ext
  · apply (mul_left_inj' (hWne m hm)).mp (show _ * W m = _ * W m from ?_)
    dsimp only [W]
    linear_combination g m * h1 - deriv g m * h0
  · apply (mul_left_inj' (hWne m hm)).mp (show _ * W m = _ * W m from ?_)
    dsimp only [W]
    linear_combination deriv f m * h0 - f m * h1

/-- A normalized Gauss basis: two holomorphic solutions, their Wronskian,
and unique spanning on the principal cut plane. -/
abbrev IsGaussSolutionBasis (a b c k : ℂ) (f g : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ f gaussCutPlane ∧ DifferentiableOn ℂ g gaussCutPlane ∧
    (∀ z ∈ gaussCutPlane, gaussHolomorphicOperator a b c f z = 0 ∧
      gaussHolomorphicOperator a b c g z = 0 ∧
      f z * deriv g z - deriv f z * g z = k * z ^ (-c) * (1 - z) ^ (c - a - b - 1)) ∧
    ∀ y : ℂ → ℂ, DifferentiableOn ℂ y gaussCutPlane →
      (∀ z ∈ gaussCutPlane, gaussHolomorphicOperator a b c y z = 0) →
      ∃! v : ℂ × ℂ, ∀ z ∈ gaussCutPlane, y z = v.1 * f z + v.2 * g z

private theorem gauss_basis_of_wronskian {a b c k : ℂ} {f g : ℂ → ℂ} (hk : k ≠ 0)
    (hf : DifferentiableOn ℂ f gaussCutPlane) (hg : DifferentiableOn ℂ g gaussCutPlane)
    (hfe : ∀ z ∈ gaussCutPlane, gaussHolomorphicOperator a b c f z = 0)
    (hge : ∀ z ∈ gaussCutPlane, gaussHolomorphicOperator a b c g z = 0)
    (hW : ∀ z ∈ gaussCutPlane,
      f z * deriv g z - deriv f z * g z = k * z ^ (-c) * (1 - z) ^ (c - a - b - 1)) :
    IsGaussSolutionBasis a b c k f g := by
  refine ⟨hf, hg, fun z hz => ⟨hfe z hz, hge z hz, hW z hz⟩,
    gauss_two_solution_span_unique a b c f g hf hg hfe hge ?_⟩
  intro z hz
  obtain ⟨h0, h1⟩ := gaussCutPlane_subset_regularPlane hz
  rw [hW z hz]
  exact mul_ne_zero (mul_ne_zero hk (Complex.cpow_ne_zero_iff.mpr (.inl h0)))
    (Complex.cpow_ne_zero_iff.mpr (.inl (sub_ne_zero.mpr h1.symm)))

section
variable {H : ℂ → ℂ → ℂ → ℂ → ℂ} (hH : IsGaussHypergeometricFamily H) (a b c : ℂ)
include hH

/-- The zero-end local basis. -/
theorem gauss_local_basis_zero
    (hc : ∀ n : ℤ, c ≠ (n : ℂ)) :
    IsGaussSolutionBasis a b c (1 - c) (gaussFMinus H a b c) (gaussFPlus H a b c) :=
  gauss_basis_of_wronskian (sub_ne_zero.mpr (by simpa using (hc 1).symm))
    (gaussFMinus_differentiableOn_cutPlane hH a b c hc) (gaussFPlus_differentiableOn_cutPlane hH a b c hc)
    (gaussFMinus_holomorphicOperator_eq_zero hH a b c hc) (gaussFPlus_holomorphicOperator_eq_zero hH a b c hc)
    (gaussFPlus_wronskian_identity hH a b c hc)

/-- The one-end local basis. -/
theorem gauss_local_basis_one
    (hδ : ∀ n : ℤ, c - a - b ≠ (n : ℂ)) :
    IsGaussSolutionBasis a b c (-(c - a - b)) (gaussGMinus H a b c) (gaussGPlus H a b c) :=
  gauss_basis_of_wronskian (neg_ne_zero.mpr (by simpa using hδ 0))
    (gaussGMinus_differentiableOn_cutPlane hH a b c hδ) (gaussGPlus_differentiableOn_cutPlane hH a b c hδ)
    (gaussGMinus_holomorphicOperator_eq_zero hH a b c hδ) (gaussGPlus_holomorphicOperator_eq_zero hH a b c hδ)
    (gaussGPlus_wronskian_identity hH a b c hδ)

end

end DOZZ.Proofs
