/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ODE.ConnectionMidpointDerivatives
public import DOZZ.Hypergeom.BasisWronskians
public import DOZZ.Hypergeom.BasisSpanning

/-! Holomorphic midpoint Cramer coefficients for the connection expansions. -/

@[expose] public section

open scoped Topology

namespace DOZZ.Proofs

/-- The spatial Wronskian evaluated at the midpoint `1/2`. -/
noncomputable def midpointWronskian (f g : ℂ → ℂ) : ℂ :=
  f (1 / 2) * deriv g (1 / 2) - deriv f (1 / 2) * g (1 / 2)

private theorem midpointWronskian_regular {F G : (ℂ × ℂ × ℂ) → ℂ → ℂ} {p : ℂ × ℂ × ℂ}
    (hF : MidpointRegular F p) (hG : MidpointRegular G p) :
    DifferentiableAt ℂ (fun q => midpointWronskian (F q) (G q)) p :=
  (hF.value.mul hG.spatialDeriv).sub (hF.spatialDeriv.mul hG.value)

/-- Cramer's rule at the bounding bases' common midpoint. -/
noncomputable def midpointCramer (f g h : ℂ → ℂ) : ℂ × ℂ :=
  (midpointWronskian f h * (midpointWronskian g h)⁻¹,
    midpointWronskian g f * (midpointWronskian g h)⁻¹)

private theorem midpointCramer_eq {f g h : ℂ → ℂ} {v : ℂ × ℂ}
    (hv : Set.EqOn f (fun z => v.1 * g z + v.2 * h z) gaussCutPlane)
    (hg : DifferentiableOn ℂ g gaussCutPlane) (hh : DifferentiableOn ℂ h gaussCutPlane)
    (hW : midpointWronskian g h ≠ 0) : midpointCramer f g h = v := by
  have hm : (1 / 2 : ℂ) ∈ gaussCutPlane := by norm_num [gaussCutPlane]
  have hn := gaussCutPlane_isOpen.mem_nhds hm
  have hder : deriv f (1 / 2) = v.1 * deriv g (1 / 2) + v.2 * deriv h (1 / 2) :=
    (hv.deriv gaussCutPlane_isOpen hm).trans
      ((((hg _ hm).differentiableAt hn).hasDerivAt.const_mul v.1).add
        (((hh _ hm).differentiableAt hn).hasDerivAt.const_mul v.2)).deriv
  have h₁ : midpointWronskian f h = v.1 * midpointWronskian g h := by
    unfold midpointWronskian
    rw [hv hm, hder]
    ring
  have h₂ : midpointWronskian g f = v.2 * midpointWronskian g h := by
    unfold midpointWronskian
    rw [hv hm, hder]
    ring
  ext <;> simp only [midpointCramer, h₁, h₂, mul_inv_cancel_right₀ hW]

section
variable (H : ℂ → ℂ → ℂ → ℂ → ℂ) (p : ℂ × ℂ × ℂ)

local notation "g₁" => gaussGMinus H (Prod.fst p) (Prod.fst (Prod.snd p)) (Prod.snd (Prod.snd p))
local notation "g₂" => gaussGPlus H (Prod.fst p) (Prod.fst (Prod.snd p)) (Prod.snd (Prod.snd p))

noncomputable def connectionMinusFirstCramerCoefficient : ℂ :=
  (midpointCramer (gaussFMinus H p.1 p.2.1 p.2.2) g₁ g₂).1

noncomputable def connectionMinusSecondCramerCoefficient : ℂ :=
  (midpointCramer (gaussFMinus H p.1 p.2.1 p.2.2) g₁ g₂).2

noncomputable def connectionPlusFirstCramerCoefficient : ℂ :=
  (midpointCramer (gaussFPlus H p.1 p.2.1 p.2.2) g₁ g₂).1

noncomputable def connectionPlusSecondCramerCoefficient : ℂ :=
  (midpointCramer (gaussFPlus H p.1 p.2.1 p.2.2) g₁ g₂).2

end

section
variable {H : ℂ → ℂ → ℂ → ℂ → ℂ} (hH : IsGaussHypergeometricFamily H) {p : ℂ × ℂ × ℂ}
  (hp : p ∈ gaussConnectionParameterDomain)
include hH hp

private theorem connectionMidpointWronskian_ne_zero :
    midpointWronskian (gaussGMinus H p.1 p.2.1 p.2.2) (gaussGPlus H p.1 p.2.1 p.2.2) ≠ 0 := by
  have hw := gaussGPlus_wronskian_identity hH p.1 p.2.1 p.2.2 hp.2 (1 / 2 : ℂ)
    (by norm_num [gaussCutPlane])
  unfold midpointWronskian
  rw [hw]
  exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr (by simpa using hp.2 0))
    (Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))))
    (Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num)))

private theorem inv_midpointWronskian_regular :
    DifferentiableAt ℂ (fun q =>
      (midpointWronskian (gaussGMinus H q.1 q.2.1 q.2.2) (gaussGPlus H q.1 q.2.1 q.2.2))⁻¹) p :=
  (midpointWronskian_regular (gaussGMinus_midpoint_regular hH hp)
    (gaussGPlus_midpoint_regular hH hp)).inv (connectionMidpointWronskian_ne_zero hH hp)

theorem connectionMinusFirstCramerCoefficient_differentiableAt :
    DifferentiableAt ℂ (connectionMinusFirstCramerCoefficient H) p :=
  (midpointWronskian_regular (gaussFMinus_midpoint_regular hH hp)
    (gaussGPlus_midpoint_regular hH hp)).mul (inv_midpointWronskian_regular hH hp)

theorem connectionMinusSecondCramerCoefficient_differentiableAt :
    DifferentiableAt ℂ (connectionMinusSecondCramerCoefficient H) p :=
  (midpointWronskian_regular (gaussGMinus_midpoint_regular hH hp)
    (gaussFMinus_midpoint_regular hH hp)).mul (inv_midpointWronskian_regular hH hp)

theorem connectionPlusFirstCramerCoefficient_differentiableAt :
    DifferentiableAt ℂ (connectionPlusFirstCramerCoefficient H) p :=
  (midpointWronskian_regular (gaussFPlus_midpoint_regular hH hp)
    (gaussGPlus_midpoint_regular hH hp)).mul (inv_midpointWronskian_regular hH hp)

theorem connectionPlusSecondCramerCoefficient_differentiableAt :
    DifferentiableAt ℂ (connectionPlusSecondCramerCoefficient H) p :=
  (midpointWronskian_regular (gaussGMinus_midpoint_regular hH hp)
    (gaussFPlus_midpoint_regular hH hp)).mul (inv_midpointWronskian_regular hH hp)

private theorem connection_midpoint_expansion {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f gaussCutPlane)
    (hode : ∀ z ∈ gaussCutPlane, gaussHolomorphicOperator p.1 p.2.1 p.2.2 f z = 0) :
    ∀ z ∈ gaussCutPlane,
      let g := gaussGMinus H p.1 p.2.1 p.2.2
      let h := gaussGPlus H p.1 p.2.1 p.2.2
      f z = (midpointCramer f g h).1 * g z + (midpointCramer f g h).2 * h z := by
  obtain ⟨hg, hh, _, hspan⟩ := gauss_local_basis_one hH p.1 p.2.1 p.2.2 hp.2
  obtain ⟨v, hv, _⟩ := hspan f hf hode
  intro z hz
  dsimp only
  rw [midpointCramer_eq hv hg hh (connectionMidpointWronskian_ne_zero hH hp)]
  exact hv z hz

/-- The corresponding zero-basis function in the common midpoint Cramer expansion. -/
theorem gaussFMinus_eq_connectionMidpointCramer :
    ∀ z ∈ gaussCutPlane, gaussFMinus H p.1 p.2.1 p.2.2 z =
      connectionMinusFirstCramerCoefficient H p * gaussGMinus H p.1 p.2.1 p.2.2 z +
      connectionMinusSecondCramerCoefficient H p * gaussGPlus H p.1 p.2.1 p.2.2 z := by
  have hzero := gauss_local_basis_zero hH p.1 p.2.1 p.2.2 hp.1
  exact connection_midpoint_expansion hH hp hzero.1 (fun z hz => (hzero.2.2.1 z hz).1)

/-- The corresponding zero-basis function in the common midpoint Cramer expansion. -/
theorem gaussFPlus_eq_connectionMidpointCramer :
    ∀ z ∈ gaussCutPlane, gaussFPlus H p.1 p.2.1 p.2.2 z =
      connectionPlusFirstCramerCoefficient H p * gaussGMinus H p.1 p.2.1 p.2.2 z +
      connectionPlusSecondCramerCoefficient H p * gaussGPlus H p.1 p.2.1 p.2.2 z := by
  have hzero := gauss_local_basis_zero hH p.1 p.2.1 p.2.2 hp.1
  exact connection_midpoint_expansion hH hp hzero.2.1 (fun z hz => (hzero.2.2.1 z hz).2.1)

end

end DOZZ.Proofs
