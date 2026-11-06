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

/-- The Wronskian of the one-end local basis, evaluated at the common midpoint. -/
noncomputable def connectionMidpointOneWronskian
    (H : ℂ → ℂ → ℂ → ℂ → ℂ) (p : ℂ × ℂ × ℂ) : ℂ :=
  gaussGMinus H p.1 p.2.1 p.2.2 (1 / 2 : ℂ) *
      deriv (gaussGPlus H p.1 p.2.1 p.2.2) (1 / 2 : ℂ) -
    deriv (gaussGMinus H p.1 p.2.1 p.2.2) (1 / 2 : ℂ) *
      gaussGPlus H p.1 p.2.1 p.2.2 (1 / 2 : ℂ)
section
variable {H : ℂ → ℂ → ℂ → ℂ → ℂ}
section
variable (hH : IsGaussHypergeometricFamily H) {p : ℂ × ℂ × ℂ} (hp : p ∈ gaussConnectionParameterDomain)
include hH hp

private theorem connectionMidpointOneWronskian_differentiableAt
    :
    DifferentiableAt ℂ (fun q => connectionMidpointOneWronskian H q) p := by
  have hGm := gaussGMinus_midpoint_differentiableAt_params hH hp
  have hGm' := gaussGMinus_midpoint_deriv_differentiableAt_params hH hp
  have hGp := gaussGPlus_midpoint_differentiableAt_params hH hp
  have hGp' := gaussGPlus_midpoint_deriv_differentiableAt_params hH hp
  change DifferentiableAt ℂ (fun q =>
    gaussGMinus H q.1 q.2.1 q.2.2 _ *
        deriv _ _ -
      deriv _ _ *
        gaussGPlus H q.1 q.2.1 q.2.2 _) p
  simp_all

private theorem connectionMidpointOneWronskian_ne_zero
    :
    connectionMidpointOneWronskian H p ≠ 0 := by
  have hmid : (1 / 2) ∈ gaussCutPlane := by norm_num [gaussCutPlane]
  have hδ : p.2.2 - p.1 - p.2.1 ≠ 0 := by
    have := hp.2 0
    simp_all
  have hformula : connectionMidpointOneWronskian H p =
      -(p.2.2 - p.1 - p.2.1) * (1 / 2) ^ (-p.2.2) *
        (1 / 2) ^ (p.2.2 - p.1 - p.2.1 - 1) := by
    have hw' := (gaussGPlus_wronskian_identity hH p.1 p.2.1 p.2.2 hp.2 _ hmid)
    norm_num at hw'
    simpa [connectionMidpointOneWronskian] using hw'
  have hfactor := neg_ne_zero.mpr hδ
  simp_all

end

end

/-- The first midpoint Cramer quotient for expanding `FMinus` in the one-end basis. -/
noncomputable def connectionMinusFirstCramerCoefficient
    (H : ℂ → ℂ → ℂ → ℂ → ℂ) (p : ℂ × ℂ × ℂ) : ℂ :=
  (gaussFMinus H p.1 p.2.1 p.2.2 (1 / 2 : ℂ) *
      deriv (gaussGPlus H p.1 p.2.1 p.2.2) (1 / 2 : ℂ) -
    deriv (gaussFMinus H p.1 p.2.1 p.2.2) (1 / 2 : ℂ) *
      gaussGPlus H p.1 p.2.1 p.2.2 (1 / 2 : ℂ)) *
    (connectionMidpointOneWronskian H p)⁻¹

/-- The second midpoint Cramer quotient for expanding `FMinus` in the one-end basis. -/
noncomputable def connectionMinusSecondCramerCoefficient
    (H : ℂ → ℂ → ℂ → ℂ → ℂ) (p : ℂ × ℂ × ℂ) : ℂ :=
  (gaussGMinus H p.1 p.2.1 p.2.2 (1 / 2 : ℂ) *
      deriv (gaussFMinus H p.1 p.2.1 p.2.2) (1 / 2 : ℂ) -
    deriv (gaussGMinus H p.1 p.2.1 p.2.2) (1 / 2 : ℂ) *
      gaussFMinus H p.1 p.2.1 p.2.2 (1 / 2 : ℂ)) *
    (connectionMidpointOneWronskian H p)⁻¹
section
variable {H : ℂ → ℂ → ℂ → ℂ → ℂ}
section
variable (hH : IsGaussHypergeometricFamily H) {p : ℂ × ℂ × ℂ} (hp : p ∈ gaussConnectionParameterDomain)
include hH hp

/-- The first Cramer coefficient in the expansion of the zero-basis solution in the one-basis
varies holomorphically on the nonresonant connection domain. -/
theorem connectionMinusFirstCramerCoefficient_differentiableAt
    :
    DifferentiableAt ℂ (fun q => connectionMinusFirstCramerCoefficient H q) p := by
  have hGp := gaussGPlus_midpoint_differentiableAt_params hH hp
  have hGp' := gaussGPlus_midpoint_deriv_differentiableAt_params hH hp
  have hnum :=
    ((gaussFMinus_midpoint_differentiableAt_params hH hp).mul hGp').sub ((gaussFMinus_midpoint_deriv_differentiableAt_params hH hp).mul hGp)
  change DifferentiableAt ℂ (fun q =>
    (gaussFMinus H q.1 q.2.1 q.2.2 _ *
        deriv _ _ -
      deriv _ _ *
        gaussGPlus H q.1 q.2.1 q.2.2 _) *
      (connectionMidpointOneWronskian H q)⁻¹) p
  exact hnum.mul ((connectionMidpointOneWronskian_differentiableAt hH hp).inv (connectionMidpointOneWronskian_ne_zero hH hp))

/-- The second Cramer coefficient in the expansion of the zero-basis solution in the one-basis
varies holomorphically on the nonresonant connection domain. -/
theorem connectionMinusSecondCramerCoefficient_differentiableAt
    :
    DifferentiableAt ℂ (fun q => connectionMinusSecondCramerCoefficient H q) p := by
  have hFm := gaussFMinus_midpoint_differentiableAt_params hH hp
  have hFm' := gaussFMinus_midpoint_deriv_differentiableAt_params hH hp
  have hnum :=
    ((gaussGMinus_midpoint_differentiableAt_params hH hp).mul hFm').sub ((gaussGMinus_midpoint_deriv_differentiableAt_params hH hp).mul hFm)
  change DifferentiableAt ℂ (fun q =>
    (gaussGMinus H q.1 q.2.1 q.2.2 _ *
        deriv _ _ -
      deriv _ _ *
        gaussFMinus H q.1 q.2.1 q.2.2 _) *
      (connectionMidpointOneWronskian H q)⁻¹) p
  exact hnum.mul ((connectionMidpointOneWronskian_differentiableAt hH hp).inv (connectionMidpointOneWronskian_ne_zero hH hp))

end

end

/-- The first midpoint Cramer quotient for expanding `FPlus` in the one-end basis. -/
noncomputable def connectionPlusFirstCramerCoefficient
    (H : ℂ → ℂ → ℂ → ℂ → ℂ) (p : ℂ × ℂ × ℂ) : ℂ :=
  (gaussFPlus H p.1 p.2.1 p.2.2 (1 / 2 : ℂ) *
      deriv (gaussGPlus H p.1 p.2.1 p.2.2) (1 / 2 : ℂ) -
    deriv (gaussFPlus H p.1 p.2.1 p.2.2) (1 / 2 : ℂ) *
      gaussGPlus H p.1 p.2.1 p.2.2 (1 / 2 : ℂ)) *
    (connectionMidpointOneWronskian H p)⁻¹

/-- The second midpoint Cramer quotient for expanding `FPlus` in the one-end basis. -/
noncomputable def connectionPlusSecondCramerCoefficient
    (H : ℂ → ℂ → ℂ → ℂ → ℂ) (p : ℂ × ℂ × ℂ) : ℂ :=
  (gaussGMinus H p.1 p.2.1 p.2.2 (1 / 2 : ℂ) *
      deriv (gaussFPlus H p.1 p.2.1 p.2.2) (1 / 2 : ℂ) -
    deriv (gaussGMinus H p.1 p.2.1 p.2.2) (1 / 2 : ℂ) *
      gaussFPlus H p.1 p.2.1 p.2.2 (1 / 2 : ℂ)) *
    (connectionMidpointOneWronskian H p)⁻¹
section
variable {H : ℂ → ℂ → ℂ → ℂ → ℂ}
section
variable (hH : IsGaussHypergeometricFamily H) {p : ℂ × ℂ × ℂ} (hp : p ∈ gaussConnectionParameterDomain)
include hH hp

/-- The first Cramer coefficient for expanding the second zero-basis function in the one-basis
varies holomorphically on the nonresonant connection domain. -/
theorem connectionPlusFirstCramerCoefficient_differentiableAt
    :
    DifferentiableAt ℂ (fun q => connectionPlusFirstCramerCoefficient H q) p := by
  have hGp := gaussGPlus_midpoint_differentiableAt_params hH hp
  have hGp' := gaussGPlus_midpoint_deriv_differentiableAt_params hH hp
  have hnum :=
    ((gaussFPlus_midpoint_differentiableAt_params hH hp).mul hGp').sub ((gaussFPlus_midpoint_deriv_differentiableAt_params hH hp).mul hGp)
  have hinv := (connectionMidpointOneWronskian_differentiableAt hH hp).inv
    (connectionMidpointOneWronskian_ne_zero hH hp)
  change DifferentiableAt ℂ (fun q =>
    (gaussFPlus H q.1 q.2.1 q.2.2 _ *
        deriv _ _ -
      deriv _ _ *
        gaussGPlus H q.1 q.2.1 q.2.2 _) *
      (connectionMidpointOneWronskian H q)⁻¹) p
  exact hnum.mul hinv

/-- The second Cramer coefficient for expanding the second zero-basis function in the one-basis
varies holomorphically on the nonresonant connection domain. -/
theorem connectionPlusSecondCramerCoefficient_differentiableAt
    :
    DifferentiableAt ℂ (fun q => connectionPlusSecondCramerCoefficient H q) p := by
  have hFp := gaussFPlus_midpoint_differentiableAt_params hH hp
  have hFp' := gaussFPlus_midpoint_deriv_differentiableAt_params hH hp
  have hnum :=
    ((gaussGMinus_midpoint_differentiableAt_params hH hp).mul hFp').sub ((gaussGMinus_midpoint_deriv_differentiableAt_params hH hp).mul hFp)
  have hinv := (connectionMidpointOneWronskian_differentiableAt hH hp).inv
    (connectionMidpointOneWronskian_ne_zero hH hp)
  change DifferentiableAt ℂ (fun q =>
    (gaussGMinus H q.1 q.2.1 q.2.2 _ *
        deriv _ _ -
      deriv _ _ *
        gaussFPlus H q.1 q.2.1 q.2.2 _) *
      (connectionMidpointOneWronskian H q)⁻¹) p
  exact hnum.mul hinv

/-- On the cut plane, the zero-basis solution has its midpoint Cramer expansion in the one-basis.
This separates the ODE spanning argument from the later Gamma evaluation of the coefficients. -/
theorem gaussFMinus_eq_connectionMidpointCramer
    :
    ∀ z ∈ gaussCutPlane,
      gaussFMinus H p.1 p.2.1 p.2.2 z =
        connectionMinusFirstCramerCoefficient H p * gaussGMinus H p.1 p.2.1 p.2.2 z +
          connectionMinusSecondCramerCoefficient H p * gaussGPlus H p.1 p.2.1 p.2.2 z := by
  have hZero := gauss_local_basis_zero hH p.1 p.2.1 p.2.2 hp.1
  have hOne := gauss_local_basis_one hH p.1 p.2.1 p.2.2 hp.2
  have hspan := hOne.2.2.2 _ hZero.1
    (fun z hz => (hZero.2.2.1 z hz).1)
  obtain ⟨v, hv, hvuniq⟩ := hspan
  have hmid : (1 / 2) ∈ gaussCutPlane := by norm_num [gaussCutPlane]
  have hFmid := hv _ hmid
  have hGmAt :=
    (hOne.1 _ hmid).differentiableAt
      (gaussCutPlane_isOpen.mem_nhds hmid)
  have hGpAt :=
    (hOne.2.1 _ hmid).differentiableAt
      (gaussCutPlane_isOpen.mem_nhds hmid)
  have hFmid' : deriv (gaussFMinus H p.1 p.2.1 p.2.2) (1 / 2) =
      v.1 * deriv (gaussGMinus H p.1 p.2.1 p.2.2) (1 / 2) +
        v.2 * deriv (gaussGPlus H p.1 p.2.1 p.2.2) (1 / 2) := by
    have hEqOn : gaussCutPlane.EqOn (gaussFMinus H p.1 p.2.1 p.2.2)
        (fun z => v.1 * gaussGMinus H p.1 p.2.1 p.2.2 z +
          v.2 * gaussGPlus H p.1 p.2.1 p.2.2 z) := hv
    calc
      deriv _ (1 / 2 : ℂ) =
          deriv (fun z => v.1 * gaussGMinus H p.1 p.2.1 p.2.2 z +
            v.2 * gaussGPlus H p.1 p.2.1 p.2.2 z) (1 / 2 : ℂ) :=
        hEqOn.deriv gaussCutPlane_isOpen hmid
      _ = v.1 * deriv _ _ +
          v.2 * deriv .. := ((hGmAt.hasDerivAt.const_mul v.1).add (hGpAt.hasDerivAt.const_mul v.2)).deriv
  have hwne : connectionMidpointOneWronskian H p ≠ 0 :=
    connectionMidpointOneWronskian_ne_zero hH hp
  have hW : connectionMidpointOneWronskian H p =
      gaussGMinus H p.1 p.2.1 p.2.2 (1 / 2 : ℂ) *
          deriv _ (1 / 2 : ℂ) -
        deriv _ (1 / 2 : ℂ) *
          gaussGPlus H p.1 p.2.1 p.2.2 (1 / 2 : ℂ) := rfl
  have hWne : gaussGMinus H p.1 p.2.1 p.2.2 (1 / 2) *
        deriv (gaussGPlus H p.1 p.2.1 p.2.2) (1 / 2) -
      deriv (gaussGMinus H p.1 p.2.1 p.2.2) (1 / 2) *
        gaussGPlus H p.1 p.2.1 p.2.2 (1 / 2) ≠ 0 := by
    rwa [← hW]
  have hWneComm : gaussGMinus H p.1 p.2.1 p.2.2 (1 / 2) *
        deriv (gaussGPlus H p.1 p.2.1 p.2.2) (1 / 2) -
      gaussGPlus H p.1 p.2.1 p.2.2 (1 / 2) *
        deriv (gaussGMinus H p.1 p.2.1 p.2.2) (1 / 2) ≠ 0 := by
    convert hWne using 1; ring
  have hcoeff₁ : connectionMinusFirstCramerCoefficient H p = v.1 := by
    unfold connectionMinusFirstCramerCoefficient
    rw [hFmid, hFmid', hW]
    field_simp [hWneComm]
    ring_nf
  have hcoeff₂ : connectionMinusSecondCramerCoefficient H p = v.2 := by
    unfold connectionMinusSecondCramerCoefficient
    rw [hFmid, hFmid', hW]
    field_simp [hWneComm]
    ring_nf
  intro z hz
  rw [hcoeff₁, hcoeff₂]
  exact hv z hz

/-- On the cut plane, the second zero-basis solution has its midpoint Cramer expansion in the
one-basis. Gamma evaluation of these parameter-dependent coefficients is a separate step. -/
theorem gaussFPlus_eq_connectionMidpointCramer
    :
    ∀ z ∈ gaussCutPlane,
      gaussFPlus H p.1 p.2.1 p.2.2 z =
        connectionPlusFirstCramerCoefficient H p * gaussGMinus H p.1 p.2.1 p.2.2 z +
          connectionPlusSecondCramerCoefficient H p * gaussGPlus H p.1 p.2.1 p.2.2 z := by
  have hZero := gauss_local_basis_zero hH p.1 p.2.1 p.2.2 hp.1
  have hOne := gauss_local_basis_one hH p.1 p.2.1 p.2.2 hp.2
  have hspan := hOne.2.2.2 _ hZero.2.1
    (fun z hz => (hZero.2.2.1 z hz).2.1)
  obtain ⟨v, hv, hvuniq⟩ := hspan
  have hmid : (1 / 2) ∈ gaussCutPlane := by norm_num [gaussCutPlane]
  have hFmid := hv _ hmid
  have hGmAt :=
    (hOne.1 _ hmid).differentiableAt
      (gaussCutPlane_isOpen.mem_nhds hmid)
  have hGpAt :=
    (hOne.2.1 _ hmid).differentiableAt
      (gaussCutPlane_isOpen.mem_nhds hmid)
  have hFmid' : deriv (gaussFPlus H p.1 p.2.1 p.2.2) (1 / 2) =
      v.1 * deriv (gaussGMinus H p.1 p.2.1 p.2.2) (1 / 2) +
        v.2 * deriv (gaussGPlus H p.1 p.2.1 p.2.2) (1 / 2) := by
    have hEqOn : gaussCutPlane.EqOn (gaussFPlus H p.1 p.2.1 p.2.2)
        (fun z => v.1 * gaussGMinus H p.1 p.2.1 p.2.2 z +
          v.2 * gaussGPlus H p.1 p.2.1 p.2.2 z) := hv
    calc
      deriv _ (1 / 2 : ℂ) =
          deriv (fun z => v.1 * gaussGMinus H p.1 p.2.1 p.2.2 z +
            v.2 * gaussGPlus H p.1 p.2.1 p.2.2 z) (1 / 2 : ℂ) :=
        hEqOn.deriv gaussCutPlane_isOpen hmid
      _ = v.1 * deriv _ _ +
          v.2 * deriv .. := ((hGmAt.hasDerivAt.const_mul v.1).add (hGpAt.hasDerivAt.const_mul v.2)).deriv
  have hwne : connectionMidpointOneWronskian H p ≠ 0 :=
    connectionMidpointOneWronskian_ne_zero hH hp
  have hW : connectionMidpointOneWronskian H p =
      gaussGMinus H p.1 p.2.1 p.2.2 (1 / 2 : ℂ) *
          deriv _ (1 / 2 : ℂ) -
        deriv _ (1 / 2 : ℂ) *
          gaussGPlus H p.1 p.2.1 p.2.2 (1 / 2 : ℂ) := rfl
  have hWne : gaussGMinus H p.1 p.2.1 p.2.2 (1 / 2) *
        deriv (gaussGPlus H p.1 p.2.1 p.2.2) (1 / 2) -
      deriv (gaussGMinus H p.1 p.2.1 p.2.2) (1 / 2) *
        gaussGPlus H p.1 p.2.1 p.2.2 (1 / 2) ≠ 0 := by
    rwa [← hW]
  have hWneComm : gaussGMinus H p.1 p.2.1 p.2.2 (1 / 2) *
        deriv (gaussGPlus H p.1 p.2.1 p.2.2) (1 / 2) -
      gaussGPlus H p.1 p.2.1 p.2.2 (1 / 2) *
        deriv (gaussGMinus H p.1 p.2.1 p.2.2) (1 / 2) ≠ 0 := by
    convert hWne using 1; ring
  have hcoeff₁ : connectionPlusFirstCramerCoefficient H p = v.1 := by
    unfold connectionPlusFirstCramerCoefficient
    rw [hFmid, hFmid', hW]
    field_simp [hWneComm]
    ring_nf
  have hcoeff₂ : connectionPlusSecondCramerCoefficient H p = v.2 := by
    unfold connectionPlusSecondCramerCoefficient
    rw [hFmid, hFmid', hW]
    field_simp [hWneComm]
    ring_nf
  intro z hz
  rw [hcoeff₁, hcoeff₂]
  exact hv z hz

end

end

end DOZZ.Proofs
