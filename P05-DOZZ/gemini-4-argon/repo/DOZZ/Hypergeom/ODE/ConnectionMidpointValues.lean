/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ODE.ParameterSeriesFamily
public import DOZZ.Hypergeom.ODE.ConnectionParameterDomain

/-! Parameter regularity of the four connection-basis values at the common midpoint. -/

@[expose] public section

namespace DOZZ.Proofs

private theorem connectionDomain_subset_poleFree {p}
    (hp : p ∈ gaussConnectionParameterDomain) : p ∈ gaussParameterPoleFreeDomain := by
  intro n hn
  apply (hp.1 (-(n : ℤ)))
  simpa using hn

private def connectionFPlusParameters (p : ℂ × ℂ × ℂ) : ℂ × ℂ × ℂ :=
  (p.1 - p.2.2 + 1, p.2.1 - p.2.2 + 1, 2 - p.2.2)

private def connectionGMinusParameters (p : ℂ × ℂ × ℂ) : ℂ × ℂ × ℂ :=
  (p.1, p.2.1, 1 + p.1 + p.2.1 - p.2.2)

private def connectionGPlusParameters (p : ℂ × ℂ × ℂ) : ℂ × ℂ × ℂ :=
  (p.2.2 - p.2.1, p.2.2 - p.1, 1 + p.2.2 - p.1 - p.2.1)




private theorem familyParameterValue_comp_differentiableAt
    {H}
    (hH : IsGaussHypergeometricFamily H) p
    (S : ℂ × ℂ × ℂ → ℂ × ℂ × ℂ)
    (hS : S p ∈ gaussParameterPoleFreeDomain)
    (hSDiff : DifferentiableAt ℂ S p) z (hz : ‖z‖ < 1) :
    DifferentiableAt ℂ (fun q : ℂ × ℂ × ℂ => H (S q).1 (S q).2.1 (S q).2.2 z) p := by
  change DifferentiableAt ℂ
    ((fun q : ℂ × ℂ × ℂ => H q.1 q.2.1 q.2.2 z) ∘ S) p
  exact (((IsGaussHypergeometricFamily.differentiableOn_params_unitDisk hH hz) (S p) hS).differentiableAt (gaussParameterPoleFreeDomain_isOpen.mem_nhds hS)).comp p hSDiff

/-- The first zero-basis value at `1/2` varies holomorphically with the parameters on the
nonresonant connection domain. -/
theorem gaussFMinus_midpoint_differentiableAt_params
    {H} (hH : IsGaussHypergeometricFamily H)
    {p} (hp : p ∈ gaussConnectionParameterDomain) :
    DifferentiableAt ℂ
      (fun q => gaussFMinus H q.1 q.2.1 q.2.2 (1 / 2 : ℂ)) p := by
  simpa [gaussFMinus] using (familyParameterValue_comp_differentiableAt hH p id (connectionDomain_subset_poleFree hp) (by fun_prop) (1 / 2 : ℂ) (by norm_num))

/-- The second zero-basis value at `1/2` varies holomorphically with the parameters. -/
theorem gaussFPlus_midpoint_differentiableAt_params
    {H} (hH : IsGaussHypergeometricFamily H)
    {p} (hp : p ∈ gaussConnectionParameterDomain) :
    DifferentiableAt ℂ
      (fun q => gaussFPlus H q.1 q.2.1 q.2.2 (1 / 2 : ℂ)) p := by
  have connectionFPlusParameters_mem : connectionFPlusParameters p ∈ gaussParameterPoleFreeDomain := by
    intro n hn
    have hcast : p.2.2 = (((n : ℤ) + 2 : ℤ) : ℂ) := by
      calc
        p.2.2 = (n : ℂ) + 2 := (by dsimp [connectionFPlusParameters] at hn; linear_combination -hn)
        _ = (((n : ℤ) + 2 : ℤ) : ℂ) := by push_cast; ring
    exact (hp.1 ((n : ℤ) + 2)) hcast
  change DifferentiableAt ℂ
    (fun q => (1 / 2 : ℂ) ^ (1 - q.2.2) *
      H (q.1 - q.2.2 + 1) (q.2.1 - q.2.2 + 1) (2 - q.2.2) (1 / 2 : ℂ)) p
  exact (show DifferentiableAt ℂ (fun q : ℂ × ℂ × ℂ => (1 / 2 : ℂ) ^ (1 - q.2.2)) p by exact (show DifferentiableAt ℂ (fun q : ℂ × ℂ × ℂ => 1 - q.2.2) p by fun_prop).const_cpow (Or.inl (by norm_num))).mul (familyParameterValue_comp_differentiableAt hH p connectionFPlusParameters (connectionFPlusParameters_mem) (by fun_prop [connectionFPlusParameters]) (1 / 2 : ℂ) (by norm_num))

/-- The first one-basis value at `1/2` varies holomorphically with the parameters. -/
theorem gaussGMinus_midpoint_differentiableAt_params
    {H} (hH : IsGaussHypergeometricFamily H)
    {p} (hp : p ∈ gaussConnectionParameterDomain) :
    DifferentiableAt ℂ
      (fun q => gaussGMinus H q.1 q.2.1 q.2.2 (1 / 2 : ℂ)) p := by
  have connectionGMinusParameters_mem : connectionGMinusParameters p ∈ gaussParameterPoleFreeDomain := by
    intro n hn
    have hcast : p.2.2 - p.1 - p.2.1 = (((n : ℤ) + 1 : ℤ) : ℂ) := by
      calc
        p.2.2 - p.1 - p.2.1 = (n : ℂ) + 1 := (by dsimp [connectionGMinusParameters] at hn; linear_combination -hn)
        _ = (((n : ℤ) + 1 : ℤ) : ℂ) := by push_cast; ring
    exact (hp.2 ((n : ℤ) + 1)) hcast
  norm_num [gaussGMinus, connectionGMinusParameters] at ⊢
  exact (familyParameterValue_comp_differentiableAt hH p connectionGMinusParameters (connectionGMinusParameters_mem) (by fun_prop [connectionGMinusParameters]) (1 / 2 : ℂ) (by norm_num))

/-- The second one-basis value at `1/2` varies holomorphically with the parameters. -/
theorem gaussGPlus_midpoint_differentiableAt_params
    {H} (hH : IsGaussHypergeometricFamily H)
    {p} (hp : p ∈ gaussConnectionParameterDomain) :
    DifferentiableAt ℂ
      (fun q => gaussGPlus H q.1 q.2.1 q.2.2 (1 / 2 : ℂ)) p := by
  have connectionGPlusParameters_mem : connectionGPlusParameters p ∈ gaussParameterPoleFreeDomain := by
    intro n hn
    let m := -((n : ℤ) + 1)
    have hcast : p.2.2 - p.1 - p.2.1 = (m : ℂ) := by
      calc
        p.2.2 - p.1 - p.2.1 = -((n : ℂ) + 1) := (by dsimp [connectionGPlusParameters] at hn; linear_combination hn)
        _ = -(((n : ℤ) + 1 : ℤ) : ℂ) := by push_cast; ring
        _ = (m : ℂ) := by dsimp [m]; rw [Int.cast_neg]
    exact (hp.2 m) hcast
  norm_num [gaussGPlus] at ⊢
  exact ((show DifferentiableAt ℂ (fun q : ℂ × ℂ × ℂ => (1 / 2 : ℂ) ^ (q.2.2 - q.1 - q.2.1)) p by exact (show DifferentiableAt ℂ (fun q : ℂ × ℂ × ℂ => q.2.2 - q.1 - q.2.1) p by fun_prop).const_cpow (Or.inl (by norm_num))).mul (by simpa [connectionGPlusParameters] using (familyParameterValue_comp_differentiableAt hH p connectionGPlusParameters (connectionGPlusParameters_mem) (by fun_prop [connectionGPlusParameters]) (1 / 2 : ℂ) (by norm_num))))

end DOZZ.Proofs
