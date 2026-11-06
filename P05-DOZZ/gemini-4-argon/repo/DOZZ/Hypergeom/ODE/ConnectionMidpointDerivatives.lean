/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ODE.ConnectionMidpointValues
public import DOZZ.Hypergeom.ODE.ParameterSpatialDerivative
public import DOZZ.Hypergeom.BasisRegularity
public import DOZZ.Hypergeom.ODE.CutPlaneTopology

/-! Parameter regularity of the spatial derivatives in the midpoint connection matrix. -/

@[expose] public section

open scoped Topology

namespace DOZZ.Proofs

private def midpointFPlusParameters (p : ℂ × ℂ × ℂ) : ℂ × ℂ × ℂ :=
  (p.1 - p.2.2 + 1, p.2.1 - p.2.2 + 1, 2 - p.2.2)

private def midpointGMinusParameters (p : ℂ × ℂ × ℂ) : ℂ × ℂ × ℂ :=
  (p.1, p.2.1, 1 + p.1 + p.2.1 - p.2.2)

private def midpointGPlusParameters (p : ℂ × ℂ × ℂ) : ℂ × ℂ × ℂ :=
  (p.2.2 - p.2.1, p.2.2 - p.1, 1 + p.2.2 - p.1 - p.2.1)

private theorem midpointFPlusParameters_mem
    {p} (hp : p ∈ gaussConnectionParameterDomain) :
    midpointFPlusParameters p ∈ gaussParameterPoleFreeDomain := by
  intro n hn
  have hcast : p.2.2 = (((n : ℤ) + 2 : ℤ) : ℂ) := by
    calc
      p.2.2 = (n : ℂ) + 2 := (by dsimp [midpointFPlusParameters] at hn; linear_combination -hn)
      _ = (((n : ℤ) + 2 : ℤ) : ℂ) := by push_cast; ring
  exact (hp.1 ((n : ℤ) + 2)) hcast

private theorem midpointGMinusParameters_mem
    {p} (hp : p ∈ gaussConnectionParameterDomain) :
    midpointGMinusParameters p ∈ gaussParameterPoleFreeDomain := by
  intro n hn
  have hcast : p.2.2 - p.1 - p.2.1 = (((n : ℤ) + 1 : ℤ) : ℂ) := by
    calc
      p.2.2 - p.1 - p.2.1 = (n : ℂ) + 1 := (by dsimp [midpointGMinusParameters] at hn; linear_combination -hn)
      _ = (((n : ℤ) + 1 : ℤ) : ℂ) := by push_cast; ring
  exact (hp.2 ((n : ℤ) + 1)) hcast

private theorem midpointGPlusParameters_mem
    {p} (hp : p ∈ gaussConnectionParameterDomain) :
    midpointGPlusParameters p ∈ gaussParameterPoleFreeDomain := by
  intro n hn
  let m := -((n : ℤ) + 1)
  have hcast : p.2.2 - p.1 - p.2.1 = (m : ℂ) := by
    calc
      p.2.2 - p.1 - p.2.1 = -((n : ℂ) + 1) := (by dsimp [midpointGPlusParameters] at hn; linear_combination hn)
      _ = -(((n : ℤ) + 1 : ℤ) : ℂ) := by push_cast; ring
      _ = (m : ℂ) := by dsimp [m]; rw [Int.cast_neg]
  exact (hp.2 m) hcast

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

private theorem familyParameterDeriv_comp_differentiableAt
    {H}
    (hH : IsGaussHypergeometricFamily H) p
    (S : ℂ × ℂ × ℂ → ℂ × ℂ × ℂ)
    (hS : S p ∈ gaussParameterPoleFreeDomain)
    (hSDiff : DifferentiableAt ℂ S p) z (hz : ‖z‖ < 1) :
    DifferentiableAt ℂ
      (fun q : ℂ × ℂ × ℂ => deriv (fun w => H (S q).1 (S q).2.1 (S q).2.2 w) z) p := by
  change DifferentiableAt ℂ
    ((fun q : ℂ × ℂ × ℂ => deriv (fun w => H q.1 q.2.1 q.2.2 w) z) ∘ S) p
  exact (IsGaussHypergeometricFamily.differentiableAt_params_deriv_unitDisk hH hS hz).comp p hSDiff

private theorem gaussSlitPlane_isOpen_for_connection : IsOpen gaussSlitPlane := by
  change IsOpen ({z : ℂ | z.im ≠ 0} ∪ {z | z.re < 1})
  exact (isOpen_compl_singleton.preimage Complex.continuous_im).union
    (isOpen_Iio.preimage Complex.continuous_re)


private theorem connectionDomain_subset_poleFree {p}
    (hp : p ∈ gaussConnectionParameterDomain) : p ∈ gaussParameterPoleFreeDomain := by
  intro n hn
  apply (hp.1 (-(n : ℤ)))
  simpa using hn

/-- The derivative of the first zero-basis function at the midpoint varies holomorphically in
the connection parameters. -/
theorem gaussFMinus_midpoint_deriv_differentiableAt_params
    {H} (hH : IsGaussHypergeometricFamily H)
    {p} (hp : p ∈ gaussConnectionParameterDomain) :
    DifferentiableAt ℂ
      (fun q => deriv (gaussFMinus H q.1 q.2.1 q.2.2) (1 / 2 : ℂ)) p := by
  change DifferentiableAt ℂ
    (fun q : ℂ × ℂ × ℂ => deriv (fun z => H q.1 q.2.1 q.2.2 z) (1 / 2 : ℂ)) p
  exact (familyParameterDeriv_comp_differentiableAt hH p id (connectionDomain_subset_poleFree hp) (by fun_prop) (1 / 2 : ℂ) (by norm_num))

/-- The derivative of the second zero-basis function at the midpoint varies holomorphically in
the connection parameters. -/
theorem gaussFPlus_midpoint_deriv_differentiableAt_params
    {H} (hH : IsGaussHypergeometricFamily H)
    {p} (hp : p ∈ gaussConnectionParameterDomain) :
    DifferentiableAt ℂ
      (fun q => deriv (gaussFPlus H q.1 q.2.1 q.2.2) (1 / 2 : ℂ)) p := by
  have gaussFPlus_deriv_midpoint_formula (p : ℂ × ℂ × ℂ) (hp : p ∈ gaussConnectionParameterDomain) : deriv (gaussFPlus H p.1 p.2.1 p.2.2) (1 / 2 : ℂ) = (1 - p.2.2) * (1 / 2 : ℂ) ^ (-p.2.2) * H (p.1 - p.2.2 + 1) (p.2.1 - p.2.2 + 1) (2 - p.2.2) (1 / 2 : ℂ) + (1 / 2 : ℂ) ^ (1 - p.2.2) * deriv (H (p.1 - p.2.2 + 1) (p.2.1 - p.2.2 + 1) (2 - p.2.2)) (1 / 2 : ℂ) := by
    have hmid : (1 / 2 : ℂ) ∈ gaussSlitPlane := by norm_num [gaussSlitPlane]
    have hHAt := (hH (p.1 - p.2.2 + 1) (p.2.1 - p.2.2 + 1) (2 - p.2.2) (by intro n; exact (midpointFPlusParameters_mem hp) n)).1 (1 / 2 : ℂ) hmid |>.differentiableAt
        (gaussSlitPlane_isOpen_for_connection.mem_nhds hmid)
    have hpowAt : DifferentiableAt ℂ (fun z => z ^ (1 - p.2.2)) (1 / 2 : ℂ) :=
      differentiableAt_id.cpow_const (Or.inl (by norm_num))
    change deriv ((fun z : ℂ => z ^ (1 - p.2.2)) *
      H (p.1 - p.2.2 + 1) (p.2.1 - p.2.2 + 1) (2 - p.2.2)) (1 / 2 : ℂ) = _
    rw [(hpowAt.hasDerivAt.mul hHAt.hasDerivAt).deriv, (show deriv (fun z => z ^ (1 - p.2.2)) (1 / 2 : ℂ) = (1 - p.2.2) * (1 / 2 : ℂ) ^ (-p.2.2) by simpa only [show (1 - p.2.2) - 1 = -p.2.2 by ring] using (Complex.deriv_cpow_const (c := 1 - p.2.2) (gaussCutPlane_subset_Complex_slitPlane (show (1 / 2 : ℂ) ∈ gaussCutPlane by norm_num [gaussCutPlane]))))]
  have hSdiff : DifferentiableAt ℂ midpointFPlusParameters p := by
    fun_prop [midpointFPlusParameters]
  have hval := familyParameterValue_comp_differentiableAt hH p midpointFPlusParameters
    (midpointFPlusParameters_mem hp) hSdiff (1 / 2 : ℂ) (by norm_num)
  have hder := familyParameterDeriv_comp_differentiableAt hH p midpointFPlusParameters
    (midpointFPlusParameters_mem hp) hSdiff (1 / 2 : ℂ) (by norm_num)
  exact ((((show DifferentiableAt ℂ (fun q : ℂ × ℂ × ℂ => 1 - q.2.2) p by fun_prop).mul (show DifferentiableAt ℂ (fun q : ℂ × ℂ × ℂ => (1 / 2 : ℂ) ^ (-q.2.2)) p by exact (show DifferentiableAt ℂ (fun q : ℂ × ℂ × ℂ => -q.2.2) p by fun_prop).const_cpow (Or.inl (by norm_num)))).mul hval).add (((show DifferentiableAt ℂ (fun q : ℂ × ℂ × ℂ => 1 - q.2.2) p by fun_prop).const_cpow (Or.inl (by norm_num)) : DifferentiableAt ℂ (fun q : ℂ × ℂ × ℂ => (1 / 2 : ℂ) ^ (1 - q.2.2)) p).mul hder)).congr_of_eventuallyEq (by filter_upwards [gaussConnectionParameterDomain_isOpen.mem_nhds hp] with q hq; exact gaussFPlus_deriv_midpoint_formula q hq)


/-- The derivative of the first one-basis function at the midpoint varies holomorphically in
the connection parameters. -/
theorem gaussGMinus_midpoint_deriv_differentiableAt_params
    {H} (hH : IsGaussHypergeometricFamily H)
    {p} (hp : p ∈ gaussConnectionParameterDomain) :
    DifferentiableAt ℂ
      (fun q => deriv (gaussGMinus H q.1 q.2.1 q.2.2) (1 / 2 : ℂ)) p := by
  have gaussGMinus_deriv_midpoint_formula (p : ℂ × ℂ × ℂ) (hp : p ∈ gaussConnectionParameterDomain) : deriv (gaussGMinus H p.1 p.2.1 p.2.2) (1 / 2 : ℂ) = -deriv (H p.1 p.2.1 (1 + p.1 + p.2.1 - p.2.2)) (1 / 2 : ℂ) := by
    have hmid : (1 / 2 : ℂ) ∈ gaussSlitPlane := by norm_num [gaussSlitPlane]
    have hcomp := (show DifferentiableAt ℂ (H p.1 p.2.1 (1 + p.1 + p.2.1 - p.2.2)) (1 - (1 / 2 : ℂ)) by convert ((hH p.1 p.2.1 (1 + p.1 + p.2.1 - p.2.2) (by intro n; exact (midpointGMinusParameters_mem hp) n)).1 (1 / 2 : ℂ) hmid |>.differentiableAt (gaussSlitPlane_isOpen_for_connection.mem_nhds hmid)) using 1; norm_num).hasDerivAt.comp (1 / 2 : ℂ) (by simpa using (hasDerivAt_id (1 / 2 : ℂ)).const_sub (1 : ℂ))
    change deriv (fun z : ℂ => H p.1 p.2.1 (1 + p.1 + p.2.1 - p.2.2) (1 - z))
      (1 / 2 : ℂ) = _
    calc
      deriv (fun z => H p.1 p.2.1 (1 + p.1 + p.2.1 - p.2.2) (1 - z))
          (1 / 2 : ℂ) =
        deriv (H p.1 p.2.1 (1 + p.1 + p.2.1 - p.2.2))
          (1 - (1 / 2 : ℂ)) * -1 := (show HasDerivAt (fun z => H p.1 p.2.1 (1 + p.1 + p.2.1 - p.2.2) (1 - z)) (deriv (H p.1 p.2.1 (1 + p.1 + p.2.1 - p.2.2)) (1 - (1 / 2 : ℂ)) * -1) (1 / 2 : ℂ) by simpa [Function.comp_def] using hcomp).deriv
      _ = -deriv (H p.1 p.2.1 (1 + p.1 + p.2.1 - p.2.2)) (1 / 2 : ℂ) := by norm_num
  exact (show DifferentiableAt ℂ (fun q : ℂ × ℂ × ℂ => -deriv (H q.1 q.2.1 (1 + q.1 + q.2.1 - q.2.2)) (1 / 2 : ℂ)) p by simpa [midpointGMinusParameters] using (familyParameterDeriv_comp_differentiableAt hH p midpointGMinusParameters (midpointGMinusParameters_mem hp) (show DifferentiableAt ℂ midpointGMinusParameters p by fun_prop [midpointGMinusParameters]) (1 / 2 : ℂ) (by norm_num)).neg).congr_of_eventuallyEq (show (fun q : ℂ × ℂ × ℂ => deriv (gaussGMinus H q.1 q.2.1 q.2.2) (1 / 2 : ℂ)) =ᶠ[𝓝 p] (fun q => -deriv (H q.1 q.2.1 (1 + q.1 + q.2.1 - q.2.2)) (1 / 2 : ℂ)) by filter_upwards [gaussConnectionParameterDomain_isOpen.mem_nhds hp] with q hq; exact gaussGMinus_deriv_midpoint_formula q hq)


/-- The derivative of the second one-basis function at the midpoint varies holomorphically in
the connection parameters. -/
theorem gaussGPlus_midpoint_deriv_differentiableAt_params
    {H} (hH : IsGaussHypergeometricFamily H)
    {p} (hp : p ∈ gaussConnectionParameterDomain) :
    DifferentiableAt ℂ
      (fun q => deriv (gaussGPlus H q.1 q.2.1 q.2.2) (1 / 2 : ℂ)) p := by
  have gaussGPlus_deriv_midpoint_formula (p : ℂ × ℂ × ℂ) (hp : p ∈ gaussConnectionParameterDomain) : deriv (gaussGPlus H p.1 p.2.1 p.2.2) (1 / 2 : ℂ) = -(p.2.2 - p.1 - p.2.1) * (1 / 2 : ℂ) ^ (p.2.2 - p.1 - p.2.1 - 1) * H (p.2.2 - p.2.1) (p.2.2 - p.1) (1 + p.2.2 - p.1 - p.2.1) (1 / 2 : ℂ) - (1 / 2 : ℂ) ^ (p.2.2 - p.1 - p.2.1) * deriv (H (p.2.2 - p.2.1) (p.2.2 - p.1) (1 + p.2.2 - p.1 - p.2.1)) (1 / 2 : ℂ) := by
    have hmid : (1 / 2 : ℂ) ∈ gaussCutPlane := by norm_num [gaussCutPlane]
    have hmidSlit := gaussCutPlane_subset_gaussSlitPlane hmid
    have hargSlit := gaussCutPlane_subset_Complex_slitPlane hmid
    have hmap : HasDerivAt (fun z => 1 - z) (-1) (1 / 2 : ℂ) := by
      simpa using (hasDerivAt_id (1 / 2 : ℂ)).const_sub (1 : ℂ)
    have hpowDeriv : deriv (fun z => (1 - z) ^ (p.2.2 - p.1 - p.2.1))
        (1 / 2 : ℂ) = -(p.2.2 - p.1 - p.2.1) *
          (1 / 2 : ℂ) ^ (p.2.2 - p.1 - p.2.1 - 1) := by
      change deriv ((fun w : ℂ => w ^ (p.2.2 - p.1 - p.2.1)) ∘
        (fun z => 1 - z)) (1 / 2 : ℂ) = _
      rw [(show deriv ((fun w => w ^ (p.2.2 - p.1 - p.2.1)) ∘ (fun z => 1 - z)) (1 / 2 : ℂ) = deriv (fun w => w ^ (p.2.2 - p.1 - p.2.1)) (1 - (1 / 2 : ℂ)) * -1 by simpa using ((show DifferentiableAt ℂ (fun w : ℂ => w ^ (p.2.2 - p.1 - p.2.1)) (1 - (1 / 2 : ℂ)) by convert (differentiableAt_id.cpow_const (c := p.2.2 - p.1 - p.2.1) hargSlit) using 1 <;> norm_num).hasDerivAt.comp (1 / 2 : ℂ) hmap).deriv), (show deriv (fun w : ℂ => w ^ (p.2.2 - p.1 - p.2.1)) (1 - (1 / 2 : ℂ)) = (p.2.2 - p.1 - p.2.1) * (1 / 2 : ℂ) ^ (p.2.2 - p.1 - p.2.1 - 1) by convert (Complex.deriv_cpow_const (c := p.2.2 - p.1 - p.2.1) (show (1 - (1 / 2 : ℂ)) ∈ Complex.slitPlane by convert hargSlit using 1; norm_num)) using 1; norm_num)]
      ring
    change deriv ((fun z : ℂ => (1 - z) ^ (p.2.2 - p.1 - p.2.1)) *
        (H (p.2.2 - p.2.1) (p.2.2 - p.1) (1 + p.2.2 - p.1 - p.2.1) ∘
          fun z => 1 - z)) (1 / 2 : ℂ) = _
    rw [(((show DifferentiableAt ℂ (fun z => 1 - z) (1 / 2 : ℂ) by fun_prop).cpow_const (Or.inl (by norm_num))).hasDerivAt.mul ((show DifferentiableAt ℂ (H (p.2.2 - p.2.1) (p.2.2 - p.1) (1 + p.2.2 - p.1 - p.2.1)) (1 - (1 / 2 : ℂ)) by convert ((hH (p.2.2 - p.2.1) (p.2.2 - p.1) (1 + p.2.2 - p.1 - p.2.1) (by intro n; exact (midpointGPlusParameters_mem hp) n)).1 (1 / 2 : ℂ) hmidSlit |>.differentiableAt (gaussSlitPlane_isOpen_for_connection.mem_nhds hmidSlit)) using 1; norm_num).hasDerivAt.comp (1 / 2 : ℂ) hmap)).deriv, hpowDeriv]
    norm_num [Function.comp_def]
    ring
  have hSdiff : DifferentiableAt ℂ midpointGPlusParameters p := by
    fun_prop [midpointGPlusParameters]
  have hval := familyParameterValue_comp_differentiableAt hH p midpointGPlusParameters
    (midpointGPlusParameters_mem hp) hSdiff (1 / 2 : ℂ) (by norm_num)
  have hder := familyParameterDeriv_comp_differentiableAt hH p midpointGPlusParameters
    (midpointGPlusParameters_mem hp) hSdiff (1 / 2 : ℂ) (by norm_num)
  exact ((((show DifferentiableAt ℂ (fun q : ℂ × ℂ × ℂ => -(q.2.2 - q.1 - q.2.1)) p by fun_prop).mul ((show DifferentiableAt ℂ (fun q : ℂ × ℂ × ℂ => q.2.2 - q.1 - q.2.1 - 1) p by fun_prop).const_cpow (Or.inl (by norm_num)) : DifferentiableAt ℂ (fun q : ℂ × ℂ × ℂ => (1 / 2 : ℂ) ^ (q.2.2 - q.1 - q.2.1 - 1)) p)).mul hval).sub (((show DifferentiableAt ℂ (fun q : ℂ × ℂ × ℂ => q.2.2 - q.1 - q.2.1) p by fun_prop).const_cpow (Or.inl (by norm_num)) : DifferentiableAt ℂ (fun q : ℂ × ℂ × ℂ => (1 / 2 : ℂ) ^ (q.2.2 - q.1 - q.2.1)) p).mul hder)).congr_of_eventuallyEq (by filter_upwards [gaussConnectionParameterDomain_isOpen.mem_nhds hp] with q hq; exact gaussGPlus_deriv_midpoint_formula q hq)

end DOZZ.Proofs
