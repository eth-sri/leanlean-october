/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ODE.ParameterSeriesFamily
public import DOZZ.Hypergeom.ODE.ConnectionParameterDomain
public import DOZZ.Hypergeom.ODE.ParameterSpatialDerivative
public import DOZZ.Hypergeom.BasisRegularity
public import DOZZ.Hypergeom.ODE.CutPlaneTopology

/-! Parameter regularity of the midpoint values and spatial derivatives. -/

@[expose] public section

open scoped Topology

namespace DOZZ.Proofs

private theorem connectionDomain_subset_poleFree {p : ℂ × ℂ × ℂ}
    (hp : p ∈ gaussConnectionParameterDomain) : p ∈ gaussParameterPoleFreeDomain := by
  intro n hn
  have h := hp.1 (-(n : ℤ))
  apply h
  simpa using hn

private def connectionFPlusParameters (p : ℂ × ℂ × ℂ) : ℂ × ℂ × ℂ :=
  (p.1 - p.2.2 + 1, p.2.1 - p.2.2 + 1, 2 - p.2.2)

private def connectionGMinusParameters (p : ℂ × ℂ × ℂ) : ℂ × ℂ × ℂ :=
  (p.1, p.2.1, 1 + p.1 + p.2.1 - p.2.2)

private def connectionGPlusParameters (p : ℂ × ℂ × ℂ) : ℂ × ℂ × ℂ :=
  (p.2.2 - p.2.1, p.2.2 - p.1, 1 + p.2.2 - p.1 - p.2.1)

section
variable {p : ℂ × ℂ × ℂ} (hp : p ∈ gaussConnectionParameterDomain)
include hp

private theorem connectionFPlusParameters_mem :
    connectionFPlusParameters p ∈ gaussParameterPoleFreeDomain := by
  intro n hn
  have hcastNat : p.2.2 = (n : ℂ) + 2 := by
    dsimp [connectionFPlusParameters] at hn
    linear_combination -hn
  have hcast : p.2.2 = (((n : ℤ) + 2 : ℤ) : ℂ) := by
    simpa
  exact (hp.1 ((n : ℤ) + 2)) hcast

private theorem connectionGMinusParameters_mem :
    connectionGMinusParameters p ∈ gaussParameterPoleFreeDomain := by
  intro n hn
  have hcastNat : p.2.2 - p.1 - p.2.1 = (n : ℂ) + 1 := by
    dsimp [connectionGMinusParameters] at hn
    linear_combination -hn
  have hcast : p.2.2 - p.1 - p.2.1 = (((n : ℤ) + 1 : ℤ) : ℂ) := by
    simpa
  exact (hp.2 ((n : ℤ) + 1)) hcast

private theorem connectionGPlusParameters_mem :
    connectionGPlusParameters p ∈ gaussParameterPoleFreeDomain := by
  intro n hn
  have hcastNat : p.2.2 - p.1 - p.2.1 = -((n : ℂ) + 1) := by
    dsimp [connectionGPlusParameters] at hn
    linear_combination hn
  let m : ℤ := -((n : ℤ) + 1)
  have hcast : p.2.2 - p.1 - p.2.1 = (m : ℂ) := by
    calc
      p.2.2 - p.1 - p.2.1 = -((n : ℂ) + 1) := hcastNat
      _ = -(((n : ℤ) + 1 : ℤ) : ℂ) := by push_cast; ring
      _ = (m : ℂ) := by dsimp [m]; rw [Int.cast_neg]
  exact (hp.2 m) hcast

end

/-- Parameter regularity of the value and the spatial derivative at the midpoint. -/
structure MidpointRegular (F : (ℂ × ℂ × ℂ) → ℂ → ℂ) (p : ℂ × ℂ × ℂ) : Prop where
  value : DifferentiableAt ℂ (fun q => F q (1 / 2)) p
  spatialDeriv : DifferentiableAt ℂ (fun q => deriv (F q) (1 / 2)) p

private def midpointArg (reflect : Bool) (z : ℂ) : ℂ := if reflect then 1 - z else z

private theorem midpointArg_apply (r : Bool) : midpointArg r (1 / 2) = 1 / 2 := by
  cases r <;> norm_num [midpointArg]

section
variable {H : ℂ → ℂ → ℂ → ℂ → ℂ} (hH : IsGaussHypergeometricFamily H) {p : ℂ × ℂ × ℂ}
include hH

/-- All four midpoint jets are instances of the same chain and product rule. -/
private theorem midpointRegular_of_params
    (S : ℂ × ℂ × ℂ → ℂ × ℂ × ℂ) (hS : S p ∈ gaussParameterPoleFreeDomain)
    (hSD : DifferentiableAt ℂ S p) (E : ℂ × ℂ × ℂ → ℂ) (hE : DifferentiableAt ℂ E p)
    (r : Bool) : MidpointRegular (fun q z => midpointArg r z ^ E q *
      H (S q).1 (S q).2.1 (S q).2.2 (midpointArg r z)) p := by
  let m : ℂ := 1 / 2
  let L (q : ℂ × ℂ × ℂ) := H (S q).1 (S q).2.1 (S q).2.2
  have hm : ‖m‖ < 1 := by norm_num [m]
  have hV : DifferentiableAt ℂ (fun q => L q m) p :=
    ((IsGaussHypergeometricFamily.differentiableOn_params_unitDisk hH hm _ hS).differentiableAt
      (gaussParameterPoleFreeDomain_isOpen.mem_nhds hS)).comp p hSD
  have hD : DifferentiableAt ℂ (fun q => deriv (L q) m) p :=
    (IsGaussHypergeometricFamily.differentiableAt_params_deriv_unitDisk hH hS hm).comp p hSD
  have hm₀ : m ≠ 0 := by norm_num [m]
  have hpow := hE.const_cpow (Or.inl hm₀)
  refine ⟨?_, ?_⟩
  · change DifferentiableAt ℂ (fun q => midpointArg r m ^ E q * L q (midpointArg r m)) p
    rw [midpointArg_apply]
    exact hpow.mul hV
  let ε : ℂ := if r then -1 else 1
  have harg : HasDerivAt (midpointArg r) ε m := by
    cases r
    · change HasDerivAt id 1 m
      exact hasDerivAt_id m
    · change HasDerivAt (fun z => 1 - z) (-1) m
      exact (hasDerivAt_id m).const_sub (1 : ℂ)
  have hreg := (((hE.mul ((hE.sub_const 1).const_cpow (Or.inl hm₀))).mul_const ε).mul hV).add
    (hpow.mul (hD.mul_const ε))
  apply hreg.congr_of_eventuallyEq
  filter_upwards [hSD.continuousAt.eventually_mem (gaussParameterPoleFreeDomain_isOpen.mem_nhds hS)] with q hq
  have hslit : m ∈ gaussSlitPlane := by norm_num [gaussSlitPlane, m]
  have hL : HasDerivAt (L q) (deriv (L q) m) (midpointArg r m) := by
    rw [show midpointArg r m = m from midpointArg_apply r]
    exact ((hH (S q).1 (S q).2.1 (S q).2.2 hq).1 m hslit).differentiableAt
      (gaussSlitPlane_isOpen.mem_nhds hslit) |>.hasDerivAt
  have hpowArg := harg.cpow_const (c := E q) (show midpointArg r m ∈ Complex.slitPlane by
    rw [show midpointArg r m = m from midpointArg_apply r]; norm_num [Complex.slitPlane, m])
  exact ((hpowArg.mul (hL.comp m harg)).deriv.trans (by
    simp only [Function.comp_apply, Pi.mul_apply, Pi.add_apply, show midpointArg r m = m from midpointArg_apply r]))

theorem gaussFMinus_midpoint_regular (hp : p ∈ gaussConnectionParameterDomain) :
    MidpointRegular (fun q => gaussFMinus H q.1 q.2.1 q.2.2) p := by
  delta gaussFMinus
  simpa [midpointArg, id] using
    midpointRegular_of_params hH id (connectionDomain_subset_poleFree hp)
      (by fun_prop) (fun _ => 0) (by fun_prop) false

theorem gaussFPlus_midpoint_regular (hp : p ∈ gaussConnectionParameterDomain) :
    MidpointRegular (fun q => gaussFPlus H q.1 q.2.1 q.2.2) p := by
  delta gaussFPlus
  simpa [midpointArg, connectionFPlusParameters] using
    midpointRegular_of_params hH connectionFPlusParameters (connectionFPlusParameters_mem hp)
      (by fun_prop [connectionFPlusParameters]) (fun q => 1 - q.2.2) (by fun_prop) false

theorem gaussGMinus_midpoint_regular (hp : p ∈ gaussConnectionParameterDomain) :
    MidpointRegular (fun q => gaussGMinus H q.1 q.2.1 q.2.2) p := by
  delta gaussGMinus
  simpa [midpointArg, connectionGMinusParameters] using
    midpointRegular_of_params hH connectionGMinusParameters (connectionGMinusParameters_mem hp)
      (by fun_prop [connectionGMinusParameters]) (fun _ => 0) (by fun_prop) true

theorem gaussGPlus_midpoint_regular (hp : p ∈ gaussConnectionParameterDomain) :
    MidpointRegular (fun q => gaussGPlus H q.1 q.2.1 q.2.2) p := by
  delta gaussGPlus
  simpa [midpointArg, connectionGPlusParameters] using
    midpointRegular_of_params hH connectionGPlusParameters (connectionGPlusParameters_mem hp)
      (by fun_prop [connectionGPlusParameters]) (fun q => q.2.2 - q.1 - q.2.1) (by fun_prop) true

end

end DOZZ.Proofs
