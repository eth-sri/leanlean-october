module

public import RequestProject.ConformalDiskCoordinates

public import RequestProject.LocalConformalVekuaSeries
public import RequestProject.NeumannH1FirstOrderGreen
public import RequestProject.DiskHardyConormal
public import RequestProject.LocalConformalBoundaryLoad
public import Mathlib.Tactic.Module

/-!
# The actual physical conormal of the Vekua remainder

The two gradient representatives of `V_E b - U b` are constructed in the
genuine physical H¹ space. Their defining series converge there, not just
in L². The actual Wirtinger identities identify their L² divergence with
`-E V_E b`. The genuine all-H¹ conormal Green identity then supplies the
physical boundary flux. Its normalized load uses the proved arclength
Jacobian; the variable-speed conformal circle is never treated as an
`IsBoundaryParam`.

All conformal coordinates are supplied, as in the existing Hardy and
Vekua construction. This module is part of the verified dependency chain.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric Filter
open scoped Topology InnerProductSpace ComplexConjugate

private theorem conormal_coeff_succ_bound (E : ℂ) (j : ℕ) :
    ‖physicalVekuaCoeff E (j + 1)‖ ≤ ‖-E / 4‖ * ‖physicalVekuaCoeff E j‖ := by
  have h := congrArg norm (physicalVekuaCoeff_succ E j)
  simp only [norm_mul, Complex.norm_natCast] at h
  have hj : (1 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by simp
  exact Trans.trans (le_mul_of_one_le_right (norm_nonneg (physicalVekuaCoeff E (j + 1))) hj) h

section BoundedSeries

variable {X H : Type*}
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]

/-- The second genuine H¹ gradient term. There is one additional affine
power and one fewer primitive than in the corresponding Vekua term. -/
def boundedPhysicalVekuaGradientBTerm (M : H →L[ℂ] H) (U : X →L[ℂ] H)
    (J : X →L[ℂ] X) (E : ℂ) (j : ℕ) : X →L[ℂ] H :=
  physicalVekuaCoeff E (j + 1) • (M.comp ((M ^ j).comp (U.comp (J ^ j))))

omit [CompleteSpace H] in
theorem boundedPhysicalVekuaGradientBTerm_apply (M : H →L[ℂ] H) (U : X →L[ℂ] H)
    (J : X →L[ℂ] X) (E : ℂ) (j : ℕ) (b : X) :
    boundedPhysicalVekuaGradientBTerm M U J E j b =
      physicalVekuaCoeff E (j + 1) • (M ^ (j + 1)) (U ((J ^ j) b)) := by
  change physicalVekuaCoeff E (j + 1) • M ((M ^ j) (U ((J ^ j) b))) = _
  rw [pow_succ', ContinuousLinearMap.mul_apply]

omit [CompleteSpace H] in
theorem norm_boundedPhysicalVekuaGradientBTerm_le (M : H →L[ℂ] H)
    (U : X →L[ℂ] H) (J : X →L[ℂ] X) (E : ℂ) (j : ℕ) :
    ‖boundedPhysicalVekuaGradientBTerm M U J E j‖ ≤
      (‖-E / 4‖ * ‖M‖) * ‖boundedPhysicalVekuaTerm M U J E j‖ := by
  let T := (M ^ j).comp (U.comp (J ^ j))
  change ‖physicalVekuaCoeff E (j + 1) • M.comp T‖ ≤
    (‖-E / 4‖ * ‖M‖) * ‖physicalVekuaCoeff E j • T‖
  rw [norm_smul, norm_smul]
  calc
    _ ≤ (‖-E / 4‖ * ‖physicalVekuaCoeff E j‖) * (‖M‖ * ‖T‖) :=
      mul_le_mul (conormal_coeff_succ_bound E j) (M.opNorm_comp_le T)
        (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = _ := by ring

omit [CompleteSpace H] in
theorem summable_norm_boundedPhysicalVekuaGradientBTerm (M : H →L[ℂ] H)
    (U : X →L[ℂ] H) (J : X →L[ℂ] X) (E : ℂ) :
    Summable (fun j : ℕ => ‖boundedPhysicalVekuaGradientBTerm M U J E j‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (norm_boundedPhysicalVekuaGradientBTerm_le M U J E)
    ((summable_norm_boundedPhysicalVekuaTerm M U J E).mul_left (‖-E / 4‖ * ‖M‖))

/-- A convergent operator series in actual H¹ in physical applications. -/
def boundedPhysicalVekuaGradientB (M : H →L[ℂ] H) (U : X →L[ℂ] H)
    (J : X →L[ℂ] X) (E : ℂ) : X →L[ℂ] H :=
  ∑' j : ℕ, boundedPhysicalVekuaGradientBTerm M U J E j

theorem boundedPhysicalVekuaGradientB_hasSum (M : H →L[ℂ] H) (U : X →L[ℂ] H)
    (J : X →L[ℂ] X) (E : ℂ) :
    HasSum (fun j : ℕ => boundedPhysicalVekuaGradientBTerm M U J E j)
      (boundedPhysicalVekuaGradientB M U J E) :=
  (summable_norm_boundedPhysicalVekuaGradientBTerm M U J E).of_norm.hasSum

theorem boundedPhysicalVekuaGradientB_hasSum_apply (M : H →L[ℂ] H)
    (U : X →L[ℂ] H) (J : X →L[ℂ] X) (E : ℂ) (b : X) :
    HasSum (fun j : ℕ => physicalVekuaCoeff E (j + 1) •
      (M ^ (j + 1)) (U ((J ^ j) b))) (boundedPhysicalVekuaGradientB M U J E b) := by
  simpa only [ContinuousLinearMap.apply_apply, boundedPhysicalVekuaGradientBTerm_apply] using
    (ContinuousLinearMap.apply ℂ H b).hasSum (boundedPhysicalVekuaGradientB_hasSum M U J E)

end BoundedSeries

private theorem conormal_gradient_x_wirtinger (Ω : Set ℂ) (u : NeumannH1 Ω) :
    h1Gradient Ω 0 u = h1WirtingerD Ω u + h1WirtingerDbar Ω u := by
  rw [h1WirtingerD_apply, h1WirtingerDbar_apply]
  module

private theorem conormal_gradient_y_wirtinger (Ω : Set ℂ) (u : NeumannH1 Ω) :
    h1Gradient Ω 1 u = Complex.I • (h1WirtingerD Ω u - h1WirtingerDbar Ω u) := by
  rw [h1WirtingerD_apply, h1WirtingerDbar_apply]
  simp only [smul_sub, smul_add, smul_smul]
  match_scalars <;> ring_nf
  simp

private theorem conormal_divergence_wirtinger (Ω : Set ℂ) (A B : NeumannH1 Ω) :
    h1GradientDivergence Ω (A + B) (Complex.I • (A - B)) =
      (2 : ℂ) • (h1WirtingerDbar Ω A + h1WirtingerD Ω B) := by
  change h1Gradient Ω 0 (A + B) + h1Gradient Ω 1 (Complex.I • (A - B)) = _
  rw [map_add, map_smul, map_sub, h1WirtingerDbar_apply, h1WirtingerD_apply]
  module

section PhysicalCoordinates

variable {F : ℂ → ℂ} (coords : ConformalDiskCoordinates F)
include coords

local notation "ΩF" => F '' ball (0 : ℂ) 1
local notation "UF" => localConformalHardyH1Extension coords
local notation "JF" => localConformalHardyPrimitive coords.one_lt_radius F coords.smooth
local notation "MF" => neumannH1AffineMultiplier coords.bounded
local notation "VF" => localConformalVekuaH1 coords

def localConformalVekuaRemainder (p E : ℂ) : L2Z →L[ℂ] NeumannH1 ΩF :=
  VF p E - UF

def localConformalVekuaGradientA (p E : ℂ) : L2Z →L[ℂ] NeumannH1 ΩF :=
  (-E / 4) • ((VF p E).comp JF)

def localConformalVekuaGradientB (p E : ℂ) : L2Z →L[ℂ] NeumannH1 ΩF :=
  boundedPhysicalVekuaGradientB (MF p) UF JF E

local notation "RF" => localConformalVekuaRemainder coords
local notation "AF" => localConformalVekuaGradientA coords
local notation "BF" => localConformalVekuaGradientB coords

theorem localConformalVekuaRemainder_apply (p E : ℂ) (b : L2Z) :
    RF p E b = VF p E b - UF b := rfl

theorem localConformalVekuaGradientA_apply (p E : ℂ) (b : L2Z) :
    AF p E b = (-E / 4) • VF p E (JF b) := rfl

theorem localConformalVekuaRemainder_hasSum (p E : ℂ) (b : L2Z) :
    HasSum (fun j : ℕ => physicalVekuaCoeff E (j + 1) •
      ((MF p) ^ (j + 1)) (UF ((JF ^ (j + 1)) b))) (RF p E b) := by
  have hs := localConformalVekuaH1_hasSum coords p E b
  simpa only [Finset.sum_range_one, physicalVekuaCoeff_zero, pow_zero,
    ContinuousLinearMap.one_apply, one_smul, localConformalVekuaRemainder_apply] using
      (hasSum_nat_add_iff' 1).2 hs

theorem localConformalVekuaGradientA_hasSum (p E : ℂ) (b : L2Z) :
    HasSum (fun j : ℕ => (physicalVekuaCoeff E (j + 1) * ((j + 1 : ℕ) : ℂ)) •
      ((MF p) ^ j) (UF ((JF ^ (j + 1)) b))) (AF p E b) := by
  have hs := (localConformalVekuaH1_hasSum coords p E (JF b)).const_smul (-E / 4)
  simpa only [localConformalVekuaGradientA_apply, physicalVekuaCoeff_succ,
    pow_succ, ContinuousLinearMap.mul_apply, smul_smul] using hs

theorem localConformalVekuaGradientB_hasSum (p E : ℂ) (b : L2Z) :
    HasSum (fun j : ℕ => physicalVekuaCoeff E (j + 1) •
      ((MF p) ^ (j + 1)) (UF ((JF ^ j) b))) (BF p E b) :=
  boundedPhysicalVekuaGradientB_hasSum_apply (MF p) UF JF E b

private theorem conormal_primitive_Dbar (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b) (j : ℕ) :
    h1WirtingerDbar ΩF (UF ((JF ^ (j + 1)) b)) = h1Value ΩF (UF ((JF ^ j) b)) := by
  rw [pow_succ']
  exact localConformalHardyH1Extension_wirtingerDbar_primitive coords _ (localConformalHardyPrimitive_pow_nonpositive coords.one_lt_radius F coords.smooth coords.holomorphic b hbn j)

-- Evaluate the two Wirtinger derivatives before converting to real gradients.
private theorem conormal_remainder_wirtingerD (p E : ℂ) (b : L2Z) :
    h1WirtingerD ΩF (RF p E b) = h1Value ΩF (AF p E b) := by
  have hr := (h1WirtingerD ΩF).hasSum (localConformalVekuaRemainder_hasSum coords p E b)
  have ha := (h1Value ΩF).hasSum (localConformalVekuaGradientA_hasSum coords p E b)
  refine hr.unique (ha.congr_fun fun j => ?_)
  rw [map_smul, map_smul, h1WirtingerD_affine_pow_of_antiholomorphic coords.bounded p _
    (localConformalHardyH1Extension_cauchyRiemann coords _) j, smul_smul]

private theorem conormal_remainder_wirtingerDbar (p E : ℂ) (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b) :
    h1WirtingerDbar ΩF (RF p E b) = h1Value ΩF (BF p E b) := by
  have hr := (h1WirtingerDbar ΩF).hasSum (localConformalVekuaRemainder_hasSum coords p E b)
  have hb := (h1Value ΩF).hasSum (localConformalVekuaGradientB_hasSum coords p E b)
  refine hr.unique (hb.congr_fun fun j => ?_)
  rw [map_smul, map_smul, h1WirtingerDbar_affine_pow, conormal_primitive_Dbar coords b hbn,
    h1Value_neumannH1AffineMultiplier_pow]

/-- The actual x gradient of the remainder has an H¹ representative. -/
theorem localConformalVekuaRemainder_gradient_x (p E : ℂ) (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b) :
    h1Gradient ΩF 0 (RF p E b) = h1Value ΩF (AF p E b + BF p E b) := by
  rw [conormal_gradient_x_wirtinger, conormal_remainder_wirtingerD,
    conormal_remainder_wirtingerDbar coords p E b hbn, map_add]

/-- The actual y gradient has the genuine antiholomorphic primitive sign. -/
theorem localConformalVekuaRemainder_gradient_y (p E : ℂ) (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b) :
    h1Gradient ΩF 1 (RF p E b) = h1Value ΩF (Complex.I • (AF p E b - BF p E b)) := by
  rw [conormal_gradient_y_wirtinger, conormal_remainder_wirtingerD,
    conormal_remainder_wirtingerDbar coords p E b hbn, map_smul, map_sub]

theorem localConformalVekuaGradientA_Dbar (p E : ℂ) (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b) :
    h1WirtingerDbar ΩF (AF p E b) = (-E / 4) • h1Value ΩF (VF p E b) := by
  rw [localConformalVekuaGradientA_apply, map_smul,
    localConformalVekuaH1_wirtingerDbar_primitive coords p E b hbn]

theorem localConformalVekuaGradientB_D (p E : ℂ) (b : L2Z) :
    h1WirtingerD ΩF (BF p E b) = (-E / 4) • h1Value ΩF (VF p E b) := by
  have hl := (h1WirtingerD ΩF).hasSum
    (localConformalVekuaGradientB_hasSum coords p E b)
  have hr := ((h1Value ΩF).hasSum
    (localConformalVekuaH1_hasSum coords p E b)).const_smul (-E / 4)
  have heq (j : ℕ) : h1WirtingerD ΩF
      (physicalVekuaCoeff E (j + 1) • ((MF p) ^ (j + 1)) (UF ((JF ^ j) b))) =
      (-E / 4) • h1Value ΩF (physicalVekuaCoeff E j • ((MF p) ^ j) (UF ((JF ^ j) b))) := by
    rw [map_smul, h1WirtingerD_affine_pow_of_antiholomorphic coords.bounded p _
      (localConformalHardyH1Extension_cauchyRiemann coords _) j, smul_smul, physicalVekuaCoeff_succ, map_smul, smul_smul]
  have hl' : HasSum (fun j : ℕ => (-E / 4) • h1Value ΩF
      (physicalVekuaCoeff E j • ((MF p) ^ j) (UF ((JF ^ j) b))))
      (h1WirtingerD ΩF (BF p E b)) := by simpa only [heq] using hl
  exact hl'.unique hr

/-- The divergence is an equality of actual L² elements, derived from
the completed H¹ series and true first-order derivatives. -/
theorem localConformalVekuaRemainder_divergence (p E : ℂ) (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b) :
    h1GradientDivergence ΩF (AF p E b + BF p E b)
      (Complex.I • (AF p E b - BF p E b)) = (-E) • h1Value ΩF (VF p E b) := by
  rw [conormal_divergence_wirtinger,
    localConformalVekuaGradientA_Dbar coords p E b hbn,
    localConformalVekuaGradientB_D coords p E b]
  module

variable {γ : ℝ → ℂ} (hγ : IsBoundaryParam (F '' ball (0 : ℂ) 1) γ)

/-- The actual ordinary-parameter L² remainder flux, built from the two
proved H¹ gradient representatives and actual weak trace multipliers. -/
def localConformalVekuaConormalRemainder (p E : ℂ) : L2Z →L[ℂ] BoundaryL2 :=
  (h1BoundaryNormalMultiplier hγ 0).comp
      ((h1BoundaryTrace coords.bounded coords.lipschitz hγ).comp (AF p E + BF p E)) +
    (h1BoundaryNormalMultiplier hγ 1).comp
      ((h1BoundaryTrace coords.bounded coords.lipschitz hγ).comp (Complex.I • (AF p E - BF p E)))

local notation "CF" => localConformalVekuaConormalRemainder coords hγ

theorem localConformalVekuaConormalRemainder_apply (p E : ℂ) (b : L2Z) :
    CF p E b = h1GradientConormalDensity coords.bounded coords.lipschitz hγ
      (AF p E b + BF p E b) (Complex.I • (AF p E b - BF p E b)) := rfl

omit coords in
private theorem conormal_phase_identity (z A B : ℂ) :
    (z.im : ℂ) * (A + B) + (-(z.re) : ℂ) * (Complex.I * (A - B)) =
      -Complex.I * z * A + Complex.I * conj z * B := by
  apply Complex.ext <;> simp <;> ring

/-- The actual flux has the expected two complex-velocity terms. This
uses the genuine constant-speed physical boundary parameter γ. -/
theorem localConformalVekuaConormalRemainder_ae (p E : ℂ) (b : L2Z) :
    (CF p E b : ℝ → ℂ) =ᵐ[volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))]
      fun θ => -Complex.I * deriv γ θ * h1BoundaryTrace coords.bounded coords.lipschitz hγ (AF p E b) θ +
        Complex.I * conj (deriv γ θ) * h1BoundaryTrace coords.bounded coords.lipschitz hγ (BF p E b) θ := by
  rw [localConformalVekuaConormalRemainder_apply]
  have hd := h1GradientConormalDensity_ae coords.bounded coords.lipschitz hγ
    (AF p E b + BF p E b) (Complex.I • (AF p E b - BF p E b))
  rw [map_add, map_smul, map_sub] at hd
  filter_upwards [hd,
    Lp.coeFn_add (h1BoundaryTrace coords.bounded coords.lipschitz hγ (AF p E b))
      (h1BoundaryTrace coords.bounded coords.lipschitz hγ (BF p E b)),
    Lp.coeFn_smul Complex.I (h1BoundaryTrace coords.bounded coords.lipschitz hγ (AF p E b) -
      h1BoundaryTrace coords.bounded coords.lipschitz hγ (BF p E b)),
    Lp.coeFn_sub (h1BoundaryTrace coords.bounded coords.lipschitz hγ (AF p E b))
      (h1BoundaryTrace coords.bounded coords.lipschitz hγ (BF p E b))] with θ hθ ha hi hs
  change h1GradientConormalDensity coords.bounded coords.lipschitz hγ
      (AF p E b + BF p E b) (Complex.I • (AF p E b - BF p E b)) θ =
    -Complex.I * deriv γ θ * h1BoundaryTrace coords.bounded coords.lipschitz hγ (AF p E b) θ +
      Complex.I * conj (deriv γ θ) * h1BoundaryTrace coords.bounded coords.lipschitz hγ (BF p E b) θ
  rw [hθ, ha, hi]
  simp only [Pi.smul_apply, smul_eq_mul, hs, Pi.sub_apply]
  exact conormal_phase_identity _ _ _

/-- The physical weak Helmholtz form equals the genuine Hardy principal
energy plus the true L² flux of the completed remainder. -/
theorem localConformalVekuaH1_weak_form (p E : ℂ) (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b) (w : NeumannH1 ΩF) :
    (∑ i : Fin 2, ⟪h1Gradient ΩF i w, h1Gradient ΩF i (VF p E b)⟫_ℂ) -
        E * ⟪h1Value ΩF w, h1Value ΩF (VF p E b)⟫_ℂ =
      ⟪coords.halfTrace w,
        normalizedConormalPrincipal ((1 - posProj) b)⟫_ℂ +
      ⟪h1BoundaryTrace coords.bounded coords.lipschitz hγ w, CF p E b⟫_ℂ := by
  have h : (∑ i : Fin 2, ⟪h1Gradient ΩF i w, h1Gradient ΩF i (RF p E b)⟫_ℂ) +
      ⟪h1Value ΩF w, h1GradientDivergence ΩF
        (AF p E b + BF p E b) (Complex.I • (AF p E b - BF p E b))⟫_ℂ =
      ⟪h1BoundaryTrace coords.bounded coords.lipschitz hγ w, h1GradientConormalDensity coords.bounded coords.lipschitz hγ
        (AF p E b + BF p E b) (Complex.I • (AF p E b - BF p E b))⟫_ℂ :=
    h1_conormal_green coords.bounded coords.lipschitz hγ (RF p E b)
      (AF p E b + BF p E b) (Complex.I • (AF p E b - BF p E b))
      (localConformalVekuaRemainder_gradient_x coords p E b hbn)
      (localConformalVekuaRemainder_gradient_y coords p E b hbn) w
  rw [localConformalVekuaRemainder_divergence coords p E b hbn, inner_smul_right,
    ← localConformalVekuaConormalRemainder_apply coords hγ p E b] at h
  have hp := localConformalHardyH1Extension_principal_conormal coords b w
  have hgrad : (∑ i : Fin 2, ⟪h1Gradient ΩF i w, h1Gradient ΩF i (RF p E b)⟫_ℂ) =
      (∑ i : Fin 2, ⟪h1Gradient ΩF i w, h1Gradient ΩF i (VF p E b)⟫_ℂ) -
        ∑ i : Fin 2, ⟪h1Gradient ΩF i w, h1Gradient ΩF i (UF b)⟫_ℂ := by
    simp only [localConformalVekuaRemainder_apply, map_sub, inner_sub_right,
      Finset.sum_sub_distrib]
  rw [← hp]
  calc
    _ = ((∑ i : Fin 2, ⟪h1Gradient ΩF i w, h1Gradient ΩF i (RF p E b)⟫_ℂ) +
          (-E) * ⟪h1Value ΩF w, h1Value ΩF (VF p E b)⟫_ℂ) +
          ∑ i : Fin 2, ⟪h1Gradient ΩF i w, h1Gradient ΩF i (UF b)⟫_ℂ := by
      rw [hgrad]
      ring
    _ = _ := by rw [h]; ring

variable {τ : ℝ → ℝ} {c : ℝ} (hτ : IsC1TraceReparam τ c)
    (hcoord : ∀ θ, F (circleMap 0 1 θ) = γ (τ θ))

/-- The normalized physical flux keeps the arclength Jacobian `τ′` in
its actual transformed L² representative. No constant-speed premise is
made about F on the circle. -/
def localConformalVekuaNormalizedConormalRemainder (p E : ℂ) (b : L2Z) : L2Z :=
  localConformalBoundaryLoad hτ (CF p E b)

include hcoord in
/-- The exact normalized weak equation for the actual Vekua vector. -/
theorem localConformalVekuaH1_normalized_weak_form (p E : ℂ) (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b) (w : NeumannH1 ΩF) :
    (∑ i : Fin 2, ⟪h1Gradient ΩF i w, h1Gradient ΩF i (VF p E b)⟫_ℂ) -
        E * ⟪h1Value ΩF w, h1Value ΩF (VF p E b)⟫_ℂ =
      ⟪coords.halfTrace w,
        normalizedConormalPrincipal ((1 - posProj) b) +
        localConformalVekuaNormalizedConormalRemainder coords hγ hτ p E b⟫_ℂ := by
  rw [localConformalVekuaH1_weak_form coords hγ p E b hbn w, inner_add_right]
  rw [localConformalVekuaNormalizedConormalRemainder,
    localConformalBoundaryLoad_inner coords hγ hτ hcoord]

end PhysicalCoordinates

end PolyaNeumann

end
