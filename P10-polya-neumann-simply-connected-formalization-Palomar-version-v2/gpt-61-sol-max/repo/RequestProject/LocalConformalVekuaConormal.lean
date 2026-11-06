module

public import RequestProject.PlanarTypes

public import RequestProject.PlanarGeometry

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

open scoped ContDiff


noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric Filter
open scoped InnerProductSpace ComplexConjugate

private theorem conormal_coeff_succ_bound E j :
    ‖physicalVekuaCoeff E (j + 1)‖ ≤ ‖-E / 4‖ * ‖physicalVekuaCoeff E j‖ := by
  have h := congrArg norm (physicalVekuaCoeff_succ E j)
  simp only [norm_mul, Complex.norm_natCast] at h
  have hj : (1 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega)
  calc
    _ ≤ ‖physicalVekuaCoeff E (j + 1)‖ * ((j + 1 : ℕ)) :=
      le_mul_of_one_le_right (norm_nonneg _) hj
    _ = _ := h

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
theorem boundedPhysicalVekuaGradientBTerm_apply M (U : X →L[ℂ] H)
    J E j b :
    boundedPhysicalVekuaGradientBTerm M U J E j b =
      physicalVekuaCoeff E (j + 1) • (M ^ (j + 1)) (U ((J ^ j) b)) := by
  change physicalVekuaCoeff E (j + 1) • M ((M ^ j) (U ((J ^ j) b))) = _
  rw [pow_succ', ContinuousLinearMap.mul_apply]

omit [CompleteSpace H] in
theorem norm_boundedPhysicalVekuaGradientBTerm_le M
    (U : X →L[ℂ] H) J E j :
    ‖boundedPhysicalVekuaGradientBTerm M U J E j‖ ≤
      (‖-E / 4‖ * ‖M‖) * ‖boundedPhysicalVekuaTerm M U J E j‖ := by
  let T  := (M ^ j).comp (U.comp (J ^ j))
  change ‖physicalVekuaCoeff E (j + 1) • M.comp T‖ ≤
    (‖-E / 4‖ * ‖M‖) * ‖physicalVekuaCoeff E j • T‖
  rw [norm_smul, norm_smul]
  calc
    _ ≤ (‖-E / 4‖ * ‖physicalVekuaCoeff E j‖) * (‖M‖ * ‖T‖) :=
      mul_le_mul (conormal_coeff_succ_bound E j) (M.opNorm_comp_le T)
        (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = _ := by ring

section
variable (M : H →L[ℂ] H) (U : X →L[ℂ] H) (J : X →L[ℂ] X) (E : ℂ)

omit [CompleteSpace H] in
include M U J E in
theorem summable_norm_boundedPhysicalVekuaGradientBTerm :
    Summable (fun j : ℕ => ‖boundedPhysicalVekuaGradientBTerm M U J E j‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (norm_boundedPhysicalVekuaGradientBTerm_le M U J E)
    ((summable_norm_boundedPhysicalVekuaTerm M U J E).mul_left (‖-E / 4‖ * ‖M‖))

/-- A convergent operator series in actual H¹ in physical applications. -/
def boundedPhysicalVekuaGradientB M (U : X →L[ℂ] H)
    J E  :=
  ∑' j : ℕ, boundedPhysicalVekuaGradientBTerm M U J E j

section
include M U J E

theorem boundedPhysicalVekuaGradientB_hasSum :
    HasSum (fun j : ℕ => boundedPhysicalVekuaGradientBTerm M U J E j)
      (boundedPhysicalVekuaGradientB M U J E) :=
  (summable_norm_boundedPhysicalVekuaGradientBTerm M U J E).of_norm.hasSum

theorem boundedPhysicalVekuaGradientB_hasSum_apply b :
    HasSum (fun j : ℕ => physicalVekuaCoeff E (j + 1) •
      (M ^ (j + 1)) (U ((J ^ j) b))) (boundedPhysicalVekuaGradientB M U J E b) := by
  simpa  [boundedPhysicalVekuaGradientBTerm_apply] using
    (ContinuousLinearMap.apply ℂ H b).hasSum (boundedPhysicalVekuaGradientB_hasSum M U J E)

end


end


end BoundedSeries

private theorem conormal_gradient_x_wirtinger Ω u :
    h1Gradient Ω 0 u = h1WirtingerD Ω u + h1WirtingerDbar Ω u := by
  rw [h1WirtingerD_apply, h1WirtingerDbar_apply]
  module

private theorem conormal_gradient_y_wirtinger Ω u :
    h1Gradient Ω 1 u = Complex.I • (h1WirtingerD Ω u - h1WirtingerDbar Ω u) := by
  rw [h1WirtingerD_apply, h1WirtingerDbar_apply]
  match_scalars <;> ring_nf
  norm_num

private theorem conormal_divergence_wirtinger (Ω : PlanarSet) (A B : NeumannH1 Ω) :
    h1GradientDivergence Ω (A + B) (Complex.I • (A - B)) =
      (2 : ℂ) • (h1WirtingerDbar Ω A + h1WirtingerD Ω B) := by
  change h1Gradient Ω 0 (A + B) + h1Gradient Ω 1 (Complex.I • (A - B)) = _
  rw [map_add, map_smul, map_sub, h1WirtingerDbar_apply, h1WirtingerD_apply]
  module

section
variable {Ω } (hb : Bornology.IsBounded Ω) (p : ℂ) (u v : NeumannH1 Ω) (j : ℕ)
local notation "neumannH1AffineMultiplierFixed" => neumannH1AffineMultiplier hb p

include Ω hb p u v j

private theorem conormal_affine_Dbar_value
    (hprim : h1WirtingerDbar Ω u = h1Value Ω v) :
    h1WirtingerDbar Ω ((neumannH1AffineMultiplierFixed ^ j) u) =
      h1Value Ω ((neumannH1AffineMultiplierFixed ^ j) v) := by
  let L  :=
    neumannAffineL2Multiplier p (neumannH1AffineBound_spec hb p)
  have hD  := h1WirtingerDbar_affine_pow hb p u j
  have hV  := h1Value_neumannH1AffineMultiplier_pow hb p v j
  simp_all only 

private theorem conormal_affine_gradient_x
    (hCR : h1Gradient Ω 0 u = Complex.I • h1Gradient Ω 1 u)
    (hprim : h1WirtingerDbar Ω u = h1Value Ω v) :
    h1Gradient Ω 0 ((neumannH1AffineMultiplierFixed ^ (j + 1)) u) =
      h1Value Ω (((j + 1 : ℕ) : ℂ) • ((neumannH1AffineMultiplierFixed ^ j) u) +
        (neumannH1AffineMultiplierFixed ^ (j + 1)) v) := by
  have hx := h1WirtingerD_affine_pow_of_antiholomorphic hb p u hCR j
  have hy := conormal_affine_Dbar_value hb p u v (j + 1) hprim
  calc
    _ = h1WirtingerD Ω ((neumannH1AffineMultiplierFixed ^ (j + 1)) u) +
        h1WirtingerDbar Ω ((neumannH1AffineMultiplierFixed ^ (j + 1)) u) :=
      conormal_gradient_x_wirtinger Ω _
    _ = ((j + 1 : ℕ) : ℂ) • h1Value Ω ((neumannH1AffineMultiplierFixed ^ j) u) +
        h1Value Ω ((neumannH1AffineMultiplierFixed ^ (j + 1)) v) :=
      congrArg₂ (fun x y : L2 Ω => x + y) hx hy
    _ = _ := by rw [map_add, map_smul]

private theorem conormal_affine_gradient_y
    (hCR : h1Gradient Ω 0 u = Complex.I • h1Gradient Ω 1 u)
    (hprim : h1WirtingerDbar Ω u = h1Value Ω v) :
    h1Gradient Ω 1 ((neumannH1AffineMultiplierFixed ^ (j + 1)) u) =
      h1Value Ω (Complex.I •
        (((j + 1 : ℕ) : ℂ) • ((neumannH1AffineMultiplierFixed ^ j) u) -
          (neumannH1AffineMultiplierFixed ^ (j + 1)) v)) := by
  have hx := h1WirtingerD_affine_pow_of_antiholomorphic hb p u hCR j
  have hy := conormal_affine_Dbar_value hb p u v (j + 1) hprim
  calc
    _ = Complex.I •
        (h1WirtingerD Ω ((neumannH1AffineMultiplierFixed ^ (j + 1)) u) -
          h1WirtingerDbar Ω ((neumannH1AffineMultiplierFixed ^ (j + 1)) u)) :=
      conormal_gradient_y_wirtinger Ω _
    _ = Complex.I •
        (((j + 1 : ℕ) : ℂ) • h1Value Ω ((neumannH1AffineMultiplierFixed ^ j) u) -
          h1Value Ω ((neumannH1AffineMultiplierFixed ^ (j + 1)) v)) :=
      congrArg (fun z : L2 Ω => Complex.I • z)
        (congrArg₂ (fun x y : L2 Ω => x - y) hx hy)
    _ = _ := by rw [map_smul, map_sub, map_smul]

end


section PhysicalCoordinates

variable {R C K } (hR : 1 < R) (F )
    (hFs : RealSmoothOnBall F R)
    (hb : Bornology.IsBounded (F '' unitDisk))
    (hL : IsLipschitzDomain (F '' unitDisk))
    (hhol : DifferentiableOn ℂ F unitDisk)
    (hinj : InjOn F unitDisk)
    (hC : DiskInverseJacobianBound F C)
    (hK : DiskDerivativeBound F K)
    (e : OpenPartialHomeomorph ℂ ℂ) (he : (e : PlaneMap) = F)
    (hsource : closedUnitDisk ⊆ e.source)
    (hes : RealSmoothOn e.symm e.target)

local notation "ΩF" => F '' unitDisk
local notation "UF" => localConformalHardyH1Extension hR F hFs hb hL hhol hinj hC hK e he hsource hes
local notation "JF" => localConformalHardyPrimitive hR F hFs
local notation "MF" => neumannH1AffineMultiplier hb
local notation "VF" => localConformalVekuaH1 hR F hFs hb hL hhol hinj hC hK e he hsource hes

def localConformalVekuaRemainder (p E : ℂ) : L2Z →L[ℂ] NeumannH1 ΩF :=
  VF p E - UF

def localConformalVekuaGradientA (p E : ℂ) : L2Z →L[ℂ] NeumannH1 ΩF :=
  (-E / 4) • ((VF p E).comp JF)

def localConformalVekuaGradientB (p E : ℂ) : L2Z →L[ℂ] NeumannH1 ΩF :=
  boundedPhysicalVekuaGradientB (MF p) UF JF E

local notation "RF" => localConformalVekuaRemainder hR F hFs hb hL hhol hinj hC hK e he hsource hes
local notation "AF" => localConformalVekuaGradientA hR F hFs hb hL hhol hinj hC hK e he hsource hes
local notation "BF" => localConformalVekuaGradientB hR F hFs hb hL hhol hinj hC hK e he hsource hes

section
variable (p E : ℂ) (b : L2Z)
include p E b

theorem localConformalVekuaRemainder_apply :
    RF p E b = VF p E b - UF b := rfl

theorem localConformalVekuaGradientA_apply :
    AF p E b = (-E / 4) • VF p E (JF b) := rfl

theorem localConformalVekuaRemainder_hasSum :
    HasSum (fun j : ℕ => physicalVekuaCoeff E (j + 1) •
      ((MF p) ^ (j + 1)) (UF ((JF ^ (j + 1)) b))) (RF p E b) := by
  have hs := localConformalVekuaH1_hasSum hR F hFs hb hL hhol hinj hC hK
    e he hsource hes p E b
  simpa only [Finset.sum_range_one, physicalVekuaCoeff_zero, pow_zero,
    ContinuousLinearMap.one_apply, one_smul, localConformalVekuaRemainder_apply] using
      (hasSum_nat_add_iff' 1).2 hs

theorem localConformalVekuaGradientA_hasSum :
    HasSum (fun j : ℕ => (physicalVekuaCoeff E (j + 1) * ((j + 1 : ℕ) : ℂ)) •
      ((MF p) ^ j) (UF ((JF ^ (j + 1)) b))) (AF p E b) := by
  have hs := (localConformalVekuaH1_hasSum hR F hFs hb hL hhol hinj hC hK
    e he hsource hes p E (JF b)).const_smul (-E / 4)
  simpa only [localConformalVekuaGradientA_apply, physicalVekuaCoeff_succ,
    pow_succ, ContinuousLinearMap.mul_apply, smul_smul] using hs

theorem localConformalVekuaGradientB_hasSum :
    HasSum (fun j : ℕ => physicalVekuaCoeff E (j + 1) •
      ((MF p) ^ (j + 1)) (UF ((JF ^ j) b))) (BF p E b) :=
  boundedPhysicalVekuaGradientB_hasSum_apply (MF p) UF JF E b

end


private theorem conormal_primitive_Dbar (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b) (j : ℕ) :
    h1WirtingerDbar ΩF (UF ((JF ^ (j + 1)) b)) = h1Value ΩF (UF ((JF ^ j) b)) := by
  rw [pow_succ', ContinuousLinearMap.mul_apply]
  exact localConformalHardyH1Extension_wirtingerDbar_primitive hR F hFs hb hL hhol hinj hC hK
    e he hsource hes _ (localConformalHardyPrimitive_pow_nonpositive hR F hFs hhol b hbn j)

section
variable (p : ℂ) (b : L2Z) (hbn : IsNonpositiveFourierSupport b) (j : ℕ)
include p b hbn j

private theorem conormal_term_gradient_x :
    h1Gradient ΩF 0 (((MF p) ^ (j + 1)) (UF ((JF ^ (j + 1)) b))) =
      h1Value ΩF (((j + 1 : ℕ) : ℂ) • ((MF p) ^ j) (UF ((JF ^ (j + 1)) b)) +
        ((MF p) ^ (j + 1)) (UF ((JF ^ j) b))) := conormal_affine_gradient_x hb p
    (UF ((JF ^ (j + 1)) b)) (UF ((JF ^ j) b)) j
    (localConformalHardyH1Extension_cauchyRiemann hR F hFs hb hL hhol hinj hC hK
      e he hsource hes _)
    (conormal_primitive_Dbar hR F hFs hb hL hhol hinj hC hK
      e he hsource hes b hbn j)

private theorem conormal_term_gradient_y :
    h1Gradient ΩF 1 (((MF p) ^ (j + 1)) (UF ((JF ^ (j + 1)) b))) =
      h1Value ΩF (Complex.I •
        (((j + 1 : ℕ) : ℂ) • ((MF p) ^ j) (UF ((JF ^ (j + 1)) b)) -
          ((MF p) ^ (j + 1)) (UF ((JF ^ j) b)))) := conormal_affine_gradient_y hb p
    (UF ((JF ^ (j + 1)) b)) (UF ((JF ^ j) b)) j
    (localConformalHardyH1Extension_cauchyRiemann hR F hFs hb hL hhol hinj hC hK
      e he hsource hes _)
    (conormal_primitive_Dbar hR F hFs hb hL hhol hinj hC hK
      e he hsource hes b hbn j)

end


section
variable (p E : ℂ) (b : L2Z)
include p E b

/-- The actual x gradient of the remainder has an H¹ representative. -/
theorem localConformalVekuaRemainder_gradient_x
    (hbn : IsNonpositiveFourierSupport b) :
    h1Gradient ΩF 0 (RF p E b) = h1Value ΩF (AF p E b + BF p E b) := by
  refine (((h1Gradient ΩF 0).hasSum (localConformalVekuaRemainder_hasSum hR F hFs hb hL hhol hinj hC hK e he hsource hes p E b)).congr_fun (fun j => ?_)).unique
    ((h1Value ΩF).hasSum ((localConformalVekuaGradientA_hasSum hR F hFs hb hL hhol hinj hC hK e he hsource hes p E b).add (localConformalVekuaGradientB_hasSum hR F hFs hb hL hhol hinj hC hK e he hsource hes p E b)))
  symm
  rw [map_smul, conormal_term_gradient_x hR F hFs hb hL hhol hinj hC hK e he hsource hes p b hbn j,
    ← map_smul, smul_add, smul_smul]

/-- The actual y gradient has the genuine antiholomorphic primitive sign. -/
theorem localConformalVekuaRemainder_gradient_y
    (hbn : IsNonpositiveFourierSupport b) :
    h1Gradient ΩF 1 (RF p E b) = h1Value ΩF (Complex.I • (AF p E b - BF p E b)) := by
  refine (((h1Gradient ΩF 1).hasSum (localConformalVekuaRemainder_hasSum hR F hFs hb hL hhol hinj hC hK e he hsource hes p E b)).congr_fun (fun j => ?_)).unique
    ((h1Value ΩF).hasSum (((localConformalVekuaGradientA_hasSum hR F hFs hb hL hhol hinj hC hK e he hsource hes p E b).sub (localConformalVekuaGradientB_hasSum hR F hFs hb hL hhol hinj hC hK e he hsource hes p E b)).const_smul Complex.I))
  symm
  rw [map_smul, conormal_term_gradient_y hR F hFs hb hL hhol hinj hC hK e he hsource hes p b hbn j,
    ← map_smul, smul_comm (physicalVekuaCoeff E (j + 1)) Complex.I, smul_sub, smul_smul]

theorem localConformalVekuaGradientA_Dbar
    (hbn : IsNonpositiveFourierSupport b) :
    h1WirtingerDbar ΩF (AF p E b) = (-E / 4) • h1Value ΩF (VF p E b) := by
  rw [localConformalVekuaGradientA_apply, map_smul,
    localConformalVekuaH1_wirtingerDbar_primitive hR F hFs hb hL hhol hinj hC hK
      e he hsource hes p E b hbn]

theorem localConformalVekuaGradientB_D :
    h1WirtingerD ΩF (BF p E b) = (-E / 4) • h1Value ΩF (VF p E b) := by
  have hl := (h1WirtingerD ΩF).hasSum
    (localConformalVekuaGradientB_hasSum hR F hFs hb hL hhol hinj hC hK
      e he hsource hes p E b)
  have hr := ((h1Value ΩF).hasSum
    (localConformalVekuaH1_hasSum hR F hFs hb hL hhol hinj hC hK
      e he hsource hes p E b)).const_smul (-E / 4)
  refine (hl.congr_fun (fun j => ?_)).unique hr
  symm
  rw [map_smul, h1WirtingerD_affine_pow_of_antiholomorphic hb p _
      (localConformalHardyH1Extension_cauchyRiemann hR F hFs hb hL hhol hinj hC hK
        e he hsource hes _) j, smul_smul, physicalVekuaCoeff_succ, map_smul, smul_smul]

/-- The divergence is an equality of actual L² elements, derived from
the completed H¹ series and true first-order derivatives. -/
theorem localConformalVekuaRemainder_divergence
    (hbn : IsNonpositiveFourierSupport b) :
    h1GradientDivergence ΩF (AF p E b + BF p E b)
      (Complex.I • (AF p E b - BF p E b)) = (-E) • h1Value ΩF (VF p E b) := by
  rw [conormal_divergence_wirtinger,
    localConformalVekuaGradientA_Dbar hR F hFs hb hL hhol hinj hC hK e he hsource hes p E b hbn,
    localConformalVekuaGradientB_D hR F hFs hb hL hhol hinj hC hK e he hsource hes p E b]
  module

end


variable {γ } (hγ : IsBoundaryParam (F '' unitDisk) γ)
local notation "h1BoundaryTraceFixed" => h1BoundaryTrace hL hγ


/-- The actual ordinary-parameter L² remainder flux, built from the two
proved H¹ gradient representatives and actual weak trace multipliers. -/
def localConformalVekuaConormalRemainder (p E : ℂ) : L2Z →L[ℂ] BoundaryL2 :=
  (h1BoundaryNormalXMultiplier hγ).comp
      ((h1BoundaryTraceFixed).comp (AF p E + BF p E)) +
    (h1BoundaryNormalYMultiplier hγ).comp
      ((h1BoundaryTraceFixed).comp (Complex.I • (AF p E - BF p E)))

local notation "CF" => localConformalVekuaConormalRemainder hR F hFs hb hL hhol hinj hC hK e he hsource hes hγ

theorem localConformalVekuaConormalRemainder_apply (p E : ℂ) (b : L2Z) :
    CF p E b = h1GradientConormalDensity hL hγ
      (AF p E b + BF p E b) (Complex.I • (AF p E b - BF p E b)) := rfl

private theorem conormal_phase_identity z A B :
    (z.im : ℂ) * (A + B) + (-z.re : ℂ) * (Complex.I * (A - B)) =
      -Complex.I * z * A + Complex.I * conj z * B := by
  apply Complex.ext <;> simp <;> ring

/-- The actual flux has the expected two complex-velocity terms. This
uses the genuine constant-speed physical boundary parameter γ. -/
theorem localConformalVekuaConormalRemainder_ae p E b :
    (CF p E b : ComplexCurve) =ᵐ[volume.restrict boundaryHalfOpenInterval]
      fun θ => -Complex.I * deriv γ θ * h1BoundaryTraceFixed (AF p E b) θ +
        Complex.I * conj (deriv γ θ) * h1BoundaryTraceFixed (BF p E b) θ := by
  rw [localConformalVekuaConormalRemainder_apply]
  have hd := h1GradientConormalDensity_ae hb hL hγ
    (AF p E b + BF p E b) (Complex.I • (AF p E b - BF p E b))
  rw [map_add, map_smul, map_sub] at hd
  filter_upwards [hd,
    Lp.coeFn_add (h1BoundaryTraceFixed (AF p E b))
      (h1BoundaryTraceFixed (BF p E b)),
    Lp.coeFn_smul Complex.I (h1BoundaryTraceFixed (AF p E b) -
      h1BoundaryTraceFixed (BF p E b)),
    Lp.coeFn_sub (h1BoundaryTraceFixed (AF p E b))
      (h1BoundaryTraceFixed (BF p E b))] with θ hθ ha hi hs
  change h1GradientConormalDensity hL hγ
      (AF p E b + BF p E b) (Complex.I • (AF p E b - BF p E b)) θ =
    -Complex.I * deriv γ θ * h1BoundaryTraceFixed (AF p E b) θ +
      Complex.I * conj (deriv γ θ) * h1BoundaryTraceFixed (BF p E b) θ
  rw [hθ, ha, hi]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hs, Pi.sub_apply]
  exact conormal_phase_identity _ _ _

/-- The physical weak Helmholtz form equals the genuine Hardy principal
energy plus the true L² flux of the completed remainder. -/
theorem localConformalVekuaH1_weak_form (p E : ℂ) (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b) (w : NeumannH1 ΩF) :
    (∑ i : Coord, ⟪h1Gradient ΩF i w, h1Gradient ΩF i (VF p E b)⟫_ℂ) -
        E * ⟪h1Value ΩF w, h1Value ΩF (VF p E b)⟫_ℂ =
      ⟪localConformalDiskHalfTrace hR F hFs hL w,
        normalizedConormalPrincipal ((1 - posProj) b)⟫_ℂ +
      ⟪h1BoundaryTraceFixed w, CF p E b⟫_ℂ := by
  have h  :=
    h1_conormal_green hb hL hγ (RF p E b)
      (AF p E b + BF p E b) (Complex.I • (AF p E b - BF p E b))
      (localConformalVekuaRemainder_gradient_x hR F hFs hb hL hhol hinj hC hK
        e he hsource hes p E b hbn)
      (localConformalVekuaRemainder_gradient_y hR F hFs hb hL hhol hinj hC hK
        e he hsource hes p E b hbn) w
  rw [localConformalVekuaRemainder_divergence hR F hFs hb hL hhol hinj hC hK
      e he hsource hes p E b hbn, inner_smul_right,
    ← localConformalVekuaConormalRemainder_apply hR F hFs hb hL hhol hinj hC hK
      e he hsource hes hγ p E b] at h
  have hp := localConformalHardyH1Extension_principal_conormal hR F hFs hb hL hhol hinj hC hK
    e he hsource hes b w
  have hgrad : (∑ i : Coord, ⟪h1Gradient ΩF i w, h1Gradient ΩF i (RF p E b)⟫_ℂ) =
      (∑ i : Coord, ⟪h1Gradient ΩF i w, h1Gradient ΩF i (VF p E b)⟫_ℂ) -
        ∑ i : Coord, ⟪h1Gradient ΩF i w, h1Gradient ΩF i (UF b)⟫_ℂ := by
    simp only [localConformalVekuaRemainder_apply, map_sub, inner_sub_right,
      Finset.sum_sub_distrib]
  rw [← hp]
  calc
    _ = ((∑ i : Coord, ⟪h1Gradient ΩF i w, h1Gradient ΩF i (RF p E b)⟫_ℂ) +
          (-E) * ⟪h1Value ΩF w, h1Value ΩF (VF p E b)⟫_ℂ) +
          ∑ i : Coord, ⟪h1Gradient ΩF i w, h1Gradient ΩF i (UF b)⟫_ℂ := by
      rw [hgrad]
      ring
    _ = _ := by rw [h]; ring

variable {τ : RealMap} {c : ℝ} (hτ : IsC1TraceReparam τ c)
    (hcoord : ∀ θ, F (unitCircleMap θ) = γ (τ θ))

/-- The normalized physical flux keeps the arclength Jacobian `τ′` in
its actual transformed L² representative. No constant-speed premise is
made about F on the circle. -/
def localConformalVekuaNormalizedConormalRemainder p E b  :=
  localConformalBoundaryLoad hτ (CF p E b)

include hcoord in
/-- The exact normalized weak equation for the actual Vekua vector. -/
theorem localConformalVekuaH1_normalized_weak_form p E (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b) w :
    (∑ i : Coord, ⟪h1Gradient ΩF i w, h1Gradient ΩF i (VF p E b)⟫_ℂ) -
        E * ⟪h1Value ΩF w, h1Value ΩF (VF p E b)⟫_ℂ =
      ⟪localConformalDiskHalfTrace hR F hFs hL w,
        normalizedConormalPrincipal ((1 - posProj) b) +
        localConformalVekuaNormalizedConormalRemainder hR F hFs hb hL hhol hinj hC hK
          e he hsource hes hγ hτ p E b⟫_ℂ := by
  rw [localConformalVekuaH1_weak_form hR F hFs hb hL hhol hinj hC hK
    e he hsource hes hγ p E b hbn w, inner_add_right]
  rw [localConformalVekuaNormalizedConormalRemainder,
    localConformalBoundaryLoad_inner hR F hFs hb hL hhol hinj hC hγ hτ hcoord]

end PhysicalCoordinates

end PolyaNeumann

end
