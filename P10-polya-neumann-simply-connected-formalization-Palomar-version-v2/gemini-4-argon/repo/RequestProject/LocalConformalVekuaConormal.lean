module

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


noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric Filter
open scoped Topology InnerProductSpace ComplexConjugate ContDiff

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
theorem boundedPhysicalVekuaGradientBTerm_apply (M : H →L[ℂ] H) U
    (J : X →L[ℂ] X) (E : ℂ) (j : ℕ) (b : X) :
    boundedPhysicalVekuaGradientBTerm M U J E j b =
      physicalVekuaCoeff E (j + 1) • (M ^ (j + 1)) (U ((J ^ j) b)) := by
  change physicalVekuaCoeff E (j + 1) • M ((M ^ j) (U ((J ^ j) b))) = _
  rw [pow_succ', ContinuousLinearMap.mul_apply]

omit [CompleteSpace H] in
theorem norm_boundedPhysicalVekuaGradientBTerm_le M
    (U : X →L[ℂ] H) J E j :
    ‖boundedPhysicalVekuaGradientBTerm M U J E j‖ ≤
      ‖-E / 4‖ * ‖M‖ * ‖boundedPhysicalVekuaTerm M U J E j‖ := by
  let T := (M ^ j).comp (U.comp (J ^ j))
  change ‖physicalVekuaCoeff E (j + 1) • M.comp T‖ ≤
    ‖-E / 4‖ * ‖M‖ * ‖physicalVekuaCoeff E j • T‖
  rw [norm_smul, norm_smul]
  calc
    _ ≤ _ :=
      mul_le_mul (by
        have h := congrArg norm (physicalVekuaCoeff_succ E j)
        simp only [norm_mul, Complex.norm_natCast] at h
        calc
          _ ≤ _ :=
            le_mul_of_one_le_right (norm_nonneg _) (by exact_mod_cast (by omega : 1 ≤ j + 1))
          _ = _ := h) (M.opNorm_comp_le T)
        (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = _ := by ring

omit [CompleteSpace H] in
/-- A convergent operator series in actual H¹ in physical applications. -/
def boundedPhysicalVekuaGradientB (M : H →L[ℂ] H) (U : X →L[ℂ] H)
    (J : X →L[ℂ] X) (E : ℂ) : X →L[ℂ] H :=
  ∑' j : ℕ, boundedPhysicalVekuaGradientBTerm M U J E j

theorem boundedPhysicalVekuaGradientB_hasSum (M : H →L[ℂ] H) U
    (J : X →L[ℂ] X) (E : ℂ) :
    HasSum (fun j => boundedPhysicalVekuaGradientBTerm M U J E j)
      (boundedPhysicalVekuaGradientB M U J E) :=
  (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_boundedPhysicalVekuaGradientBTerm_le M U J E) ((summable_norm_boundedPhysicalVekuaTerm M U J E).mul_left (‖-E / 4‖ * ‖M‖))).of_norm.hasSum

theorem boundedPhysicalVekuaGradientB_hasSum_apply (M : H →L[ℂ] H)
    (U : X →L[ℂ] H) (J : X →L[ℂ] X) (E : ℂ) (b : X) :
    HasSum (fun j => physicalVekuaCoeff E (j + 1) •
      (M ^ (j + 1)) (U ((J ^ j) b))) (boundedPhysicalVekuaGradientB M U J E b) := by
  simpa [boundedPhysicalVekuaGradientBTerm_apply] using
    (ContinuousLinearMap.apply ℂ H b).hasSum (boundedPhysicalVekuaGradientB_hasSum M U J E)

end BoundedSeries

private theorem conormal_divergence_wirtinger Ω A B :
    h1GradientDivergence Ω (A + B) (Complex.I • (A - B)) =
      2 • (h1WirtingerDbar Ω A + h1WirtingerD Ω B) := by
  change h1Gradient Ω 0 (A + B) + h1Gradient Ω 1 (Complex.I • (A - B)) = _
  rw [map_add, map_smul, map_sub, h1WirtingerDbar_apply, h1WirtingerD_apply]
  module

private theorem conormal_affine_Dbar_value 
    hb p u v j
    (hprim : h1WirtingerDbar Ω u = h1Value Ω v) :
    h1WirtingerDbar Ω ((neumannH1AffineMultiplier hb p ^ j) u) =
      h1Value Ω ((neumannH1AffineMultiplier hb p ^ j) v) := by
  exact (h1WirtingerDbar_affine_pow hb p u j).trans ((congrArg (fun w : L2 Ω => ((neumannAffineL2Multiplier p (neumannH1AffineBound_spec hb p)) ^ j) w) hprim).trans (h1Value_neumannH1AffineMultiplier_pow hb p v j).symm)

private theorem conormal_affine_gradient_x 
    hb p u v j
    (hCR : h1Gradient Ω 0 u = Complex.I • h1Gradient Ω 1 u)
    (hprim : h1WirtingerDbar Ω u = h1Value Ω v) :
    h1Gradient Ω 0 ((neumannH1AffineMultiplier hb p ^ (j + 1)) u) =
      h1Value Ω (((j + 1 : ℕ) : ℂ) • (neumannH1AffineMultiplier hb p ^ j) u +
        (neumannH1AffineMultiplier hb p ^ (j + 1)) v) := by
  calc
    _ = _ :=
      (show h1Gradient Ω 0 _ = h1WirtingerD Ω _ + h1WirtingerDbar Ω _ by
        rw [h1WirtingerD_apply, h1WirtingerDbar_apply]
        module)
    _ = _ :=
      congrArg₂ (fun x y : L2 Ω => x + y) (h1WirtingerD_affine_pow_of_antiholomorphic hb p u hCR j) (conormal_affine_Dbar_value hb p u v (j + 1) hprim)
    _ = _ := by rw [map_add, map_smul]

private theorem conormal_affine_gradient_y 
    hb p u v j
    (hCR : h1Gradient Ω 0 u = Complex.I • h1Gradient Ω 1 u)
    (hprim : h1WirtingerDbar Ω u = h1Value Ω v) :
    h1Gradient Ω 1 ((neumannH1AffineMultiplier hb p ^ (j + 1)) u) =
      h1Value Ω (Complex.I •
        (((j + 1 : ℕ) : ℂ) • (neumannH1AffineMultiplier hb p ^ j) u -
          (neumannH1AffineMultiplier hb p ^ (j + 1)) v)) := by
  calc
    _ = _ :=
      (show h1Gradient Ω 1 _ = Complex.I • (h1WirtingerD Ω _ - h1WirtingerDbar Ω _) by
        rw [h1WirtingerD_apply, h1WirtingerDbar_apply]
        simp [smul_sub, smul_smul]
        match_scalars <;> ring_nf
        all_goals simp)
    _ = _ :=
      congrArg (fun z : L2 Ω => Complex.I • z)
        (congrArg₂ (fun x y : L2 Ω => x - y) (h1WirtingerD_affine_pow_of_antiholomorphic hb p u hCR j) (conormal_affine_Dbar_value hb p u v (j + 1) hprim))
    _ = _ := by rw [map_smul, map_sub, map_smul]

private theorem conormal_scaled_map_add {H Y : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (G V : H →L[ℂ] Y) (c a : ℂ) r x y
    (he : G r = V (a • x + y)) :
    G (c • r) = V ((c * a) • x + c • y) := by
  calc
    _ = _ := map_smul G c r
    _ = _ := congrArg (fun z => c • z) he
    _ = _ := (map_smul V c _).symm
    _ = _ := by rw [smul_add, smul_smul]

private theorem conormal_scaled_map_sub {H Y : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (G V : H →L[ℂ] Y) (c a d : ℂ) r x y
    (he : G r = V (d • (a • x - y))) :
    G (c • r) = V (d • ((c * a) • x - c • y)) := by
  calc
    _ = _ := map_smul G c r
    _ = _ := congrArg (fun z => c • z) he
    _ = _ := (map_smul V c _).symm
    _ = _ := by
      congr 1
      module

private theorem conormal_map_series_add {H Y : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (G V : H →L[ℂ] Y) (r a b : ℕ → H) R A B
    (hr : HasSum r R) (ha : HasSum a A) (hb : HasSum b B)
    (he : ∀ j, G (r j) = V (a j + b j)) :
    G R = V (A + B) := by
  exact (show HasSum (fun j => V (a j + b j)) (G R) by
    simpa [he] using G.hasSum hr).unique (V.hasSum (ha.add hb))

private theorem conormal_map_series_sub {H Y : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (G V : H →L[ℂ] Y) (c : ℂ) (r a b : ℕ → H) R A B
    (hr : HasSum r R) (ha : HasSum a A) (hb : HasSum b B)
    (he : ∀ j, G (r j) = V (c • (a j - b j))) :
    G R = V (c • (A - B)) := by
  exact (show HasSum (fun j => V (c • (a j - b j))) (G R) by
    simpa [he] using G.hasSum hr).unique (V.hasSum ((ha.sub hb).const_smul c))

section PhysicalCoordinates

variable {R C K : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ ∞ F (ball 0 R))
    (hb : Bornology.IsBounded (F '' ball 0 1))
    (hL : IsLipschitzDomain (F '' ball 0 1))
    (hhol : DifferentiableOn ℂ F (ball 0 1))
    (hinj : InjOn F (ball 0 1))
    (hC : ∀ z ∈ ball 0 1, 1 ≤ C * ‖deriv F z‖ ^ 2)
    (hK : ∀ z ∈ ball 0 1, ‖fderiv ℝ F z 1‖ ≤ K)
    (e : OpenPartialHomeomorph ℂ ℂ) (he : ↑e = F)
    (hsource : closedBall 0 1 ⊆ e.source)
    (hes : ContDiffOn ℝ ∞ e.symm e.target)

local notation "ΩF" => F '' ball (0 : ℂ) 1
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

theorem localConformalVekuaRemainder_apply p E b :
    RF p E b = VF p E b - UF b := rfl

theorem localConformalVekuaGradientA_apply p E b :
    AF p E b = (-E / 4) • VF p E (JF b) := rfl

local notation "Φ1" => localConformalVekuaH1_hasSum hR F hFs hb hL hhol hinj hC hK e he hsource hes

theorem localConformalVekuaRemainder_hasSum p E b :
    HasSum (fun j => physicalVekuaCoeff E (j + 1) •
      ((MF p) ^ (j + 1)) (UF ((JF ^ (j + 1)) b))) (RF p E b) := by
  simpa [Finset.sum_range_one, physicalVekuaCoeff_zero, localConformalVekuaRemainder_apply] using
      (hasSum_nat_add_iff' 1).2 (Φ1 p E b)

theorem localConformalVekuaGradientA_hasSum p E b :
    HasSum (fun j => (physicalVekuaCoeff E (j + 1) * ((j + 1 : ℕ) : ℂ)) •
      ((MF p) ^ j) (UF ((JF ^ (j + 1)) b))) (AF p E b) := by
  simpa only [localConformalVekuaGradientA_apply, physicalVekuaCoeff_succ,
    pow_succ, ContinuousLinearMap.mul_apply, smul_smul] using (Φ1 p E (JF b)).const_smul (-E / 4)

theorem localConformalVekuaGradientB_hasSum (p E : ℂ) b :
    HasSum (fun j => physicalVekuaCoeff E (j + 1) •
      ((MF p) ^ (j + 1)) (UF ((JF ^ j) b))) (BF p E b) :=
  boundedPhysicalVekuaGradientB_hasSum_apply (MF p) UF JF E b

local notation "Φ4" => h1Value ΩF

private theorem conormal_primitive_Dbar (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b) j :
    h1WirtingerDbar ΩF (UF ((JF ^ (j + 1)) b)) = Φ4 (UF ((JF ^ j) b)) := by
  rw [pow_succ', ContinuousLinearMap.mul_apply]
  exact localConformalHardyH1Extension_wirtingerDbar_primitive hR F hFs hb hL hhol hinj hC hK
    e he hsource hes _ (localConformalHardyPrimitive_pow_nonpositive hR F hFs hhol b hbn j)

local notation "Φ3" => localConformalHardyH1Extension_cauchyRiemann hR F hFs hb hL hhol hinj hC hK e he hsource hes

local notation "Φ8" => conormal_primitive_Dbar hR F hFs hb hL hhol hinj hC hK e he hsource hes

private theorem conormal_term_gradient_x p (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b) j :
    h1Gradient ΩF 0 (((MF p) ^ (j + 1)) (UF ((JF ^ (j + 1)) b))) =
      Φ4 (((j + 1 : ℕ) : ℂ) • ((MF p) ^ j) (UF ((JF ^ (j + 1)) b)) +
        ((MF p) ^ (j + 1)) (UF ((JF ^ j) b))) := by
  exact conormal_affine_gradient_x hb p
    (UF ((JF ^ (j + 1)) b)) (UF ((JF ^ j) b)) j
    (Φ3 _)
    (Φ8 b hbn j)

private theorem conormal_term_gradient_y p (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b) j :
    h1Gradient ΩF 1 (((MF p) ^ (j + 1)) (UF ((JF ^ (j + 1)) b))) =
      Φ4 (Complex.I •
        (((j + 1 : ℕ) : ℂ) • ((MF p) ^ j) (UF ((JF ^ (j + 1)) b)) -
          ((MF p) ^ (j + 1)) (UF ((JF ^ j) b)))) := by
  exact conormal_affine_gradient_y hb p
    (UF ((JF ^ (j + 1)) b)) (UF ((JF ^ j) b)) j
    (Φ3 _)
    (Φ8 b hbn j)

/-- The actual x gradient of the remainder has an H¹ representative. -/
local notation "Φ2" => localConformalVekuaGradientB_hasSum hR F hFs hb hL hhol hinj hC hK e he hsource hes

local notation "Φ5" => localConformalVekuaRemainder_hasSum hR F hFs hb hL hhol hinj hC hK e he hsource hes

local notation "Φ6" => localConformalVekuaGradientA_hasSum hR F hFs hb hL hhol hinj hC hK e he hsource hes

theorem localConformalVekuaRemainder_gradient_x p E (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b) :
    h1Gradient ΩF 0 (RF p E b) = Φ4 (AF p E b + BF p E b) := by
  have heq j : h1Gradient ΩF 0
      (physicalVekuaCoeff E (j + 1) • ((MF p) ^ (j + 1)) (UF ((JF ^ (j + 1)) b))) =
      Φ4
        ((physicalVekuaCoeff E (j + 1) * (j + 1 : ℕ)) •
          ((MF p) ^ j) (UF ((JF ^ (j + 1)) b)) +
          physicalVekuaCoeff E (j + 1) • ((MF p) ^ (j + 1)) (UF ((JF ^ j) b))) := by
    exact conormal_scaled_map_add (h1Gradient ΩF 0) (Φ4)
      (physicalVekuaCoeff E (j + 1)) (j + 1 : ℕ)
      (((MF p) ^ (j + 1)) (UF ((JF ^ (j + 1)) b)))
      (((MF p) ^ j) (UF ((JF ^ (j + 1)) b)))
      (((MF p) ^ (j + 1)) (UF ((JF ^ j) b)))
      (conormal_term_gradient_x hR F hFs hb hL hhol hinj hC hK
        e he hsource hes p b hbn j)
  exact conormal_map_series_add (h1Gradient ΩF 0) (Φ4)
    (fun j => physicalVekuaCoeff E (j + 1) •
      ((MF p) ^ (j + 1)) (UF ((JF ^ (j + 1)) b)))
    (fun j => (physicalVekuaCoeff E (j + 1) * (j + 1 : ℕ)) •
      ((MF p) ^ j) (UF ((JF ^ (j + 1)) b)))
    (fun j => physicalVekuaCoeff E (j + 1) •
      ((MF p) ^ (j + 1)) (UF ((JF ^ j) b)))
    (RF p E b) (AF p E b) (BF p E b)
    (Φ5 p E b)
    (Φ6 p E b)
    (Φ2 p E b) heq

/-- The actual y gradient has the genuine antiholomorphic primitive sign. -/
theorem localConformalVekuaRemainder_gradient_y p E (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b) :
    h1Gradient ΩF 1 (RF p E b) = Φ4 (Complex.I • (AF p E b - BF p E b)) := by
  have heq j : h1Gradient ΩF 1
      (physicalVekuaCoeff E (j + 1) • ((MF p) ^ (j + 1)) (UF ((JF ^ (j + 1)) b))) =
      Φ4 (Complex.I •
        ((physicalVekuaCoeff E (j + 1) * (j + 1 : ℕ)) •
          ((MF p) ^ j) (UF ((JF ^ (j + 1)) b)) -
          physicalVekuaCoeff E (j + 1) • ((MF p) ^ (j + 1)) (UF ((JF ^ j) b)))) := by
    exact conormal_scaled_map_sub (h1Gradient ΩF 1) (Φ4)
      (physicalVekuaCoeff E (j + 1)) (j + 1 : ℕ) Complex.I
      (((MF p) ^ (j + 1)) (UF ((JF ^ (j + 1)) b)))
      (((MF p) ^ j) (UF ((JF ^ (j + 1)) b)))
      (((MF p) ^ (j + 1)) (UF ((JF ^ j) b)))
      (conormal_term_gradient_y hR F hFs hb hL hhol hinj hC hK
        e he hsource hes p b hbn j)
  exact conormal_map_series_sub (h1Gradient ΩF 1) (Φ4) Complex.I
    (fun j => physicalVekuaCoeff E (j + 1) •
      ((MF p) ^ (j + 1)) (UF ((JF ^ (j + 1)) b)))
    (fun j => (physicalVekuaCoeff E (j + 1) * (j + 1 : ℕ)) •
      ((MF p) ^ j) (UF ((JF ^ (j + 1)) b)))
    (fun j => physicalVekuaCoeff E (j + 1) •
      ((MF p) ^ (j + 1)) (UF ((JF ^ j) b)))
    (RF p E b) (AF p E b) (BF p E b)
    (Φ5 p E b)
    (Φ6 p E b)
    (Φ2 p E b) heq

theorem localConformalVekuaGradientA_Dbar p E (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b) :
    h1WirtingerDbar ΩF (AF p E b) = (-E / 4) • Φ4 (VF p E b) := by
  rw [localConformalVekuaGradientA_apply, map_smul,
    localConformalVekuaH1_wirtingerDbar_primitive hR F hFs hb hL hhol hinj hC hK
      e he hsource hes p E b hbn]

theorem localConformalVekuaGradientB_D p E b :
    h1WirtingerD ΩF (BF p E b) = (-E / 4) • Φ4 (VF p E b) := by
  have heq j : h1WirtingerD ΩF
      (physicalVekuaCoeff E (j + 1) • ((MF p) ^ (j + 1)) (UF ((JF ^ j) b))) =
      (-E / 4) • Φ4 (physicalVekuaCoeff E j • ((MF p) ^ j) (UF ((JF ^ j) b))) := by
    rw [map_smul, h1WirtingerD_affine_pow_of_antiholomorphic hb p _
      (Φ3 _) j, smul_smul, physicalVekuaCoeff_succ, map_smul, smul_smul]
  exact (show HasSum (fun j => (-E / 4) • Φ4 (physicalVekuaCoeff E j • ((MF p) ^ j) (UF ((JF ^ j) b)))) (h1WirtingerD ΩF (BF p E b)) by simpa only [heq] using ((h1WirtingerD ΩF).hasSum (Φ2 p E b))).unique (((Φ4).hasSum (Φ1 p E b)).const_smul (-E / 4))

/-- The divergence is an equality of actual L² elements, derived from
the completed H¹ series and true first-order derivatives. -/
theorem localConformalVekuaRemainder_divergence p E (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b) :
    h1GradientDivergence ΩF (AF p E b + BF p E b)
      (Complex.I • (AF p E b - BF p E b)) = (-E) • Φ4 (VF p E b) := by
  rw [conormal_divergence_wirtinger,
    localConformalVekuaGradientA_Dbar hR F hFs hb hL hhol hinj hC hK e he hsource hes p E b hbn,
    localConformalVekuaGradientB_D hR F hFs hb hL hhol hinj hC hK e he hsource hes p E b]
  module

variable {γ : ℝ → ℂ} (hγ : IsBoundaryParam (F '' ball 0 1) γ)

/-- The actual ordinary-parameter L² remainder flux, built from the two
proved H¹ gradient representatives and actual weak trace multipliers. -/
local notation "Φ0" => h1BoundaryTrace hb hL hγ

def localConformalVekuaConormalRemainder (p E : ℂ) : L2Z →L[ℂ] BoundaryL2 :=
  (h1BoundaryNormalXMultiplier hγ).comp
      ((Φ0).comp (AF p E + BF p E)) +
    (h1BoundaryNormalYMultiplier hγ).comp
      ((Φ0).comp (Complex.I • (AF p E - BF p E)))

local notation "CF" => localConformalVekuaConormalRemainder hR F hFs hb hL hhol hinj hC hK e he hsource hes hγ

theorem localConformalVekuaConormalRemainder_apply p E b :
    CF p E b = h1GradientConormalDensity hb hL hγ
      (AF p E b + BF p E b) (Complex.I • (AF p E b - BF p E b)) := rfl

/-- The actual flux has the expected two complex-velocity terms. This
uses the genuine constant-speed physical boundary parameter γ. -/
theorem localConformalVekuaConormalRemainder_ae p E b :
    (CF p E b : ℝ → ℂ) =ᵐ[volume.restrict (Ioc 0 (2 * Real.pi))]
      fun θ => -Complex.I * deriv γ θ * Φ0 (AF p E b) θ +
        Complex.I * conj (deriv γ θ) * Φ0 (BF p E b) θ := by
  rw [localConformalVekuaConormalRemainder_apply]
  have hd := h1GradientConormalDensity_ae hb hL hγ
    (AF p E b + BF p E b) (Complex.I • (AF p E b - BF p E b))
  rw [map_add, map_smul, map_sub] at hd
  filter_upwards [hd,
    Lp.coeFn_add (Φ0 (AF p E b))
      (Φ0 (BF p E b)),
    Lp.coeFn_smul Complex.I (Φ0 (AF p E b) -
      Φ0 (BF p E b)),
    Lp.coeFn_sub (Φ0 (AF p E b))
      (Φ0 (BF p E b))] with θ hθ ha hi hs
  change h1GradientConormalDensity hb hL hγ
      (AF p E b + BF p E b) (Complex.I • (AF p E b - BF p E b)) θ = _
  rw [hθ, ha, hi]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hs, Pi.sub_apply]
  exact (by
    apply Complex.ext <;> simp <;> ring)

/-- The physical weak Helmholtz form equals the genuine Hardy principal
energy plus the true L² flux of the completed remainder. -/
local notation "Φ7" => h1Gradient ΩF

theorem localConformalVekuaH1_weak_form p E (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b) w :
    (∑ i : Fin 2, ⟪Φ7 i w, Φ7 i (VF p E b)⟫_ℂ) -
        E * ⟪Φ4 w, Φ4 (VF p E b)⟫_ℂ =
      ⟪localConformalDiskHalfTrace hR F hFs hL w,
        normalizedConormalPrincipal ((1 - posProj) b)⟫_ℂ +
      ⟪Φ0 w, CF p E b⟫_ℂ := by
  have h :=
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
  rw [← localConformalHardyH1Extension_principal_conormal hR F hFs hb hL hhol hinj hC hK e he hsource hes b w]
  calc
    _ = ((∑ i : Fin 2, ⟪Φ7 i w, Φ7 i (RF p E b)⟫_ℂ) +
          (-E) * ⟪Φ4 w, Φ4 (VF p E b)⟫_ℂ) +
          ∑ i : Fin 2, ⟪Φ7 i w, Φ7 i (UF b)⟫_ℂ := by
      rw [show (∑ i : Fin 2, ⟪Φ7 i w, Φ7 i (RF p E b)⟫_ℂ) = (∑ i : Fin 2, ⟪Φ7 i w, Φ7 i (VF p E b)⟫_ℂ) - ∑ i : Fin 2, ⟪Φ7 i w, Φ7 i (UF b)⟫_ℂ by
        simp only [localConformalVekuaRemainder_apply, map_sub, inner_sub_right,
          Finset.sum_sub_distrib]]
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
theorem localConformalVekuaH1_normalized_weak_form p E (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b) w :
    (∑ i : Fin 2, ⟪Φ7 i w, Φ7 i (VF p E b)⟫_ℂ) -
        E * ⟪Φ4 w, Φ4 (VF p E b)⟫_ℂ =
      ⟪localConformalDiskHalfTrace hR F hFs hL w,
        normalizedConormalPrincipal ((1 - posProj) b) +
        localConformalVekuaNormalizedConormalRemainder hR F hFs hb hL hhol hinj hC hK
          e he hsource hes hγ hτ p E b⟫_ℂ := by
  rw [localConformalVekuaH1_weak_form hR F hFs hb hL hhol hinj hC hK
    e he hsource hes hγ p E b hbn w, inner_add_right, localConformalVekuaNormalizedConormalRemainder,
    localConformalBoundaryLoad_inner hR F hFs hb hL hhol hinj hC hγ hτ hcoord]

end PhysicalCoordinates

end PolyaNeumann

end
