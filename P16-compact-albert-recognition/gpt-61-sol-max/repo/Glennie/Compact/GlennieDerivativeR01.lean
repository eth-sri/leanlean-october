/- Actual native differential of Phi in its third Albert argument.
All exposition and Lean code are AI-generated under Robert MacGregor's direction.
No novelty is asserted. No derivative or differentiability premise for Phi
is assumed. The native Hilbert norm and pairing are the existing raw trace ones.
-/
module
public import Mathlib.Tactic.Simps.Basic
public import AlbertGeometry.LinearSimp

public import Glennie.Compact.GlennieScalarPotentialR01
public import Glennie.Compactness
public import Mathlib.Analysis.Calculus.FDeriv.Bilinear
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.Ring

@[expose] public section
namespace Glennie.Compact.GlennieDerivativeR01

open Glennie
open Glennie.Compact.GlennieScalarPotentialR01

noncomputable section
-- Match Compactness at the native/Hilbert inherited-instance boundary.
-- This changes elaboration transparency, not the heartbeat limit or proof rules.
set_option backward.isDefEq.respectTransparency false
@[simp] theorem pairingContinuous_apply (a b : Albert) :
    nativeInnerContinuous a b = inner a b := rfl

/-- The existing native U operator, linear and continuous in its argument. -/
def UContinuous (x : Albert) : Albert →L[ℝ] Albert :=
  (2 : ℝ) • (jordanContinuous x).comp (jordanContinuous x) -
    jordanContinuous (jordan x x)

/-- The actual commutator, using the scalar-potential module's definition. -/
def commUContinuous (x y : Albert) : Albert →L[ℝ] Albert :=
  (UContinuous x).comp (UContinuous y) -
    (UContinuous y).comp (UContinuous x)

@[simp] theorem commUContinuous_apply (x y z : Albert) :
    commUContinuous x y z = commU x y z := by
  simp only [commUContinuous, UContinuous, sub_apply, smul_apply,
    ContinuousLinearMap.comp_apply, jordanContinuous_apply_apply, U, commU]

/-- A continuous linear expression for the base-variable derivative of U.
Its equality with the actual derivative is proved below. -/
@[simps! apply] def UBaseDerivative (z p : Albert) : Albert →L[ℝ] Albert :=
  (2 : ℝ) • (jordanContinuous (jordan z p) +
    (jordanContinuous z).comp (jordanContinuous p) -
    (jordanContinuous p).comp (jordanContinuous z))

theorem UBaseDerivative_eq_triple (z p h : Albert) :
    UBaseDerivative z p h = doubledTriple h p z := by
  simp only [UBaseDerivative_apply, doubledTriple,
    jordan_comm z p, jordan_comm p h, jordan_comm (jordan p z) h,
    jordan_comm z (jordan h p), jordan_comm z h,
    jordan_comm p (jordan h z)]

/-! ## Actual Frechet differentiation of the native quadratic map -/

/-- Product rule for the existing native continuous bilinear Jordan product. -/
theorem hasFDerivAt_jordan
    {f g : Albert → Albert} {f' g' : Albert →L[ℝ] Albert} {z : Albert}
    (hf : HasFDerivAt f f' z) (hg : HasFDerivAt g g' z) :
    HasFDerivAt (fun w => jordan (f w) (g w))
      ((jordanContinuous (f z)).comp g' +
        (jordanContinuous (g z)).comp f') z := by
  have hp := jordanContinuous.hasFDerivAt_of_bilinear hf hg
  change HasFDerivAt (fun w => jordan (f w) (g w)) _ z at hp
  refine hp.congr_fderiv ?_
  apply ContinuousLinearMap.ext
  intro h
  change jordan (f z) (g' h) + jordan (f' h) (g z) =
    jordan (f z) (g' h) + jordan (g z) (f' h)
  rw [jordan_comm (f' h) (g z)]

/-- This differentiates w |-> U w p on the full native Albert space.
No frame, nonzero, generation, or spectral assumption occurs. -/
theorem hasFDerivAt_U_base (z p : Albert) :
    HasFDerivAt (fun w : Albert => U w p) (UBaseDerivative z p) z := by
  have hi : HasFDerivAt (fun w : Albert => w)
      (ContinuousLinearMap.id ℝ Albert) z := hasFDerivAt_id z
  have hc := hasFDerivAt_const (𝕜 := ℝ) p z
  have h := ((hasFDerivAt_jordan hi (hasFDerivAt_jordan hi hc)).const_smul (2 : ℝ)).sub
    (hasFDerivAt_jordan (hasFDerivAt_jordan hi hi) hc)
  refine h.congr_fderiv ?_
  apply ContinuousLinearMap.ext
  intro h
  simp only [clm_eval, albert_linear, UBaseDerivative_apply, jordanContinuous_apply_apply, jordan_zero_right]
  module

/-! ## Trace adjunction identifies the derivative with native G8 -/

/-- The precise adjunction needed for the variable-base U derivative. -/
theorem doubledTriple_adjoint (a h p z : Albert) :
    inner a (doubledTriple h p z) = inner h (doubledTriple a z p)  := by
  simp only [doubledTriple, albert_linear]
  grind only [inner_jordan_associative, jordan_comm, inner_comm]

theorem hasFDerivAt_phi_third (x y z : Albert) :
    HasFDerivAt (fun w : Albert => phi x y w)
      (nativeInnerContinuous (glennieVector x y z)) z := by
  have hp := nativeInnerContinuous.hasFDerivAt_of_bilinear
    ((commUContinuous x y).hasFDerivAt         )
    (hasFDerivAt_U_base z (jordan x y))
  simp only [pairingContinuous_apply, commUContinuous_apply] at hp
  change HasFDerivAt (fun w => phi x y w) _ z at hp
  refine hp.congr_fderiv ?_
  apply ContinuousLinearMap.ext
  intro h
  simp only [add_apply, ContinuousLinearMap.precompL_apply,
    ContinuousLinearMap.precompR, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compL_apply, pairingContinuous_apply, commUContinuous_apply]
  rw [UBaseDerivative_eq_triple, doubledTriple_adjoint,
    commU_pairing x y h (U z (jordan x y)),
    inner_comm (glennieVector x y z) h,
    glennieVector, inner_sub_right]
  ring

/-! ## Metric scaling and useful derivative consequences -/

/-- The directional derivative is the derivative of the literal affine curve. -/
theorem hasDerivAt_phi_third_affine (x y z h : Albert) :
    HasDerivAt (fun t : ℝ => phi x y (z + t • h))
      (inner h (glennieVector x y z)) 0 := by
  have hlinear : HasDerivAt (fun t : ℝ => t • h) h 0 := by
    simpa only [id_eq, one_smul] using (hasDerivAt_id (0 : ℝ)).smul_const h
  have hc :=
    HasDerivAt.const_add z hlinear
  simpa only [Function.comp_def, zero_smul, add_zero, pairingContinuous_apply,
    inner_comm (glennieVector x y z) h] using
    (hasFDerivAt_phi_third x y (z + (0 : ℝ) • h)).comp_hasDerivAt 0 hc

end
end Glennie.Compact.GlennieDerivativeR01
