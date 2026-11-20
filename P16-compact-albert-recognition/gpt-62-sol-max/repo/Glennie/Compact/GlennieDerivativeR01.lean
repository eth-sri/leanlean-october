/- Actual native differential of Phi in its third Albert argument.
All exposition and Lean code are AI-generated under Robert MacGregor's direction.
No novelty is asserted. No derivative or differentiability premise for Phi
is assumed. The native Hilbert norm and pairing are the existing raw trace ones.
-/
module

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
set_option autoImplicit false
set_option maxHeartbeats 800000
-- Match Compactness at the native/Hilbert inherited-instance boundary.
-- This changes elaboration transparency, not the heartbeat limit or proof rules.
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

/-! ## Existing native operations as continuous linear maps -/

@[simp] theorem pairingContinuous_apply (a b : Albert) :
    nativeInnerContinuous a b = inner a b := rfl

/-- The existing native U operator, linear and continuous in its argument. -/
def UContinuous (x : Albert) : Albert →L[ℝ] Albert :=
  (2 : ℝ) • (jordanContinuous x).comp (jordanContinuous x) -
    jordanContinuous (jordan x x)

@[simp] theorem UContinuous_apply (x z : Albert) :
    UContinuous x z = U x z := rfl

/-- The actual commutator, using the scalar-potential module's definition. -/
def commUContinuous (x y : Albert) : Albert →L[ℝ] Albert :=
  (UContinuous x).comp (UContinuous y) -
    (UContinuous y).comp (UContinuous x)

@[simp] theorem commUContinuous_apply (x y z : Albert) :
    commUContinuous x y z = commU x y z := by
  simp only [commUContinuous, sub_apply, ContinuousLinearMap.comp_apply,
    UContinuous_apply, commU]

/-- A continuous linear expression for the base-variable derivative of U.
Its equality with the actual derivative is proved below. -/
def UBaseDerivative (z p : Albert) : Albert →L[ℝ] Albert :=
  (2 : ℝ) • (jordanContinuous (jordan z p) +
    (jordanContinuous z).comp (jordanContinuous p) -
    (jordanContinuous p).comp (jordanContinuous z))

@[simp] theorem UBaseDerivative_apply (z p h : Albert) :
    UBaseDerivative z p h =
      (2 : ℝ) • (jordan (jordan z p) h +
        jordan z (jordan p h) - jordan p (jordan z h)) := rfl

theorem UBaseDerivative_eq_triple (z p h : Albert) :
    UBaseDerivative z p h = doubledTriple h p z := by
  simp only [UBaseDerivative_apply, doubledTriple, jordan_comm]

/-! ## Actual Frechet differentiation of the native quadratic map -/

/-- Product rule for the existing native continuous bilinear Jordan product. -/
theorem hasFDerivAt_jordan
    {f g : Albert → Albert} {f' g' : Albert →L[ℝ] Albert} {z : Albert}
    (hf : HasFDerivAt f f' z) (hg : HasFDerivAt g g' z) :
    HasFDerivAt (fun w => jordan (f w) (g w))
      ((jordanContinuous (f z)).comp g' +
        (jordanContinuous (g z)).comp f') z := by
  refine (jordanContinuous.hasFDerivAt_of_bilinear hf hg).congr_fderiv ?_
  ext h : 1
  exact congrArg (jordan (f z) (g' h) + ·) (jordan_comm (f' h) (g z))

/-- This differentiates w |-> U w p on the full native Albert space.
No frame, nonzero, generation, or spectral assumption occurs. -/
theorem hasFDerivAt_U_base (z p : Albert) :
    HasFDerivAt (fun w : Albert => U w p) (UBaseDerivative z p) z := by
  have hi := hasFDerivAt_id (𝕜 := ℝ) z
  have hp := (jordanContinuous p).hasFDerivAt (x := z)
  have hd := ((hasFDerivAt_jordan hi hp).const_smul (2 : ℝ)).sub
    ((jordanContinuous p).hasFDerivAt.comp z (hasFDerivAt_jordan hi hi))
  have hh := hd.congr_of_eventuallyEq (f₁ := fun w : Albert => U w p)
    (Filter.Eventually.of_forall fun w => by simp [U, Function.comp_def, jordanContinuous_apply, jordan_comm p])
  refine hh.congr_fderiv ?_
  ext h : 1
  simp only [UBaseDerivative_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    add_apply, sub_apply, smul_apply, id_eq, jordanContinuous_apply,  jordan_add_left, jordan_comm p]
  module

/-! ## Trace adjunction identifies the derivative with native G8 -/

/-- The precise adjunction needed for the variable-base U derivative. -/
theorem doubledTriple_adjoint (a h p z : Albert) :
    inner a (doubledTriple h p z) = inner h (doubledTriple a z p) := by
  have swap (u v w : Albert) : inner u (jordan v w) = inner v (jordan u w) := by
    rw [← inner_jordan_associative, jordan_comm u v, inner_jordan_associative]
  have cross (u v : Albert) : inner a (jordan (jordan h u) v) = inner h (jordan (jordan a v) u) := by
    rw [jordan_comm (jordan h u), ← inner_jordan_associative, swap]
  simp only [doubledTriple, inner_smul_right, inner_add_right, inner_sub_right, cross]
  rw [swap a h, jordan_comm p z]

/-- Actual native Frechet derivative of Phi in its third argument.
The derivative is proved from the bilinear product rule, not supplied as a field. -/
theorem hasFDerivAt_phi_third (x y z : Albert) :
    HasFDerivAt (fun w : Albert => phi x y w)
      (nativeInnerContinuous (glennieVector x y z)) z := by
  have hp := nativeInnerContinuous.hasFDerivAt_of_bilinear
    ((commUContinuous x y).hasFDerivAt (x := z))
    (hasFDerivAt_U_base z (jordan x y))
  have hfun : (fun w : Albert =>
      nativeInnerContinuous (commUContinuous x y w) (U w (jordan x y))) =
      (fun w : Albert => phi x y w) := by
    funext w
    simp only [pairingContinuous_apply, commUContinuous_apply, phi, commU]
  rw [hfun] at hp
  refine hp.congr_fderiv ?_
  ext h : 1
  simp only [add_apply, ContinuousLinearMap.precompL_apply,
    ContinuousLinearMap.precompR, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compL_apply, pairingContinuous_apply, commUContinuous_apply]
  rw [UBaseDerivative_eq_triple, doubledTriple_adjoint,
    commU_pairing x y h (U z (jordan x y)),
    inner_comm (glennieVector x y z) h,
    glennieVector, inner_sub_right]
  ring

/-! ## Metric scaling and useful derivative consequences -/

/-- Differentiate the literal affine line through the third argument. -/
theorem hasDerivAt_phi_third_affine (x y z h : Albert) :
    HasDerivAt (fun t : ℝ => phi x y (z + t • h))
      (inner h (glennieVector x y z)) 0 := by
  have hc : HasDerivAt (fun t : ℝ => z + t • h) h 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).smul_const h).const_add z)
  simpa [Function.comp_def, inner_comm] using (hasFDerivAt_phi_third x y (z + (0 : ℝ) • h)).comp_hasDerivAt 0 hc

end
end Glennie.Compact.GlennieDerivativeR01
