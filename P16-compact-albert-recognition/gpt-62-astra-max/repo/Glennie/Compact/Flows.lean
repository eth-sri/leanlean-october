module

public import Glennie.Compact.InnerDerivation
public import Glennie.Compactness
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Topology.Algebra.Module.FiniteDimension

@[expose] public section
namespace Glennie.Compact.Flows
noncomputable section
open NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
local notation "Op" => E →L[ℝ] E
local instance : NormedAlgebra ℚ Op := .restrictScalars ℚ ℝ _

/-- Exponential in the operator norm. -/
def opExp (D : Op) : Op := exp D

theorem deriv_opExp : HasStrictFDerivAt (opExp (E := E)) (1 : Op →L[ℝ] Op) 0 := hasStrictFDerivAt_exp_zero

theorem continuous_opExp : Continuous (opExp (E := E)) := exp_continuous

@[simp] theorem opExp_zero : opExp (0 : Op) = 1 := exp_zero

theorem cancel (D : Op) (x : E) : exp D (exp (-D) x) = x := by
  rw [← mul_apply_eq_comp, ← exp_add_of_commute (Commute.refl D).neg_right, add_neg_cancel, exp_zero, one_apply_eq_self]

theorem orbit_deriv (D : Op) (x : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => exp (s • D) x) (D (exp (t • D) x)) t := by
  simpa using (hasDerivAt_exp_smul_const' D t).clm_apply (hasDerivAt_const t x)

private theorem start (D : Op) (x : E) : opExp ((0:ℝ) • D) x = x := by simp
private theorem initial (D : Op) (x : E) : HasDerivAt (fun t : ℝ => opExp (t • D) x) (D x) 0 := by
  simpa [opExp] using orbit_deriv D x 0

private theorem constant {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : ℝ → F}
    (h : ∀ t, HasDerivAt f 0 t) : f 1 = f 0 :=
  is_const_of_deriv_eq_zero (fun t => (h t).differentiableAt) (fun t => (h t).deriv) _ _

/-- Conjugating multiplication by exp(tD) gives a constant curve. -/
theorem exp_prod (D : Op) (j : E →L[ℝ] Op) (hd : ∀ x y, D (j x y) = j (D x) y + j x (D y))
    (x y : E) : exp D (j x y) = j (exp D x) (exp D y) := by
  have h (t : ℝ) : HasDerivAt (fun s : ℝ => exp (s • -D) (j (exp (s • D) x) (exp (s • D) y))) 0 t := by
    have hu : HasDerivAt (fun s : ℝ => j (exp (s • D) x)) (j (D (exp (t • D) x))) t :=
      j.hasFDerivAt.comp_hasDerivAt t (orbit_deriv D x t)
    simpa only [Function.comp_apply,mul_apply_eq_comp, neg_apply, ← hd, map_neg, neg_add_cancel] using
      (hasDerivAt_exp_smul_const (-D) t).clm_apply (hu.clm_apply (orbit_deriv D y t))
  simpa [cancel] using (congrArg (fun z : E => exp D z) (constant h)).symm

theorem exp_trace (D : Op) (tr : E →L[ℝ] ℝ) (ht : ∀ x, tr (D x) = 0) (x : E) : tr (exp D x) = tr x := by
  have h (t : ℝ) : HasDerivAt (fun s : ℝ => tr (exp (s • D) x)) 0 t :=
    (ht _) ▸ tr.hasFDerivAt.comp_hasDerivAt t (orbit_deriv D x t)
  simpa using constant h

def expEquiv (D : Op) := LinearEquiv.ofLinearMap (exp D).toLinearMap (exp (-D)).toLinearMap
  (LinearMap.ext (cancel D)) (LinearMap.ext fun x => by simpa using cancel (-D) x)

set_option maxHeartbeats 2000000
abbrev EndA := Albert →L[ℝ] Albert
def flowAut (D : EndA) (hd : IsJordanDerivation D.toLinearMap) (ht : TraceFree D.toLinearMap) : CompactAutomorphism :=
  ⟨expEquiv D, exp_prod D jordanContinuous hd, exp_trace D (LinearMap.toContinuousLinearMap traceLinear) ht⟩

/-- Stationarity on every one-parameter group of inner derivations. -/
theorem stationary (f : Albert →L[ℝ] ℝ) (x a b : Albert)
    (h : ∀ g : CompactAutomorphism, f (g.equiv x) ≤ f x) : f (innerDer a b x) = 0 := by
  let D : EndA := (innerDerLinear a b).toContinuousLinearMap
  have path (t : ℝ) : f (opExp (t • D) x) ≤ f x :=
    h (flowAut (t • D) ((isJordanDerivation_innerDerLinear a b).smul t) ((traceFree_innerDerLinear a b).smul t))
  have max : IsLocalMax (fun t : ℝ => f (opExp (t • D) x)) 0 :=
    Filter.Eventually.of_forall fun t => by simpa only [start] using path t
  have der := f.hasFDerivAt.comp_hasDerivAt 0 (initial D x)
  exact max.hasDerivAt_eq_zero der

end
end Glennie.Compact.Flows
