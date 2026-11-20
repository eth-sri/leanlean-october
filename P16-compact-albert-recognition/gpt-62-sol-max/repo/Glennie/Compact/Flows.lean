module
public import Glennie.Compact.InnerDerivation
public import Glennie.Compactness
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Comp

@[expose] public section
namespace Glennie.Compact.Flows
open NormedSpace ContinuousLinearMap
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

abbrev End := Albert →L[ℝ] Albert
local instance : NormedSpace ℝ Albert := inferInstance
local instance : NormedRing End := ContinuousLinearMap.toNormedRing
local instance : IsTopologicalRing End := inferInstance

local instance : NormedAlgebra ℚ End := .restrictScalars ℚ ℝ _

abbrev traceCLM : Albert →L[ℝ] ℝ := traceLinear.toContinuousLinearMap

theorem exp_cancel (D : End) (x : Albert) : exp D (exp (-D) x) = x := by
  rw [← mul_apply_eq_comp, ← exp_add_of_commute (Commute.refl D).neg_right,
    add_neg_cancel, exp_zero, one_apply_eq_self]

private theorem flow_derivative (D : End) (x : Albert) (t : ℝ) :
    HasDerivAt (fun s : ℝ => exp (s • D) x) (D (exp (t • D) x)) t := by
  simpa [mul_apply_eq_comp] using
    (hasDerivAt_exp_smul_const' D t).clm_apply (hasDerivAt_const t x)

theorem exp_jordan (D : End) (hD : IsJordanDerivation D.toLinearMap)
    (a b : Albert) : exp D (jordan a b) = jordan (exp D a) (exp D b) := by
  let F (s : ℝ) := exp (s • D)
  let G (s : ℝ) := exp (s • -D)
  have hz (s : ℝ) : HasDerivAt (fun u => G u (jordan (F u a) (F u b))) 0 s := by
    have hp := (jordanContinuous.hasFDerivAt.comp_hasDerivAt s (flow_derivative D a s)).clm_apply
      (flow_derivative D b s)
    refine ((hasDerivAt_exp_smul_const (-D) s).clm_apply hp).congr_deriv ?_
    have h : D (jordan (F s a) (F s b)) = jordan (D (F s a)) (F s b) +
        jordan (F s a) (D (F s b)) := hD _ _
    dsimp only [F] at h
    simp only [Function.comp_apply, mul_apply_eq_comp, neg_apply, jordanContinuous_apply,
      ← h, map_neg, neg_add_cancel]
  have h := is_const_of_deriv_eq_zero (fun s => (hz s).differentiableAt) (fun s => (hz s).deriv) 1 0
  have h' : exp (-D) (jordan (exp D a) (exp D b)) = jordan a b := by
    simpa [F, G, one_apply_eq_self] using h
  simpa [exp_cancel] using (congrArg (fun z => exp D z) h').symm

theorem exp_trace (D : End) (hD : TraceFree D.toLinearMap) (a : Albert) :
    trace (exp D a) = trace a := by
  have hz (s : ℝ) : HasDerivAt (fun u : ℝ => trace (exp (u • D) a)) 0 s :=
    (traceCLM.hasFDerivAt.comp_hasDerivAt s (flow_derivative D a s)).congr_deriv (hD _)
  simpa [one_apply_eq_self] using
    is_const_of_deriv_eq_zero (fun s => (hz s).differentiableAt) (fun s => (hz s).deriv) 1 0

/-- Exponentiating a trace-free derivation gives a product and trace automorphism. -/
def expAut (D : End) (hD : IsJordanDerivation D.toLinearMap) (hT : TraceFree D.toLinearMap) :
    CompactAutomorphism where
  equiv := LinearEquiv.ofLinearMap (exp D).toLinearMap (exp (-D)).toLinearMap
    (LinearMap.ext (exp_cancel D)) (LinearMap.ext fun x => by simpa using exp_cancel (-D) x)
  map_jordan := exp_jordan D hD
  map_trace := exp_trace D hT

end
end Glennie.Compact.Flows
