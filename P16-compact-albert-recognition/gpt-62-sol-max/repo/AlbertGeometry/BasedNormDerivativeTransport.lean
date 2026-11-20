/-
Actual derivative and log-metric naturality of a based
whole-cubic norm equivalence. No trace, adjoint, product, Jordan or curvature
preservation is an input. Existence of a recognition map remains a separate
full endpoint obligation. The actual homogeneous-carrier representation
producer supplies these forms; they do not restrict the final theorem.
-/
module

public import AlbertGeometry.CubicHessian
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Topology.Algebra.Module.FiniteDimension
@[expose] public section
namespace AlbertGeometry.BasedNormDerivativeTransport
noncomputable section
open Glennie.SubmissionR04Intrinsic
open AlbertGeometry.Cubic
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace BasedNormIso

@[simp] theorem rawTraceForm_apply (P : BasedCubic E) (e u v : E) :
    rawPair P e u v = traceAt P e u * traceAt P e v - cubicHessian P e u v := by rfl

/-- The mandatory raw/geometric scale derives from the actual twice-log
calculus theorem and actual normalization, not from a metric convention. -/
theorem rawTraceForm_eq_three_logMetric (P : BasedCubic E)
    (e : E) (he : cubic P e = 1) (u v : E) :
    rawPair P e u v = 3 * metric P e u v := by
  have hpos : 0 < cubic P e := by rw [he]; norm_num
  rw [rawTraceForm_apply, logHessianForm_apply P hpos, he]
  simp only [traceAt]
  ring

end BasedNormIso
end
end AlbertGeometry.BasedNormDerivativeTransport
