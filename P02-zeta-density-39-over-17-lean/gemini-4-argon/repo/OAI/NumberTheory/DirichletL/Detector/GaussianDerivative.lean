module
public import OAI.NumberTheory.DirichletL.Detector.GaussianLow
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical ContDiff Topology
open Filter Set Metric
namespace SevenEighths.ProbePhysical

def gaussianLog (z : ℂ) : ℂ :=
  ((1/(2*Real.pi):ℝ):ℂ)*(Real.pi:ℂ)^(1/2:ℂ)*Complex.exp (-(Complex.log z)^2/4)

lemma gaussianLog_ofReal (y : ℝ) : gaussianLog (y:ℂ)=gaussianMellinProfile y := rfl

lemma gaussianLog_analytic (z : ℂ) (hz : 0<z.re) : AnalyticAt ℂ gaussianLog z := by
  have hl := analyticAt_clog (Complex.mem_slitPlane_iff.mpr (Or.inl hz))
  unfold gaussianLog
  exact analyticAt_const.mul (((hl.pow 2).neg.div_const (c:=4)).cexp)

lemma gaussianLog_scaled_analytic (r : ℝ) (hr : 0<r) (z : ℂ) (hz : 0<z.re) :
    AnalyticAt ℂ (fun w : ℂ=>gaussianLog ((r:ℂ)*w)) z := by
  have h : 0<((r:ℂ)*z).re := by simpa using mul_pos hr hz
  exact (gaussianLog_analytic _ h).comp (analyticAt_const.mul analyticAt_id)
