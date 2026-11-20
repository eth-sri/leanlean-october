/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Weighted.CompactIntegral
public import BergmanWeakType.Weighted.RadialFlux
public import BergmanWeakType.PolarMeasure

/-! # Differentiation of angular means and radial divergence -/

@[expose] public section

noncomputable section

open MeasureTheory Set Real
open scoped Topology

namespace BergmanWeakType.Weighted

def angularMean (F : PolarFn) (r : ℝ) := ∫ θ, F r θ ∂angleMeasure

theorem continuousOn_angularMean {F : PolarFn} {S : Set ℝ}
    (h : ContinuousOn F.uncurry (S ×ˢ univ)) : ContinuousOn (angularMean F) S :=
  continuousOn_average isCompact_Icc ae_angle (h.mono (by grind))

namespace Field

theorem slice_cont (F : Field) (i : Part) {r : ℝ} (hr : r ∈ radii) : Continuous (F.val i r) := by
  apply continuousOn_univ.mp ((F.cont i).comp (continuous_const.prodMk continuous_id).continuousOn _)
  simp_all

/-- The circular mean, with its first and second radial derivatives. -/
def ray (F : Field) : Ray where
  v := angularMean (F.val .v)
  d := angularMean (F.val .r)
  e := angularMean (F.val .rr)
  cont := continuousOn_angularMean (F.cont .v)
  contD := continuousOn_angularMean (F.cont .r)
  jet r hr := integral_jet isCompact_Icc ae_angle (fun i ↦ (F.cont i).mono
    (show unitInterval ×ˢ Icc (-π) π ⊆ radii ×ˢ univ by grind)) continuous_id
    (isOpen_Ioo.mem_nhds hr) (fun t _ u hu ↦ F.jet (.rad t) u (inner_sq hu))

/-- The angular derivative integrates to zero by periodicity, so taking the
circular mean commutes with the differential operator. -/
theorem ray_err (F : Field) (k : ℝ) {r : ℝ} (hr : r ∈ unitInterval) :
    F.ray.err k r = ∫ t, (F.eval r t).error k r ∂angleMeasure := by
  have cont i := F.slice_cont i (Ioo_subset_Ico_self hr)
  have hi i := integrable_on_support isCompact_Icc ae_angle (cont i).continuousOn
  have hz : ∫ t, (F.val .tt) r t ∂angleMeasure = 0 := by
    rw [angleMeasure, integral_smul_measure, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (by linarith [pi_pos]), intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun t _ ↦ show HasDerivAt (F.val .t r) (F.val .tt r t) t from (F.jet (.ang r) t (inner_sq hr)).2) ((cont .tt).intervalIntegrable _ _), show F.val .t r π = F.val .t r (-π) from F.period .t r, sub_self, smul_zero]
  simp (disch := first | exact hi _ | fun_prop) only [Ray.err,ray,Jet.error,Field.eval,angularMean,rhs,integral_sub,integral_add,
    integral_const_mul,integral_div,hz,zero_div,add_zero]

end Field
end BergmanWeakType.Weighted
