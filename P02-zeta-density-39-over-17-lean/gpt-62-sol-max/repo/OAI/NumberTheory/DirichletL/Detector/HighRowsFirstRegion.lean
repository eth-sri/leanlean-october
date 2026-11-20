module
public import OAI.NumberTheory.DirichletL.Detector.HighRowsHolomorphic

@[expose] public section

namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler

theorem unramifiedClosed_first_region_bound (Q : ℝ) (A eta v x w z : ℂ) (eps : ℝ)
    (hQ : 4≤Q) (hA : ‖A‖≤1) (heta : ‖eta‖≤1) (hv : ‖v‖≤1)
    (heps : 0<eps) (hx : (51/100:ℝ)≤x.re) (hz : (17/50:ℝ)≤z.re)
    (hw : -(1/100:ℝ)≤w.re) (hxw : 1+eps≤x.re+w.re) :
    ‖unramifiedClosed Q A eta v x w z-1‖≤240*Q^(-1-min eps (1/50:ℝ)) := by
  apply unramifiedClosed_bound_of_exponents Q A eta v x w z (1/100) _ hQ hA heta hv
  all_goals linarith [min_le_left eps (1/50:ℝ), min_le_right eps (1/50:ℝ), le_min heps.le (by norm_num : (0:ℝ) ≤ 1/50)]

end SevenEighths.ProbeEuler
end

end OAI
