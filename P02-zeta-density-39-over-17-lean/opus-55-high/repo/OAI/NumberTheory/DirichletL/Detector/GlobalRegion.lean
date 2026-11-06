module
public import OAI.NumberTheory.DirichletL.Detector.EulerRegion

@[expose] public section

namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler

theorem unramifiedClosed_open_region_bound (Q : ℝ) (A eta v x w z : ℂ)
    (hQ : 4 ≤ Q) (hA : ‖A‖ ≤ 1) (heta : ‖eta‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    (hx : (7/8:ℝ) ≤ x.re) (hw : (9/10:ℝ) ≤ w.re) (hz : (4/25:ℝ) ≤ z.re) :
    ‖unramifiedClosed Q A eta v x w z - 1‖ ≤ 240 * Q ^ (-(17/10:ℝ)) := by pf_18 24 25 221 100 9 10 31 17 10

end SevenEighths.ProbeEuler
end

end OAI
