module
public import OAI.NumberTheory.DirichletL.Detector.HighRowsFirstRegion

@[expose] public section

namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler

theorem unramifiedClosed_first_neighborhood_bound (Q : ℝ) (A eta v x w z : ℂ) (eps : ℝ)
    (hQ : 4≤Q) (hA : ‖A‖≤1) (heta : ‖eta‖≤1) (hv : ‖v‖≤1)
    (heps : 0<eps) (hx : (101/200:ℝ)≤x.re) (hz : (27/80:ℝ)≤z.re)
    (hw : -(3/200:ℝ)≤w.re) (hxw : 1+eps≤x.re+w.re) :
    ‖unramifiedClosed Q A eta v x w z-1‖≤240*Q^(-1-min eps (1/50:ℝ)) := by pf_12 3 200 26 25 81 40 211 200 101

end SevenEighths.ProbeEuler
end

end OAI
