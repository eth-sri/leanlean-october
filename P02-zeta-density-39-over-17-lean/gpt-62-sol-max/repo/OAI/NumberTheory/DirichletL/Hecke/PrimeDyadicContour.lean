module
public import OAI.NumberTheory.DirichletL.Hecke.PrimeDyadicEuler

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open MeasureTheory Set Complex
namespace SevenEighths.HeckePrimeDyadic
open HeckeFamily HeckeDyadic

theorem series_differentiableAt_nonprincipal (χ : Character) (hχ : χ.residue≠1)
    {s : ℂ} (hz : LFunction χ s≠0) : DifferentiableAt ℂ (series χ) s := by
  have h := (LFunction_entire_nonprincipal χ hχ).analyticAt s
  exact (h.deriv.neg.div h hz).differentiableAt

theorem series_differentiableAt_right (χ : Character) {s : ℂ}
    (hs : 1<s.re) : DifferentiableAt ℂ (series χ) s := by
  have ha : AnalyticAt ℂ (LFunction χ) s := by
    apply (Complex.analyticOnNhd_iff_differentiableOn (Complex.isOpen_re_gt 1)).2 ?_ s hs
    intro z hz
    exact (LFunction_differentiableAt χ
      (by intro h; norm_num [h] at hz) (Or.inl (by intro h; norm_num [h] at hz))).differentiableWithinAt
  exact (ha.deriv.neg.div ha (LFunction_ne_zero_of_one_lt_re χ hs)).differentiableAt

end SevenEighths.HeckePrimeDyadic

end

end OAI
