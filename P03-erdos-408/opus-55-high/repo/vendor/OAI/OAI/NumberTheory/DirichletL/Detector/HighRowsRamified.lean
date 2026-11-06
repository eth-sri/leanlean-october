module

public import OAI.NumberTheory.DirichletL.Detector.HighRowsFiniteBounds

@[expose] public section

namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler
open ConcretePrimeRowBridge
variable (p : ActualEisensteinCubic.O) (hp : Prime p) [(Ideal.span {p}:Ideal ActualEisensteinCubic.O).IsMaximal]
  (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (ActualEisensteinCubic.O ⧸ Ideal.span {p})≠2)

def ramifiedClosed (eta a rho x w z : ℂ) (j : ℕ) : ℂ :=
  1+(1-coordV (Ideal.absNorm (Ideal.span {p})) z)*
    rowClosedMarked p hp hg eta a ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) (coordV (Ideal.absNorm (Ideal.span {p})) z) rho j

include hc in

theorem sourceRowSeries_ramified (eta a rho x w z : ℂ) (hρ : rho^6=1)
    (hV : ‖coordV (Ideal.absNorm (Ideal.span {p})) z‖<1)
    (hR : ‖evenRatio (Ideal.absNorm (Ideal.span {p})) a
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x)) (coordV (Ideal.absNorm (Ideal.span {p})) z)‖<1)
    (hW : ‖rho*((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w))‖<1)
    (j : ℕ) (hj0 : j≠0) (hj : j<6) :
    sourceRowSeries p hp hg eta a rho x w z j*(1-coordV (Ideal.absNorm (Ideal.span {p})) z)=
      ramifiedClosed p hp hg eta a rho x w z j := by
  rw [sourceRowSeries_eq_closed p hp hg hc eta a rho x w z hρ hV hR hW j hj,ite_eq_right hj0,add_zero]
  unfold ramifiedClosed
  have hn := one_sub_ne_zero_of_norm_lt_one _ hV
  field_simp

end SevenEighths.ProbeEuler
end

end OAI
