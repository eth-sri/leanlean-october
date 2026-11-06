module
public import OAI.NumberTheory.DirichletL.Detector.HighRowsCentralBase
public import OAI.NumberTheory.DirichletL.Detector.HighRowsCentralEntry
public import OAI.NumberTheory.DirichletL.Detector.HighRowsSelectedRamified
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)

def ramifiedStrictSelected (eta a rho x w z : ℂ) (j : ℕ) : ℂ :=
  star eta*(Ideal.absNorm (Ideal.span {p}):ℂ)^x*(1-coordV (Ideal.absNorm (Ideal.span {p})) z)*
    (rowMarkedTerm p hp hg eta a ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) (coordV (Ideal.absNorm (Ideal.span {p})) z) rho j 1 0 1 0 /
      (1-evenRatio (Ideal.absNorm (Ideal.span {p})) a ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
        (coordV (Ideal.absNorm (Ideal.span {p})) z)))

include hc in
include hc in
theorem ramifiedSelected_central_regular (eta a rho x w z : ℂ) (alpha eps : ℝ)
    (hQ : (4:ℝ)≤Ideal.absNorm (Ideal.span {p}))
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (halpha : (51/100:ℝ)≤alpha) (halpha1 : alpha≤1) (heps : 0<eps) (heps1 : eps≤1/1000)
    (hx : x.re=alpha+16*eps) (hw : w.re=1-alpha-6*eps) (hz : z.re=17/50)
    (j : ℕ) (hj : j<6) :
    ‖ramifiedSelected p hp hg eta a rho x w z j-ramifiedStrictSelected p hp hg eta a rho x w z j‖≤
      385*(Ideal.absNorm (Ideal.span {p}):ℝ)^(1/2:ℝ) := by
  pm_3834
  pm_3925
  have hQ1 : 1≤Q := by linarith
  pm_463
  have hH := ramifiedClosed_first_region_bound p hp hg hc eta a rho x w z hQ heta ha hρ
    (by grind) (by grind) (by grind) (by grind) j hj
  have hV := first_region_V_half _ hQ z (by grind)
  have h1V : ‖1-coordV Q z‖≤3/2 := by
    pm_6852 h
    change ‖coordV Q z‖≤1/2 at hV
    linarith
  pm_3884
  have hqw : ‖(Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)‖≤Q^(1/2:ℝ) := by
    rw [←Complex.ofReal_natCast,Complex.norm_cpow_eq_rpow_re_of_pos hQ0,Complex.neg_re]
    exact Real.rpow_le_rpow_of_exponent_le hQ1 (by rw [hw];linarith)
  have hid (B V M T q H : ℂ) : B*V*M-q*H-B*V*T=B*V*(M-T)-q*H := by ring
  unfold ramifiedSelected ramifiedStrictSelected
  rw [hid]
  pm_6990
  calc
    _≤(Q^x.re*(3/2))*(128*Q^(1/2-x.re))+Q^(1/2:ℝ)*193 := by
      gcongr
    _=385*Q^(1/2:ℝ) := by
      have ht : Q^x.re*Q^(1/2-x.re)=Q^(1/2:ℝ) := by rw [←Real.rpow_add hQ0];congr 1;ring
      nlinarith [ht]
end SevenEighths.ProbeEuler
end

end OAI
