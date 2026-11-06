module
public import OAI.NumberTheory.DirichletL.Detector.HighRowsCentralRamified
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)

lemma ramifiedStrictSelected_from_entry (eta a rho x w z : ℂ) (j : ℕ) (b : ℝ)
    (hQ : (4:ℝ)≤Ideal.absNorm (Ideal.span {p})) (heta : ‖eta‖≤1) (ha : ‖a‖≤1)
    (hx : (51/100:ℝ)≤x.re) (hz : (17/50:ℝ)≤z.re)
    (ht : ‖sourceRowTerm p hp hg eta a rho x w z j 1 0 1 0‖≤
      2*(Ideal.absNorm (Ideal.span {p}):ℝ)^b) :
    ‖ramifiedStrictSelected p hp hg eta a rho x w z j‖≤
      6*(Ideal.absNorm (Ideal.span {p}):ℝ)^(x.re+b) := by
  pm_3834
  pm_3925
  pm_1302
  pm_6731
  simp only [Complex.ofReal_natCast] at hr
  have hv := first_region_V_half _ hQ z hz
  pm_6852 hs
  have h1V : ‖1-coordV Q z‖≤3/2 := by change ‖coordV Q z‖≤1/2 at hv;linarith
  pm_3884
  unfold ramifiedStrictSelected
  rw [div_eq_mul_inv]
  simp only [norm_mul] at hphase ⊢
  calc
    _≤(Q^x.re*(3/2))*((2*Q^b)*2) := by gcongr
    _=6*Q^(x.re+b) := by rw [Real.rpow_add hQ0];ring

include hc in
theorem ramifiedStrictSelected_central_norm (eta a rho x w z : ℂ)
    (hQ : (4:ℝ)≤Ideal.absNorm (Ideal.span {p}))
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (hx : (51/100:ℝ)≤x.re) (hz : (17/50:ℝ)≤z.re) (j : ℕ) (hj : j<6) :
    ‖ramifiedStrictSelected p hp hg eta a rho x w z j‖≤
      6*(Ideal.absNorm (Ideal.span {p}):ℝ)^(1-w.re) := by
  have hb := ramifiedStrictSelected_from_entry p hp hg eta a rho x w z j (1-x.re-w.re)
    hQ heta ha hx hz (sourceRowTerm_central_strict_norm p hp hg hc eta a rho x w z heta ha hρ j hj)
  convert hb using 1 ; congr 2 ; ring

include hc in
theorem ramifiedStrictSelected_boundary_norm (eta a rho x w z : ℂ)
    (hQ : (4:ℝ)≤Ideal.absNorm (Ideal.span {p}))
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (hx : (51/100:ℝ)≤x.re) (hz : (17/50:ℝ)≤z.re) (j : ℕ) (hj : j≤1) :
    ‖ramifiedStrictSelected p hp hg eta a rho x w z j‖≤
      6*(Ideal.absNorm (Ideal.span {p}):ℝ)^(-w.re) := by
  have hb := ramifiedStrictSelected_from_entry p hp hg eta a rho x w z j (-x.re-w.re)
    hQ heta ha hx hz (sourceRowTerm_central_boundary_norm p hp hg hc eta a rho x w z heta ha hρ j hj)
  convert hb using 1 ; congr 2 ; ring
end SevenEighths.ProbeEuler
end

end OAI
