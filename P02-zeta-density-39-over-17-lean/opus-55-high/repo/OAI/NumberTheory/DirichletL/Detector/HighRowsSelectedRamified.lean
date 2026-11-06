module
public import OAI.NumberTheory.DirichletL.Detector.HighRowsSelectedBound
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)

def ramifiedSelected (eta a rho x w z : ℂ) (j : ℕ) : ℂ :=
  star eta*(Ideal.absNorm (Ideal.span {p}):ℂ)^x*(1-coordV (Ideal.absNorm (Ideal.span {p})) z)*
    rowClosedMarked p hp hg eta a ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) (coordV (Ideal.absNorm (Ideal.span {p})) z) rho j -
    (Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)*ramifiedClosed p hp hg eta a rho x w z j

lemma ramifiedSelected_eq_replacement (eta a rho x w z : ℂ) (j : ℕ) :
    ramifiedSelected p hp hg eta a rho x w z j =
      ProbeLocal.compensatedReplacement (coordV (Ideal.absNorm (Ideal.span {p})) z) 0 0
        (rowClosedMarked p hp hg eta a ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
          ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) (coordV (Ideal.absNorm (Ideal.span {p})) z) rho j)
        (star eta*(Ideal.absNorm (Ideal.span {p}):ℂ)^x) ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) := by
  rw [ProbeLocal.continued_ramified_compensation]
  pm_545 ramifiedSelected ramifiedClosed ProbeLocal.continuedCorrection mul_zero sub_zero mul_one div_one

include hc in
include hc in
theorem ramifiedSelected_bound (eta a rho x w z : ℂ)
    (hQ : (4:ℝ)≤Ideal.absNorm (Ideal.span {p}))
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (hx : (7/8:ℝ)≤x.re) (hw : (1/2:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re) (j : ℕ) (hj : j<6) :
    ‖ramifiedSelected p hp hg eta a rho x w z j‖≤385*(Ideal.absNorm (Ideal.span {p}):ℝ)^(max (1-w.re) 0) := by
  pm_7340 Q p
  let B : ℝ := max (1-w.re) 0
  pm_3925
  pm_7253
  have hB0 : 0≤B := le_max_right _ _
  have hM := rowClosedMarked_selected_bound p hp hg hc eta a rho x w z hQ heta ha hρ hx hw hz j hj
  have hH := ramifiedClosed_first_region_bound p hp hg hc eta a rho x w z hQ heta ha hρ
    (by linarith) (by linarith) hz (by linarith) j hj
  have hV := first_region_V_half _ hQ z hz
  have h1V : ‖1-coordV (Ideal.absNorm (Ideal.span {p})) z‖≤3/2 := by
    pm_3916 hh
    simp only [norm_one] at hh
    linarith
  have hphase : ‖star eta*(Ideal.absNorm (Ideal.span {p}):ℂ)^x‖≤Q^x.re := by
    change ‖star eta*(Q:ℂ)^x‖≤Q^x.re
    rw [norm_mul,norm_star,Complex.norm_cpow_eq_rpow_re_of_pos hQ0]
    exact mul_le_of_le_one_left (Real.rpow_nonneg hQ0.le _) heta
  have hq : ‖(Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)‖≤Q^B := by
    change ‖(Q:ℂ)^(-w)‖≤Q^B
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hQ0,Complex.neg_re]
    exact Real.rpow_le_rpow_of_exponent_le hQ1 (by dsimp [B];linarith)
  have he : Q^x.re*Q^(-x.re+B)=Q^B := by rw [←Real.rpow_add hQ0];congr 1;ring
  unfold ramifiedSelected
  pm_6990
  calc
    _ ≤ (Q^x.re*(3/2))*(128*Q^(-x.re+B))+Q^B*193 := by
      gcongr
    _ = 385*Q^B := by nlinarith [he]

end SevenEighths.ProbeEuler
end

end OAI
