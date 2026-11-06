module
public import OAI.NumberTheory.DirichletL.Detector.HighRowsSelectedTerms
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)

include hc in
include hc in
lemma rowBaseFinite_selected_bound (eta a rho x w z : ℂ)
    (hQ : (4:ℝ)≤Ideal.absNorm (Ideal.span {p}))
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (hx : (7/8:ℝ)≤x.re) (hw : (1/2:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re)
    (j e l : ℕ) (hj : j<6)
    (hf : (e=0 ∧ l=2) ∨ (e=1 ∧ l=0) ∨ (e=0 ∧ l=1) ∨ (e=1 ∧ l=1)) :
    ‖rowBaseFinite p hp hg eta a ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) (coordV (Ideal.absNorm (Ideal.span {p})) z)
      rho j e l‖≤16*(Ideal.absNorm (Ideal.span {p}):ℝ)^(-x.re+max (1-w.re) 0) := by
  pm_3824
  pm_7829
  have ht' (k : Fin 2) (m : ℕ) :
      ‖rowMarkedTerm p hp hg eta a ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
        ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) (coordV (Ideal.absNorm (Ideal.span {p})) z)
        rho j e l k.val m‖≤2*(Ideal.absNorm (Ideal.span {p}):ℝ)^(-x.re+max (1-w.re) 0) := by
    pm_3913
    exact sourceRowTerm_selected_base p hp hg hc eta a rho x w z heta ha hρ hx hw hz
      j e l k.val m hj (by omega) hf
  unfold rowBaseFinite
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _k : Fin 2,8*(Ideal.absNorm (Ideal.span {p}):ℝ)^(-x.re+max (1-w.re) 0) := by
      pm_3914
      have hd : ‖rowMarkedTerm p hp hg eta a ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
          ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) (coordV (Ideal.absNorm (Ideal.span {p})) z)
          rho j e l k.val 2/(1-coordV (Ideal.absNorm (Ideal.span {p})) z)‖≤4*(Ideal.absNorm (Ideal.span {p}):ℝ)^(-x.re+max (1-w.re) 0) := by
        rw [div_eq_mul_inv,norm_mul]
        exact (mul_le_mul (ht' k 2) hv (norm_nonneg _) (by positivity)).trans_eq (by ring)
      linarith
    _ = _ := by simp;ring

include hc in
theorem rowClosedMarked_selected_bound (eta a rho x w z : ℂ)
    (hQ : (4:ℝ)≤Ideal.absNorm (Ideal.span {p}))
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (hx : (7/8:ℝ)≤x.re) (hw : (1/2:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re) (j : ℕ) (hj : j<6) :
    ‖rowClosedMarked p hp hg eta a ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) (coordV (Ideal.absNorm (Ideal.span {p})) z) rho j‖≤128*(Ideal.absNorm (Ideal.span {p}):ℝ)^(-x.re+max (1-w.re) 0) := by
  pm_3824
  have h02 := rowBaseFinite_selected_bound p hp hg hc eta a rho x w z hQ heta ha hρ hx hw hz j 0 2 hj (by omega)
  have h10 := rowBaseFinite_selected_bound p hp hg hc eta a rho x w z hQ heta ha hρ hx hw hz j 1 0 hj (by omega)
  have h01 := rowBaseFinite_selected_bound p hp hg hc eta a rho x w z hQ heta ha hρ hx hw hz j 0 1 hj (by omega)
  have h11 := rowBaseFinite_selected_bound p hp hg hc eta a rho x w z hQ heta ha hρ hx hw hz j 1 1 hj (by omega)
  have hr := ProbeLocal.inv_one_sub_norm_le_two _ (first_region_R_half _ hQ a x z ha (by linarith) hz)
  pm_3915

end SevenEighths.ProbeEuler
end

end OAI
