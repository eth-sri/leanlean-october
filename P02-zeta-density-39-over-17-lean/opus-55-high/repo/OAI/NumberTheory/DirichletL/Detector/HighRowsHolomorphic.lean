module
public import OAI.NumberTheory.DirichletL.Detector.HighRowsRamified
public import OAI.NumberTheory.DirichletL.Detector.GlobalHolomorphic
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : goodLambda∉Ideal.span {p})

section
variable (eta a rho : ℂ) (X W V : ℂ→ℂ) (t : ℂ) (hX : DifferentiableAt ℂ X t) (hW : DifferentiableAt ℂ W t) (hV : DifferentiableAt ℂ V t)
include eta a rho X W V t hX hW hV
lemma rowMarkedTerm_differentiableAt
    (j e l k m : ℕ) :
    DifferentiableAt ℂ (fun s=>rowMarkedTerm p hp hg eta a (X s) (W s) (V s) rho j e l k m) t := by
  unfold rowMarkedTerm
  split_ifs
  · fun_prop
  · unfold rowWeightedScalar weightedScalar
    fun_prop

lemma rowBaseFinite_differentiableAt
    (hv : 1-V t≠0) (j e l : ℕ) :
    DifferentiableAt ℂ (fun s=>rowBaseFinite p hp hg eta a (X s) (W s) (V s) rho j e l) t := by
  have hd (k m : ℕ) := rowMarkedTerm_differentiableAt p hp hg eta a rho X W V t hX hW hV j e l k m
  unfold rowBaseFinite
  fun_prop (disch := assumption)

lemma rowClosedMarked_differentiableAt
    (hv : 1-V t≠0) (hr : 1-evenRatio (Ideal.absNorm (Ideal.span {p})) a (X t) (V t)≠0) (j : ℕ) :
    DifferentiableAt ℂ (fun s=>rowClosedMarked p hp hg eta a (X s) (W s) (V s) rho j) t := by
  have hd (e l : ℕ) := rowBaseFinite_differentiableAt p hp hg eta a rho X W V t hX hW hV hv j e l
  have hR : DifferentiableAt ℂ (fun s=>evenRatio (Ideal.absNorm (Ideal.span {p})) a (X s) (V s)) t := by
    unfold evenRatio
    fun_prop
  unfold rowClosedMarked
  fun_prop (disch := assumption)
end

lemma ramifiedClosed_differentiableAt (eta a rho : ℂ) (X W Z : ℂ→ℂ) (t : ℂ)
    (hX : DifferentiableAt ℂ X t) (hW : DifferentiableAt ℂ W t) (hZ : DifferentiableAt ℂ Z t)
    (hv : 1-coordV (Ideal.absNorm (Ideal.span {p})) (Z t)≠0)
    (hr : 1-coordR (Ideal.absNorm (Ideal.span {p})) (a^2) (X t) (Z t)≠0) (j : ℕ) :
    DifferentiableAt ℂ (fun s=>ramifiedClosed p hp hg eta a rho (X s) (W s) (Z s) j) t := by
  pm_3830
  have hcx : DifferentiableAt ℂ (fun s=>(Ideal.absNorm (Ideal.span {p}):ℂ)^(-X s)) t := by
    exact hX.neg.const_cpow (Or.inl (by exact_mod_cast hQ.ne'))
  have hcw : DifferentiableAt ℂ (fun s=>(Ideal.absNorm (Ideal.span {p}):ℂ)^(-W s)) t := by
    exact hW.neg.const_cpow (Or.inl (by exact_mod_cast hQ.ne'))
  have hcv := (coordV_differentiable _ hQ).differentiableAt.comp t hZ
  change DifferentiableAt ℂ (fun s=>coordV (Ideal.absNorm (Ideal.span {p})) (Z s)) t at hcv
  have hr' := evenRatio_eq_coordR (Ideal.absNorm (Ideal.span {p}):ℝ) hQ a (X t) (Z t)
  simp only [Complex.ofReal_natCast] at hr'
  have hd := rowClosedMarked_differentiableAt p hp hg eta a rho _ _ _ t hcx hcw hcv hv
    (by rw [hr'];exact hr) j
  unfold ramifiedClosed
  fun_prop

end SevenEighths.ProbeEuler
end

end OAI
