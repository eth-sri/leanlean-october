module
public import OAI.NumberTheory.DirichletL.Detector.HighRowsTail
public import OAI.NumberTheory.DirichletL.Detector.HighRowsZero
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)

def rowBaseFinite (eta a X W V rho : ℂ) (j e l : ℕ) : ℂ :=
  ∑ k : Fin 2,
    (rowMarkedTerm p hp hg eta a X W V rho j e l k.val 0+
     rowMarkedTerm p hp hg eta a X W V rho j e l k.val 1+
     rowMarkedTerm p hp hg eta a X W V rho j e l k.val 2/(1-V))

def rowClosedMarked (eta a X W V rho : ℂ) (j : ℕ) : ℂ :=
  (rowBaseFinite p hp hg eta a X W V rho j 0 2+
   rowBaseFinite p hp hg eta a X W V rho j 1 0+
   rowBaseFinite p hp hg eta a X W V rho j 0 1+
   rowBaseFinite p hp hg eta a X W V rho j 1 1)/
    (1-evenRatio (Ideal.absNorm (Ideal.span {p})) a X V)

include hc in
theorem rowMarkedSeries_eq_closed (eta a X W V rho : ℂ) (hρ : rho^6=1)
    (hV : ‖V‖<1) (hR : ‖evenRatio (Ideal.absNorm (Ideal.span {p})) a X V‖<1)
    (j : ℕ) (hj : j<6) :
    rowMarkedSeries p hp hg eta a X W V rho j=rowClosedMarked p hp hg eta a X W V rho j := by
  rw [rowMarkedSeries_four_families p hp hg hc eta a X W V rho hρ hV hR j hj]
  unfold rowClosedMarked rowBaseFinite
  rw [rowInner_base_rational p hp hg hc eta a X W V rho hV j 0 2 (by omega) (by omega),
    rowInner_base_rational p hp hg hc eta a X W V rho hV j 1 0 (by omega) (by omega),
    rowInner_base_rational p hp hg hc eta a X W V rho hV j 0 1 (by omega) (by omega),
    rowInner_base_rational p hp hg hc eta a X W V rho hV j 1 1 (by omega) (by omega)]

include hc in
lemma rowInner_zero_squarefree_summable (eta a X W V rho : ℂ) (hρ : rho^6=1)
    (hV : ‖V‖<1) (hR : ‖evenRatio (Ideal.absNorm (Ideal.span {p})) a X V‖<1)
    (j : ℕ) (hj : j<6) : Summable (fun l=>rowInner p hp hg eta a X W V rho j 0 l) := by
  pm_1166
  pm_1167
  pm_3867 hs he hs.sum_range_add
  have ho : HasSum (fun r=>rowInner p hp hg eta a X W V rho j 0 (2*r+1))
      (rowInner p hp hg eta a X W V rho j 0 1/(1-evenRatio (Ideal.absNorm (Ideal.span {p})) a X V)) := by
    grind
  exact (he.even_add_odd ho).summable

def sourceRowSeries (eta a rho x w z : ℂ) (j : ℕ) : ℂ :=
  ∑ e : Fin 2,∑' l,∑' k,∑' m,sourceRowTerm p hp hg eta a rho x w z j e.val l k m

include hc in

theorem sourceRowSeries_eq_closed (eta a rho x w z : ℂ) (hρ : rho^6=1)
    (hV : ‖coordV (Ideal.absNorm (Ideal.span {p})) z‖<1)
    (hR : ‖evenRatio (Ideal.absNorm (Ideal.span {p})) a
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x)) (coordV (Ideal.absNorm (Ideal.span {p})) z)‖<1)
    (hW : ‖rho*((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w))‖<1) (j : ℕ) (hj : j<6) :
    sourceRowSeries p hp hg eta a rho x w z j=
      1/(1-coordV (Ideal.absNorm (Ideal.span {p})) z)+
      (if j=0 then (rho*((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)))/
        (1-rho*((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w))) else 0)+
      rowClosedMarked p hp hg eta a ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
        ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) (coordV (Ideal.absNorm (Ideal.span {p})) z) rho j := by
  pm_3848
  let Z0 := 1/(1-V)+(if j=0 then rho*W/(1-rho*W) else 0)
  have he0 (l : ℕ) : (∑' k,∑' m,sourceRowTerm p hp hg eta a rho x w z j 0 l k m)=
      rowInner p hp hg eta a X W V rho j 0 l+(if l=0 then Z0 else 0) := by
    by_cases hl : l=0
    · subst l
      simp only [sourceRowTerm_zero,rowInner_zero,ite_true,zero_add]
      exact rowZeroIndexSeries_eq p hp (actualSextic (Ideal.span {p}) hg) (rho*W) V j hW hV
    · rw [ite_eq_right hl,add_zero]
      apply tsum_congr
      intro k
      apply tsum_congr
      intro m
      exact sourceRowTerm_pos p hp hg eta a rho x w z j 0 l k m (by omega)
  have he1 (l : ℕ) : (∑' k,∑' m,sourceRowTerm p hp hg eta a rho x w z j 1 l k m)=
      rowInner p hp hg eta a X W V rho j 1 l := by
    apply tsum_congr
    intro k
    apply tsum_congr
    intro m
    exact sourceRowTerm_pos p hp hg eta a rho x w z j 1 l k m (by omega)
  have hs := rowInner_zero_squarefree_summable p hp hg hc eta a X W V rho hρ hV hR j hj
  have hc' := rowMarkedSeries_eq_closed p hp hg hc eta a X W V rho hρ hV hR j hj
  unfold rowMarkedSeries at hc'
  simp only [Fin.sum_univ_two,Fin.val_zero,Fin.val_one] at hc'
  unfold sourceRowSeries
  pm_94 Fin.sum_univ_two Fin.val_zero Fin.val_one he0 he1
  rw [hs.tsum_add (hasSum_ite_eq 0 Z0).summable,tsum_ite_eq]
  change _=Z0+rowClosedMarked p hp hg eta a X W V rho j
  rw [←hc']
  ring

end SevenEighths.ProbeEuler
end

end OAI
