module
public import OAI.NumberTheory.DirichletL.Detector.HighRowsActual
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

lemma rowMarkedTerm_unramified (eta a X W V rho : ℂ) (e l k m : ℕ) :
    rowMarkedTerm p hp hg eta a X W V rho 0 e l k m=
      principalMarkedTerm p hp hg (eta/rho) (a/rho^3) X (rho*W) V e l k m := by
  unfold rowMarkedTerm principalMarkedTerm
  split_ifs
  · rfl
  · simp only [zero_add,rowWeightedScalar_parameters]

lemma rowMarkedSeries_unramified (eta a X W V rho : ℂ) :
    rowMarkedSeries p hp hg eta a X W V rho 0=
      principalMarkedSeries p hp hg (eta/rho) (a/rho^3) X (rho*W) V := by
  unfold rowMarkedSeries principalMarkedSeries rowInner principalInner
  pm_3827
  exact rowMarkedTerm_unramified p hp hg eta a X W V rho e.val l k m

include hc in
lemma rowClosedMarked_unramified (eta a X W V rho : ℂ) (hρ : rho^6=1)
    (hV : ‖V‖<1) (hR : ‖evenRatio (Ideal.absNorm (Ideal.span {p})) a X V‖<1) :
    rowClosedMarked p hp hg eta a X W V rho 0=
      markedFactor (evenRatio (Ideal.absNorm (Ideal.span {p})) a X V) V
        (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹
        (eta*((Ideal.absNorm (Ideal.span {p}):ℂ)-1)*X*W)
        (-(eta/rho)*X+(rho*W)*evenRatio (Ideal.absNorm (Ideal.span {p})) a X V) 1 := by
  have hn : rho≠0 := by intro h; simp [h] at hρ
  rw [←rowMarkedSeries_eq_closed p hp hg hc eta a X W V rho hρ hV hR 0 (by decide),
    rowMarkedSeries_unramified p hp hg,
    principalMarkedSeries_eq p hp hg hc _ _ _ _ _ hV
      (by simpa only [evenRatio_unit _ _ _ _ _ hρ] using hR),
    evenRatio_unit _ _ _ _ _ hρ]
  congr 1
  field_simp

include hc in

include hc in

theorem sourceRowSeries_unramified_euler (eta a rho x w z : ℂ) (hρ : rho^6=1)
    (hV : ‖coordV (Ideal.absNorm (Ideal.span {p})) z‖<1)
    (hR : ‖coordR (Ideal.absNorm (Ideal.span {p})) (a^2) x z‖<1)
    (hW : ‖coordW (Ideal.absNorm (Ideal.span {p})) rho w‖<1)
    (hD : 1-coordD (Ideal.absNorm (Ideal.span {p})) eta rho x≠0) :
    let Q : ℝ := Ideal.absNorm (Ideal.span {p})
    sourceRowSeries p hp hg eta a rho x w z 0=
      (1-coordD Q eta rho x)/((1-coordV Q z)*(1-coordW Q rho w))*
        unramifiedClosed Q (a^2) eta rho x w z := by
  dsimp only
  pm_3830
  pm_5043 hr evenRatio_eq_coordR a z
  have hr' : ‖evenRatio (Ideal.absNorm (Ideal.span {p})) a
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x)) (coordV (Ideal.absNorm (Ideal.span {p})) z)‖<1 := by
    rw [hr]; exact hR
  rw [sourceRowSeries_eq_closed p hp hg hc eta a rho x w z hρ hV hr' hW 0 (by decide)]
  rw [rowClosedMarked_unramified p hp hg hc _ _ _ _ _ _ hρ hV hr',hr]
  pm_5043 hk coordK_eq_geometric eta w
  rw [←hk]
  have hinv : rho⁻¹=star rho := Complex.inv_eq_conj (Complex.norm_eq_one_of_pow_eq_one hρ (by decide))
  have hv := one_sub_ne_zero_of_norm_lt_one _ hV
  have hw := one_sub_ne_zero_of_norm_lt_one _ hW
  simp only [ite_true,div_eq_mul_inv,hinv]
  unfold unramifiedClosed ProbeLocal.continuedCorrection
  dsimp only
  simp only [coordW,coordD,Complex.ofReal_natCast] at hD hw ⊢
  field_simp [hD,hv,hw]
  ; ring

end SevenEighths.ProbeEuler
end

end OAI
