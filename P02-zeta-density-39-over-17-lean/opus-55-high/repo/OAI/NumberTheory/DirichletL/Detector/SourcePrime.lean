module
public import OAI.NumberTheory.DirichletL.Detector.SourceCoefficient
public import OAI.NumberTheory.DirichletL.Detector.PhysicalLocalEuler
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic ActualEisensteinCoordinates CompletedGauss CanonicalRowCompletion
open CanonicalQuadraticSieve ConcretePrimeRowBridge CubicEisenstein ConcreteTraceCRT
open ProbePhase ProbeEuler ProbePrimePower FiniteGaussPhase QuadraticGaussRay
local notation "O" => ActualEisensteinCubic.O

section
variable (p : O)
include p
theorem gaussTwo_prime_localGamma (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (hprimary : goodLambda^2∣p-1) (hI : primaryGenerator (Ideal.span {p})≠0) :
    gaussTwo (Ideal.span {p}) hI=localGamma p hp.ne_zero hg 2 := by
  let pp : Unit→ O := fun _=>p
  pm_8011 hp.ne_zero
  have hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {pp i})) := by
    intro i j hij
    grind
  have hi : primaryGenerator (Ideal.span {∏i,pp i})≠0 := by aesop
  have he := gaussTwo_eq_canonicalProductGauss pp hpp hcop (fun _=>hg) (fun _=>hprimary) hi
  rw [canonicalProductGauss_cross_factors pp hpp hcop (fun _ => hg) (fun _ => 2)] at he
  aesop

theorem G_prime_localG (hp : p≠0)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p})≠2) (hprimary : goodLambda^2∣p-1) :
    G p=MixedGaussConversion.localG p hp hg := by
  let pp : Unit→ O := fun _=>p
  pm_8011 hp
  have hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {pp i})) := by
    intro i j hij
    exact (hij (Subsingleton.elim i j)).elim
  have he := canonicalProductG_eq_fixedGValue pp hpp hcop (fun _=>hg)
    (fun _=>hchar) (fun _=>hprimary)
  unfold canonicalProductG at he
  pm_5683
  simpa [pp,G,fixedGQuotientValue,MixedGaussConversion.localG,breveLocalG,breveGamma3,
    ConcreteBreveE.normalizedTraceGauss] using he.symm

theorem localGamma_one_two_full_signal (hp : p≠0)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p})≠2) (hprimary : goodLambda^2∣p-1) :
    localGamma p hp hg 1 * localGamma p hp hg 2 =
      -FiniteGaussPhase.angularFactor p * G p := by
  rw [G_prime_localG p hp hg hchar hprimary]
  exact localGamma_one_two_signal p hp hg hchar hprimary

lemma angularFactor_pow (n : ℕ) : angularFactor (p^n)=angularFactor p^n := by
  pm_94 angularFactor map_pow norm_pow Complex.ofReal_pow div_pow
end

lemma gaussTwo_one : gaussTwo (1:Ideal O) (by rw [primaryGenerator_one]; exact one_ne_zero)=1 := by
  have hI : CubicSieve.Admissible (1:Ideal O) := ⟨squarefree_one,by rw [primaryGenerator_one]; exact one_ne_zero⟩
  rw [gaussTwo_eq_elementFourier (1:Ideal O) hI]
  pm_94 primaryGenerator_one map_one norm_one Complex.ofReal_one div_one
  have hrow (a : O) : CubicSieve.cubicRow (1:Ideal O) a=1 := by
    rw [CubicSieve.cubicRow,←idealRowHom_square,map_one,one_pow]
  rw [show CubicSieve.cubicRow (1:Ideal O)=(fun _=>1) from funext hrow]
  have he : elementFourier 1 one_ne_zero (fun _=>1) 1=sexticGauss 1 one_ne_zero 1 := by
    unfold elementFourier sexticGauss
    apply tsum_congr
    intro x
    simp only [Ideal.span_singleton_one,←Ideal.one_eq_top,map_one,one_mul]
  rw [he,sexticGauss_one]

lemma gaussTwo_prime_power_small (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (hprimary : goodLambda^2∣p-1) (e : ℕ) (he : e≤1)
    (hI : primaryGenerator (Ideal.span {p^e})≠0) :
    gaussTwo (Ideal.span {p^e}) hI=localGamma p hp.ne_zero hg 2^e := by
  pm_6074
  · simpa only [pow_zero,Ideal.span_singleton_one,←Ideal.one_eq_top] using gaussTwo_one
  · have hi : primaryGenerator (Ideal.span {p})≠0 := by simpa only [pow_one] using hI
    simpa only [pow_one] using gaussTwo_prime_localGamma p hp hg hprimary hi

lemma corrected_prime_cubic_signal (p : O) (hp : p≠0)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p})≠2) (hprimary : goodLambda^2∣p-1)
    (hs : Supported (Ideal.span {p})) :
    localGamma p hp hg 2 * star (angularFactor p) * star (G p) = -(localGamma p hp hg 1)⁻¹ := by
  have hsig := localGamma_one_two_full_signal p hp hg hchar hprimary
  pm_7430 hchar
  have hne : localGamma p hp hg 1≠0 := by intro h; rw [h,norm_zero] at hn; norm_num at hn
  have hG : G p*star (G p)=1 := by
    rw [mul_comm]
    exact G_conjugate_cancel p (supported_residue_odd p hs)
      (cubicTwo_isUnit_of_odd p (supported_residue_odd p hs))
  apply mul_left_cancel₀ hne
  calc
    _ = (localGamma p hp hg 1*localGamma p hp hg 2)*star (angularFactor p)*star (G p) := by ring
    _ = -1 := by
      rw [hsig]
      calc
        _ = -(angularFactor p*star (angularFactor p))*(G p*star (G p)) := by ring
        _ = _ := by rw [angularFactor_mul_star p hp,hG]; ring
    _ = _ := by rw [mul_neg,mul_inv_cancel₀ hne]

end SevenEighths.ProbePhysical
end

end OAI
