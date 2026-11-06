module

public import OAI.NumberTheory.DirichletL.Detector.GramGlobalExtension

@[expose] public section

namespace OAI

noncomputable section
namespace SevenEighths.ProbeGramCommon
open CompletedGauss ConcretePrimeRowBridge
open CenteredMomentCorrelation CenteredMomentCanonical

lemma actualSextic_power_nonprincipal (P : Ideal ActualEisensteinCubic.O) [P.IsMaximal]
    (hg : goodLambda∉P) (hchar : ringChar (ActualEisensteinCubic.O⧸P)≠2) (e : ℕ) (he : ¬6∣e) :
    actualSextic P hg^e≠1 := by
  intro h
  have hd := (orderOf_dvd_iff_pow_eq_one).mpr h
  rw [actualSextic_order_six P hg hchar] at hd
  omega

theorem primePower_mean_zero (P : Ideal ActualEisensteinCubic.O) [P.IsMaximal]
    (hg : goodLambda∉P) (hchar : ringChar (ActualEisensteinCubic.O⧸P)≠2)
    (c e : ℕ) (hc : 1≤c) (he : ¬6∣e) [Fintype (ActualEisensteinCubic.O⧸P^c)] (d : ActualEisensteinCubic.O) :
    (∑x : ActualEisensteinCubic.O⧸P^c,(actualSextic P hg^e)
      (Ideal.Quotient.mk P d*primePowerReduction P hc x))=0 := by
  let : Fintype (ActualEisensteinCubic.O⧸P) := Fintype.ofFinite _
  simp_rw [map_mul]
  rw [←Finset.mul_sum,sum_reduction _ (primePowerReduction_surjective P hc),
    MulChar.sum_eq_zero_of_ne_one (actualSextic_power_nonprincipal P hg hchar e he),mul_zero,mul_zero]

theorem crt_joint_mean_zero (Q P : Ideal ActualEisensteinCubic.O) [P.IsMaximal]
    (hg : goodLambda∉P) (hchar : ringChar (ActualEisensteinCubic.O⧸P)≠2)
    (c e : ℕ) (hc : 1≤c) (he : ¬6∣e) (hcop : IsCoprime Q (P^c))
    [Fintype (ActualEisensteinCubic.O⧸Q)] [Fintype (ActualEisensteinCubic.O⧸P^c)] [Fintype (ActualEisensteinCubic.O⧸Q*P^c)]
    (F : (ActualEisensteinCubic.O⧸Q)→(ActualEisensteinCubic.O⧸Q*P^c)→ℂ) (d : ActualEisensteinCubic.O) :
    (∑x : ActualEisensteinCubic.O⧸Q*P^c,∑y : ActualEisensteinCubic.O⧸Q*P^c,
      (actualSextic P hg^e) (Ideal.Quotient.mk P d*
        primePowerReduction P hc ((Ideal.quotientMulEquivQuotientProd Q (P^c) hcop x).2))*
      F ((Ideal.quotientMulEquivQuotientProd Q (P^c) hcop x).1) y)=0 := by
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro y hy
  let E := Ideal.quotientMulEquivQuotientProd Q (P^c) hcop
  have heq := E.toEquiv.sum_comp (fun p : (ActualEisensteinCubic.O⧸Q)×(ActualEisensteinCubic.O⧸P^c)=>
    (actualSextic P hg^e) (Ideal.Quotient.mk P d*primePowerReduction P hc p.2)*F p.1 y)
  change (∑x : ActualEisensteinCubic.O⧸Q*P^c,(actualSextic P hg^e)
    (Ideal.Quotient.mk P d*primePowerReduction P hc (E x).2)*F (E x).1 y)=0
  calc
    _ = ∑p : (ActualEisensteinCubic.O⧸Q)×(ActualEisensteinCubic.O⧸P^c),(actualSextic P hg^e)
        (Ideal.Quotient.mk P d*primePowerReduction P hc p.2)*F p.1 y := heq
    _ = 0 := by
      rw [Fintype.sum_prod_type]
      simp_rw [←Finset.sum_mul,primePower_mean_zero P hg hchar c e hc he d,zero_mul]
      simp

end SevenEighths.ProbeGramCommon
end

end OAI
