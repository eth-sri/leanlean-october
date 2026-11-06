module

public import OAI.NumberTheory.DirichletL.Detector.GramMean

@[expose] public section

namespace OAI

noncomputable section
namespace SevenEighths.ProbeGramCommon
open CompletedGauss ConcretePrimeRowBridge
open CenteredMomentCorrelation

theorem joint_mean_of_local_factor (Q P : Ideal ActualEisensteinCubic.O) [P.IsMaximal]
    (hg : goodLambda∉P) (hchar : ringChar (ActualEisensteinCubic.O⧸P)≠2)
    (c e : ℕ) (hc : 1≤c) (he : ¬6∣e) (hcop : IsCoprime Q (P^c))
    [Fintype (ActualEisensteinCubic.O⧸Q)] [Fintype (ActualEisensteinCubic.O⧸P^c)] [Fintype (ActualEisensteinCubic.O⧸Q*P^c)]
    (F : ActualEisensteinCubic.O→ActualEisensteinCubic.O→ℂ) (hF : ∀x z y,x-z∈Q → F x y=F z y) (d : ActualEisensteinCubic.O) :
    (∑x : ActualEisensteinCubic.O⧸Q*P^c,∑y : ActualEisensteinCubic.O⧸Q*P^c,
      (actualSextic P hg^e) (Ideal.Quotient.mk P (d*x.out))*F x.out y.out)=0 := by
  let E := Ideal.quotientMulEquivQuotientProd Q (P^c) hcop
  have hE (x : ActualEisensteinCubic.O⧸Q*P^c) : E x=(Ideal.Quotient.mk Q x.out,Ideal.Quotient.mk (P^c) x.out) := by
    conv_lhs => rw [←Ideal.Quotient.mk_out x]
    rfl
  have hf (x : ActualEisensteinCubic.O⧸Q*P^c) (y : ActualEisensteinCubic.O) : F x.out y=F (E x).1.out y := by
    apply hF
    apply Ideal.Quotient.eq.mp
    rw [Ideal.Quotient.mk_out,hE]
  have hp (x : ActualEisensteinCubic.O⧸Q*P^c) : Ideal.Quotient.mk P (d*x.out)=
      Ideal.Quotient.mk P d*primePowerReduction P hc (E x).2 := by
    rw [map_mul,hE]
    rfl
  have hz := crt_joint_mean_zero Q P hg hchar c e hc he hcop
    (fun x y=>F x.out y.out) d
  convert hz using 1
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  rw [hp,hf]

end SevenEighths.ProbeGramCommon
end

end OAI
