module

public import OAI.NumberTheory.DirichletL.Detector.HighRowsClosed

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CompletedGauss ConcretePrimeRowBridge ProbePrimePower
open CubicEisenstein

theorem actualSextic_unit_six (p b : ActualEisensteinCubic.O) [(Ideal.span {p}:Ideal ActualEisensteinCubic.O).IsMaximal]
    (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (ActualEisensteinCubic.O ⧸ Ideal.span {p})≠2)
    (hb : IsCoprime b p) :
    (actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ b))^6=1 := by
  have h := congrArg (fun χ : MulChar (ActualEisensteinCubic.O ⧸ Ideal.span {p}) ℂ =>
    χ (Ideal.Quotient.mk _ b)) (actualSextic_six _ hg hc)
  simpa only [MulChar.pow_apply' _ (by decide : (6:ℕ)≠0),
    MulChar.one_apply ((isUnit_quotient_span_iff p b).mpr hb.symm)] using h

end SevenEighths.ProbePhysical
end

end OAI
