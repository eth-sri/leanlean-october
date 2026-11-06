module

public import OAI.NumberTheory.DirichletL.Detector.HighRowsClosed

@[expose] public section

namespace OAI

noncomputable section

namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower ProbeEuler CanonicalQuadraticSieve CanonicalRowCompletion ProbeRow CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

theorem actualSextic_unit_six (p b : O) [(Ideal.span {p}:Ideal O).IsMaximal]
    (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)
    (hb : IsCoprime b p) :
    (actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ b))^6=1 := by
  have h := congrArg (fun χ : MulChar (O ⧸ Ideal.span {p}) ℂ =>
    χ (Ideal.Quotient.mk _ b)) (actualSextic_six _ hg hc)
  simpa only [MulChar.pow_apply' _ (by decide : (6:ℕ)≠0),
    MulChar.one_apply ((isUnit_quotient_span_iff p b).mpr hb.symm)] using h

end SevenEighths.ProbePhysical
end

end OAI
