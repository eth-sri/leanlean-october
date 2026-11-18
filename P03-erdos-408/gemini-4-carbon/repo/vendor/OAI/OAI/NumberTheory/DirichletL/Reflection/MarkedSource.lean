module

public import OAI.NumberTheory.DirichletL.Reflection.MarkedJoined

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

namespace PrimeFamily
variable {ι : Type*} (P : PrimeFamily ι)
lemma generator_prime (i : ι) : Prime (P.generator i) :=
  (Ideal.span_singleton_prime (P.generator_ne_zero i)).mp inferInstance

def restrict (A : Finset ι) : PrimeFamily A where
  ideal i := P.ideal i.val
  maximal i := P.maximal i.val
  good i := P.good i.val

lemma restrict_pairwise (hP : Pairwise (Function.onFun IsCoprime P.ideal)) (A : Finset ι) :
    Pairwise (Function.onFun IsCoprime (P.restrict A).ideal) := by
  intro i k hik
  exact hP (fun h => hik (Subtype.ext h))

def activeControlled [Fintype ι]
    (hP : Pairwise (Function.onFun IsCoprime P.ideal))
    (c : Eis) (G : ∀ h : Eis⧸Ideal.span {c}, FixedFourierGeometry c h)
    (N : Eis) (hN : ∀ h, (9:Eis)*(G h).c0∣N)
    (hNp : ∀ i, IsCoprime (Ideal.span {N}) (P.ideal i))
    (h : Eis⧸Ideal.span {c}) (A : Finset ι) :
    ControlledStratumArithmetic (fun i : A => P.generator i.val) N (G h).a0 (G h).c0 (G h).mode :=
  Classical.choice ((P.restrict A).exists_controlled N (G h).a0 (G h).c0 (G h).mode
    (G h).denominator_ne_zero (hN h) (G h).primary (G h).coprime
    (P.restrict_pairwise hP A) (fun i => hNp i.val))

end PrimeFamily
end
end SevenEighths.InverseReflectedPhase

end OAI
