module
public import OAI.NumberTheory.DirichletL.Reflection.MarkedSource
public import OAI.NumberTheory.DirichletL.Descent.ReflectedDual

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

variable {ι : Type*} [Fintype ι]
def activeMarks (A S : Finset ι) : Finset A := Finset.univ.filter (fun i => i.val∈S)

omit [Fintype ι] in
lemma mem_activeMarks (A S : Finset ι) (i : A) : i∈activeMarks A S ↔ i.val∈S := by
  simp [activeMarks]

omit [Fintype ι] in
lemma mixedPrimeFunction_restrict (P : PrimeFamily ι) (j : ι→ℕ) (A S : Finset ι)
    (i : A) (x : Eis⧸Ideal.span {P.generator i.val}) :
    mixedPrimeFunction (P.restrict A).generator (P.restrict A).generator_good
      (fun i => j i.val) (activeMarks A S) i x =
    mixedPrimeFunction P.generator P.generator_good j S i.val x := by
  simp only [mixedPrimeFunction,mem_activeMarks]
  rfl

omit [Fintype ι] in
lemma localActiveWeight_restrict (P : PrimeFamily ι) (j : ι→ℕ) (A S : Finset ι)
    (v : ∀ i : A, (Eis⧸Ideal.span {P.generator i.val})ˣ) :
    localActiveWeight P.generator P.generator_ne_zero
      (mixedPrimeFunction P.generator P.generator_good j S) A v =
    fullLocalFourierWeight (P.restrict A).generator_ne_zero
      (mixedPrimeFunction (P.restrict A).generator (P.restrict A).generator_good
        (fun i => j i.val) (activeMarks A S)) v := by
  unfold localActiveWeight fullLocalFourierWeight
  apply Finset.prod_congr rfl
  intro i hi
  congr 1
  funext x
  exact (mixedPrimeFunction_restrict P j A S i x).symm

end
end SevenEighths.InverseReflectedPhase

end OAI
