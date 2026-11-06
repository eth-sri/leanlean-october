module

public import OAI.NumberTheory.DirichletL.Reflection.ThreeBlocks

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss LocalReflectionBrackets
noncomputable section


variable {ι : Type*} [Fintype ι] {p : ι → ActualEisensteinCubic.O} {N a c : ActualEisensteinCubic.O} {mode : Bool}


def ramifiedBlock [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i}) (j : ι → ℕ) (S : Finset ι) (u : ActualEisensteinCubic.Oˣ) (m : ℕ) : ℂ :=
  ∏ i ∈ S, unitArgumentFactor (actualSextic (Ideal.span {p i}) (hg i)) (j i)
    (Ideal.Quotient.mk _ (u.val*ConcretePrimeRowBridge.goodLambda^m))

section
variable [∀ i, (Ideal.span {p i}).IsMaximal]

theorem ramifiedPhase_three_blocks  
    (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i}) (R P F : Finset ι)
    (hRP : Disjoint R P) (hF : Disjoint (R ∪ P) F) (hu : (R ∪ P) ∪ F = Finset.univ)
    (j : ι → ℕ) (hRj : ∀ i ∈ R, j i = 1) (hPj : ∀ i ∈ P, j i = 0)
     u   m  :
    ramifiedBranchPhase (fun i => Ideal.span {p i}) hg j u m =
      ramifiedBlock hg (fun _ => 1) R u m * ramifiedBlock hg (fun _ => 0) P u m *
      ramifiedBlock hg j F u m := by
  have hh : ramifiedBranchPhase (fun i => Ideal.span {p i}) hg j u m =
      ramifiedBlock hg j R u m * ramifiedBlock hg j P u m * ramifiedBlock hg j F u m := by
    unfold ramifiedBranchPhase ramifiedBlock
    rw [← Finset.prod_union hRP,← Finset.prod_union hF,hu]
    rfl
  rw [hh]
  congr 2
  · apply Finset.prod_congr rfl
    intro i hi
    rw [hRj i hi]
  · apply Finset.prod_congr rfl
    intro i hi
    rw [hPj i hi]

theorem modelRowPhase_three_blocks  
    (D : ControlledStratumArithmetic p N a c mode)
     s 
     hp  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hprimary : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)  R P F 
    (hRP : Disjoint R P) (hF : Disjoint (R ∪ P) F) (hu : (R ∪ P) ∪ F = Finset.univ)
     j  (hRj : ∀ i ∈ R, j i = 1) (hPj : ∀ i ∈ P, j i = 0)
     u   m  :
    D.modelRowPhase s hp hg j u m =
      (residualWithFrozen hp hg c R F * ramifiedBlock hg (fun _ => 1) R
        (sourcePhaseUnit s.index s.phaseUpperUnit u) (sourcePhaseExponent s.index m)) *
      (markedWithFrozen hp hg c P F * ramifiedBlock hg (fun _ => 0) P
        (sourcePhaseUnit s.index s.phaseUpperUnit u) (sourcePhaseExponent s.index m)) *
      (star D.fixedFactor * frozenPhase D hp hg j F * ramifiedBlock hg j F
        (sourcePhaseUnit s.index s.phaseUpperUnit u) (sourcePhaseExponent s.index m)) := by
  dsimp only [ControlledStratumArithmetic.modelRowPhase]
  rw [activePhase_three_blocks D hp hg hcop hprimary R P F hRP hF hu j hRj hPj,
    ramifiedPhase_three_blocks hg R P F hRP hF hu j hRj hPj]
  ring

end

end
end SevenEighths.InverseReflectedPhase

end OAI
