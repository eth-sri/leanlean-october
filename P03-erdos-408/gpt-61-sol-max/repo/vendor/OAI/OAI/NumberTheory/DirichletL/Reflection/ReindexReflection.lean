module

public import OAI.NumberTheory.DirichletL.Reflection.Reindex
public import OAI.NumberTheory.DirichletL.Descent.ReflectedDual

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss InverseMoment
noncomputable section


variable {ι κ : Type*} [Fintype ι] [Fintype κ] {p : ι→ActualEisensteinCubic.O} {N a c : ActualEisensteinCubic.O} {mode : Bool}

section
variable (D : ControlledStratumArithmetic p N a c mode) (e : κ≃ι)

lemma reindexControlled_matrix_one     :
    (reindexControlled D e).matrix (fun _ => 1)=D.matrix (fun _ => 1) := by
  change D.matrix (unitFrequencyEquiv p e (fun _ => 1))=_
  rw [unitFrequencyEquiv_one]

lemma reindexControlled_fixedFactor     :
    (reindexControlled D e).fixedFactor=D.fixedFactor := by
  unfold ControlledStratumArithmetic.fixedFactor
  rw [reindexControlled_matrix_one]

lemma reindexControlled_U     :
    (reindexControlled D e).U=D.U := rfl

end

def reindexMarks (e : κ≃ι) (S : Finset ι)  := Finset.univ.filter (fun k => e k∈S)

omit [Fintype ι] in
lemma mem_reindexMarks (e : κ≃ι)  S   k  : k∈reindexMarks e S ↔ e k∈S := by
  simp [reindexMarks]

section
variable [∀ i, (Ideal.span {p i}).IsMaximal] (D : ControlledStratumArithmetic p N a c mode) (e : κ≃ι)

lemma mixedActiveBracket_reindex  
       
     hp  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
     j   S   k  (x : ActualEisensteinCubic.O) :
    mixedActiveBracket (fun k => hp (e k)) (fun k => hg (e k)) (fun k => j (e k))
      (reindexMarks e S) (reindexControlled D e) k x =mixedActiveBracket hp hg j S D (e k) x := by
  simp only [mixedActiveBracket,mem_reindexMarks]
  rfl

theorem mixedReflectedValue_reindex  
       
     s 
     hp   hc  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
     j   S   W   X  :
    mixedReflectedValue (reindexControlled D e) s (fun k => hp (e k)) hc (fun k => hg (e k))
      (fun k => j (e k)) (reindexMarks e S) W X =mixedReflectedValue D s hp hc hg j S W X := by
  have hprod (x : ActualEisensteinCubic.O) :
      (∏ k, mixedActiveBracket (fun k => hp (e k)) (fun k => hg (e k)) (fun k => j (e k))
        (reindexMarks e S) (reindexControlled D e) k x)=∏ i, mixedActiveBracket hp hg j S D i x := by
    simp_rw [mixedActiveBracket_reindex]
    exact e.prod_comp (fun i => mixedActiveBracket hp hg j S D i x)
  simp only [mixedReflectedValue,e.prod_comp p,reindexControlled_fixedFactor,
    reindexControlled_matrix_one,reindexControlled_U,hprod]

end
end
end SevenEighths.InverseReflectedPhase

end OAI
