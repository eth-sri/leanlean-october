module

public import OAI.NumberTheory.DirichletL.Reflection.OriginalTransport

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical
open CubicEisenstein InverseMoment
noncomputable section
variable {ι κ : Type*} [Fintype ι] [Fintype κ] {p : ι→ActualEisensteinCubic.O} {q : κ→ActualEisensteinCubic.O}
    {N a c : ActualEisensteinCubic.O} {mode : Bool}

omit [Fintype ι] [Fintype κ] in
lemma pullback_generator_eq (e : κ≃ι) (h : (fun k => p (e k))=q) :
    (fun i => q (e.symm i))=p := by
  grind

def pullbackControlled (e : κ≃ι) (h : (fun k => p (e k))=q)
    (D : ControlledStratumArithmetic q N a c mode) :
    ControlledStratumArithmetic p N a c mode :=
  castControlled (pullback_generator_eq e h) (reindexControlled D e.symm)

lemma reindexMarks_symm (e : κ≃ι) (S : Finset ι) :
    reindexMarks e.symm (reindexMarks e S)=S := by
  ext i
  simp only [mem_reindexMarks,Equiv.apply_symm_apply]

theorem mixedReflectedValue_pullback
    [∀ i, (Ideal.span {p i}).IsMaximal] [∀ k, (Ideal.span {q k}).IsMaximal]
    (e : κ≃ι) (h : (fun k => p (e k))=q)
    (D : ControlledStratumArithmetic q N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i≠0) (hq : ∀ k, q k≠0) (hc : c≠0)
    (hgp : ∀ i, ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i}) (hgq : ∀ k, ConcretePrimeRowBridge.goodLambda∉Ideal.span {q k})
    (j : ι→ℕ) (S : Finset ι) (W : ℝ→ℂ) (X : ℝ) :
    mixedReflectedValue (pullbackControlled e h D) s hp hc hgp j S W X=
      mixedReflectedValue D s hq hc hgq (fun k => j (e k)) (reindexMarks e S) W X := by
  unfold pullbackControlled
  rw [mixedReflectedValue_cast _ _ s (by grind) hp hc
    (by grind) hgp]
  have hj : (fun i => j (e (e.symm i)))=j := by funext i; simp only [Equiv.apply_symm_apply]
  have he := mixedReflectedValue_reindex D e.symm s hq hc hgq
    (fun k => j (e k)) (reindexMarks e S) W X
  rw [hj,reindexMarks_symm] at he
  omega
end
end SevenEighths.InverseReflectedPhase

end OAI
