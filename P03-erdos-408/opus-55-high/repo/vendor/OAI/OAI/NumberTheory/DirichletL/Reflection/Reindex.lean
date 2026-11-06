module

public import OAI.NumberTheory.DirichletL.Reflection.MarkedSource

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical
open CubicEisenstein FiniteGaussPhase ShortDraftCRT
noncomputable section
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

lemma cofactor_reindex (p : ι→ActualEisensteinCubic.O) (e : κ≃ι) (k : κ) :
    cofactor (fun k => p (e k)) k=cofactor p (e k) := by
  unfold cofactor
  apply Finset.prod_equiv e
  · simp
  simp

lemma finiteCrossNumerator_reindex (a c l : ActualEisensteinCubic.O) (p : ι→ActualEisensteinCubic.O) (e : κ≃ι) (h : ι→ActualEisensteinCubic.O) :
    finiteCrossNumerator a c l (fun k => p (e k)) (fun k => h (e k))=
      finiteCrossNumerator a c l p h := by
  unfold finiteCrossNumerator
  simp_rw [cofactor_reindex]
  rw [e.prod_comp,e.sum_comp (fun i => h i*cofactor p i)]

def unitFrequencyEquiv (p : ι→ActualEisensteinCubic.O) (e : κ≃ι) :
    (∀ k, (ActualEisensteinCubic.O⧸Ideal.span {p (e k)})ˣ)≃(∀ i, (ActualEisensteinCubic.O⧸Ideal.span {p i})ˣ) :=
  Equiv.piCongrLeft (fun i => (ActualEisensteinCubic.O⧸Ideal.span {p i})ˣ) e

omit [Fintype ι] [Fintype κ] in
lemma unitFrequencyEquiv_apply (p : ι→ActualEisensteinCubic.O) (e : κ≃ι)
    (v : ∀ k, (ActualEisensteinCubic.O⧸Ideal.span {p (e k)})ˣ) (k : κ) :
    unitFrequencyEquiv p e v (e k)=v k := Equiv.piCongrLeft_apply_apply _ _ _ _

omit [Fintype ι] [Fintype κ] in
lemma unitFrequencyEquiv_one (p : ι→ActualEisensteinCubic.O) (e : κ≃ι) :
    unitFrequencyEquiv p e (fun _ => 1)=(fun _ => 1) := by
  funext i
  obtain ⟨k,rfl⟩ := e.surjective i
  exact unitFrequencyEquiv_apply p e _ k

def reindexControlled {p : ι→ActualEisensteinCubic.O} {N a c : ActualEisensteinCubic.O} {mode : Bool}
    (D : ControlledStratumArithmetic p N a c mode) (e : κ≃ι) :
    ControlledStratumArithmetic (fun k => p (e k)) N a c mode where
  lift v k := D.lift (unitFrequencyEquiv p e v) (e k)
  lift_period v k := D.lift_period _ _
  lift_residue v k := (D.lift_residue _ _).trans (congrArg Units.val (unitFrequencyEquiv_apply p e v k))
  U := D.U
  w := D.w
  bezout := by simpa only [e.prod_comp] using D.bezout
  sigma k := D.sigma (e k)
  epsilon k := D.epsilon (e k)
  sigma_value k := by simpa only [cofactor_reindex] using D.sigma_value (e k)
  epsilon_value k := by simpa only [cofactor_reindex] using D.epsilon_value (e k)
  matrix v := D.matrix (unitFrequencyEquiv p e v)
  numerator v := by
    rw [D.numerator,finiteCrossNumerator_reindex]
  denominator v := by simpa only [e.prod_comp] using D.denominator (unitFrequencyEquiv p e v)
  matrix_fixed v i j := by
    simpa only [unitFrequencyEquiv_one] using D.matrix_fixed (unitFrequencyEquiv p e v) i j
  conditions v := D.conditions (unitFrequencyEquiv p e v)
end
end SevenEighths.InverseReflectedPhase

end OAI
