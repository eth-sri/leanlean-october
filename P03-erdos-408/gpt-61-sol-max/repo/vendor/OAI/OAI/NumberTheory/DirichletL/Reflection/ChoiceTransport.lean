module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Reflection.FixedTuples
public import OAI.NumberTheory.DirichletL.Reflection.OriginalTransport

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section

variable {σ φ τ : Type*} [Fintype σ] [DecidableEq σ] [Fintype τ]

def fixedTupleCoefficient (L : σ→Finset (Ideal ActualEisensteinCubic.O)) (w : ∀ i,L i→ℂ) (p : σ→Ideal ActualEisensteinCubic.O)  :=
  if hp:∀ i,p i∈L i then ∏ i,w i ⟨p i,hp i⟩ else 0

omit [DecidableEq σ] in
lemma fixedTupleCoefficient_at (L : σ→Finset (Ideal ActualEisensteinCubic.O)) (w : ∀ i,L i→ℂ) (p : ∀ i,L i) :
    fixedTupleCoefficient L w (fun i => (p i).val)=∏ i,w i (p i) := by
  simp_all [fixedTupleCoefficient]

omit [DecidableEq σ] in
lemma fixedTupleCoefficient_norm (L : σ→Finset (Ideal ActualEisensteinCubic.O)) (w : ∀ i,L i→ℂ)
    (hw : ∀ i P,‖w i P‖≤1)  p  : ‖fixedTupleCoefficient L w p‖≤1 := by
  unfold fixedTupleCoefficient
  split
  · exact slot_coefficient_norm L w hw _
  · simp

variable {N a c : ActualEisensteinCubic.O} {mode : Bool}
variable (G : PrimeFamily τ) (K : Ideal ActualEisensteinCubic.O) (hK : Admissible K)
    (L : σ→Finset (Ideal ActualEisensteinCubic.O)) (F : φ→Ideal ActualEisensteinCubic.O)
    (hne : (fixedSlotTupleSet L F).Nonempty)
    (hmax : ∀ i,∀ P∈L i,P.IsMaximal)
    (hgood : ∀ i,∀ P∈L i,ConcretePrimeRowBridge.goodLambda∉P)
    (hL : Pairwise (fun i j => Disjoint (L i) (L j))) (hprime : ∀ i,∀ P∈L i,Prime P)
    (p : supportedSlotChoices L F K)

end
end SevenEighths.InverseReflectedPhase

end OAI
