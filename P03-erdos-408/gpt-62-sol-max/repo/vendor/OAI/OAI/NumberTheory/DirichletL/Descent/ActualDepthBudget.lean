module

public import OAI.NumberTheory.DirichletL.Descent.ActualChildStateDepth
public import OAI.NumberTheory.DirichletL.Descent.ActualChildStateTriples

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMoment

def actualDepth (Mmax cutoff : ℝ) : ℕ := ⌈2*Mmax/(3*cutoff)⌉₊+1

lemma actualDepth_pos (Mmax cutoff : ℝ) : 0<actualDepth Mmax cutoff := by
  exact Nat.succ_pos _

end SevenEighths.InverseMoment
end

end OAI
