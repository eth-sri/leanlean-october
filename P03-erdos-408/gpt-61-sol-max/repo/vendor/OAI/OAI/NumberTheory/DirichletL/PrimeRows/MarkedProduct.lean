module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.PrimeRows.MarkedLocal
public import OAI.NumberTheory.DirichletL.PrimeRows.Euler

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEulerFinsupp


def markExclusions (S : Finset (Ideal HeckeFamily.O)) (T : Finset PrimeIdeal)  :=
  S∪T.image Subtype.val

theorem markExclusions_prime  S  (hS : ∀P∈S,Prime P)
     T  : ∀P∈markExclusions S T,Prime P := by
  intro P hP
  rcases Finset.mem_union.mp hP with hP|hP
  · exact hS P hP
  grind

@[simp] theorem mem_markExclusions  S   T   P  :
    P.val∈markExclusions S T ↔ P.val∈S ∨ P∈T := by
  simp only [markExclusions,Finset.mem_union,Finset.mem_image]
  aesop

end SevenEighths.ProbeHighRowFamily

end

end OAI
