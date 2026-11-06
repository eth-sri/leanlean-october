module

public import OAI.NumberTheory.DirichletL.PrimeRows.MarkedLocal
public import OAI.NumberTheory.DirichletL.PrimeRows.Euler

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeHighRowFamily
open ProbePhysical

def markExclusions (S : Finset (Ideal HeckeFamily.O)) (T : Finset PrimeIdeal) : Finset (Ideal HeckeFamily.O) :=
  S∪T.image Subtype.val

theorem markExclusions_prime (S : Finset (Ideal HeckeFamily.O)) (hS : ∀P∈S,Prime P)
    (T : Finset PrimeIdeal) : ∀P∈markExclusions S T,Prime P := by
  intro P hP
  rcases Finset.mem_union.mp hP with hP|hP
  · simp_all
  grind

@[simp] theorem mem_markExclusions (S : Finset (Ideal HeckeFamily.O)) (T : Finset PrimeIdeal) (P : PrimeIdeal) :
    P.val∈markExclusions S T ↔ P.val∈S ∨ P∈T := by
  simp only [markExclusions,Finset.mem_union,Finset.mem_image]
  grind

end SevenEighths.ProbeHighRowFamily

end

end OAI
