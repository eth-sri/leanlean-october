module

public import OAI.NumberTheory.DirichletL.Reflection.Canonical
public import OAI.NumberTheory.DirichletL.Descent.SlotProducts

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical
open InverseMoment
noncomputable section
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

def tupleRepresentative (tuples : Finset (σ→Ideal ActualEisensteinCubic.O)) (hne : tuples.Nonempty)
    (P : Ideal ActualEisensteinCubic.O) : σ→Ideal ActualEisensteinCubic.O :=
  if h : ∃ p∈tuples, slotTupleProduct p=P then h.choose else hne.choose

omit [DecidableEq σ] in
lemma tupleRepresentative_mem (tuples : Finset (σ→Ideal ActualEisensteinCubic.O)) (hne : tuples.Nonempty)
    (P : Ideal ActualEisensteinCubic.O) : tupleRepresentative tuples hne P∈tuples := by
  unfold tupleRepresentative
  split
  next h => grind
  grind

omit [DecidableEq σ] in
lemma tupleRepresentative_product (tuples : Finset (σ→Ideal ActualEisensteinCubic.O)) (hne : tuples.Nonempty)
    (P : Ideal ActualEisensteinCubic.O) (hP : P∈tuples.image slotTupleProduct) :
    slotTupleProduct (tupleRepresentative tuples hne P)=P := by
  have h := Finset.mem_image.mp hP
  simp only [tupleRepresentative,dite_eq_left h]
  grind

omit [DecidableEq σ] in
lemma tupleRepresentative_at_product (tuples : Finset (σ→Ideal ActualEisensteinCubic.O)) (hne : tuples.Nonempty)
    (hinj : Set.InjOn slotTupleProduct (↑tuples : Set (σ→Ideal ActualEisensteinCubic.O)))
    (p : σ→Ideal ActualEisensteinCubic.O) (hp : p∈tuples) :
    tupleRepresentative tuples hne (slotTupleProduct p)=p :=
  hinj (tupleRepresentative_mem tuples hne _) hp
    (tupleRepresentative_product tuples hne _ (by grind))

def tuplePrimeFamily (tuples : Finset (σ→Ideal ActualEisensteinCubic.O)) (hne : tuples.Nonempty)
    (hmax : ∀ p∈tuples, ∀ i, (p i).IsMaximal)
    (hgood : ∀ p∈tuples, ∀ i, ConcretePrimeRowBridge.goodLambda∉p i) (P : Ideal ActualEisensteinCubic.O) : PrimeFamily σ where
  ideal := tupleRepresentative tuples hne P
  maximal := hmax _ (tupleRepresentative_mem tuples hne P)
  good := hgood _ (tupleRepresentative_mem tuples hne P)

omit [DecidableEq σ] in
lemma tuplePrimeFamily_product (tuples : Finset (σ→Ideal ActualEisensteinCubic.O)) (hne : tuples.Nonempty)
    (hmax : ∀ p∈tuples, ∀ i, (p i).IsMaximal)
    (hgood : ∀ p∈tuples, ∀ i, ConcretePrimeRowBridge.goodLambda∉p i) (P : Ideal ActualEisensteinCubic.O)
    (hP : P∈tuples.image slotTupleProduct) :
    (∏ i, (tuplePrimeFamily tuples hne hmax hgood P).ideal i)=P :=
  tupleRepresentative_product tuples hne P hP

omit [DecidableEq σ] in
lemma tuplePrimeFamily_at_product (tuples : Finset (σ→Ideal ActualEisensteinCubic.O)) (hne : tuples.Nonempty)
    (hmax : ∀ p∈tuples, ∀ i, (p i).IsMaximal)
    (hgood : ∀ p∈tuples, ∀ i, ConcretePrimeRowBridge.goodLambda∉p i)
    (hinj : Set.InjOn slotTupleProduct (↑tuples : Set (σ→Ideal ActualEisensteinCubic.O)))
    (p : σ→Ideal ActualEisensteinCubic.O) (hp : p∈tuples) :
    (tuplePrimeFamily tuples hne hmax hgood (slotTupleProduct p)).ideal=p :=
  tupleRepresentative_at_product tuples hne hinj p hp

end
end SevenEighths.InverseReflectedPhase

end OAI
