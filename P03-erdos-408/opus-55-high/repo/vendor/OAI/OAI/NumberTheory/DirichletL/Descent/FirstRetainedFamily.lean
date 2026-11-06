module

public import OAI.NumberTheory.DirichletL.Descent.FirstPhysicalFamily

@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped Classical
open SecondPassArithmetic
noncomputable section
variable {ι : Type*} [DecidableEq ι]

def firstRetainedSource (p : ι→ActualEisensteinCubic.O) (labels : Finset (Ideal ActualEisensteinCubic.O)) (b : CubeCoordinates ι) (Y : ℝ) :
    Finset (Ideal ActualEisensteinCubic.O×ActualEisensteinCubic.O) :=
  labels.biUnion (fun f=> (nonzeroChildFrequencyBall
    (firstPhysicalMultiplier p b.support b.leftExponent b.rightExponent b.leftBit b.rightBit f) Y).image
      (fun h=>(f,h)))

theorem mem_firstRetainedSource (p : ι→ActualEisensteinCubic.O) (labels : Finset (Ideal ActualEisensteinCubic.O)) (b : CubeCoordinates ι) (Y : ℝ)
    (x : Ideal ActualEisensteinCubic.O×ActualEisensteinCubic.O) :
    x∈firstRetainedSource p labels b Y ↔ x.1∈labels ∧ x.2∈nonzeroChildFrequencyBall
      (firstPhysicalMultiplier p b.support b.leftExponent b.rightExponent b.leftBit b.rightBit x.1) Y := by
  rcases x with ⟨f,h⟩
  simp [firstRetainedSource]

theorem sum_firstRetainedSource {A : Type*} [AddCommMonoid A]
    (p : ι→ActualEisensteinCubic.O) (labels : Finset (Ideal ActualEisensteinCubic.O)) (b : CubeCoordinates ι) (Y : ℝ) (H : Ideal ActualEisensteinCubic.O×ActualEisensteinCubic.O→A) :
    ∑ x∈firstRetainedSource p labels b Y,H x =
    ∑ f∈labels,∑ h∈nonzeroChildFrequencyBall
      (firstPhysicalMultiplier p b.support b.leftExponent b.rightExponent b.leftBit b.rightBit f) Y,H (f,h) := by
  unfold firstRetainedSource
  rw [Finset.sum_biUnion]
  · simp
  · intro f hf g hg hfg
    apply Finset.disjoint_left.mpr
    grind

variable (p : ι→ActualEisensteinCubic.O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

end
end SevenEighths.InverseMoment

end OAI
