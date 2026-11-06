module
public import OAI.NumberTheory.DirichletL.Descent.FirstPhysicalFamily

@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
noncomputable section
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]

def firstRetainedSource (p : ι→O) (labels : Finset (Ideal O)) (b : CubeCoordinates ι) (Y : ℝ) :
    Finset (Ideal O×O) :=
  labels.biUnion (fun f=> (nonzeroChildFrequencyBall
    (firstPhysicalMultiplier p b.support b.leftExponent b.rightExponent b.leftBit b.rightBit f) Y).image
      (fun h=>(f,h)))

theorem mem_firstRetainedSource (p : ι→O) (labels : Finset (Ideal O)) (b : CubeCoordinates ι) (Y : ℝ)
    (x : Ideal O×O) :
    x∈firstRetainedSource p labels b Y ↔ x.1∈labels ∧ x.2∈nonzeroChildFrequencyBall
      (firstPhysicalMultiplier p b.support b.leftExponent b.rightExponent b.leftBit b.rightBit x.1) Y := by
  rcases x with ⟨f,h⟩
  simp [firstRetainedSource]

theorem sum_firstRetainedSource {A : Type*} [AddCommMonoid A]
    (p : ι→O) (labels : Finset (Ideal O)) (b : CubeCoordinates ι) (Y : ℝ) (H : Ideal O×O→A) :
    ∑ x∈firstRetainedSource p labels b Y,H x =
    ∑ f∈labels,∑ h∈nonzeroChildFrequencyBall
      (firstPhysicalMultiplier p b.support b.leftExponent b.rightExponent b.leftBit b.rightBit f) Y,H (f,h) := by
  unfold firstRetainedSource
  rw [Finset.sum_biUnion]
  simp_all
  · intro f hf g hg hfg
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨h,hh,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨k,hk,he⟩ := Finset.mem_image.mp hy
    grind

variable (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

end
end SevenEighths.InverseMoment

end OAI
