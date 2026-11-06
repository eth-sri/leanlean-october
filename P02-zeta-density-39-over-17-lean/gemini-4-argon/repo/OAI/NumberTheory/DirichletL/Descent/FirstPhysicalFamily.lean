module
public import OAI.NumberTheory.DirichletL.Descent.FirstCanonicalEnergy
public import OAI.NumberTheory.DirichletL.Descent.FirstFamilySource

@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def firstCanonicalCoefficient (b : CubeCoordinates ι) (C : Finset ι)
    (negative : Bool) (Ψ : O→*ℂ) (m d : O) (H : Finset ι→ℂ) (x : Ideal O×O) : Finset ι→ℂ :=
  firstBareCubeCoefficient p hp hg hcop b.support (fun i=>b.leftExponent i+b.rightExponent i)
    b.leftBit b.rightBit negative
    (canonicalCubeResidual p hg b C negative Ψ m (ConcretePrimeRowBridge.idealGenerator x.1) H) d

theorem firstCanonicalCoefficient_old (b : CubeCoordinates ι) (C : Finset ι)
    (negative : Bool) (Ψ : O→*ℂ) (m d : O) (H : Finset ι→ℂ) (x : Ideal O×O) :
    firstCanonicalCoefficient p hp hcop hg b C negative Ψ m d H x =
      firstOldLabelCoefficient p hp hcop hg b.support (fun i=>b.leftExponent i+b.rightExponent i)
        b.leftBit b.rightBit negative
        (multiplicativeCoreColumn p Ψ m
          (fun U=>H (((if negative then b.rightDivisor else b.leftDivisor)∪C)∪U)))
        (∏i∈C,p i) d x.1 := rfl

lemma first_unblocked_physical (F : Finset ι) (C₁ C₂ : Finset ι→ℂ)
    (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (A₁ A₂ C R K : ℝ) (d h : O) :
    firstBlockedPhysicalRows p hg F (fun _=>1) C₁ C₂ W₁ W₂ Φ A₁ A₂ C R K d h =
      firstPhysicalCommonRows p hg F C₁ C₂ W₁ W₂ Φ A₁ A₂ C R K d h := by
  rw [firstPhysicalCommonRows_indexed]
  simp only [firstBlockedPhysicalRows,one_mul]
