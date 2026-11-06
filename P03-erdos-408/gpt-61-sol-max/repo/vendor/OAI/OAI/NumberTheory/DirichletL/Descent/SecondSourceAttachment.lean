module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Descent.SecondPhysicalRecursive

@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondFibers
open InverseInitialArithmetic (sourceIdeal)
noncomputable section

variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]

@[ext] structure SecondParentSource (ι : Type*) (Jo : ℕ) where
  cube : CubeCoordinates ι
  firstCommon : Finset ι
  firstDivisor : Finset ι
  quotient : Ideal ActualEisensteinCubic.O
  oldAssigned : Fin Jo → SmoothMobiusCorrection.PrimeIdeal

def attachSecondExpansion {Jo : ℕ} (parent : SecondParentSource ι Jo)
    (x : SecondExpansionData ι) : MarkedSecondSource ι Jo 0 where
  cube := parent.cube
  firstCommon := parent.firstCommon
  firstDivisor := parent.firstDivisor
  second := x
  quotient := parent.quotient
  oldAssigned := parent.oldAssigned
  newAssigned := Fin.elim0

def secondParentOf {Jo : ℕ} (x : MarkedSecondSource ι Jo 0) : SecondParentSource ι Jo where
  cube := x.cube
  firstCommon := x.firstCommon
  firstDivisor := x.firstDivisor
  quotient := x.quotient
  oldAssigned := x.oldAssigned

omit [DecidableEq ι] in
theorem attachSecondExpansion_injective {Jo : ℕ} (parent : SecondParentSource ι Jo) :
    Function.Injective (attachSecondExpansion parent) := by
  intro x y h
  exact congrArg MarkedSecondSource.second h

omit [DecidableEq ι] in
theorem attachSecondExpansion_recover {Jo : ℕ} (x : MarkedSecondSource ι Jo 0) :
    attachSecondExpansion (secondParentOf x) x.second = x := by
  apply MarkedSecondSource.ext <;> try rfl
  funext i
  exact Fin.elim0 i

variable (p : ι → ActualEisensteinCubic.O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

def secondParentLabel {Jo } (parent : SecondParentSource ι Jo)  :=
  (∏ i∈parent.firstCommon,p i)*jLabel p parent.cube.support
    (fun i => parent.cube.leftExponent i+parent.cube.rightExponent i)
    parent.cube.leftBit parent.cube.rightBit

def secondParentDivisor {Jo } (parent : SecondParentSource ι Jo)  :=
  primeSubsetGenerator (fun i => Ideal.span {p i}) parent.firstDivisor

def secondParentPuncture {Jo } (m : ActualEisensteinCubic.O) (parent : SecondParentSource ι Jo)  :=
  (m*ConcretePrimeRowBridge.idealGenerator parent.quotient)*
    b0Label p parent.cube.support (fun i => parent.cube.leftExponent i+parent.cube.rightExponent i)
      parent.cube.leftBit parent.cube.rightBit*secondParentDivisor p parent


section
variable (hinj : Function.Injective (fun i => Ideal.span {p i})) (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1) {Jo : ℕ} (parent : SecondParentSource ι Jo) (x : SecondExpansionData ι) (source : Finset (SecondExpansionData ι)) (hE : ∀ x∈source,x.divisor ⊆ x.sourceCommon) (pool : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O) (z : SecondRayIndex)



include hinj hpr hE in
theorem secondExpansionSource_attached
     
     
       
       
           
    (slots₁ slots₂ : Finset σ)  lists₁ lists₂   a₁ a₂ 
     W₁ W₂   Φ   X Y  :
    secondExpansionSource p hp hcop hg pool Ψ (secondParentPuncture p m parent)
      (secondParentLabel p parent) (secondParentDivisor p parent) z source
      (fun U => primeMark slots₁ lists₁ a₁ U*W₁ (primeProductNorm p U/X))
      (fun U => primeMark slots₂ lists₂ a₂ U*W₂ (primeProductNorm p U/X)) Φ Y =
    (Y : ℂ)*secondRayCoefficient z *
      ∑ x∈source.image (attachSecondExpansion parent),
        actualSecondSignedWeight p hp hcop hg Ψ (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x *
          actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ m z)
            slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ Φ Y X := by
  have he := secondExpansionSource_signed_profile p hp hcop hg hinj hpr pool Ψ
    (secondParentPuncture p m parent) (secondParentLabel p parent) (secondParentDivisor p parent)
    z source hE ∅ ∅ slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ Φ X Y
  simp only [Finset.empty_union] at he
  rw [he]
  congr 1
  rw [Finset.sum_image (fun x hx y hy h => attachSecondExpansion_injective parent h)]
  rfl

end

end
end SevenEighths.InverseMoment

end OAI
