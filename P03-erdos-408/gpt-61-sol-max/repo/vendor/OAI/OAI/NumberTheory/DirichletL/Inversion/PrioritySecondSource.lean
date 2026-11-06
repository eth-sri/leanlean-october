module

public import OAI.NumberTheory.DirichletL.Inversion.FirstPriorityParents
public import OAI.NumberTheory.DirichletL.Descent.SecondFullSource

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InversePrioritySecondSource
open ActualEisensteinCubic SecondPassArithmetic FirstPassCubeLabels FirstCauchyArithmetic
open InverseMoment InverseInitialArithmetic InverseFirstPriorityParents
open InversePrincipalEnergy InverseSecondPrincipalCaller RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
variable {ι σ κ : Type*} [DecidableEq ι] [DecidableEq σ] [DecidableEq κ]
variable {Jo : ℕ} (p : ι→O) [∀ i,(Ideal.span {p i}).IsMaximal]

def quotientSupport (y : SecondParentSource ι Jo)  :=
  Function.extend (sourceIdeal p) id (fun _=>∅) y.quotient

theorem quotientSupport_parent (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (x : Source ι Jo) : quotientSupport p (parent p x)=x.quotientSupport :=
  (sourceIdeal_injective p hinj).extend_apply _ _ _

omit [DecidableEq σ] in
theorem quotientSupport_attach (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (J : Finset σ) (q : Source ι Jo × ((∀ i∈J,ι)×(∀ i∈J,ι))) :
    quotientSupport p (attach p J q)=q.1.quotientSupport :=
  quotientSupport_parent p hinj q.1

def residualLists (negative : Bool) (lists : σ→Finset ι)
    (y : SecondParentSource ι Jo) (i : σ)  :=
  lists i \ (((if negative then y.cube.rightDivisor else y.cube.leftDivisor)∪y.firstCommon)∪
    quotientSupport p y)

omit [DecidableEq σ] [∀ i,(Ideal.span {p i}).IsMaximal] in
theorem residualLists_disjoint  negative  (lists : σ→Finset ι)
    (y : SecondParentSource ι Jo) (i : σ) :
    Disjoint (residualLists p negative lists y i) (quotientSupport p y) := by
  apply Finset.disjoint_left.mpr
  intro q hq hd
  exact (Finset.mem_sdiff.mp hq).2 (Finset.mem_union_right _ hd)

def retainedPool (pool : Finset ι) (parents : Finset (SecondParentSource ι Jo))
    (R : SecondParentSource ι Jo→Finset ι→Finset ι→ℝ)
    (label : SecondParentSource ι Jo→Finset ι→SecondExpansionData ι→κ)
    (residual : Finset ι) (j : κ)  :=
  attachedSecondFamily parents (fun y=>secondDyadicSector pool (secondVariableCutoff p y (R y))
    residual (label y) j)

omit [∀ i,(Ideal.span {p i}).IsMaximal] in
theorem mem_retainedPool (pool : Finset ι) (parents : Finset (SecondParentSource ι Jo))
    (R : SecondParentSource ι Jo→Finset ι→Finset ι→ℝ)
    (label : SecondParentSource ι Jo→Finset ι→SecondExpansionData ι→κ)
     residual   j  (x : MarkedSecondSource ι Jo 0) :
    x∈retainedPool p pool parents R label residual j ↔
      secondParentOf x∈parents ∧ x.second∈secondDyadicSector pool
        (secondVariableCutoff p (secondParentOf x) (R (secondParentOf x))) residual
        (label (secondParentOf x)) j := mem_attachedSecondFamily _ _ _

variable (hp : ∀ i,p i≠0)
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def parentPoisson (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (pool : Finset ι) (negative : Bool) (Ψ : O→*ℂ) (m : O)
    (slots J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (ω : ℝ→ℂ) (X t Y : ℝ) (r : RayCharacter×RayCharacter) (core : FirstCoreIndex)
    (y : SecondParentSource ι Jo)  :=
  firstFreshSecondPoisson p hp hg hinj pool (quotientSupport p y) y.cube.support
    (fun i=>y.cube.leftExponent i+y.cube.rightExponent i) y.cube.leftBit y.cube.rightBit negative
    (if negative then r.1 else r.2) Ψ m
    (primeMark (slots\J) (residualLists p negative lists y) a) ω X
    (∏ i∈y.firstCommon,p i) (secondParentDivisor p y) core t Y

def retainedRow (pool : Finset ι) (negative : Bool) (Ψ : O→*ℂ) (m : O)
    (slots J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (V : ℝ→ℂ) (X Y : ℝ) (ray : SecondRayIndex) (x : MarkedSecondSource ι Jo 0)  :=
  actualSecondSignedWeight p hp hcop hg Ψ
    (m*ConcretePrimeRowBridge.idealGenerator x.quotient) ray x *
    actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ m ray)
      (slots\J) (slots\J) (residualLists p negative lists (secondParentOf x))
      (residualLists p negative lists (secondParentOf x)) a a V V rowMajorant Y X

theorem parentPoisson_full [Fintype κ]
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (y : SecondParentSource ι Jo) (pool : Finset ι)
    (hq : y.quotient=sourceIdeal p (quotientSupport p y))
    (negative : Bool) (Ψ : O→*ℂ) (m : O)
    (slots J : Finset σ)  lists   a 
     om   lo hi   hlo   hs 
     X t Y  (hX : 0<X) (hY : 0<Y)  r   core 
     R   label  :
    let Ψ₀ := firstCoreTwist negative (if negative then r.1 else r.2) Ψ core
    let V := principalWindow om lo hi hlo hs negative t
    let H := markedRadial p (slots\J) (residualLists p negative lists y) a ∅ V X
    let K := secondVariableCutoff p y R
    parentPoisson p hp hg hinj pool negative Ψ m slots J lists a om X t Y r core y =
      truncatedSecondZero p hg pool Ψ₀ (secondParentPuncture p m y)
        (secondParentLabel p y) (secondParentDivisor p y) H rowMajorant Y K +
      (∑ ray : SecondRayIndex,∑ residual∈pool.powerset,∑ j : κ,
        (Y:ℂ)*secondRayCoefficient ray *
          ∑ x∈(secondDyadicSector pool K residual label j).image (attachSecondExpansion y),
            retainedRow p hp hcop hg pool negative Ψ₀ m slots J lists a V X Y ray x) +
      secondSourceTail p hp hg hinj pool Ψ₀ (secondParentPuncture p m y)
        (secondParentLabel p y) (secondParentDivisor p y) H rowMajorant Y K := by
  intro Ψ₀ V H K
  have hsum : (∑ ray : SecondRayIndex,∑ residual∈pool.powerset,∑ j : κ,
      (Y:ℂ)*secondRayCoefficient ray *
        ∑ x∈(secondDyadicSector pool K residual label j).image (attachSecondExpansion y),
          actualSecondSignedWeight p hp hcop hg Ψ₀
            (m*ConcretePrimeRowBridge.idealGenerator x.quotient) ray x *
          actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ₀ m ray)
            (slots\J) (slots\J) (residualLists p negative lists y) (residualLists p negative lists y)
            a a V V rowMajorant Y X) =
    ∑ ray : SecondRayIndex,∑ residual∈pool.powerset,∑ j : κ,
      (Y:ℂ)*secondRayCoefficient ray *
        ∑ x∈(secondDyadicSector pool K residual label j).image (attachSecondExpansion y),
          retainedRow p hp hcop hg pool negative Ψ₀ m slots J lists a V X Y ray x := by
    apply Finset.sum_congr rfl
    intro ray hray
    apply Finset.sum_congr rfl
    intro residual hresidual
    apply Finset.sum_congr rfl
    intro j hj
    apply congrArg ((Y:ℂ)*secondRayCoefficient ray * ·)
    apply Finset.sum_congr rfl
    intro x hx
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hx
    rfl
  have he := first_parent_full_second_source p hp hcop hg hinj hc hpr y pool (quotientSupport p y) hq
    negative (if negative then r.1 else r.2) Ψ m (slots\J) (residualLists p negative lists y) a
    (fun i _=>residualLists_disjoint p negative lists y i) om lo hi hlo hs X t Y hX hY core R label
  exact he.trans (congrArg (fun z : ℂ=>truncatedSecondZero p hg pool Ψ₀ (secondParentPuncture p m y)
    (secondParentLabel p y) (secondParentDivisor p y) H rowMajorant Y K + z +
    secondSourceTail p hp hg hinj pool Ψ₀ (secondParentPuncture p m y)
      (secondParentLabel p y) (secondParentDivisor p y) H rowMajorant Y K) hsum)

omit [∀ i,(Ideal.span {p i}).IsMaximal] in

theorem retained_sum
    (pool : Finset ι) (parents : Finset (SecondParentSource ι Jo))
    (R : SecondParentSource ι Jo→Finset ι→Finset ι→ℝ)
    (label : SecondParentSource ι Jo→Finset ι→SecondExpansionData ι→κ)
    (residual : Finset ι) (j : κ) (w : SecondParentSource ι Jo→ℂ)
    (H : MarkedSecondSource ι Jo 0→ℂ) :
    (∑ y∈parents,w y*∑ x∈(secondDyadicSector pool (secondVariableCutoff p y (R y))
      residual (label y) j).image (attachSecondExpansion y),H x) =
    ∑ x∈retainedPool p pool parents R label residual j,w (secondParentOf x)*H x := by
  rw [retainedPool,sum_attachedSecondFamily]
  apply Finset.sum_congr rfl
  intro y hy
  rw [Finset.sum_image (fun _ _ _ _ h=>attachSecondExpansion_injective y h),Finset.mul_sum]
  rfl

end SevenEighths.InversePrioritySecondSource

end

end OAI
