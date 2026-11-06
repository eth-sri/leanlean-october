module

public import OAI.NumberTheory.DirichletL.Inversion.WholePriorityValidSource

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical SchwartzMap

namespace SevenEighths.InverseWholePriorityRetainedSource
open ActualEisensteinCubic SecondPassArithmetic
open InverseMoment InverseInitialArithmetic InverseFirstPriorityParents InversePrioritySecondSource
open InverseMomentWholePriorityParents InverseMomentWholePriorityPhysical
open RayFourExpansion InversePrincipalEnergy
variable {ι σ κ : Type*} [DecidableEq ι] [DecidableEq σ] [DecidableEq κ]
variable {Jo : ℕ} (p : ι→ActualEisensteinCubic.O) [∀ i,(Ideal.span {p i}).IsMaximal]

def unifiedSource (pool : Finset ι) (parents : Finset (SecondParentSource ι Jo))
    (R : SecondParentSource ι Jo→Finset ι→Finset ι→ℝ) :
    Finset (MarkedSecondSource ι Jo 0) :=
  attachedSecondFamily parents (fun y=>secondExpansionPool pool
    (fun G E=>(secondVariableCutoff p y (R y) G E).erase 0))

omit [∀ i,(Ideal.span {p i}).IsMaximal] in
theorem mem_unifiedSource (pool : Finset ι) (parents : Finset (SecondParentSource ι Jo))
    (R : SecondParentSource ι Jo→Finset ι→Finset ι→ℝ) (x : MarkedSecondSource ι Jo 0) :
    x∈unifiedSource p pool parents R ↔ secondParentOf x∈parents ∧
      x.second.sourceCommon⊆pool ∧ x.second.divisor⊆x.second.sourceCommon ∧
      x.second.overlap⊆pool ∧ x.second.frequency∈nonzeroChildFrequencyBall
        (actualSecondMultiplier p x) (R (secondParentOf x) x.second.sourceCommon x.second.divisor) := by
  rw [unifiedSource,mem_attachedSecondFamily,mem_secondExpansionPool]
  rfl

omit [∀ i,(Ideal.span {p i}).IsMaximal] in
theorem unified_frequency_ne_zero (pool : Finset ι) (parents : Finset (SecondParentSource ι Jo))
    (R : SecondParentSource ι Jo→Finset ι→Finset ι→ℝ) (x : MarkedSecondSource ι Jo 0)
    (hx : x∈unifiedSource p pool parents R) : x.second.frequency≠0 :=
  (Finset.mem_erase.mp ((mem_unifiedSource p pool parents R x).mp hx).2.2.2.2).1

omit [∀ i,(Ideal.span {p i}).IsMaximal] in

theorem unified_mem_sector
    (pool : Finset ι) (parents : Finset (SecondParentSource ι Jo))
    (R : SecondParentSource ι Jo→Finset ι→Finset ι→ℝ)
    (label : SecondParentSource ι Jo→Finset ι→SecondExpansionData ι→κ)
    (x : MarkedSecondSource ι Jo 0) (hx : x∈unifiedSource p pool parents R) :
    x∈retainedPool p pool parents R label (x.second.sourceCommon\x.second.divisor)
      (label (secondParentOf x) (x.second.sourceCommon\x.second.divisor) x.second) := by
  obtain ⟨hy,hz⟩ := (mem_attachedSecondFamily _ _ x).mp hx
  apply (mem_retainedPool p _ _ _ _ _ _ x).mpr
  exact ⟨hy,Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr (by grind),rfl⟩⟩

omit [∀ i,(Ideal.span {p i}).IsMaximal] in

theorem sectors_sum [Fintype κ]
    (pool : Finset ι) (parents : Finset (SecondParentSource ι Jo))
    (R : SecondParentSource ι Jo→Finset ι→Finset ι→ℝ)
    (label : SecondParentSource ι Jo→Finset ι→SecondExpansionData ι→κ)
    (H : MarkedSecondSource ι Jo 0→ℂ) :
    (∑ residual∈pool.powerset,∑ j : κ,∑ x∈retainedPool p pool parents R label residual j,H x)=
      ∑ x∈unifiedSource p pool parents R,H x := by
  simp only [retainedPool,unifiedSource,sum_attachedSecondFamily]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext j; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y hy
  rw [Finset.sum_comm]
  simp_rw [sum_secondDyadicSector]
  exact sum_secondExpansionSector pool _ _

omit [∀ i,(Ideal.span {p i}).IsMaximal] in

theorem parent_retained_sum [Fintype κ]
    (pool : Finset ι) (parents : Finset (SecondParentSource ι Jo))
    (R : SecondParentSource ι Jo→Finset ι→Finset ι→ℝ)
    (label : SecondParentSource ι Jo→Finset ι→SecondExpansionData ι→κ)
    (w : SecondParentSource ι Jo→ℂ) (H : MarkedSecondSource ι Jo 0→ℂ) :
    (∑ y∈parents,w y*(∑ residual∈pool.powerset,∑ j : κ,
      ∑ x∈(secondDyadicSector pool (secondVariableCutoff p y (R y)) residual (label y) j).image
        (attachSecondExpansion y),H x)) =
      ∑ x∈unifiedSource p pool parents R,w (secondParentOf x)*H x := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext residual; rw [Finset.sum_comm]
  simp_rw [←Finset.mul_sum,retained_sum]
  exact sectors_sum p pool parents R label _

theorem unified_conditions (hp : ∀ i,p i≠0)
    (extra : CubeCoordinates ι→Finset ι) (source : Finset (Source ι Jo))
    (hs : ∀ x∈source,SourceValid p x) (he : ∀ x∈source,extra x.cube⊆x.cube.support)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (pool : Finset ι)
    (R : SecondParentSource ι (Jo+(J.card+J.card))→Finset ι→Finset ι→ℝ) :
    ActualSecondSourceConditions p (unifiedSource p pool
      (wholeAssignedParents p (fun x=>extra x.cube) source negative J lists) R) := by
  apply whole_assigned_family_conditions p hp (fun x=>extra x.cube) source hs he negative J lists
  intro y hy x hx
  exact ((mem_secondExpansionPool _ _ x).mp hx).2.1

theorem unified_deleted_support
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (extra : CubeCoordinates ι→Finset ι) (source : Finset (Source ι Jo))
    (hs : ∀ x∈source,SourceValid p x) (he : ∀ x∈source,extra x.cube⊆x.cube.support)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (pool : Finset ι)
    (R : SecondParentSource ι (Jo+(J.card+J.card))→Finset ι→Finset ι→ℝ)
    (x : MarkedSecondSource ι (Jo+(J.card+J.card)) 0)
    (hx : x∈unifiedSource p pool (wholeAssignedParents p (fun x=>extra x.cube)
      source negative J lists) R) :
    ∀ i∈InverseMomentWholeRetainedSource.deleted p extra negative x,
      i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal ActualEisensteinCubic.O)∣x.quotient :=
  InverseMomentWholeRetainedSource.retained_deleted_support p hinj extra source hs he
    negative J lists pool R (fun _ _ _=>()) _ () x
    (unified_mem_sector p pool _ R (fun _ _ _=>()) x hx)

omit [DecidableEq σ] [∀ i,(Ideal.span {p i}).IsMaximal] in

theorem deleted_lists (extra : CubeCoordinates ι→Finset ι) (negative : Bool)
    (lists : σ→Finset ι) (x : MarkedSecondSource ι Jo 0) :
    residualLists p negative (fun i=>lists i\extra x.cube) (secondParentOf x)=
      fun i=>lists i\InverseMomentWholeRetainedSource.deleted p extra negative x := by
  funext i
  ext k
  simp only [residualLists,InverseMomentWholeRetainedSource.deleted,Finset.mem_sdiff,Finset.mem_union]
  tauto

def wholeRow (hp : ∀ i,p i≠0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (extra : CubeCoordinates ι→Finset ι) (pool : Finset ι) (negative : Bool)
    (Ψ : ActualEisensteinCubic.O→*ℂ) (m : ActualEisensteinCubic.O) (slots J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (V : ℝ→ℂ) (X Y : ℝ) (ray : SecondRayIndex) (x : MarkedSecondSource ι Jo 0) : ℂ :=
  retainedRow p hp hcop hg pool negative Ψ m slots J (fun i=>lists i\extra x.cube) a V X Y ray x

theorem wholeRow_eq (hp : ∀ i,p i≠0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (extra : CubeCoordinates ι→Finset ι) (pool : Finset ι) (negative : Bool)
    (Ψ : ActualEisensteinCubic.O→*ℂ) (m : ActualEisensteinCubic.O) (slots J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (V : ℝ→ℂ) (X Y : ℝ) (ray : SecondRayIndex) (x : MarkedSecondSource ι Jo 0) :
    wholeRow p hp hcop hg extra pool negative Ψ m slots J lists a V X Y ray x =
      actualSecondSignedWeight p hp hcop hg Ψ
        (m*ConcretePrimeRowBridge.idealGenerator x.quotient) ray x *
      actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ m ray)
        (slots\J) (slots\J)
        (fun i=>lists i\InverseMomentWholeRetainedSource.deleted p extra negative x)
        (fun i=>lists i\InverseMomentWholeRetainedSource.deleted p extra negative x)
        a a V V rowMajorant Y X := by
  unfold wholeRow retainedRow
  rw [deleted_lists]

theorem whole_retained_sum [Fintype κ] (hp : ∀ i,p i≠0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (extra : CubeCoordinates ι→Finset ι) (pool : Finset ι)
    (parents : Finset (SecondParentSource ι Jo)) (w : SecondParentSource ι Jo→ℂ)
    (negative : Bool) (Ψ : ActualEisensteinCubic.O→*ℂ) (m : ActualEisensteinCubic.O) (slots J : Finset σ)
    (lists : σ→Finset ι) (a : σ→ι→ℂ) (V : ℝ→ℂ) (X Y : ℝ)
    (R : SecondParentSource ι Jo→Finset ι→Finset ι→ℝ)
    (label : SecondParentSource ι Jo→Finset ι→SecondExpansionData ι→κ) :
    (∑ y∈parents,w y*(∑ ray : SecondRayIndex,∑ residual∈pool.powerset,∑ j : κ,
      (Y:ℂ)*secondRayCoefficient ray *
        ∑ x∈(secondDyadicSector pool (secondVariableCutoff p y (R y)) residual (label y) j).image
          (attachSecondExpansion y),
          retainedRow p hp hcop hg pool negative Ψ m slots J (fun i=>lists i\extra y.cube)
            a V X Y ray x)) =
    ∑ ray : SecondRayIndex,(Y:ℂ)*secondRayCoefficient ray *
      ∑ x∈unifiedSource p pool parents R,w (secondParentOf x)*
        wholeRow p hp hcop hg extra pool negative Ψ m slots J lists a V X Y ray x := by
  have hrow (y : SecondParentSource ι Jo) (ray : SecondRayIndex) (residual : Finset ι) (j : κ) :
      (∑ x∈(secondDyadicSector pool (secondVariableCutoff p y (R y)) residual (label y) j).image
          (attachSecondExpansion y),
          retainedRow p hp hcop hg pool negative Ψ m slots J (fun i=>lists i\extra y.cube)
            a V X Y ray x) =
      ∑ x∈(secondDyadicSector pool (secondVariableCutoff p y (R y)) residual (label y) j).image
          (attachSecondExpansion y),
          wholeRow p hp hcop hg extra pool negative Ψ m slots J lists a V X Y ray x := by
    apply Finset.sum_congr rfl
    intro x hx
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hx
    rfl
  simp_rw [hrow,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ray hray
  simp_rw [←Finset.mul_sum]
  simp_rw [mul_left_comm _ ((Y:ℂ)*secondRayCoefficient ray),←Finset.mul_sum]
  congr 1
  exact parent_retained_sum p pool parents R label w _

def coefficientBound : ℝ := 512*(32*512)

theorem coefficientBound_pos : 0<coefficientBound := by norm_num [coefficientBound]

variable (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem priorityOuter_norm (b : CubeCoordinates ι) (negative : Bool) (Ψ : ActualEisensteinCubic.O→*ℂ) (m : ActualEisensteinCubic.O)
    (selector : Finset ι→ℂ) (r : RayCharacter×RayCharacter) (core : FirstCoreIndex) (D : Finset ι)
    (hselector : ‖selector D‖≤1) (hΨ : ‖Ψ (∏ i∈D,p i)‖≤1) :
    ‖(priorityOuter p hg b negative Ψ m selector r core D:ℂ)‖≤coefficientBound := by
  have hr : ‖crossCoeff r.1 r.2‖≤512 :=
    (Finset.single_le_sum (by simp) (Finset.mem_univ r.2)).trans
      ((Finset.single_le_sum (fun j _=>by positivity)
        (Finset.mem_univ r.1)).trans crossCoeff_sum_norm_le)
  have hc : ‖firstCoreOuter p hg b.support (fun i=>b.leftExponent i+b.rightExponent i)
      b.leftBit b.rightBit negative Ψ m D core‖≤32*512 :=
    (Finset.single_le_sum (by simp)
      (Finset.mem_univ core)).trans
      (firstCoreOuter_mass p hg b.support _ b.leftBit b.rightBit negative Ψ m D hΨ)
  rw [Complex.norm_real,Real.norm_of_nonneg (by unfold priorityOuter; positivity)]
  unfold priorityOuter coefficientBound
  exact mul_le_mul ((mul_le_of_le_one_right (norm_nonneg _) hselector).trans hr) hc
    (norm_nonneg _) (by norm_num)

theorem fullPhysical_unified [Fintype κ] (hp : ∀ i,p i≠0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (extra : CubeCoordinates ι→Finset ι) (pool : Finset ι)
    (parents : Finset (SecondParentSource ι Jo)) (w : SecondParentSource ι Jo→ℂ)
    (negative : Bool) (Ψ : ActualEisensteinCubic.O→*ℂ) (m : ActualEisensteinCubic.O) (slots J : Finset σ)
    (lists : σ→Finset ι) (a : σ→ι→ℂ) (V : 𝓢(ℝ,ℂ)) (X Y : ℝ)
    (r : RayCharacter×RayCharacter) (core : FirstCoreIndex)
    (R : Finset ι→Finset ι→ℝ) (label : Finset ι→SecondExpansionData ι→κ) :
    let Ψ₀ := firstCoreTwist negative (if negative then r.1 else r.2) Ψ core
    let H := fun y : SecondParentSource ι Jo=>markedRadial p (slots\J)
      (residualLists p negative (fun i=>lists i\extra y.cube) y) a ∅ V X
    let K := fun y : SecondParentSource ι Jo=>secondVariableCutoff p y R
    (∑ y∈parents,w y*fullPhysical p hp hcop hg hinj extra pool negative Ψ m slots J lists a
      V X Y r core R label y) =
      (∑ y∈parents,w y*truncatedSecondZero p hg pool Ψ₀ (secondParentPuncture p m y)
        (secondParentLabel p y) (secondParentDivisor p y) (H y) rowMajorant Y (K y)) +
      (∑ ray : SecondRayIndex,(Y:ℂ)*secondRayCoefficient ray *
        ∑ x∈unifiedSource p pool parents (fun _=>R),w (secondParentOf x)*
          wholeRow p hp hcop hg extra pool negative Ψ₀ m slots J lists a V X Y ray x) +
      (∑ y∈parents,w y*secondSourceTail p hp hg hinj pool Ψ₀ (secondParentPuncture p m y)
        (secondParentLabel p y) (secondParentDivisor p y) (H y) rowMajorant Y (K y)) := by
  intro Ψ₀ H K
  simp only [fullPhysical,mul_add,Finset.sum_add_distrib]
  rw [whole_retained_sum p hp hcop hg extra pool parents w negative Ψ₀ m slots J lists a
    V X Y (fun _=>R) (fun _=>label)]

end SevenEighths.InverseWholePriorityRetainedSource

end

end OAI
