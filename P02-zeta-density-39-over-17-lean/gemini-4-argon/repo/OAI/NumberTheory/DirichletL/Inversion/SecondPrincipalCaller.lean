module
public import OAI.NumberTheory.DirichletL.Descent.FirstToSecond
public import OAI.NumberTheory.DirichletL.Descent.PrincipalChild

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
namespace SevenEighths.InverseSecondPrincipalCaller
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic FourierBridge SecondPassIntegration CompletedHeight InverseMoment InversePrincipalEnergy RayFourExpansion

def principalWindow (om : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a)
    (hs : Function.support om ⊆ Set.Icc a b) (negative : Bool) (t : ℝ) : 𝓢(ℝ,ℂ) :=
  if negative then conjugateProfile (uniformTwistedSchwartz om a b ha hs (om.smooth ⊤) t)
  else uniformTwistedSchwartz om a b ha hs (om.smooth ⊤) t

theorem principalWindow_apply (om : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a)
    (hs : Function.support om ⊆ Set.Icc a b) (negative : Bool) (t x : ℝ) :
    principalWindow om a b ha hs negative t x =
      if negative then normTwistedSource (fun y => star (om y)) (-t) x
      else normTwistedSource om t x := by
  cases negative <;> simp only [principalWindow,Bool.false_eq_true,ite_false,ite_true,
    conjugateProfile_apply,uniformTwistedSchwartz_apply,normTwistedSource,
    star_mul,logPhase_conjugate,mul_comm]

theorem principalWindow_norm (om : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a)
    (hs : Function.support om ⊆ Set.Icc a b) (negative : Bool) (t x : ℝ) :
    ‖principalWindow om a b ha hs negative t x‖=‖om x‖ := by
  rw [principalWindow_apply]
  cases negative <;> simp [normTwistedSource,logPhase_norm]

theorem principalWindow_support (om : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a)
    (hs : Function.support om ⊆ Set.Icc a b) (negative : Bool) (t : ℝ) :
    Function.support (principalWindow om a b ha hs negative t) = Function.support om := by
  ext x
  change (_≠0) ↔ (_≠0)
  rw [←norm_ne_zero_iff,principalWindow_norm,norm_ne_zero_iff]

theorem principalWindow_seminorm_zero (om : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a)
    (hs : Function.support om ⊆ Set.Icc a b) (negative : Bool) (t : ℝ) :
    SchwartzMap.seminorm ℝ 0 0 (principalWindow om a b ha hs negative t)=
      SchwartzMap.seminorm ℝ 0 0 om := by
  apply le_antisymm
  · apply SchwartzMap.seminorm_le_bound ℝ 0 0 _ (apply_nonneg _ _)
    intro x
    simpa only [pow_zero,one_mul,norm_iteratedFDeriv_zero,principalWindow_norm]
      using SchwartzMap.norm_le_seminorm ℝ om x
  · apply SchwartzMap.seminorm_le_bound ℝ 0 0 _ (apply_nonneg _ _)
    intro x
    simpa only [pow_zero,one_mul,norm_iteratedFDeriv_zero,principalWindow_norm]
      using SchwartzMap.norm_le_seminorm ℝ (principalWindow om a b ha hs negative t) x

theorem principalWindow_upper (om : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a)
    (hs : Function.support om ⊆ Set.Icc a b) (M : ℝ) (hb : b≤Real.exp M)
    (negative : Bool) (t x : ℝ) (hx : principalWindow om a b ha hs negative t x≠0) :
    x≤Real.exp M := by
  have hmem : x∈Function.support om := by
    rw [←principalWindow_support om a b ha hs negative t]
    exact hx
  exact (hs hmem).2.trans hb

section Arithmetic
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι→Eis) (hp : ∀ i,p i≠0)

include hp in

theorem whole_columnLog (D U : Finset ι) (hDU : Disjoint D U) (X : ℝ) :
    columnLog p (primeProductNorm p D*X) (D∪U)=Real.log (primeProductNorm p U/X) := by
  unfold columnLog
  rw [primeProductNorm_union p D U hDU,
    mul_div_mul_left _ _ (primeProductNorm_pos p hp D).ne']

omit [DecidableEq σ] in

theorem primeMark_union_of_lists_disjoint (slots : Finset σ) (lists : σ→Finset ι)
    (coeff : σ→ι→ℂ) (D U : Finset ι)
    (hD : ∀ i∈slots,Disjoint (lists i) D) :
    primeMark slots lists coeff (D∪U)=primeMark slots lists coeff U := by
  unfold primeMark
  apply Finset.prod_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro k hk
  have hh := Finset.disjoint_left.mp (hD i hi) hk
  simp only [Finset.mem_union,hh,false_or]

include hp in

theorem firstCoreTest_markedRadial (slots : Finset σ) (lists : σ→Finset ι)
    (coeff : σ→ι→ℂ) (D U : Finset ι) (hDU : Disjoint D U)
    (hD : ∀ i∈slots,Disjoint (lists i) D)
    (om : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a) (hs : Function.support om⊆Set.Icc a b)
    (negative : Bool) (X t : ℝ) (hX : 0<X) :
    firstCoreTest (primeMark slots lists coeff) (fun u=>om (Real.exp u))
      (columnLog p (primeProductNorm p D*X)) negative (-t) D U =
    markedRadial p slots lists coeff ∅ (principalWindow om a b ha hs negative t) X U := by
  have ht : ∀ y : ℝ,logPhase (-t) (-y)=logPhase t y := by
    intro y
    unfold logPhase
    congr 1
    push_cast
    ring
  simp only [firstCoreTest,primeMark_union_of_lists_disjoint slots lists coeff D U hD,
    whole_columnLog p hp D U hDU X,ht,
    Real.exp_log (div_pos (primeProductNorm_pos p hp U) hX),
    markedRadial,Finset.empty_union,principalWindow]
  cases negative <;> simp only [Bool.false_eq_true,ite_false,ite_true,
    conjugateProfile_apply,uniformTwistedSchwartz_apply,normTwistedSource,star_mul] <;> ring

variable [∀ i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem secondInputCoefficient_overlap_zero
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (Ψ : Eis→*ℂ) (m c d : Eis) (H : Finset ι→ℂ) (D U : Finset ι)
    (hDU : ¬Disjoint D U) :
    secondInputCoefficient p hg Ψ (m*∏ i∈D,p i) c d H U=0 := by
  rw [secondInputCoefficient_fixed_mask (p := p) (hg := hg),commonProduct_mask p hg hinj]
  split_ifs with h
  · exact (hDU h.symm).elim
  · exact zero_mul _

include hp in

theorem firstCoreTest_coefficient (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (slots : Finset σ) (lists : σ→Finset ι) (coeff : σ→ι→ℂ) (D U : Finset ι)
    (hD : ∀ i∈slots,Disjoint (lists i) D)
    (om : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a) (hs : Function.support om⊆Set.Icc a b)
    (negative : Bool) (X t : ℝ) (hX : 0<X) (Ψ : Eis→*ℂ) (m c d : Eis) :
    secondInputCoefficient p hg Ψ (m*∏ i∈D,p i) c d
      (firstCoreTest (primeMark slots lists coeff) (fun u=>om (Real.exp u))
        (columnLog p (primeProductNorm p D*X)) negative (-t) D) U =
    secondInputCoefficient p hg Ψ (m*∏ i∈D,p i) c d
      (markedRadial p slots lists coeff ∅ (principalWindow om a b ha hs negative t) X) U := by
  by_cases hd : Disjoint D U
  · unfold secondInputCoefficient
    rw [firstCoreTest_markedRadial p hp slots lists coeff D U hd hD om a b ha hs negative X t hX]
  · rw [secondInputCoefficient_overlap_zero p hg hinj Ψ m c d _ D U hd,
      secondInputCoefficient_overlap_zero p hg hinj Ψ m c d _ D U hd]
