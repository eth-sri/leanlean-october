module
public import OAI.NumberTheory.DirichletL.Descent.FirstGlobalSourceEnergy
public import OAI.NumberTheory.DirichletL.Descent.GlobalParentEnergy

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.InverseFirstGlobalParents
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic FirstCauchyArithmetic RayFourExpansion InverseMoment InverseFirstPriorityParents InverseMomentWholePriorityParents InverseWholePriorityValidSource InversePrioritySecondSource
open InverseInitialArithmetic (sourceIdeal)
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]

def ofOriginal (k : FirstOriginalOuter ι) : Source ι 0 where
  cube := k.1
  firstCommon := k.2.1
  firstDivisor := k.2.2
  quotientSupport := ∅
  oldAssigned := Fin.elim0

def toOriginal (x : Source ι 0) : FirstOriginalOuter ι :=
  ⟨x.cube,⟨x.firstCommon,x.firstDivisor⟩⟩

omit [DecidableEq ι] in
@[simp] theorem toOriginal_ofOriginal (k : FirstOriginalOuter ι) :
    toOriginal (ofOriginal k)=k := by cases k with | mk b k => cases k; rfl

omit [DecidableEq ι] in
@[simp] theorem toOriginal_fill (x : Source ι 0) (D : Finset ι) :
    toOriginal (fillFirstQuotient x D)=toOriginal x := rfl

omit [DecidableEq ι] in
theorem ofOriginal_injective : Function.Injective (ofOriginal (ι:=ι)) :=
  Function.LeftInverse.injective toOriginal_ofOriginal

def originalOuterSource (pool : Finset ι) (Q : Finset (ι→₀ℕ)) : Finset (Source ι 0) :=
  (firstOriginalOuter pool Q).image ofOriginal

def originalSelector (selector : FirstOriginalOuter ι→Finset ι→ℂ)
    (x : Source ι 0) (D : Finset ι) : ℂ := selector (toOriginal x) D

omit [DecidableEq ι] in
@[simp] theorem originalSelector_ofOriginal (selector : FirstOriginalOuter ι→Finset ι→ℂ)
    (k : FirstOriginalOuter ι) (D : Finset ι) :
    originalSelector selector (ofOriginal k) D=selector k D := by
  simp only [originalSelector,toOriginal_ofOriginal]

omit [DecidableEq ι] in
@[simp] theorem originalSelector_ofOriginal_fun (selector : FirstOriginalOuter ι→Finset ι→ℂ)
    (k : FirstOriginalOuter ι) : originalSelector selector (ofOriginal k)=selector k :=
  funext (originalSelector_ofOriginal selector k)

def originalParentSource (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (selector : FirstOriginalOuter ι→Finset ι→ℂ) : Finset (Source ι 0) :=
  globalParentSource (originalOuterSource pool Q) pool (originalSelector selector)

theorem mem_originalParentSource (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (selector : FirstOriginalOuter ι→Finset ι→ℂ) (x : Source ι 0) :
    x∈originalParentSource pool Q selector ↔
      ∃k∈firstOriginalOuter pool Q,∃D∈pool.powerset,
        selector k D≠0 ∧ fillFirstQuotient (ofOriginal k) D=x := by
  simp only [originalParentSource,globalParentSource,Finset.mem_biUnion,
    originalOuterSource,Finset.mem_image,Finset.mem_filter]
  constructor
  · rintro ⟨y,⟨k,hk,rfl⟩,D,⟨hD,hs⟩,he⟩
    exact ⟨k,hk,D,hD,by simpa using hs,he⟩
  · rintro ⟨k,hk,D,hD,hs,he⟩
    exact ⟨ofOriginal k,⟨k,hk,rfl⟩,D,⟨hD,by simpa using hs⟩,he⟩

theorem original_fill_valid (p : ι→O) (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (k : FirstOriginalOuter ι) (hk : k∈firstOriginalOuter pool Q) (D : Finset ι) :
    SourceValid p (fillFirstQuotient (ofOriginal k) D) := by
  obtain ⟨hb,hC,hE⟩:=(mem_firstOriginalOuter pool Q k).mp hk
  refine ⟨reopenedCubeFamily_admissible Q k.1 hb,?_,?_,?_⟩
  · exact Finset.disjoint_left.mpr (fun i hi hiB=>
      (Finset.mem_sdiff.mp (Finset.mem_powerset.mp hC hi)).2 hiB)
  · exact (Finset.mem_powerset.mp hE).trans
      (Finset.union_subset_union_right (Finset.filter_subset _ _))
  · exact fun i=>Fin.elim0 i
