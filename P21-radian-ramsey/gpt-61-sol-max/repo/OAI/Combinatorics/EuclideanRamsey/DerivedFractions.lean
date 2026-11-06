/-
From openai/math (https://github.com/openai/math), commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, lean/OAI/Combinatorics/EuclideanRamsey/DerivedFractions.lean;
licensed under the Apache License, Version 2.0 (see LICENSES/Apache-2.0.txt and NOTICE).
Modified: ported to the Lean module system for Lean v4.35.0-rc2 / Mathlib v4.35.0-rc2 (this
notice, a `module` header, `public import`, `@[expose] public section`); subsequently
refactored and proof-compressed while preserving the main results.
-/
module

public import OAI.Combinatorics.EuclideanRamsey.PathFractions

@[expose] public section

namespace OAI.EuclideanRamsey






open scoped commutatorElement
variable {G : Type*} [Group G]

def Derived (N : Subgroup G) : ℕ → Subgroup G
  | 0 => N
  | n+1 => ⁅Derived N n,Derived N n⁆
instance derived_normal (N : Subgroup G) [N.Normal] (n : ℕ) : (Derived N n).Normal := by
  induction n with
  | zero => aesop
  | succ n ih => exact Subgroup.commutator_normal _ _
def PairCoverage {ι : Type*} (M : Submonoid (ι → G)) (N : Subgroup G) : Prop :=
  ∀ i j : ι,i≠j → ∀ a∈N,∀ b∈N,∃ z∈M,z i=a ∧ z j=b

theorem derived_subset_single (N : Subgroup G) [N.Normal] (n : ℕ) :
    ∀ (ι : Type*) [Fintype ι] [DecidableEq ι] (M : Submonoid (ι → G))
      (hd : HasDiagonal M) (_hi : PairInverse M) (_hc : PairCoverage M N),
      Fintype.card ι ≤ n+2 → ∀ i,Derived N n ≤ singleFractions M hd i := by
  induction n with
  | zero =>
    intro ι _ _ M hd _ hc hcard i a ha
    change RightFraction M (Pi.mulSingle i a)
    by_cases h : ∃ j : ι,j≠i
    · obtain ⟨j,hji⟩ := h
      obtain ⟨z,hz,hzi,hzj⟩ := hc i j (Ne.symm hji) a ha 1 N.one_mem
      have he : z=Pi.mulSingle i a := by
        ext l
        by_cases hli : l=i
        · subst l; simpa using hzi
        · have hlj : l=j := by
            by_contra hlj
            have := Fintype.two_lt_card_iff.mpr ⟨i,j,l,Ne.symm hji,Ne.symm hli,Ne.symm hlj⟩
            omega
          subst l
          simpa [Pi.mulSingle_eq_of_ne hli] using hzj
      exact ⟨z,hz,1,M.one_mem,by simpa using he.symm⟩
    · have he : (fun _ : ι => a)=Pi.mulSingle i a := by
        ext l
        have hl : l=i := by by_contra hh; exact h ⟨l,hh⟩
        simp [hl]
      exact ⟨_,hd a,1,M.one_mem,by simpa using he.symm⟩
  | succ n ih =>
    intro ι _ _ M hd hi hc hcard i
    by_cases hsmall : Fintype.card ι ≤ 2
    · exact (Subgroup.commutator_le_left _ _).trans (ih ι M hd hi hc (by omega) i)
    obtain ⟨j,hji,k,hki,hjk⟩ := Finset.one_lt_card.mp
      (show 1 < (Finset.univ.erase i).card by simp; omega)
    simp only [Finset.mem_erase,Finset.mem_univ,and_true] at hji hki
    have hkj := Ne.symm hjk
    change ⁅Derived N n,Derived N n⁆ ≤ _
    apply Subgroup.commutator_le.mpr
    intro a ha b hb
    have lift j (hji : j≠i) a (ha : a∈Derived N n) :
        ∃ z : ι → G,RightFraction M z ∧ z i=a ∧ ∀ l,l≠i → l≠j → z l=1 := by
      let κ := {l : ι // l≠j}
      let M' := M.map (MonoidHom.pi fun l : κ => Pi.evalMonoidHom (fun _ : ι => G) l.val)
      let i' : κ := ⟨i,Ne.symm hji⟩
      have hκ : Fintype.card κ ≤ n+2 := by
        have hh := Fintype.card_subtype_lt (p:=fun l : ι => l≠j) (x:=j) (by simp)
        change Fintype.card κ < Fintype.card ι at hh
        omega
      have hd' : HasDiagonal M' := fun g => ⟨fun _ => g,hd g,rfl⟩
      have hi' : PairInverse M' := by
        rintro u v _ ⟨w,hw,rfl⟩
        obtain ⟨b,hb,hu,hv⟩ := hi u.val v.val w hw
        exact ⟨_,⟨b,hb,rfl⟩,hu,hv⟩
      have hc' : PairCoverage M' N := by
        intro u v huv a ha b hb
        obtain ⟨z,hz,hu,hv⟩ := hc u.val v.val (fun he => huv (Subtype.ext he)) a ha b hb
        exact ⟨_,⟨z,hz,rfl⟩,hu,hv⟩
      obtain ⟨_,⟨u,hu,rfl⟩,_,⟨v,hv,rfl⟩,he⟩ := ih κ M' hd' hi' hc' hκ i' ha
      have he l : (u*v⁻¹) l.val = (Pi.mulSingle i' a : κ → G) l := (congrFun he l).symm
      refine ⟨u*v⁻¹,⟨u,hu,v,hv,rfl⟩,?_,?_⟩
      · simpa [i'] using he i'
      · intro l hli hlj
        have hh := he ⟨l,hlj⟩
        have hn : (⟨l,hlj⟩ : κ) ≠ i' := by intro he; exact hli (Subtype.mk.inj he)
        simpa [Pi.mulSingle_eq_of_ne hn] using hh
    obtain ⟨z,hz,hzi,hsz⟩ := lift j hji a ha
    obtain ⟨t,ht,hti,hst⟩ := lift k hki b hb
    have hsz' : ∀ l,l≠i → l≠j → z⁻¹ l=1 := by simpa using hsz
    have hst' : ∀ l,l≠i → l≠k → t⁻¹ l=1 := by simpa using hst
    have hh := ((hz.mul_pair hi ht i k hst).mul_pair hi hz.inv i j hsz').mul_pair hi ht.inv i k hst'
    have he : z*t*z⁻¹*t⁻¹ = Pi.mulSingle i ⁅a,b⁆ := by
      ext l
      by_cases hli : l=i <;> by_cases hlj : l=j <;> simp_all [commutatorElement_def]
    rwa [he] at hh

variable {X : Type*}
def freeAugmentation (X : Type*) : FreeGroup X →* Multiplicative ℤ :=
  FreeGroup.lift (fun _ => Multiplicative.ofAdd 1)
abbrev AugKernel (X : Type*) : Subgroup (FreeGroup X) := (freeAugmentation X).ker
lemma augmentation_kernel_le (x₀ : X) (Q : Subgroup (FreeGroup X)) [Q.Normal]
    (h : ∀ x y,(QuotientGroup.mk' Q) (FreeGroup.of x)=(QuotientGroup.mk' Q) (FreeGroup.of y)) :
    AugKernel X≤Q := by
  let q := QuotientGroup.mk' Q
  let t := q (FreeGroup.of x₀)
  let cy := zpowersHom _ t
  have he : q=cy.comp (freeAugmentation X) := by
    apply FreeGroup.ext_hom
    intro x
    simpa [cy,freeAugmentation,t,q] using h x x₀
  intro g hg
  apply (QuotientGroup.eq_one_iff _).mp
  change q g=1
  rw [he,MonoidHom.comp_apply]
  simpa using congrArg cy hg
end OAI.EuclideanRamsey
