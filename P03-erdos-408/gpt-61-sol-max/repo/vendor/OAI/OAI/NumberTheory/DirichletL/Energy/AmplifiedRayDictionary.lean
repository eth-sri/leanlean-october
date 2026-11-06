module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Moments.FirstAnnularActiveInput
public import OAI.NumberTheory.DirichletL.Moments.AllocatedRayDictionary
public import OAI.NumberTheory.DirichletL.Moments.AmplificationChildSourceCaps

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyAmplifiedRayDictionary
open HeckeFamily CenteredMomentSecondHeightFamily CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentAmplificationChildInput
open CenteredMomentAmplificationChildSourceCaps CenteredMomentAllocatedRayDictionary
open CenteredMomentFirstAnnularInput CenteredMomentHeckeSlots CenteredMomentRetainedEnergy
open CenteredMomentInductionEnergy CenteredMomentCommonMaskEnergy
open CenteredMomentEligibleEnergy CenteredMomentCommonHeightEnvelope
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α]
local instance {β : Type*} : DecidableEq β := Classical.decEq _

lemma active_pools_subset (s : Input α)  j  :
    (activeInput s).pools j⊆s.pools j := by
  cases j with
  | inl i => exact Finset.filter_subset _ _
  | inr j => exact Finset.Subset.refl _

lemma actualAllocations_mono {β : Type*} [Fintype β]
    (S T : β→Finset (Ideal O)) (h : ∀i,S i⊆T i)  C  :
    actualAllocations S C⊆actualAllocations T C := by
  intro B hB
  obtain ⟨hlabel,hprod⟩ := Finset.mem_filter.mp hB
  obtain ⟨v,hv,hvB⟩ := Finset.mem_image.mp hlabel
  refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨v,?_,hvB⟩,hprod⟩
  grind

abbrev restoreAllocation (s : Input α) (C )
    (B : actualAllocations (activeInput s).pools C) : actualAllocations s.pools C :=
  ⟨B.val,actualAllocations_mono _ _ (active_pools_subset s) C B.property⟩

section
variable (s : Input α)
include s

@[simp] lemma restoreAllocation_val    C 
     B  : (restoreAllocation s C B).val=B.val := rfl

lemma rowSlot_active    i   η   m A z   t v  :
    rowSlot η m A z ((activeInput s).slots i)
      (heightCoefficient ((activeInput s).toData.coefficient i) v) t=
    rowSlot η m A z (s.slots i) (heightCoefficient (s.toData.coefficient i) v) t := by
  unfold rowSlot
  apply Finset.sum_subset (Finset.filter_subset _ _)
  simp_all [heightCoefficient, Data.coefficient, activeInput]

def restoredError (s : Input α) (C R ) (B )
    (τ ) (t ) (Q ) (k )
    (Bp : actualAllocations (activeInput (child s C R B τ t)).pools (Q^k))
    (υ : Character) (v : ℝ)  :=
  twiceChild s C R B τ t Q k (restoreAllocation (child s C R B τ t) (Q^k) Bp) υ v



end


variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
variable {s : Input α} {η₀ : Character} {θ : α→RayQuotient.Characters M H}
  {w σ freq : α→ℝ} {W : ℝ→ℂ} {bslot Z : ℝ}

section
variable (h : Matches M H hH s η₀ θ w σ freq W bslot Z) (C R : Ideal O) (B : actualAllocations s.pools C) (τ : Character) (t : ℝ)
include h C R B τ t

theorem matches_child  
            :
    Matches M H hH (child s C R B τ t) η₀
      (fun i=>θ i.val) (fun i=>w i.val) (fun i=>σ i.val)
      (fun i=>freq i.val) W bslot Z := by
  constructor
  · intro i I;exact h.character i.val I
  · intro i y;exact h.profile i.val y
  · intro i;exact h.pool i.val
  · intro i;exact h.scale i.val

section
variable (Q : Ideal O) (k : ℕ)
include Q k

theorem matches_twiceChild  
           
       
     Bp   υ   v  :
    Matches M H hH (twiceChild s C R B τ t Q k Bp υ v) η₀
      (fun i=>θ i.val.val) (fun i=>w i.val.val) (fun i=>σ i.val.val)
      (fun i=>freq i.val.val) W bslot Z :=
  matches_child M H hH (matches_child M H hH h C R B τ t) (Q^k) (R*C) Bp υ v

theorem restoredError_matches  
           
       
     Bp 
     υ   v  :
    Matches M H hH (restoredError s C R B τ t Q k Bp υ v) η₀
      (fun i=>θ i.val.val) (fun i=>w i.val.val) (fun i=>σ i.val.val)
      (fun i=>freq i.val.val) W bslot Z :=
  (by solve_by_elim [matches_twiceChild, restoreAllocation, child])

end

end


end SevenEighths.CenteredMomentEnergyAmplifiedRayDictionary

end

end OAI
