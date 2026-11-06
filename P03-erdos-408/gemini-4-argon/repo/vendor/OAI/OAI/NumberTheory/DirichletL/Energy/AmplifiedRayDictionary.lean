module

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

lemma active_pools_subset (s : Input α) (j : α⊕Fin 2) :
    (activeInput s).pools j⊆s.pools j := by
  cases j with
  | inl i => exact Finset.filter_subset _ _
  | inr j => exact Finset.Subset.refl _

lemma actualAllocations_mono {β : Type*} [Fintype β]
    (S T : β→Finset (Ideal O)) (h : ∀i,S i⊆T i) (C : Ideal O) :
    actualAllocations S C⊆actualAllocations T C := by
  intro B hB
  obtain ⟨hlabel,hprod⟩ := Finset.mem_filter.mp hB
  obtain ⟨v,hv,hvB⟩ := Finset.mem_image.mp hlabel
  refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨v,?_,hvB⟩,hprod⟩
  exact Fintype.mem_piFinset.mpr (fun i=>h i (Fintype.mem_piFinset.mp hv i))

abbrev restoreAllocation (s : Input α) (C : Ideal O)
    (B : actualAllocations (activeInput s).pools C) : actualAllocations s.pools C :=
  ⟨B.val,actualAllocations_mono _ _ (active_pools_subset s) C B.property⟩

@[simp] lemma restoreAllocation_val (s : Input α) (C : Ideal O)
    (B : actualAllocations (activeInput s).pools C) : (restoreAllocation s C B).val=B.val := rfl

lemma rowSlot_active (s : Input α) (i : α) (η : Character) (m A z : O) (t v : ℝ) :
    rowSlot η m A z ((activeInput s).slots i)
      (heightCoefficient ((activeInput s).toData.coefficient i) v) t=
    rowSlot η m A z (s.slots i) (heightCoefficient (s.toData.coefficient i) v) t := by
  unfold rowSlot
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro I hI hn
  have hz : s.W i ((I.absNorm:ℝ)/s.P i)=0 := by
    by_contra hh
    exact hn (Finset.mem_filter.mpr ⟨hI,hh⟩)
  simp only [heightCoefficient,Data.coefficient,activeInput,hz,mul_zero,zero_mul]

def restoredError (s : Input α) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) (Q : Ideal O) (k : ℕ)
    (Bp : actualAllocations (activeInput (child s C R B τ t)).pools (Q^k))
    (υ : Character) (v : ℝ) : Input (liveIndices Bp.val) :=
  twiceChild s C R B τ t Q k (restoreAllocation (child s C R B τ t) (Q^k) Bp) υ v

lemma error_source_active (s : Input α) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) (Q : Ideal O) (k : ℕ)
    (Bp : actualAllocations (activeInput (child s C R B τ t)).pools (Q^k))
    (υ : Character) (v : ℝ) :
    child (activeInput (child s C R B τ t)) (Q^k) (R*C) Bp υ v=
      activeInput (restoredError s C R B τ t Q k Bp υ v) := rfl

section Ray
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
variable {s : Input α} {η₀ : Character} {θ : α→RayQuotient.Characters M H}
  {w σ freq : α→ℝ} {W : ℝ→ℂ} {bslot Z : ℝ}

theorem matches_child (h : Matches M H hH s η₀ θ w σ freq W bslot Z)
    (C R : Ideal O) (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) :
    Matches M H hH (child s C R B τ t) η₀
      (fun i=>θ i.val) (fun i=>w i.val) (fun i=>σ i.val)
      (fun i=>freq i.val) W bslot Z := by
  constructor
  · intro i I;exact h.character i.val I
  · intro i y;exact h.profile i.val y
  · intro i;exact h.pool i.val
  · intro i;exact h.scale i.val

theorem matches_twiceChild (h : Matches M H hH s η₀ θ w σ freq W bslot Z)
    (C R : Ideal O) (B : actualAllocations s.pools C) (τ : Character) (t : ℝ)
    (Q : Ideal O) (k : ℕ)
    (Bp : actualAllocations (child s C R B τ t).pools (Q^k)) (υ : Character) (v : ℝ) :
    Matches M H hH (twiceChild s C R B τ t Q k Bp υ v) η₀
      (fun i=>θ i.val.val) (fun i=>w i.val.val) (fun i=>σ i.val.val)
      (fun i=>freq i.val.val) W bslot Z :=
  matches_child M H hH (matches_child M H hH h C R B τ t) (Q^k) (R*C) Bp υ v

theorem restoredError_matches (h : Matches M H hH s η₀ θ w σ freq W bslot Z)
    (C R : Ideal O) (B : actualAllocations s.pools C) (τ : Character) (t : ℝ)
    (Q : Ideal O) (k : ℕ)
    (Bp : actualAllocations (activeInput (child s C R B τ t)).pools (Q^k))
    (υ : Character) (v : ℝ) :
    Matches M H hH (restoredError s C R B τ t Q k Bp υ v) η₀
      (fun i=>θ i.val.val) (fun i=>w i.val.val) (fun i=>σ i.val.val)
      (fun i=>freq i.val.val) W bslot Z :=
  matches_twiceChild M H hH h C R B τ t Q k (restoreAllocation (child s C R B τ t) (Q^k) Bp) υ v

end Ray
end SevenEighths.CenteredMomentEnergyAmplifiedRayDictionary

end

end OAI
