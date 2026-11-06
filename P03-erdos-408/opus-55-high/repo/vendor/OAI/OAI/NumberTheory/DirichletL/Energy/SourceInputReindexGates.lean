module

public import OAI.NumberTheory.DirichletL.Moments.SourceInputReindex
public import OAI.NumberTheory.DirichletL.Moments.AllocatedRayDictionary
public import OAI.NumberTheory.DirichletL.Moments.FirstSecondInputGates
public import OAI.NumberTheory.DirichletL.Moments.FirstAnnularActiveInput
public import OAI.NumberTheory.DirichletL.Moments.FirstChildProfileControl

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical

namespace SevenEighths.CenteredMomentEnergySourceInputReindexGates
open CenteredMomentCommonRadialData
open CenteredMomentSourceInputReindex CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentAddedZeroUniform
local notation "O" => HeckeFamily.O
variable {α β : Type*} [Fintype α] [Fintype β]
local instance {κ : Type*} : DecidableEq κ := Classical.decEq _

section Dictionary
variable (M : Ideal HeckeFamily.O) [NeZero M]
local instance : Finite (HeckeFamily.O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (HeckeFamily.O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

end Dictionary

lemma allocationLabels_map (e : α≃β) (s : Input α) (C : Ideal HeckeFamily.O) :
    (allocationLabels s.pools C).image (tupleMap e)=
      allocationLabels (reindex e s).pools C := by
  unfold allocationLabels
  rw [←pools_map,Finset.image_image,Finset.image_image]
  congr 1

lemma actualAllocations_map (e : α≃β) (s : Input α) (C : Ideal HeckeFamily.O) :
    (actualAllocations s.pools C).image (tupleMap e)=
      actualAllocations (reindex e s).pools C := by
  change ((allocationLabels s.pools C).filter (fun B=>finiteTupleProduct B=C)).image (tupleMap e)=
    (allocationLabels (reindex e s).pools C).filter (fun B=>finiteTupleProduct B=C)
  rw [←allocationLabels_map e s C,Finset.filter_image]
  simp only [tupleMap_product]

def allocationEquiv (e : α≃β) (s : Input α) (C : Ideal HeckeFamily.O) :
    actualAllocations s.pools C ≃ actualAllocations (reindex e s).pools C where
  toFun B := ⟨tupleMap e B.val,by
    rw [←actualAllocations_map]
    exact Finset.mem_image.mpr ⟨B.val,B.property,rfl⟩⟩
  invFun B := ⟨(tupleMap e).symm B.val,by
    have hh : B.val∈(actualAllocations s.pools C).image (tupleMap e) := by
      simpa only [actualAllocations_map e s C] using B.property
    obtain ⟨v,hv,hvB⟩:=Finset.mem_image.mp hh
    simpa only [←hvB,Equiv.symm_apply_apply] using hv⟩
  left_inv B := Subtype.ext ((tupleMap e).symm_apply_apply B.val)
  right_inv B := Subtype.ext ((tupleMap e).apply_symm_apply B.val)

@[simp] lemma allocationEquiv_val (e : α≃β) (s : Input α) (C : Ideal HeckeFamily.O)
    (B : actualAllocations s.pools C) :
    (allocationEquiv e s C B).val=tupleMap e B.val := rfl

def liveEquiv (e : α≃β) (B : Tuple α) : liveIndices B ≃ liveIndices (tupleMap e B) where
  toFun i := ⟨e i.val,by
    simpa only [liveIndices,Finset.mem_filter,Finset.mem_univ,true_and,
      tupleMap_apply,Equiv.sumCongr_symm,Equiv.sumCongr_apply,Sum.map_inl,
      Equiv.symm_apply_apply] using (Finset.mem_filter.mp i.property).2⟩
  invFun j := ⟨e.symm j.val,by
    simpa only [liveIndices,Finset.mem_filter,Finset.mem_univ,true_and,
      tupleMap_apply,Equiv.sumCongr_symm,Equiv.sumCongr_apply,Sum.map_inl]
      using (Finset.mem_filter.mp j.property).2⟩
  left_inv i := Subtype.ext (e.symm_apply_apply i.val)
  right_inv j := Subtype.ext (e.apply_symm_apply j.val)

@[simp] lemma liveEquiv_val (e : α≃β) (B : Tuple α) (i : liveIndices B) :
    (liveEquiv e B i).val=e i.val := rfl

@[simp] lemma liveEquiv_symm_val (e : α≃β) (B : Tuple α)
    (j : liveIndices (tupleMap e B)) : ((liveEquiv e B).symm j).val=e.symm j.val := rfl

end SevenEighths.CenteredMomentEnergySourceInputReindexGates

end

end OAI
