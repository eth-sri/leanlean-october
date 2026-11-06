module
public import OAI.NumberTheory.DirichletL.Moments.CommonPrimeSlots
public import OAI.NumberTheory.DirichletL.Moments.SourceProfileMass
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentCommonProfile
open ActualEisensteinCubic CenteredMomentSourceProfileMass CenteredMomentAddedZeroUniform
open CenteredMomentCommonPrimeSlots CenteredMomentCommonAllocationBox
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

def liveIndices (B : Tuple ι) : Finset ι := Finset.univ.filter (fun i => B (Sum.inl i)=1)

def remainingTuple (B u : Tuple ι) : Tuple (liveIndices B) :=
  Sum.elim (fun i => u (Sum.inl i.val)) (fun j => u (Sum.inr j))

section
variable (B u : Tuple ι)
include B u
@[simp] theorem remainingTuple_slot (i : liveIndices B) :
    remainingTuple B u (Sum.inl i)=u (Sum.inl i.val) := rfl

@[simp] theorem remainingTuple_plain (j : Fin 2) :
    remainingTuple B u (Sum.inr j)=u (Sum.inr j) := rfl

theorem remaining_product
    (hf : ∀ i,B (Sum.inl i)≠1 → u (Sum.inl i)=1) :
    finiteTupleProduct u=finiteTupleProduct (remainingTuple B u) := by
  pm_162 finiteTupleProduct Fintype.prod_sum_type Fin.prod_univ_two remainingTuple Sum.elim_inl Sum.elim_inr
  rw [Finset.prod_coe_sort (liveIndices B) (fun i => u (Sum.inl i))]
  congr 1
  pm_3521 Finset.prod_subset i hi hnot
  apply hf i
  intro hBi
  grind

theorem slot_profiles_split
    (hf : ∀ i,B (Sum.inl i)≠1 → u (Sum.inl i)=1)
    (β : ι → Ideal O → ℂ) :
    (∏ i,β i (B (Sum.inl i)*u (Sum.inl i)))=
      (∏ i∈Finset.univ.filter (fun i => B (Sum.inl i)≠1),β i (B (Sum.inl i)))*
        ∏ i : liveIndices B,β i.val (u (Sum.inl i.val)) := by
  rw [Finset.prod_coe_sort (liveIndices B) (fun i => β i (u (Sum.inl i)))]
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i => B (Sum.inl i)=1)
    (fun i => β i (B (Sum.inl i)*u (Sum.inl i))),mul_comm]
  apply congrArg₂ (·*·)
  · apply Finset.prod_congr rfl
    intro i hi
    rw [hf i (Finset.mem_filter.mp hi).2,mul_one]
  · apply Finset.prod_congr rfl
    intro i hi
    rw [(Finset.mem_filter.mp hi).2,one_mul]

theorem profile_common_allocation (C R s : Ideal O)
    (hB : finiteTupleProduct B=C) (hsC : s∣C)
    (hf : ∀ i,B (Sum.inl i)≠1 → u (Sum.inl i)=1)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) :
    profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s (fun i => B i*u i)=
      ((∏ i∈Finset.univ.filter (fun i => B (Sum.inl i)≠1),
          ν i (B (Sum.inl i))*Wslot i ((Ideal.absNorm (B (Sum.inl i)):ℝ)/P i))*
        (if IsCoprime C R then 1 else 0))*
        profileCoefficient R (fun i : liveIndices B => ν i.val) (fun i => Wslot i.val) (fun i => P i.val)
          W₁ W₂ X₁ X₂ Y₁ Y₂ (B₁*B (Sum.inr 0)) (B₂*B (Sum.inr 1)) 1 (remainingTuple B u) := by
  have hprod : finiteTupleProduct (fun i => B i*u i)=C*finiteTupleProduct (remainingTuple B u) := by
    rw [finiteTupleProduct,Finset.prod_mul_distrib]
    change finiteTupleProduct B*finiteTupleProduct u=_
    rw [hB,remaining_product B u hf]
  have hdiv : s∣C*finiteTupleProduct (remainingTuple B u) := dvd_mul_of_dvd_left hsC _
  unfold profileCoefficient
  rw [slot_profiles_split B u hf (fun i I=> ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)),hprod]
  simp only [hdiv,ite_true,one_dvd,mul_one,remainingTuple_slot,remainingTuple_plain,
    IsCoprime.mul_left_iff]
  rw [mul_assoc B₁,mul_assoc B₂]
  by_cases hC : IsCoprime C R <;>
    by_cases hu : IsCoprime (finiteTupleProduct (remainingTuple B u)) R <;>
    simp_all only [true_and,false_and,ite_true,ite_false,mul_zero,zero_mul,mul_one]
  ring
end

end SevenEighths.CenteredMomentCommonProfile

end

end OAI
