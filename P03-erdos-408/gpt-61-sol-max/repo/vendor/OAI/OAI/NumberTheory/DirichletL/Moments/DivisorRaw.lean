module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Moments.DivisorRows

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentDivisorRaw
open CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction CenteredMomentDivisorSlots
open CenteredMomentDivisorRectangle CenteredMomentDivisorRows CenteredMomentHeckeExpansion
open CenteredMomentHeckeSlots CenteredMomentHeckeHeight HeckeFamily

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def frozenIndices (D ) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))  :=
  Finset.univ.filter (fun i => (selectedPrimes D Finset.univ a (Sum.inl i)).Nonempty)

def liveIndices (D ) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))  :=
  Finset.univ.filter (fun i => ¬(selectedPrimes D Finset.univ a (Sum.inl i)).Nonempty)

theorem split_slot_product {M : Type*} [CommMonoid M] (D : Ideal ActualEisensteinCubic.O)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2))) (f : ι → M) :
    (∏ i∈frozenIndices D a,f i)*(∏ i∈liveIndices D a,f i)=∏ i,f i :=
  Finset.prod_filter_mul_prod_filter_not _ _ _

section
variable (η : Character) (m A z : ActualEisensteinCubic.O) (t : ℝ) (D : Ideal ActualEisensteinCubic.O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))

theorem selected_live_slot      
       
     i  (hi : i ∈ liveIndices D a)  S   β  :
    rowSlot η m A z S (fun I => if selectedSlot D a i∣I then β I else 0) t =
      rowSlot η m A z S β t := by
  have he := selectedDivisor_empty D Finset.univ a (Sum.inl i)
    (Finset.not_nonempty_iff_eq_empty.mp (Finset.mem_filter.mp hi).2)
  simp only [selectedSlot,he,one_dvd,ite_true]

theorem selected_frozen_slot_bound      
       
    (i : ι) (hi : i ∈ frozenIndices D a) (S : Finset (Ideal ActualEisensteinCubic.O))
    (hS : ∀ I∈S,Prime I) (β : Ideal ActualEisensteinCubic.O → ℂ)  M  (hM : 0 ≤ M)
    (hβ : ∀ I∈S,‖β I‖ ≤ M) :
    ‖rowSlot η m A z S (fun I => if selectedSlot D a i∣I then β I else 0) t‖ ≤ M := by
  obtain ⟨P,hP⟩ := (Finset.mem_filter.mp hi).2
  exact selected_slot_bound η m A z t (selectedSlot D a i) P
    (IdealMobiusDivisorSum.support_prime P.property) (Finset.dvd_prod_of_mem _ hP)
    S hS β M hM hβ

theorem selected_slot_product_bound      
       
    (S : ι → Finset (Ideal ActualEisensteinCubic.O)) (hS : ∀ i,∀ I∈S i,Prime I)
    (β : ι → Ideal ActualEisensteinCubic.O → ℂ) (M : ι → ℝ) (hM : ∀ i,0 ≤ M i)
    (hβ : ∀ i,∀ I∈S i,‖β i I‖ ≤ M i) :
    (∏ i,‖rowSlot η m A z (S i) (fun I => if selectedSlot D a i∣I then β i I else 0) t‖) ≤
      (∏ i∈frozenIndices D a,M i)*∏ i∈liveIndices D a,‖rowSlot η m A z (S i) (β i) t‖ := by
  rw [← split_slot_product D a]
  apply mul_le_mul
  · apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
    intro i hi
    solve_by_elim [selected_frozen_slot_bound]
  · apply le_of_eq
    apply Finset.prod_congr rfl
    simp_all [selected_live_slot]
  · exact Finset.prod_nonneg (fun _ _ => norm_nonneg _)
  · exact Finset.prod_nonneg (fun i _ => hM i)

end

def selectedNorm (D ) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))  :=
  (Ideal.absNorm (selectedPlain D a 0):ℝ)*(Ideal.absNorm (selectedPlain D a 1):ℝ)

section
variable (D : Ideal ActualEisensteinCubic.O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))

theorem selectedNorm_pos     :
    0 < selectedNorm D a := by
  apply mul_pos <;> exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
    (selectedDivisor_ne_zero D Finset.univ a _))

def rawRemaining (D ) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (T : ℝ) (P : ι → ℝ)  := (T/selectedNorm D a)*∏ i∈liveIndices D a,P i

def formalReductionFactor (D ) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (P : ι → ℝ)  := selectedNorm D a*∏ i∈frozenIndices D a,P i

theorem raw_scale_identity    
     T   P  :
    rawRemaining D a T P*formalReductionFactor D a P=T*∏ i,P i := by
  grind [rawRemaining, formalReductionFactor, split_slot_product, selectedNorm_pos]

end

end SevenEighths.CenteredMomentDivisorRaw

end

end OAI
