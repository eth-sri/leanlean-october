module
public import OAI.NumberTheory.DirichletL.Descent.Marks
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
noncomputable section
variable {σ ι : Type*} [DecidableEq σ] [DecidableEq ι]

def slotAssignmentWeight (I : Finset σ) (a : σ → ι → ℂ)
    (q : ∀ i ∈ I, ι) : ℂ := ∏ i ∈ I.attach, a i.val (q i.val i.property)

theorem primeMark_supported_assignments (I : Finset σ) (L : σ → Finset ι)
    (a : σ → ι → ℂ) (A : Finset ι) :
    primeMark I L a A = ∑ q ∈ I.pi (fun i => L i ∩ A), slotAssignmentWeight I a q := by
  simp only [primeMark,primeSlot,Finset.sum_ite_mem,slotAssignmentWeight]
  exact Finset.prod_sum I (fun i => L i ∩ A) a

theorem slotAssignmentWeight_norm_le_one (I : Finset σ) (L : σ → Finset ι)
    (a : σ → ι → ℂ) (A : Finset ι) (q : ∀ i ∈ I, ι)
    (hq : q ∈ I.pi (fun i => L i ∩ A))
    (ha : ∀ i ∈ I, ∀ p ∈ L i, ‖a i p‖ ≤ 1) : ‖slotAssignmentWeight I a q‖ ≤ 1 := by
  rw [slotAssignmentWeight,norm_prod]
  apply Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
  intro i _
  exact ha i.val i.property _ (Finset.mem_inter.mp (Finset.mem_pi.mp hq i.val i.property)).1

def indexedSlotAssignment (I : Finset σ) (q : ∀ i ∈ I, ι) : Fin I.card → ι :=
  fun j => q ((I.equivFin).symm j).val ((I.equivFin).symm j).property

omit [DecidableEq σ] [DecidableEq ι] in
theorem indexedSlotAssignment_injective (I : Finset σ) :
    Function.Injective (indexedSlotAssignment (ι:=ι) I) := by
  intro q r h
  funext i hi
  have he := congrFun h (I.equivFin ⟨i,hi⟩)
  simpa [indexedSlotAssignment] using he

theorem indexedSlotAssignment_support (I : Finset σ) (L : σ → Finset ι)
    (A : Finset ι) (q : ∀ i ∈ I, ι) (hq : q ∈ I.pi (fun i => L i ∩ A))
    (j : Fin I.card) :
    indexedSlotAssignment I q j ∈ L ((I.equivFin).symm j).val ∩ A :=
  Finset.mem_pi.mp hq _ _
