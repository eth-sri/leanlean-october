module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Detector.LowSelectedSum

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical


abbrev LowUnselectedTuple {K } (slots : Fin K→Finset ActualEisensteinCubic.O) (J : Finset (Fin K)) :=
  ∀i : J,↥(slots i.val)
abbrev LowSelectedTuple {K } (slots : Fin K→Finset ActualEisensteinCubic.O) (J ) :=
  ∀i : SelectedSlot J,↥(slots i.val)

def lowSlotTupleEquiv {K : ℕ} (slots : Fin K→Finset ActualEisensteinCubic.O) (J : Finset (Fin K)) :
    (∀i,↥(slots i)) ≃ LowUnselectedTuple slots J×LowSelectedTuple slots J where
  toFun p := (fun i=>p i.val,fun i=>p i.val)
  invFun p i := if hi : i∈J then p.1 ⟨i,hi⟩ else p.2 ⟨i,by simp [hi]⟩
  left_inv p := by
    funext i
    dsimp only
    split_ifs <;> rfl
  right_inv p := by
    apply Prod.ext
    · funext i
      simp only [dite_eq_left i.property]
    grind

def lowSlotJoin {K } (slots ) (J : Finset (Fin K))
    (a : LowUnselectedTuple slots J) (b : LowSelectedTuple slots J) : Fin K→ActualEisensteinCubic.O :=
  fun i=>((lowSlotTupleEquiv slots J).symm (a,b) i).val

section
variable {K : ℕ} (slots : Fin K→Finset ActualEisensteinCubic.O) (hslots : ∀i x,x∈slots i→x≠0) (J : Finset (Fin K)) (a : LowUnselectedTuple slots J) (b : LowSelectedTuple slots J)

include hslots in
lemma lowSlotJoin_nonzero    
       
        (i : Fin K) :
    lowSlotJoin slots J a b i≠0 := hslots i _ ((lowSlotTupleEquiv slots J).symm (a,b) i).property

lemma lowSlotJoin_unselected      
        (i : J) :
    lowSlotJoin slots J a b i.val=(a i).val := by
  simp_all [lowSlotJoin, lowSlotTupleEquiv]

lemma lowSlotJoin_selected      
        (i : SelectedSlot J) :
    lowSlotJoin slots J a b i.val=(b i).val := by
  have hi : i.val∉J := (Finset.mem_sdiff.mp i.property).2
  simp_all [lowSlotJoin, lowSlotTupleEquiv]

lemma lowSlotJoin_unselectedProduct      
        :
    slotProduct (lowSlotJoin slots J a b) J=∏i : J,(a i).val := by
  unfold slotProduct
  rw [←Finset.prod_coe_sort J]
  simp only [lowSlotJoin_unselected]

lemma lowSlotJoin_selectedProduct      
        :
    slotProduct (lowSlotJoin slots J a b) (Finset.univ\J)=∏i : SelectedSlot J,(b i).val := by
  unfold slotProduct
  rw [←Finset.prod_coe_sort (Finset.univ\J)]
  simp only [lowSlotJoin_selected]

lemma lowSlotJoin_selectedFactor      
       
    (W : Fin K→ℝ→ℂ) (P : Fin K→ℝ)  t  :
    selectedSlotFactor W P (lowSlotJoin slots J a b) J t=
      ∏i : SelectedSlot J,W i.val (elementNorm (b i).val/P i.val)*
        FourierBridge.logPhase (-t) (Real.log (elementNorm (b i).val/P i.val)) := by
  unfold selectedSlotFactor
  simp only [lowSlotJoin_selected]

theorem sum_lowSlotJoin      
    (F : (Fin K→ActualEisensteinCubic.O)→ℂ) :
    (∑p : (∀i,↥(slots i)),F (fun i=>(p i).val))=
      ∑a : LowUnselectedTuple slots J,∑b : LowSelectedTuple slots J,F (lowSlotJoin slots J a b) := by
  calc
    _ = ∑p : LowUnselectedTuple slots J×LowSelectedTuple slots J,F (lowSlotJoin slots J p.1 p.2) :=
      (Equiv.sum_comp (lowSlotTupleEquiv slots J).symm (fun p=>F (fun i=>(p i).val))).symm
    _ = _ := Fintype.sum_prod_type _

end

end SevenEighths.ProbePhysical
end

end OAI
