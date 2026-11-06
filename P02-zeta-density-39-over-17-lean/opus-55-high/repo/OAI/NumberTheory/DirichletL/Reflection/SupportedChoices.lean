module
public import OAI.NumberTheory.DirichletL.Reflection.TupleMasks
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {σ φ : Type*} [Fintype σ] [DecidableEq σ]

def supportedSlotChoices (L : σ→ Finset (Ideal Eis)) (F : φ→ Ideal Eis) (K : Ideal Eis) :=
  {p : ∀ i,L i // IsCoprime K (∏ i,(p i).val) ∧ ∀ j i,(p i).val≠F j}

instance supportedSlotChoices_fintype (L : σ→ Finset (Ideal Eis)) (F : φ→ Ideal Eis) (K : Ideal Eis) :
    Fintype (supportedSlotChoices L F K) := inferInstanceAs (Fintype {_p : ∀ i,L i // _})

def supportedSlotSplit (L : σ→ Finset (Ideal Eis)) (T : Finset σ) (F : φ→ Ideal Eis) (K : Ideal Eis) :
    supportedSlotChoices L F K ≃
      supportedSlotChoices (fun i : {i // i∉T} => L i.val) F K ×
        supportedSlotChoices (fun i : T => L i.val) F K where
  toFun p :=
    let q := slotChoiceSplit L T p.val
    have h := (slot_choice_mask_split L T q.1 q.2 F K).mp (by simpa only [q,Prod.mk.eta,Equiv.symm_apply_apply] using p.property)
    (⟨q.2,h.1⟩,⟨q.1,h.2⟩)
  invFun q := ⟨(slotChoiceSplit L T).symm (q.2.val,q.1.val),
    (slot_choice_mask_split L T q.2.val q.1.val F K).mpr ⟨q.1.property,q.2.property⟩⟩
  left_inv p := by aesop
  right_inv q := by
    apply Prod.ext <;> apply Subtype.ext
    pm_7417 Prod.snd
    pm_7417 Prod.fst

end
end SevenEighths.InverseReflectedPhase

end OAI
