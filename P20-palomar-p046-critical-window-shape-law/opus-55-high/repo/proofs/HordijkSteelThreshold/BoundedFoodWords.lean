module

public import proofs.HordijkSteelThreshold.FoodWordParents
public import proofs.HordijkSteelThreshold.BinaryWordCode

@[expose] public section

namespace HordijkSteelThreshold

variable (L N : ℕ)

/-- The actual finite word-graph vertex domain: one food root and only
nonfood words inside the ambient cap. No parity condition above N is needed. -/
def BoundedFoodWord  :=
  {s : List Bool // s = [] ∨ (L < s.length ∧ s.length ≤ N)}

theorem boundedFoodWord_length_le {L N : ℕ} (v : BoundedFoodWord L N) :
    v.val.length ≤ N := by
  grind

instance boundedFoodWord_finite  : Finite (BoundedFoodWord L N) :=
  .of_injective (fun v => (⟨⟨v.val.length, by grind⟩, listWord v.val⟩ : Σ m : Fin $ N + 1, RAF.Polymer.Word m.val))
    fun u v h => Subtype.ext $ binaryWordCode_injective_length (congrArg (·.1.val) h) $ congrArg (·.2.val) h

noncomputable instance boundedFoodWord_fintype  : Fintype (BoundedFoodWord L N) :=
  Fintype.ofFinite _

def boundedFoodRoot  : BoundedFoodWord L N := ⟨[], Or.inl rfl⟩


def boundedFoodLeft {L N : ℕ} (v : BoundedFoodWord L N) : BoundedFoodWord L N :=
  ⟨foodWordLeft L v.val, by grind [foodWordLeft, boundedFoodWord_length_le]⟩

def boundedFoodRight {L N : ℕ} (v : BoundedFoodWord L N) : BoundedFoodWord L N :=
  ⟨foodWordRight L v.val, by grind [foodWordRight, boundedFoodWord_length_le]⟩

theorem boundedFoodParents_commute {L N : ℕ} (v : BoundedFoodWord L N) :
    boundedFoodLeft (boundedFoodRight v) = boundedFoodRight (boundedFoodLeft v) :=
  Subtype.ext $ foodWordParents_commute L v.val

theorem boundedFood_zero_height {L N : ℕ} (v : BoundedFoodWord L N)
    (h : foodWordHeight L v.val = 0) : v = boundedFoodRoot L N :=
  Subtype.ext (by have := v.property; grind [foodWordHeight, boundedFoodRoot])

end HordijkSteelThreshold
